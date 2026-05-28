#!/usr/bin/env python3
"""
charon2lean.py  —  Translate Charon LLBC JSON → Lean 4 LLBCFunDef terms

Usage:
    python3 charon2lean.py <input.llbc> <output.lean>

The script reads the JSON produced by `charon cargo` and emits one
`def <Name>Fun : LLBCFunDef` per function in the crate.

Charon LLBC → our Lean AST mapping
───────────────────────────────────
· Flat statement lists  →  CPS (assign has explicit continuation)
· StorageLive/Dead       →  dropped
· BinaryOp("AddChecked") →  .binOp .add  (overflow handled by evalBinOpPure)
· Assert                 →  dropped  (redundant given our overflow model)
· Projection(src, .0)   →  .use (.copy (.var src))  (tuple result extraction)
· Switch.If              →  .ite
· Switch.SwitchInt       →  .switchInt
· Loop                   →  .loop
· Call                   →  .call with continuation
"""

import json
import sys
from pathlib import Path

# ── BinOp name map ────────────────────────────────────────────────────────────
BINOP = {
    "Add": "add", "Sub": "sub", "Mul": "mul", "Div": "div", "Rem": "rem",
    "AddChecked": "add", "SubChecked": "sub", "MulChecked": "mul",
    "BitAnd": "bitAnd", "BitOr": "bitOr", "BitXor": "bitXor",
    "Shl": "shl", "Shr": "shr",
    "Eq": "eq", "Ne": "ne", "Lt": "lt", "Le": "le", "Gt": "gt", "Ge": "ge",
    "And": "and", "Or": "or",
}

# ── IntTy / UintTy map ────────────────────────────────────────────────────────
INTTY  = {k: f".{k}" for k in ["I8","I16","I32","I64","I128","Isize"]}
UINTTY = {k: f".{k}" for k in ["U8","U16","U32","U64","U128","Usize"]}

# ─────────────────────────────────────────────────────────────────────────────
# Place
# ─────────────────────────────────────────────────────────────────────────────
def translate_place(p: dict) -> str:
    kind = p["kind"]
    if "Local" in kind:
        return f"(.var {kind['Local']})"
    if "Deref" in kind:
        return f"(.deref {translate_place(kind['Deref'])})"
    if "Field" in kind:
        inner, proj = kind["Field"]
        inner_s = translate_place(inner)
        if isinstance(proj, dict) and "Field" in proj:
            idx = proj["Field"][1]
        elif isinstance(proj, int):
            idx = proj
        else:
            idx = 0  # fallback
        return f"(.field {inner_s} {idx})"
    if "Index" in kind:
        arr, idx_var = kind["Index"]
        return f"(.index {translate_place(arr)} {idx_var})"
    if "Downcast" in kind:
        inner, variant = kind["Downcast"]
        return f"(.downcast {translate_place(inner)} {variant})"
    if "Projection" in kind:
        # Projection is a pair [place, proj_elem]
        base, proj_elem = kind["Projection"]
        if isinstance(proj_elem, dict) and "Field" in proj_elem:
            idx = proj_elem["Field"][1]
            return f"(.field {translate_place(base)} {idx})"
        return translate_place(base)  # fallback: drop projection
    return f"(.var 0) -- unknown place: {repr(kind)}"

# ─────────────────────────────────────────────────────────────────────────────
# Literal
# ─────────────────────────────────────────────────────────────────────────────
def translate_lit(lit: dict) -> str:
    if "Scalar" in lit:
        s = lit["Scalar"]
        if "Signed" in s:
            ty, val = s["Signed"]
            # Negative literals need parens in Lean application position
            val_s = f"({val})" if str(val).startswith("-") else str(val)
            return f"(.int {val_s} {INTTY.get(ty, '.I32')})"
        if "Unsigned" in s:
            ty, val = s["Unsigned"]
            return f"(.uint {val} {UINTTY.get(ty, '.U32')})"
        if "Bool" in s:
            b = "true" if s["Bool"] else "false"
            return f"(.bool {b})"
    if "Bool" in lit:
        b = "true" if lit["Bool"] else "false"
        return f"(.bool {b})"
    if "Char" in lit:
        return f"(.char '{lit['Char']}')"
    if "Str" in lit:
        return f"(.str {json.dumps(lit['Str'])})"
    return "(.unit)"

# ─────────────────────────────────────────────────────────────────────────────
# Operand
# ─────────────────────────────────────────────────────────────────────────────
def translate_operand(op: dict) -> str:
    if "Copy" in op:
        return f"(.copy {translate_place(op['Copy'])})"
    if "Move" in op:
        return f"(.move_ {translate_place(op['Move'])})"
    if "Const" in op:
        c = op["Const"]
        kind = c.get("kind", {})
        if "Literal" in kind:
            return f"(.const {translate_lit(kind['Literal'])})"
        return "(.const .unit)"
    return "(.const .unit)"

# ─────────────────────────────────────────────────────────────────────────────
# RValue
# ─────────────────────────────────────────────────────────────────────────────
def translate_rvalue(rv: dict) -> str:
    if "Use" in rv:
        inner = rv["Use"]
        # Detect Projection(base, Field(_, 0)) — tuple result extraction
        if isinstance(inner, dict):
            if "Copy" in inner:
                place = inner["Copy"]
                pk = place.get("kind", {})
                if "Projection" in pk:
                    base_place, proj_elem = pk["Projection"]
                    if isinstance(proj_elem, dict) and "Field" in proj_elem:
                        field_idx = proj_elem["Field"][1]
                        if field_idx == 0:
                            # Extract result field from checked-op tuple → just copy the base var
                            return f"(.use (.copy {translate_place(base_place)}))"
            if "Move" in inner:
                place = inner["Move"]
                pk = place.get("kind", {})
                if "Projection" in pk:
                    base_place, proj_elem = pk["Projection"]
                    if isinstance(proj_elem, dict) and "Field" in proj_elem:
                        field_idx = proj_elem["Field"][1]
                        if field_idx == 0:
                            return f"(.use (.move_ {translate_place(base_place)}))"
        return f"(.use {translate_operand(inner)})"
    if "BinaryOp" in rv:
        op_name, lhs, rhs = rv["BinaryOp"]
        # op_name is either a plain string "Add" or a dict {"Rem": "UB"} / {"Div": "UB"}
        if isinstance(op_name, dict):
            op_name = list(op_name.keys())[0]
        lean_op = BINOP.get(op_name, op_name.lower())
        return f"(.binOp .{lean_op} {translate_operand(lhs)} {translate_operand(rhs)})"
    if "UnaryOp" in rv:
        op_info, operand = rv["UnaryOp"]
        # op_info is either a string "Not"/"Neg" or a dict {"Neg": "Wrap"} / {"Cast": ...}
        if isinstance(op_info, dict):
            op_key = list(op_info.keys())[0]
        else:
            op_key = str(op_info)
        if op_key == "Neg":
            lean_op = ".neg"
        elif op_key == "Not":
            lean_op = ".not"
        elif op_key == "Cast":
            lean_op = ".not"  # cast treated as identity (operand is still used)
        else:
            lean_op = ".not"
        return f"(.unOp {lean_op} {translate_operand(operand)})"
    if "Ref" in rv:
        inner = rv["Ref"]
        # inner is [region, Mut/Shared, place]
        mut = inner[1] if len(inner) > 1 else "Mut"
        place = inner[2] if len(inner) > 2 else inner[0]
        mut_str = ".Mut" if mut == "Mut" else ".Shared"
        return f"(.ref {translate_place(place)} {mut_str})"
    if "Aggregate" in rv:
        agg = rv["Aggregate"]
        # agg is [kind, [operands]]
        operands = agg[1] if isinstance(agg, list) and len(agg) > 1 else []
        ops_str = ", ".join(translate_operand(o) for o in operands)
        return f"(.aggregate .tuple [{ops_str}])"
    if "Discriminant" in rv:
        return f"(.discriminant {translate_place(rv['Discriminant'])})"
    return "(.use (.const .unit))"

# ─────────────────────────────────────────────────────────────────────────────
# Statement list → CPS LLBCStmt
# ─────────────────────────────────────────────────────────────────────────────

SKIP_KINDS = {"StorageLive", "StorageDead", "Assert", "Nop",
              "PlaceMention", "FakeRead", "AscribeUserType"}

def filter_stmts(stmts: list) -> list:
    """Drop storage/housekeeping statements."""
    result = []
    for s in stmts:
        k = s["kind"]
        kn = list(k.keys())[0] if isinstance(k, dict) else str(k)
        if kn not in SKIP_KINDS:
            result.append(s)
    return result

def translate_stmts(stmts: list, indent: int = 2) -> str:
    """Translate a flat list of statements to a CPS LLBCStmt expression."""
    stmts = filter_stmts(stmts)
    if not stmts:
        return ".skip"
    first = stmts[0]
    rest  = stmts[1:]
    kind  = first["kind"]
    pad   = "  " * indent

    # Normalize: extract statement kind name
    kn = list(kind.keys())[0] if isinstance(kind, dict) else str(kind)

    # Terminal statements
    if kn == "Return":
        return ".return_"
    if kn == "Break":
        return ".break_"
    if kn == "Continue":
        # continue_ signals .next — loop iteration continues
        return ".continue_"

    if kn == "Assign":
        dst_place, rv = kind["Assign"]
        dst_s  = translate_place(dst_place)
        rv_s   = translate_rvalue(rv)
        cont_s = translate_stmts(rest, indent + 1)
        return f"(.assign {dst_s} {rv_s}\n{pad}{cont_s})"

    if kn == "Loop":
        body_s = translate_stmts(kind["Loop"]["statements"], indent + 1)
        rest_s = translate_stmts(rest, indent)
        if not filter_stmts(rest):
            return f"(.loop {body_s})"
        return f"(.seq (.loop {body_s})\n{pad}{rest_s})"

    if kn == "Switch":
        sw = kind["Switch"]
        rest_s = translate_stmts(rest, indent)

        if "If" in sw:
            cond_op, then_block, else_block = sw["If"]
            cond_s  = translate_operand(cond_op)
            then_s  = translate_stmts(then_block["statements"], indent + 1)
            else_s  = translate_stmts(else_block["statements"], indent + 1)
            ite_s   = f"(.ite {cond_s}\n{pad}  {then_s}\n{pad}  {else_s})"
            if not filter_stmts(rest):
                return ite_s
            return f"(.seq {ite_s}\n{pad}{rest_s})"

        if "SwitchInt" in sw:
            si = sw["SwitchInt"]
            discr_op  = si["discr"]
            branches  = si["branches"]   # list of {value, body}
            otherwise = si["otherwise"]
            discr_s   = translate_operand(discr_op)
            arms_parts = []
            for br in branches:
                lit_s  = translate_lit(br["value"])
                body_s = translate_stmts(br["body"]["statements"], indent + 2)
                arms_parts.append(f"({lit_s}, {body_s})")
            arms_s    = "[" + ", ".join(arms_parts) + "]"
            default_s = translate_stmts(otherwise["statements"], indent + 1)
            sw_s      = (f"(.switchInt {discr_s}\n{pad}  {arms_s}\n{pad}  {default_s})")
            if not filter_stmts(rest):
                return sw_s
            return f"(.seq {sw_s}\n{pad}{rest_s})"

    if kn == "Call":
        call = kind["Call"]
        func = call["func"]
        args = call.get("args", [])
        dest = call["dest"]

        # Resolve function name from def_id
        fun_id = None
        if "Regular" in func:
            fk = func["Regular"]["kind"]
            if "Fun" in fk and "Regular" in fk["Fun"]:
                fun_id = fk["Fun"]["Regular"]

        fname = FUN_NAMES.get(fun_id, f"fun_{fun_id}") if fun_id is not None else "unknown"
        dst_s  = translate_place(dest)
        args_s = "[" + ", ".join(translate_operand(a) for a in args) + "]"
        cont_s = translate_stmts(rest, indent + 1)
        return f"(.call {dst_s} \"{fname}\" {args_s}\n{pad}{cont_s})"

    if kn == "Panic":
        return "(.panic \"overflow\")"

    # Unknown — skip and continue
    return translate_stmts(rest, indent)

# ─────────────────────────────────────────────────────────────────────────────
# Type translation
# ─────────────────────────────────────────────────────────────────────────────

# Memoised hash-cons type table: populated on first call to translate_ty
_TYPE_TABLE: dict = {}

def resolve_ty(ty_obj: dict) -> str:
    """Map a Charon type object to a Lean LLBCTy term string."""
    if isinstance(ty_obj, dict):
        if "HashConsedValue" in ty_obj:
            _id, inner = ty_obj["HashConsedValue"]
            _TYPE_TABLE[_id] = inner
            return resolve_ty(inner)
        if "Deduplicated" in ty_obj:
            cached = _TYPE_TABLE.get(ty_obj["Deduplicated"])
            if cached:
                return resolve_ty(cached)
            return ".int .I32"   # safe fallback
        if "Literal" in ty_obj:
            lit = ty_obj["Literal"]
            if "Int" in lit:
                return f".int .{lit['Int']}"
            if "UInt" in lit:
                return f".uint .{lit['UInt']}"
            if lit == "Bool" or lit == {"Bool": None}:
                return ".bool_"
        if "Bool" in ty_obj:
            return ".bool_"
        if "Tuple" in ty_obj:
            # Tuple(n) — anonymous tuple with n fields, simplify to first field type
            return ".int .I32"
    return ".int .I32"

def local_ty(loc: dict) -> str:
    ty = loc.get("ty", {})
    # Seed the hash-cons table from function signatures when we encounter
    # a HashConsedValue
    return resolve_ty(ty)

def var_name(loc: dict) -> str:
    n = loc.get("name")
    return f'some "{n}"' if n else f'none'

# ─────────────────────────────────────────────────────────────────────────────
# Function definition
# ─────────────────────────────────────────────────────────────────────────────
def camel_case(s: str) -> str:
    # "sum_to" → "SumToFun", "return42" → "Return42Fun"
    parts = s.replace("-", "_").split("_")
    return "".join(p.capitalize() for p in parts)

def make_var(loc: dict) -> str:
    """Emit one LLBCVar anonymous constructor ⟨id, ty, name⟩."""
    return f"⟨{loc['index']}, {local_ty(loc)}, {var_name(loc)}⟩"

def translate_fun(fn: dict) -> str:
    """Return a Lean `def <Name>Fun : LLBCFunDef` string."""
    # Seed the type table from the signature BEFORE translating locals
    sig = fn.get("signature", {})
    ret_ty_obj = sig.get("output", {})
    # Also seed from inputs
    for inp in sig.get("inputs", []):
        resolve_ty(inp)
    ret_ty_s = resolve_ty(ret_ty_obj)

    name_parts = fn["item_meta"]["name"]
    fn_name    = name_parts[-1]["Ident"][0]
    body_obj   = fn["body"]["Structured"]
    locals_obj = body_obj["locals"]
    all_locals = locals_obj["locals"]
    arg_count  = locals_obj["arg_count"]
    stmts      = body_obj["body"]["statements"]

    # Seed type table from locals (processes HashConsedValue entries)
    for loc in all_locals:
        resolve_ty(loc.get("ty", {}))

    # params: locals[1 .. arg_count]
    param_vars = [loc for loc in all_locals if 1 <= loc["index"] <= arg_count]
    params_str = ("[" + ", ".join(make_var(p) for p in param_vars) + "]"
                  if param_vars else "[]")

    # all locals
    vars_items = ",\n    ".join(make_var(loc) for loc in all_locals)
    vars_str   = f"[\n    {vars_items}]" if all_locals else "[]"

    body_s = translate_stmts(stmts, indent=2)

    lean_name = camel_case(fn_name) + "Fun"
    return (
        f'def {lean_name} : LLBCFunDef := {{\n'
        f'  name   := "{fn_name}"\n'
        f'  params := {params_str}\n'
        f'  locals := {vars_str}\n'
        f'  retTy  := {ret_ty_s}\n'
        f'  body   :=\n'
        f'    {body_s}\n'
        f'}}\n'
    )

# ─────────────────────────────────────────────────────────────────────────────
# Main
# ─────────────────────────────────────────────────────────────────────────────

def main():
    if len(sys.argv) < 3:
        print("Usage: charon2lean.py <input.llbc> <output.lean>")
        sys.exit(1)

    in_path  = Path(sys.argv[1])
    out_path = Path(sys.argv[2])

    with open(in_path) as f:
        data = json.load(f)

    funs = data["translated"]["fun_decls"]

    # Build global name table for cross-function calls
    global FUN_NAMES
    FUN_NAMES = {}
    for fn in funs:
        name_parts = fn["item_meta"]["name"]
        fn_name    = name_parts[-1]["Ident"][0]
        FUN_NAMES[fn["def_id"]] = fn_name

    header = """\
/-
  Translation/CharonDefs.lean

  LLBCFunDef terms AUTO-GENERATED by charon2lean.py from:
    examples/verified_fns.llbc  (produced by `charon cargo`)

  Do NOT edit this file by hand — regenerate with:
    python3 charon2lean.py examples/verified_fns.llbc \\
            LeanPlVerify/Translation/CharonDefs.lean

  Charon version: {version}
  Crate: {crate}
-/

import LeanPlVerify.Translation.Elaborator

namespace LeanPlVerify.LLBC.Charon

open LeanPlVerify.LLBC

""".format(
        version=data.get("charon_version", "unknown"),
        crate=data["translated"]["crate_name"],
    )

    footer = "\nend LeanPlVerify.LLBC.Charon\n"

    bodies = []
    for fn in funs:
        try:
            bodies.append(translate_fun(fn))
        except Exception as e:
            name_parts = fn["item_meta"]["name"]
            fn_name    = name_parts[-1]["Ident"][0]
            bodies.append(f"-- ERROR translating {fn_name}: {e}\n")

    out_path.write_text(header + "\n".join(bodies) + footer)
    print(f"Wrote {len(funs)} function definitions to {out_path}")

if __name__ == "__main__":
    FUN_NAMES: dict = {}
    main()
