#!/usr/bin/env python3
"""Translate selected functions of src/shogi.c into the MiniC deep
embedding (formal/MiniC/Semantics.lean).

Forked from syoyo/tinygltf formal/tools/c2lean.py @ 97789b3 (MIT, see
formal/MiniC/LICENSE-MIT). Changes: source/output/function list for
tinyshogi, namespace MiniC, enumerators with implicit values.

Input is clang's fully type-annotated AST (-ast-dump=json), so every implicit
conversion is explicit. Struct layouts (field offsets, sizeof) are obtained
by compiling and running a probe program with the same compiler/target, so
they are the layouts the real compiler uses.

Anything outside the supported subset raises an error: the translator is
part of the trusted base and must never guess.

Usage:
    python3 formal/tools/c2lean.py            # regenerate
    python3 formal/tools/c2lean.py --check    # fail if output is stale
"""
import json
import os
import re
import struct
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = os.path.join(ROOT, "src", "shogi.c")
OUT = os.path.join(ROOT, "formal", "Shogi", "C", "Gen.lean")
CLANG = os.environ.get("CLANG", "clang")
TARGET = "x86_64-linux-gnu"

# Functions forming the verified core, in dependency order.
FUNCTIONS = [
    # T0/T7 layer 1: piece and square helpers (pure, scalar arguments).
    "shogi_piece",
    "shogi_piece_color",
    "shogi_piece_type",
    "shogi_is_promoted",
    "shogi_unpromoted_type",
    "shogi_can_promote",
    "promoted_type",
    "row_of",
    "col_of",
    "on_board",
    "square_at",
    "in_promotion_zone",
    "forced_promotion",
    "hand_index",
    "piece_letter",
    # T7 layer 2: attacks and king lookup (read the board and const tables).
    "step_piece_attacks",
    "step_square_attacked",
    "square_attacked",
    "shogi_piece_attacks_square",
    "find_king",
    "same_king_ray",
    "shogi_is_in_check",
    # T8: move generation.
    "add_move",
    "add_normal_move",
    "add_step",
    "add_slide",
    "add_pseudo_drops",
    "generate_pseudo_for_color",
    "generate_pseudo",
    "shogi_generate_pseudo",
    "shogi_generate_pseudo_for_color",
    # T9: legality filter (probe make/unmake, pins, uchifuzume).
    "king_safety_prepare",
    "same_move",
    "make_legal_probe",
    "unmake_legal_probe",
    "generate_legal_mut_internal",
    "shogi_generate_legal_mut",
    # T9: make / unmake (hash and history bookkeeping).
    "position_hash",
    "reset_history",
    "shogi_make_move_internal",
    "shogi_make_move",
    "shogi_make_move_undo_internal",
    "shogi_make_move_undo",
    "shogi_make_move_undo_fast",
    "shogi_unmake_move",
    "shogi_search_null_move",
    # T10: material, declaration, repetition.
    "validate_material",
    "declaration_points",
    "shogi_is_declaration_win",
    "shogi_repetition_result",
]

# Layout numbers exported as Lean constants (for building MiniC memories
# from positions in tests and proofs): (Lean name, C expression).
LAYOUT_EXPORTS = [
    ("sizeof_ShogiPosition", "sizeof(ShogiPosition)"),
    ("off_board", "offsetof(ShogiPosition, board)"),
    ("off_hand", "offsetof(ShogiPosition, hand)"),
    ("off_side", "offsetof(ShogiPosition, side)"),
    ("off_king_square", "offsetof(ShogiPosition, king_square)"),
    ("off_move_number", "offsetof(ShogiPosition, move_number)"),
    ("off_hash", "offsetof(ShogiPosition, hash)"),
    ("off_history_length", "offsetof(ShogiPosition, history_length)"),
    ("off_history", "offsetof(ShogiPosition, history)"),
    ("off_history_mover", "offsetof(ShogiPosition, history_mover)"),
    ("off_history_check", "offsetof(ShogiPosition, history_check)"),
    ("sizeof_ShogiUndo", "sizeof(ShogiUndo)"),
]

# File-scope `static const` objects the verified functions read. Each gets
# its own memory block; its initial bytes are dumped by the layout probe
# (compiled by the same clang), so they are the bytes the compiler emits.
GLOBALS = [
    "step_attack_probes",
    "step_attack_probe_count",
    "attack_rays",
    "attack_ray_length",
    "attack_ray_masks",
    # Filled once by shogi_init() and only read afterwards ("after-init"
    # globals): dumped by the probe after calling shogi_init(). The
    # translator rejects every store rooted at a global.
    "zobrist_board",
    "zobrist_hand",
    "zobrist_side",
    "fast_check_bookkeeping",
]
AFTER_INIT = {"zobrist_board", "zobrist_hand", "zobrist_side", "fast_check_bookkeeping"}
GLOBAL_BLOCK = 8192

# String literals live in one read-only block at this index.
LIT_BLOCK = 4096

INT_TYPES = {
    "unsigned char": (8, False), "signed char": (8, True), "char": (8, True),
    "unsigned short": (16, False), "short": (16, True),
    "unsigned int": (32, False), "int": (32, True),
    "unsigned long": (64, False), "long": (64, True),
    "unsigned long long": (64, False), "long long": (64, True),
    "_Bool": (8, False), "bool": (8, False),
}


def const_int(node):
    """Integer value of a constant expression node."""
    if isinstance(node, dict):
        if "value" in node and node["kind"] in ("ConstantExpr", "IntegerLiteral",
                                                "CharacterLiteral", "UnaryOperator"):
            try:
                return int(node["value"])
            except (TypeError, ValueError):
                pass
        if node["kind"] == "DeclRefExpr":
            ref = node.get("referencedDecl", {})
            if ref.get("kind") == "EnumConstantDecl" and ref.get("id") in ENUM_VALUES:
                return ENUM_VALUES[ref["id"]]
        if node["kind"] == "UnaryOperator" and node.get("opcode") == "-":
            return -const_int(node["inner"][0])
        if node["kind"] == "BinaryOperator" and node.get("opcode") == "+":
            return const_int(node["inner"][0]) + const_int(node["inner"][1])
        if node["kind"] == "BinaryOperator" and node.get("opcode") == "*":
            return const_int(node["inner"][0]) * const_int(node["inner"][1])
        for v in node.get("inner", []) or []:
            try:
                return const_int(v)
            except Unsupported:
                pass
    raise Unsupported("cannot evaluate case label")


# Enumerator values by declaration id (filled by collect_enums) and the
# typedef names of enum types (filled by collect_records).
ENUM_VALUES = {}
ENUM_TYPEDEFS = set()


class Unsupported(Exception):
    pass


def die(msg, node=None):
    loc = ""
    if node is not None:
        r = node.get("range", {}).get("begin", {})
        loc = f" (line {r.get('line', '?')})"
    raise Unsupported(msg + loc)


def ctype(node_or_type):
    t = node_or_type.get("type", node_or_type) if isinstance(node_or_type, dict) else node_or_type
    return t.get("desugaredQualType", t.get("qualType"))


def strip_quals(t):
    """Removes cv-qualifiers (`const`/`volatile`), including pointer-level
    ones such as `char *const`, and normalises spacing."""
    t = re.sub(r"\b(const|volatile|restrict|__restrict)\b", " ", t)
    t = re.sub(r"\s*\*\s*", "*", t)
    return re.sub(r"\s+", " ", t).strip()


class Ctx:
    def __init__(self, enums, layout):
        self.enums = enums
        self.layout = layout
        self.literals = []          # list of bytes strings
        self.used_globals = set()
        self.literal_offsets = {}   # bytes -> offset

    def literal(self, data):
        if data not in self.literal_offsets:
            self.literal_offsets[data] = sum(len(x) + 1 for x in self.literals)
            self.literals.append(data)
        return self.literal_offsets[data]

    def literal_bytes(self):
        out = []
        for x in self.literals:
            out.extend(x)
            out.append(0)
        return out


def int_ty(t, node=None, enums=None):
    t = strip_quals(t)
    if t in INT_TYPES:
        w, s = INT_TYPES[t]
        return w, s
    if t.startswith("enum ") or t in ENUM_TYPEDEFS:
        # The probe asserts that each enum typedef is a 32-bit unsigned type
        # (clang/GCC pick `unsigned int` when no enumerator is negative).
        if t in ENUM_TYPEDEFS:
            ENUM_CHECKS.add(t)
        return 32, False
    die(f"unsupported integer type '{t}'", node)


def lean_intty(w, s):
    return f"⟨{w}, {'true' if s else 'false'}⟩"


RECORDS = set()
ENUM_CHECKS = set()


def is_ptr(t):
    return strip_quals(t).endswith("*")


def is_struct(t):
    """True for struct/union types (not pointers to them)."""
    t = strip_quals(t)
    if t.endswith("*"):
        return False
    if t.startswith("struct ") or t.startswith("union "):
        return True
    return t in RECORDS


def scalar_ty(t, node=None):
    t = strip_quals(t)
    if t == "double":
        return ".f64"
    if t.endswith("*"):
        return ".ptr"
    w, s = int_ty(t, node)
    return f"(.int {lean_intty(w, s)})"


# Record field lists by type name (typedef or tag): [(field, type)].
RECORD_FIELDS = {}
# Functions returning a struct: translated with a hidden first parameter
# (pointer to the caller's result object), like the usual `sret` ABI.
SRET_FUNCS = set()

U64 = "⟨64, false⟩"
I32 = "⟨32, true⟩"


def strip_implicit(n):
    while n["kind"] in ("ParenExpr",) or (n["kind"] == "ImplicitCastExpr"
                                           and n["castKind"] in ("NoOp", "LValueToRValue")):
        n = n["inner"][0]
    return n


def is_array(t):
    return "[" in strip_quals(t)


def walk_nodes(n):
    if isinstance(n, dict):
        yield n
        for v in n.get("inner", []) or []:
            yield from walk_nodes(v)
        for key in ("cond", "body"):
            if isinstance(n.get(key), dict):
                yield from walk_nodes(n[key])


class FnTranslator:
    """Translates one function. Expressions are put in A-normal form: every
    call becomes a statement that assigns a fresh local, inserted before the
    statement that needs it (inside the conditional branch for `&&`, `||`
    and `?:`), so C's evaluation order and short-circuiting are kept and no
    call is ever evaluated inside an expression. Locals that are arrays,
    structs, or have their address taken live in memory blocks (`.alloc`).
    By-value struct parameters are copied by the callee on entry; struct
    results are written through a hidden first parameter."""

    def __init__(self, ctx, fn, fids):
        self.ctx = ctx
        self.fn = fn
        self.fids = fids
        self.vars = {}
        self.names = []
        self.loops = []
        self.pre = []
        self.ntmp = 0
        self.mem = set()
        self.sret = None

    def var_id(self, decl):
        key = decl.get("id") or decl["name"]
        if key not in self.vars:
            self.vars[key] = len(self.vars)
            self.names.append(decl["name"])
        return self.vars[key]

    def fresh(self, hint="t"):
        self.ntmp += 1
        return self.var_id({"id": f"__{hint}{self.ntmp}", "name": f"__{hint}{self.ntmp}"})

    def ref_var(self, ref, node):
        key = ref.get("id")
        if key in self.vars:
            return self.vars[key]
        die(f"reference to unknown local '{ref.get('name')}'", node)

    def emit(self, st):
        if not self.pre:
            die("internal: no statement context")
        self.pre[-1].append(st)

    def with_pre(self, f):
        self.pre.append([])
        out = f()
        pre = self.pre.pop()
        return pre, out

    def sizeof(self, t, node=None):
        return self.ctx.layout.sizeof(strip_quals(t), node)

    # ---- pre-scan --------------------------------------------------------
    def prescan(self):
        for n in walk_nodes(self.fn):
            if n.get("kind") in ("VarDecl", "ParmVarDecl") and n.get("type"):
                t = ctype(n)
                if is_array(t) or is_struct(t):
                    self.mem.add(n["id"])
            if n.get("kind") == "UnaryOperator" and n.get("opcode") == "&":
                x = strip_implicit(n["inner"][0])
                if x["kind"] == "DeclRefExpr" and x["referencedDecl"]["kind"] in ("VarDecl", "ParmVarDecl"):
                    self.mem.add(x["referencedDecl"]["id"])

    # ---- lvalues -------------------------------------------------------
    def lvalue(self, n):
        k = n["kind"]
        if k == "ParenExpr":
            return self.lvalue(n["inner"][0])
        if k == "DeclRefExpr":
            ref = n["referencedDecl"]
            if ref["kind"] == "VarDecl" and ref.get("id") not in self.vars:
                name = ref.get("name")
                if name not in GLOBALS:
                    die(f"reference to global '{name}' outside GLOBALS", n)
                if name not in AFTER_INIT and "const" not in n.get("type", {}).get("qualType", ""):
                    die(f"global '{name}' is not const", n)
                self.ctx.used_globals.add(name)
                return ("mem", f"(.const (.ptr {GLOBAL_BLOCK + GLOBALS.index(name)} 0))", ctype(n))
            if ref["kind"] in ("VarDecl", "ParmVarDecl"):
                vid = self.ref_var(ref, n)
                if ref["id"] in self.mem:
                    return ("mem", f"(.var {vid})", ctype(n))
                return ("var", vid)
            die(f"unsupported lvalue ref kind {ref['kind']}", n)
        if k == "MemberExpr":
            base = n["inner"][0]
            off = self.member_offset(n)
            if n["isArrow"]:
                return ("mem", f"(.field {self.rvalue(base)} {off})", ctype(n))
            lv = self.lvalue(base)
            if lv[0] != "mem":
                die("member of non-memory struct", n)
            return ("mem", f"(.field {lv[1]} {off})", ctype(n))
        if k == "StringLiteral":
            return ("mem", self.string_literal(n), ctype(n))
        if k == "ArraySubscriptExpr":
            base, idx = n["inner"]
            elem = self.sizeof(ctype(n), n)
            b = self.rvalue(base)
            i = self.rvalue(idx)
            return ("mem", f"(.index {b} {i} {elem})", ctype(n))
        if k == "UnaryOperator" and n["opcode"] == "*":
            return ("mem", self.rvalue(n["inner"][0]), ctype(n))
        if k == "CompoundLiteralExpr":
            t = ctype(n)
            tmp = self.fresh("lit")
            self.emit(f"(.alloc {tmp} {self.sizeof(t, n)})")
            self.init_mem(f"(.var {tmp})", t, n["inner"][0])
            return ("mem", f"(.var {tmp})", t)
        die(f"unsupported lvalue {k}", n)

    def member_offset(self, n):
        base = n["inner"][0]
        bt = strip_quals(ctype(base))
        if n["isArrow"]:
            if not bt.endswith("*"):
                die("arrow on non-pointer", n)
            bt = strip_quals(bt[:-1])
        return self.ctx.layout.offsetof(bt, n["name"], n)

    def addr_of_struct(self, n):
        """Address of a struct-valued expression (lvalue or compound literal)."""
        x = strip_implicit(n)
        lv = self.lvalue(x)
        if lv[0] != "mem":
            die("struct not in memory", n)
        return lv[1]

    # ---- initialisers ----------------------------------------------------
    def init_mem(self, addr, t, init):
        """Store an initialiser into zero-filled memory at `addr`."""
        t = strip_quals(t)
        k = init["kind"]
        if k == "ImplicitValueInitExpr":
            return
        if k == "InitListExpr":
            subs = init.get("inner", [])
            if is_array(t):
                for i, sub in enumerate(subs):
                    st = ctype(sub)
                    a = f"(.index {addr} (.const (.int {U64} {i})) {self.sizeof(st, sub)})"
                    self.init_mem(a, st, sub)
                return
            fields = RECORD_FIELDS.get(t)
            if fields is None:
                die(f"initialiser for unknown record {t}", init)
            for (fname, ft), sub in zip(fields, subs):
                off = self.ctx.layout.offsetof(t, fname, init)
                self.init_mem(f"(.field {addr} {off})", ft, sub)
            return
        if is_struct(t):
            self.emit(f"(.memcpy {addr} {self.addr_of_struct(init)} (.const (.int {U64} {self.sizeof(t, init)})))")
            return
        self.emit(f"(.store {scalar_ty(t, init)} {addr} {self.rvalue(init)})")

    # ---- rvalues -------------------------------------------------------
    def rvalue(self, n):
        k = n["kind"]
        if k == "ParenExpr":
            return self.rvalue(n["inner"][0])
        if k == "IntegerLiteral" or k == "CharacterLiteral":
            w, s = int_ty(ctype(n), n)
            v = int(n["value"]) % (1 << w)
            return f"(.const (.int {lean_intty(w, s)} {v}))"
        if k == "FloatingLiteral":
            if strip_quals(ctype(n)) != "double":
                die("non-double float literal", n)
            bits = struct.unpack("<Q", struct.pack("<d", float(n["value"])))[0]
            return f"(.const (.f64 {bits}))"
        if k == "DeclRefExpr":
            ref = n["referencedDecl"]
            if ref["kind"] == "EnumConstantDecl":
                v = self.ctx.enums[ref["id"]]
                w, s = int_ty(ctype(n), n)
                return f"(.const (.int {lean_intty(w, s)} {v % (1 << w)}))"
            die("DeclRefExpr used as rvalue without LValueToRValue", n)
        if k == "UnaryExprOrTypeTraitExpr" and n.get("name") == "sizeof":
            t = n.get("argType", {}).get("qualType") or ctype(n["inner"][0])
            return f"(.const (.int {U64} {self.sizeof(t, n)}))"
        if k in ("ImplicitCastExpr", "CStyleCastExpr"):
            ck = n["castKind"]
            inner = n["inner"][0]
            if ck == "LValueToRValue":
                if is_struct(ctype(n)):
                    die("struct value used in an expression", n)
                lv = self.lvalue(inner)
                if lv[0] == "var":
                    return f"(.var {lv[1]})"
                return f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
            if ck == "IntegralCast":
                w, s = int_ty(ctype(n), n)
                return f"(.cast {lean_intty(w, s)} {self.rvalue(inner)})"
            if ck in ("NoOp", "BitCast"):
                return self.rvalue(inner)
            if ck == "IntegralToBoolean":
                w, s_ = int_ty(ctype(inner), n)
                return (f"(.cast {lean_intty(8, False)} (.bin .ne (some {lean_intty(w, s_)}) "
                        f"{self.rvalue(inner)} (.const (.int {lean_intty(w, s_)} 0))))")
            if ck == "NullToPointer":
                return "(.const .null)"
            if ck == "ArrayToPointerDecay":
                if inner["kind"] == "StringLiteral":
                    return self.string_literal(inner)
                lv = self.lvalue(inner)
                if lv[0] != "mem":
                    die("decay of non-memory array", n)
                return lv[1]
            if ck == "FunctionToPointerDecay":
                die("function pointer", n)
            die(f"unsupported cast {ck}", n)
        if k == "BinaryOperator":
            op = n["opcode"]
            a, b = n["inner"]
            if op in ("&&", "||"):
                va = self.rvalue(a)
                pre_b, vb = self.with_pre(lambda: self.rvalue(b))
                form = "land" if op == "&&" else "lor"
                if not pre_b:
                    return f"(.{form} {va} {vb})"
                # `b` contains calls: evaluate it only on the branch that needs it
                tmp = self.fresh()
                one = f"(.const (.int {I32} 1))"
                zero = f"(.const (.int {I32} 0))"
                rhs = self.seq(pre_b + [f"(.set {tmp} (.{form} {zero if op == '||' else one} {vb}))"])
                if op == "&&":
                    self.emit(f"(.ite {va} {rhs} (.set {tmp} {zero}))")
                else:
                    self.emit(f"(.ite {va} (.set {tmp} {one}) {rhs})")
                return f"(.var {tmp})"
            ops = {"+": "add", "-": "sub", "*": "mul", "/": "div", "%": "mod",
                   "<<": "shl", ">>": "shr", "&": "band", "|": "bor", "^": "bxor",
                   "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "==": "eq", "!=": "ne"}
            if op not in ops:
                die(f"unsupported binary operator {op} in expression", n)
            if op in ("<", "<=", ">", ">=", "==", "!="):
                ot = strip_quals(ctype(a))
                if is_ptr(ot):
                    if op not in ("==", "!="):
                        die("ordered pointer comparison", n)
                    return f"(.bin .{ops[op]} none {self.rvalue(a)} {self.rvalue(b)})"
                t = "none" if ot == "double" else f"(some {lean_intty(*int_ty(ot, n))})"
            else:
                rt = strip_quals(ctype(n))
                if is_ptr(rt):
                    die("pointer arithmetic via +/-; use subscripts", n)
                t = f"(some {lean_intty(*int_ty(rt, n))})"
            return f"(.bin .{ops[op]} {t} {self.rvalue(a)} {self.rvalue(b)})"
        if k == "UnaryOperator":
            op = n["opcode"]
            a = n["inner"][0]
            if op == "!":
                return f"(.un .lnot {lean_intty(32, True)} {self.rvalue(a)})"
            if op == "-":
                return f"(.un .neg {lean_intty(*int_ty(ctype(n), n))} {self.rvalue(a)})"
            if op == "~":
                return f"(.un .bnot {lean_intty(*int_ty(ctype(n), n))} {self.rvalue(a)})"
            if op == "&":
                lv = self.lvalue(a)
                if lv[0] != "mem":
                    die("address of a register local", n)
                return lv[1]
            if op in ("++", "--"):
                lv = self.lvalue(a)
                cur = f"(.var {lv[1]})" if lv[0] == "var" else f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
                old = self.fresh()
                self.emit(f"(.set {old} {cur})")
                self.emit(self.incdec(lv, f"(.var {old})", n))
                if n.get("isPostfix"):
                    return f"(.var {old})"
                new = self.fresh()
                cur2 = f"(.var {lv[1]})" if lv[0] == "var" else f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
                self.emit(f"(.set {new} {cur2})")
                return f"(.var {new})"
            die(f"unsupported unary operator {op} in expression", n)
        if k == "ConditionalOperator":
            c, a, b = n["inner"]
            vc = self.rvalue(c)
            pa, va = self.with_pre(lambda: self.rvalue(a))
            pb, vb = self.with_pre(lambda: self.rvalue(b))
            if not pa and not pb:
                return f"(.cond {vc} {va} {vb})"
            tmp = self.fresh()
            self.emit(f"(.ite {vc} {self.seq(pa + [f'(.set {tmp} {va})'])} "
                      f"{self.seq(pb + [f'(.set {tmp} {vb})'])})")
            return f"(.var {tmp})"
        if k == "CallExpr":
            builtin = self.builtin_call(n)
            if builtin is not None:
                return builtin
            name, fid, args = self.call_parts(n)
            if name in SRET_FUNCS:
                die("struct-returning call used as a value", n)
            if strip_quals(ctype(n)) == "void":
                die("void call used as a value", n)
            tmp = self.fresh()
            self.emit(f"(.call (some {tmp}) {fid} [{', '.join(args)}])")
            return f"(.var {tmp})"
        if k in ("MemberExpr", "ArraySubscriptExpr"):
            lv = self.lvalue(n)
            if lv[0] != "mem":
                die(f"{k} of a non-memory object", n)
            if is_struct(lv[2]):
                die("struct value used in an expression", n)
            return f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
        if k == "StringLiteral":
            die("string literal used as a value", n)
        die(f"unsupported expression {k}", n)

    def incdec(self, lv, cur, n):
        w, s = int_ty(ctype(n), n)
        pw, ps = (32, True) if w < 32 else (w, s)
        op = "add" if n["opcode"] == "++" else "sub"
        val = (f"(.cast {lean_intty(w, s)} (.bin .{op} (some {lean_intty(pw, ps)}) "
               f"(.cast {lean_intty(pw, ps)} {cur}) (.const (.int {lean_intty(pw, ps)} 1))))")
        return self.assign(lv, val, n)

    def string_literal(self, n):
        data = n["value"].encode("utf-8")
        off = self.ctx.literal(data)
        return f"(.const (.ptr {LIT_BLOCK} {off}))"

    def callee_name(self, n):
        callee = n["inner"][0]
        while callee["kind"] in ("ImplicitCastExpr", "ParenExpr"):
            callee = callee["inner"][0]
        if callee["kind"] != "DeclRefExpr":
            return None
        return callee["referencedDecl"].get("name")

    def builtin_call(self, n):
        """C library calls and builtins used as values."""
        name = self.callee_name(n)
        if name is None:
            return None
        if name in ("memcmp", "__builtin_memcmp"):
            args = [self.rvalue(x) for x in n["inner"][1:]]
            return f"(.memcmp {args[0]} {args[1]} {args[2]})"
        if name in ("strlen", "__builtin_strlen"):
            args = [self.rvalue(x) for x in n["inner"][1:]]
            return f"(.strlen {args[0]})"
        if name == "abs":
            (x,) = [self.rvalue(x) for x in n["inner"][1:]]
            return (f"(.cond (.bin .lt (some {I32}) {x} (.const (.int {I32} 0))) "
                    f"(.un .neg {I32} {x}) {x})")
        if name == "__builtin_ctz":
            (x,) = [self.rvalue(x) for x in n["inner"][1:]]
            return f"(.un .ctz ⟨32, false⟩ {x})"
        if name in ("memset", "memcpy"):
            die(f"{name} used as a value", n)
        return None

    def call_parts(self, n, sret_ptr=None):
        callee = n["inner"][0]
        while callee["kind"] in ("ImplicitCastExpr", "ParenExpr"):
            callee = callee["inner"][0]
        if callee["kind"] != "DeclRefExpr" or callee["referencedDecl"]["kind"] != "FunctionDecl":
            die("indirect call", n)
        name = callee["referencedDecl"]["name"]
        if name not in self.fids:
            die(f"call to untranslated function {name}", n)
        args = []
        for x in n["inner"][1:]:
            if is_struct(ctype(x)):
                args.append(self.addr_of_struct(x))   # callee copies on entry
            else:
                args.append(self.rvalue(x))
        if name in SRET_FUNCS:
            if sret_ptr is None:
                die("struct-returning call without destination", n)
            args = [sret_ptr] + args
        return name, self.fids[name], args

    # ---- statements ----------------------------------------------------
    def assign(self, lv, rhs_lean, n):
        if lv[0] == "mem" and "(.const (.ptr " in lv[1]:
            die("store into a global or string literal", n)
        if lv[0] == "var":
            return f"(.set {lv[1]} {rhs_lean})"
        return f"(.store {scalar_ty(lv[2], n)} {lv[1]} {rhs_lean})"

    def stmt(self, n):
        pre, body = self.with_pre(lambda: self.stmt_core(n))
        return self.seq(pre + [body])

    def stmt_core(self, n):
        if not n:
            return ".skip"
        k = n["kind"]
        if k == "CompoundStmt":
            return self.seq([self.stmt(x) for x in n.get("inner", [])])
        if k == "NullStmt":
            return ".skip"
        if k == "DeclStmt":
            for d in n["inner"]:
                self.decl(d)
            return ".skip"
        if k == "ReturnStmt":
            if "inner" in n:
                e = n["inner"][0]
                if self.sret is not None:
                    size = self.sizeof(ctype(e), n)
                    self.emit(f"(.memcpy (.var {self.sret}) {self.addr_of_struct(e)} "
                              f"(.const (.int {U64} {size})))")
                    return "(.ret none)"
                return f"(.ret (some {self.rvalue(e)}))"
            return "(.ret none)"
        if k == "BreakStmt":
            return ".brk"
        if k == "ContinueStmt":
            return ".cont"
        if k == "IfStmt":
            inner = n["inner"]
            c = self.rvalue(inner[0])
            a = self.stmt(inner[1])
            b = self.stmt(inner[2]) if n.get("hasElse") else ".skip"
            return f"(.ite {c} {a} {b})"
        if k == "WhileStmt":
            c, body = n["inner"]
            pc, vc = self.with_pre(lambda: self.rvalue(c))
            return self.hoist(f"(.loop {self.seq(pc + [f'(.ite {vc} {self.stmt(body)} .brk)'])} .skip)")
        if k == "ForStmt":
            init, condvar, cond, inc, body = n["inner"]
            if condvar:
                die("for with condition variable", n)
            init_s = self.stmt(init) if init else ".skip"
            if cond:
                pc, vc = self.with_pre(lambda: self.rvalue(cond))
            else:
                pc, vc = [], "(.const (.int ⟨32, true⟩ 1))"
            body_s = self.stmt(body)
            inc_s = self.stmt(inc) if inc else ".skip"
            return self.seq([init_s, self.hoist(
                f"(.loop {self.seq(pc + [f'(.ite {vc} {body_s} .brk)'])} {inc_s})")])
        if k == "SwitchStmt":
            return self.switch(n)
        if k == "BinaryOperator" and n["opcode"] == ",":
            return self.seq([self.stmt(x) for x in n["inner"]])
        if k == "BinaryOperator" and n["opcode"] == "=":
            lhs, rhs = n["inner"]
            if is_struct(ctype(lhs)):
                dst = self.lvalue(lhs)[1]
                src = self.addr_of_struct(rhs)
                size = self.sizeof(ctype(lhs), n)
                return f"(.memcpy {dst} {src} (.const (.int {U64} {size})))"
            r = rhs
            while r["kind"] == "ParenExpr" or (r["kind"] == "ImplicitCastExpr" and r["castKind"] == "NoOp"):
                r = r["inner"][0]
            val = self.rvalue(rhs)
            lv = self.lvalue(lhs)
            return self.assign(lv, val, n)
        if k == "CompoundAssignOperator":
            lhs, rhs = n["inner"]
            ops = {"+=": "add", "-=": "sub", "*=": "mul", "|=": "bor", "&=": "band",
                   "^=": "bxor", "<<=": "shl", ">>=": "shr"}
            op = ops.get(n["opcode"]) or die(f"unsupported {n['opcode']}", n)
            ct = int_ty(ctype(n["computeResultType"]), n)
            lt = int_ty(ctype(lhs), n)
            rv = self.rvalue(rhs)
            lv = self.lvalue(lhs)
            cur = f"(.var {lv[1]})" if lv[0] == "var" else f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
            rhs_c = rv if op in ("shl", "shr") else f"(.cast {lean_intty(*ct)} {rv})"
            val = f"(.cast {lean_intty(*lt)} (.bin .{op} (some {lean_intty(*ct)}) (.cast {lean_intty(*ct)} {cur}) {rhs_c}))"
            return self.assign(lv, val, n)
        if k == "UnaryOperator" and n["opcode"] in ("++", "--"):
            lv = self.lvalue(n["inner"][0])
            cur = f"(.var {lv[1]})" if lv[0] == "var" else f"(.load {scalar_ty(lv[2], n)} {lv[1]})"
            return self.incdec(lv, cur, n)
        if k == "CallExpr":
            name = self.callee_name(n)
            if name in ("memset", "memcpy"):
                a = [self.rvalue(x) for x in n["inner"][1:]]
                if a[0].startswith("(.const (.ptr "):
                    die(f"{name} into a global or string literal", n)
                return f"(.{name} {a[0]} {a[1]} {a[2]})"
            if self.builtin_call(n) is not None:
                return ".skip"
            _, fid, args = self.call_parts(n)
            return f"(.call none {fid} [{', '.join(args)}])"
        if k in ("CStyleCastExpr",) and n["castKind"] == "ToVoid":
            return ".skip"
        die(f"unsupported statement {k}", n)

    def decl(self, d):
        if d["kind"] != "VarDecl":
            die("unsupported declaration", d)
        t = ctype(d)
        if d.get("storageClass") == "static":
            # a `static const` local is only read: an initialised copy per call
            # has the same behaviour
            if "const" not in d.get("type", {}).get("qualType", "") or not is_array(t):
                die("static local", d)
        vid = self.var_id(d)
        init = d["inner"][0] if "inner" in d else None
        if d["id"] in self.mem:
            self.emit(f"(.alloc {vid} {self.sizeof(t, d)})")
            if init is None:
                return
            ri = strip_implicit(init)
            if ri["kind"] == "CallExpr" and self.callee_name(ri) in SRET_FUNCS:
                _, fid, args = self.call_parts(ri, sret_ptr=f"(.var {vid})")
                self.emit(f"(.call none {fid} [{', '.join(args)}])")
                return
            self.init_mem(f"(.var {vid})", t, init)
            return
        if init is not None:
            self.emit(f"(.set {vid} {self.rvalue(init)})")

    def hoist(self, term):
        """Loops become named definitions so proofs can treat them opaquely."""
        name = f"{self.fn['name']}_loop{len(self.loops)}"
        self.loops.append((name, term))
        return name

    @staticmethod
    def terminates(node):
        while node is not None:
            k = node["kind"]
            if k in ("ReturnStmt", "BreakStmt"):
                return True
            if k == "CompoundStmt":
                inner = node.get("inner") or []
                node = inner[-1] if inner else None
                continue
            return False
        return False

    def switch(self, n):
        """`switch` with grouped case labels; supports fallthrough, `default`,
        and statements that follow a case label as siblings (e.g. `break`)."""
        cond, body = n["inner"][0], n["inner"][1]
        sel = self.rvalue(cond)
        st = lean_intty(*int_ty(ctype(cond), n))
        groups = []  # [labels, stmts]

        def absorb(node):
            labels = []
            while True:
                subs = node.get("inner", [])
                if node["kind"] == "DefaultStmt":
                    labels.append(None)
                    rest = subs
                else:
                    labels.append(const_int(subs[0]))
                    rest = subs[1:]
                if len(rest) == 1 and rest[0]["kind"] in ("CaseStmt", "DefaultStmt"):
                    node = rest[0]
                    continue
                return labels, list(rest)

        for c in body.get("inner", []):
            if c["kind"] in ("CaseStmt", "DefaultStmt"):
                labels, stmts = absorb(c)
                groups.append([labels, stmts])
            elif groups:
                groups[-1][1].append(c)
            else:
                die(f"statement before the first case label", c)
        if not groups:
            return ".skip"
        # break inside a case leaves the switch: translate each group body as a
        # one-shot loop so `.brk` exits it (and `continue` is rejected).
        bodies = []
        for _, stmts in groups:
            for x in stmts:
                for y in walk_nodes(x):
                    if y.get("kind") == "ContinueStmt":
                        die("continue inside switch", y)
            bodies.append(self.seq([self.stmt(x) for x in stmts] or [".skip"]))
        fall = [None] * len(groups)
        nxt = ".skip"
        for idx in range(len(groups) - 1, -1, -1):
            stmts = groups[idx][1]
            term = bool(stmts) and self.terminates(stmts[-1])
            fall[idx] = bodies[idx] if term else self.seq([bodies[idx], nxt])
            nxt = fall[idx]
        default = ".skip"
        for idx, (labels, _) in enumerate(groups):
            if None in labels:
                default = fall[idx]
        chain = default
        for idx in range(len(groups) - 1, -1, -1):
            for label in reversed([l for l in groups[idx][0] if l is not None]):
                chain = (f"(.ite (.bin .eq (some {st}) {sel} (.const (.int {st} {label}))) "
                         f"{fall[idx]} {chain})")
        # `break` statements in the chain exit this loop (one iteration)
        if any(y.get("kind") == "BreakStmt" for g in groups for x in g[1] for y in walk_nodes(x)
               if not self._inside_loop(x, y)):
            return f"(.loop (.seq {chain} .brk) .skip)"
        return chain

    @staticmethod
    def _inside_loop(root, target):
        """True if `target` lies inside a loop nested in `root`."""
        def go(n, in_loop):
            if n is target:
                return in_loop
            for v in n.get("inner", []) or []:
                if isinstance(v, dict):
                    r = go(v, in_loop or n.get("kind") in ("ForStmt", "WhileStmt", "DoStmt", "SwitchStmt"))
                    if r is not None:
                        return r
            return None
        return bool(go(root, False))

    def seq(self, items):
        items = [x for x in items if x != ".skip"]
        if not items:
            return ".skip"
        out = items[-1]
        for x in reversed(items[:-1]):
            out = f"(.seq {x} {out})"
        return out

    def translate(self):
        self.prescan()
        params = [x for x in self.fn["inner"] if x["kind"] == "ParmVarDecl"]
        pids = []
        if self.fn["name"] in SRET_FUNCS:
            self.sret = self.fresh("sret")
            pids.append(self.sret)
        pids += [self.var_id(p) for p in params]
        body = [x for x in self.fn["inner"] if x["kind"] == "CompoundStmt"][0]
        prologue = []
        for p in params:
            if p["id"] in self.mem:
                vid = self.vars[p["id"]]
                t = ctype(p)
                incoming = self.fresh("in")
                prologue.append(f"(.set {incoming} (.var {vid}))")
                prologue.append(f"(.alloc {vid} {self.sizeof(t, p)})")
                if is_struct(t):
                    prologue.append(f"(.memcpy (.var {vid}) (.var {incoming}) "
                                    f"(.const (.int {U64} {self.sizeof(t, p)})))")
                else:
                    prologue.append(f"(.store {scalar_ty(t, p)} (.var {vid}) (.var {incoming}))")
        b = self.stmt(body)
        return pids, self.seq(prologue + [b])


class Layout:
    """Field offsets and sizes, measured with the real compiler."""

    def __init__(self):
        self.queries = {q: None for _, q in LAYOUT_EXPORTS}
        self.results = None
        self.globals = list(GLOBALS)
        self.global_bytes = {}

    def _q(self, expr):
        if self.results is not None:
            if expr not in self.results:
                die(f"layout query {expr} missing after probing")
            return self.results[expr]
        self.queries[expr] = None
        return f"@@{expr}@@"

    def offsetof(self, rec, field, node=None):
        return self._q(f"offsetof({rec}, {field})")

    def sizeof(self, t, node=None):
        return self._q(f"sizeof({t})")

    def probe(self):
        with tempfile.TemporaryDirectory() as d:
            c = os.path.join(d, "probe.c")
            exe = os.path.join(d, "probe")
            with open(c, "w") as f:
                f.write(f'#include "{SRC}"\n#include <stddef.h>\n#include <stdio.h>\n')
                for t in sorted(ENUM_CHECKS):
                    f.write(f'_Static_assert(sizeof({t}) == 4 && ({t})-1 > 0, '
                            f'"{t} must be a 32-bit unsigned enum");\n')
                f.write("int main(void) {\n    shogi_init();\n")
                for q in self.queries:
                    f.write(f'    printf("%zu\\n", (size_t){q});\n')
                for g in self.globals:
                    f.write(f'    for (size_t i = 0; i < sizeof({g}); ++i) '
                            f'printf("%u ", (unsigned)((const unsigned char *)&{g})[i]);\n')
                    f.write('    printf("\\n");\n')
                f.write("    return 0;\n}\n")
            subprocess.check_call([CLANG, f"--target={TARGET}", "-std=c11", "-w",
                                   f"-I{ROOT}", "-o", exe, c])
            lines = subprocess.check_output([exe]).decode().splitlines()
        nq = len(self.queries)
        self.results = dict(zip(self.queries, (int(v) for v in lines[:nq])))
        self.global_bytes = {g: [int(x) for x in line.split()]
                             for g, line in zip(self.globals, lines[nq:])}


def load_ast():
    out = subprocess.check_output(
        [CLANG, "-Xclang", "-ast-dump=json", "-fsyntax-only", "-std=c11",
         f"--target={TARGET}", f"-I{ROOT}", SRC], stderr=subprocess.DEVNULL)
    return json.loads(out)


def collect_enums(ast):
    enums = {}

    def walk(n):
        if isinstance(n, dict):
            if n.get("kind") == "EnumDecl":
                # C11 6.7.2.2p3: an enumerator without '=' is previous + 1
                # (the first is 0). clang only annotates explicit values.
                value = -1
                for k in n.get("inner", []):
                    if k.get("kind") == "EnumConstantDecl":
                        inner = k.get("inner")
                        value = int(inner[0]["value"]) if inner else value + 1
                        enums[k["id"]] = value
                        ENUM_VALUES[k["id"]] = value
            for v in n.get("inner", []):
                walk(v)
    walk(ast)
    return enums


def collect_records(ast):
    """Names of struct/union types (tags and typedefs of records), their
    field lists, and the functions that return a struct."""
    by_id = {}
    for n in walk_nodes(ast):
        if n.get("kind") == "RecordDecl":
            by_id[n["id"]] = n
    for n in walk_nodes(ast):
        if n.get("kind") == "TypedefDecl":
            for x in walk_nodes(n):
                if x.get("kind") == "RecordType" and x.get("decl", {}).get("id") in by_id:
                    rec = by_id[x["decl"]["id"]]
                    RECORD_FIELDS[n["name"]] = [(f["name"], ctype(f)) for f in rec.get("inner", [])
                                               if f.get("kind") == "FieldDecl"]
                    break
    for n in walk_nodes(ast):
        if n.get("kind") == "FunctionDecl":
            ret = n.get("type", {}).get("qualType", "").split("(")[0].strip()
            if ret in RECORD_FIELDS or ret.startswith("struct "):
                SRET_FUNCS.add(n["name"])
    def walk(n):
        if isinstance(n, dict):
            k = n.get("kind")
            if k in ("RecordDecl", "CXXRecordDecl") and n.get("name"):
                RECORDS.add(n["name"])
            if k == "TypedefDecl" and n.get("name"):
                inner = n.get("inner") or []
                t = inner[0].get("type", {}).get("qualType", "") if inner else ""
                if t.startswith("struct ") or t.startswith("union "):
                    RECORDS.add(n["name"])
                elif t.startswith("enum "):
                    ENUM_TYPEDEFS.add(n["name"])
                elif t in RECORDS:
                    RECORDS.add(n["name"])
            for v in n.get("inner", []):
                walk(v)
    walk(ast)


def generate():
    ast = load_ast()
    collect_records(ast)
    enums = collect_enums(ast)
    fns = {}
    for n in ast["inner"]:
        if n.get("kind") == "FunctionDecl" and n.get("name") in FUNCTIONS and "inner" in n:
            if any(x["kind"] == "CompoundStmt" for x in n["inner"]):
                fns[n["name"]] = n
    missing = [f for f in FUNCTIONS if f not in fns]
    if missing:
        die(f"functions not found: {missing}")
    fids = {name: i for i, name in enumerate(FUNCTIONS)}
    layout = Layout()
    ctx = Ctx(enums, layout)
    # Two passes: collect layout queries, probe, then emit with real numbers.
    for _ in range(2):
        out = []
        for name in FUNCTIONS:
            tr = FnTranslator(ctx, fns[name], fids)
            pids, body = tr.translate()
            out.append((name, pids, body, tr.names, tr.loops))
        if layout.results is None:
            layout.probe()
    lines = [
        "/-",
        "  GENERATED by formal/tools/c2lean.py from src/shogi.c — DO NOT EDIT.",
        f"  Target layout: {TARGET} (LP64, little-endian).",
        "-/",
        "import MiniC.Semantics",
        "",
        "namespace Shogi.C.Gen",
        "open MiniC",
        "",
    ]
    for i, (name, pids, body, names, loops) in enumerate(out):
        for lname, lterm in loops:
            lines.append(f"/-- A loop of `{name}`. -/")
            lines.append(f"def {lname} : Stmt := {lterm}")
            lines.append("")
        lines.append(f"/-- `{name}` (function id {i}). Locals: "
                     + ", ".join(f"{j}={nm}" for j, nm in enumerate(names)) + " -/")
        lines.append(f"def fid_{name} : Nat := {i}")
        lines.append(f"def {name} : Func where")
        lines.append(f"  params := {pids}")
        lines.append(f"  body := {body}")
        lines.append("")
    for i, g in enumerate(GLOBALS):
        data = layout.global_bytes[g]
        # 1 KiB chunks keep each literal within the elaborator's limits
        chunks = [data[k:k + 1024] for k in range(0, len(data), 1024)] or [[]]
        for ci, ch in enumerate(chunks):
            lines.append(f"def global_{g}_{ci} : List UInt8 := {ch!r}".replace(", ", ","))
        lines.append(f"/-- Initial bytes of `{g}` (block {GLOBAL_BLOCK + i}), dumped by the probe. -/")
        lines.append(f"def global_{g} : List UInt8 := "
                     + " ++ ".join(f"global_{g}_{ci}" for ci in range(len(chunks))))
        lines.append("")
    for name, q in LAYOUT_EXPORTS:
        lines.append(f"/-- `{q}`, measured by the probe. -/")
        lines.append(f"def {name} : Nat := {layout.results[q]}")
        lines.append("")
    lines.append("/-- The translated globals, as (block, bytes). -/")
    lines.append("def globals : List (Nat × List UInt8) := ["
                 + ", ".join(f"({GLOBAL_BLOCK + i}, global_{g})" for i, g in enumerate(GLOBALS)) + "]")
    lines.append("")
    lit = ctx.literal_bytes()
    lines.append("/-- String literals referenced by the translated functions. -/")
    lines.append("def literals : List UInt8 := " + repr(lit).replace("'", '"'))
    lines.append("")
    lines.append("def prog : Prog := fun f =>")
    lines.append("  match f with")
    for i, (name, _, _, _, _) in enumerate(out):
        lines.append(f"  | {i} => some {name}")
    lines.append("  | _ => none")
    lines.append("")
    lines.append("end Shogi.C.Gen")
    return "\n".join(lines) + "\n"


def main():
    try:
        text = generate()
    except Unsupported as e:
        print(f"c2lean: unsupported construct: {e}", file=sys.stderr)
        return 2
    if "--check" in sys.argv:
        with open(OUT) as f:
            if f.read() != text:
                print("c2lean: formal/Shogi/C/Gen.lean is stale; run formal/tools/c2lean.py",
                      file=sys.stderr)
                return 1
        return 0
    with open(OUT, "w") as f:
        f.write(text)
    print("wrote", OUT)
    return 0


if __name__ == "__main__":
    sys.exit(main())
