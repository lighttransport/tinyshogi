#!/usr/bin/env python3
"""Try c2lean on every function of src/shogi.c separately and list the
first rejection of each (the subset gap list in PLAN.md §1.2)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import c2lean as c

ast = c.load_ast()
c.collect_records(ast)
enums = c.collect_enums(ast)
fns = [n for n in ast["inner"] if n.get("kind") == "FunctionDecl" and "inner" in n
       and any(x["kind"] == "CompoundStmt" for x in n["inner"])
       and "includedFrom" not in n.get("loc", {})]
fids = {n["name"]: i for i, n in enumerate(fns)}
ctx = c.Ctx(enums, c.Layout())
ok, bad = [], []
for n in fns:
    try:
        c.FnTranslator(ctx, n, fids).translate()
        ok.append(n["name"])
    except c.Unsupported as e:
        bad.append((n["name"], str(e)))
print(f"accepted {len(ok)}/{len(fns)}: {' '.join(ok)}")
for name, why in bad:
    print(f"REJECT {name}: {why}")
