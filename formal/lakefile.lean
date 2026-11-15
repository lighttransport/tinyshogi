import Lake
open Lake DSL

package «tinyshogi_formal» where
  leanOptions := #[]

/-- MiniC operational semantics (vendored from tinygltf, MIT). -/
@[default_target]
lean_lib «MiniC» where
  srcDir := "."

@[default_target]
lean_lib «Shogi» where
  srcDir := "."

/-- Differential-testing driver (see tools/cdiff.py). -/
lean_exe «cdiff» where
  root := `CDiff

/-- Untrusted Lean → C emitter for src/shogi_tables.h. -/
lean_exe «gentables» where
  root := `tools.GenTables
