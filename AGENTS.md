# AGENTS.md

Guidance for coding agents working in tinyshogi.

## Project-specific checks

The browser demo lives in `web/`. Changes to the web UI should preserve the
font-independent SVG piece rendering, responsive board layout, and the default
Japanese piece mode / White auto-play configuration unless the task says
otherwise.

Before handing off web changes, run:

```sh
cd web
npm test
npm run test:wasm
npm run build
cd ..
git diff --check
```

## Mandatory pre-push audit

Before any push, audit the exact commits that will leave the local checkout.
For a normal push, use the configured upstream range:

```sh
RANGE="$(git rev-parse --abbrev-ref --symbolic-full-name @{upstream})..HEAD"
git log --oneline "$RANGE"
```

Run all of the following checks against that range. A finding must be resolved
before pushing.

### 1. Credentials, personal paths, and private asset names

Inspect added content and commit messages for API keys, tokens, passwords,
private keys, `.env` files, internal hostnames, personal filesystem paths, and
customer/proprietary asset names:

```sh
git diff "$RANGE" -- ':!**/*.md' ':!**/*.txt' \
  | grep -nEi 'AKIA[0-9A-Z]{16}|ASIA[0-9A-Z]{16}|AIza[0-9A-Za-z_-]{35}|(api[_-]?key|secret|token|password|passwd|bearer|private[_-]?key)[[:space:]]*[:=]' \
  || echo "No credential-shaped strings found"

{ git log "$RANGE" --format='%B'; git diff "$RANGE" -- 'src/*' 'web/*' 'tests/*'; } \
  | grep -inE '/home/[a-z]|/Users/[A-Za-z]|C:\\Users\\' \
  && echo "ABORT: personal path found" || echo "No personal paths found"
```

Run `gitleaks` or `trufflehog` over the same range when installed. Treat any
finding as a stop condition; do not push a secret and plan to remove it later.

### 2. Build artifacts

The push range must not add generated build state such as `web/build/`,
`web/dist/`, `node_modules/`, object files, shared libraries, CMake/Ninja
state, or Python caches:

```sh
git diff --name-only "$RANGE" \
  | grep -Ei '(^|/)(build|build_py|build_py_ext|build_test|dist|node_modules|__pycache__)/|(^|/)(CMakeCache\.txt|CMakeFiles|build\.ninja|compile_commands\.json)|\.(a|o|so|dylib|dll|lib|pdb|pyc|ninja_deps|ninja_log)$' \
  && echo "ABORT: build artifact found" || echo "No build artifacts found"
```

### 3. Unintended binary or asset data

Review the changed-file list and diff sizes. Reject arbitrary captures,
archives, PDFs, large images, model files, and other data that cannot be
regenerated from source. SVG artwork and the Japanese glyph license are
intentional web assets; generated `web/dist/` output is not.

```sh
git diff --stat "$RANGE"
git diff --name-only "$RANGE" \
  | grep -iE '\.(blend|fbx|glb|gltf|abc|mb|ma|exr|hdr|tif|tiff|pdf|wasm)$|(^|/)captures?/' \
  && echo "ABORT: unexpected binary/asset path" || echo "No flagged binary/asset paths"
```

### 4. Push authorization

After checks 1–3 and the project tests pass, summarize the branch, remote,
fast-forward/force status, outgoing commits, audit results, and test results.
Ask for fresh user authorization immediately before pushing. Previous push
approval does not carry over to a later push.

After a successful push, confirm the remote commit and leave unrelated branches
untouched.
