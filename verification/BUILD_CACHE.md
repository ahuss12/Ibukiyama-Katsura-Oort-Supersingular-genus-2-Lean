# Compiled cache for checkpoint 32

The optional `supersingular-curves-checkpoint-32-build-cache.tar.zst` contains
completed project and vendor build artifacts, including all five newly
checked modules and the old dependencies rebuilt during this continuation.
Exact counts, source hashes and artifact hashes appear in
`checkpoint-32-build-cache-manifest.json`; the archive hash appears in
`checkpoint-32-build-cache-record.json`.

This is still a partial cache. It excludes the aggregate, unchecked drafts,
diagnostic copies, Lake setup JSON, compiler and external packages. Extract
it from the checkpoint-32 project directory after extracting the source ZIP.
Restore the exact Lean and package revisions, obtain the matching Mathlib
cache (the saved checkpoint-31 Mathlib archive is compatible), and run:

```sh
bash verification/verify_checkpoint32.sh
```

The full aggregate will require additional builds. The numerical continuation
has an upstream import-memory blocker documented in `drafts/checkpoint32/README.md`.
Cached objects do not turn unchecked drafts into proofs. Historical cache
notes follow.

# Compiled cache for checkpoint 30

The optional `supersingular-curves-checkpoint-30-build-cache.tar.zst` contains
195 project proof modules and 2,375 vendor modules, including the newly
checked recurrence/compactness chain and its prescribed-quotient dependency.
It omits the aggregate, reproducible setup JSON, compiler, external packages,
and artifacts without retained proof sources. It is a partial cache.

Extract the checkpoint-30 source ZIP, then extract this cache from the
project directory. Install the pinned Lean toolchain and external packages
from `lake-manifest.json`, obtain their Mathlib cache, and run
`bash verification/verify_checkpoint30.sh`.

`checkpoint-30-build-cache-manifest.json` records the included files and
proof-source hashes. `checkpoint-30-build-cache-record.json` records the
archive hash. Proof sources and checking remain authoritative.

## Historical checkpoint-29 cache


The optional `supersingular-curves-checkpoint-29-build-cache.tar.zst` preserves
the compiled geometric chain checked at checkpoint 29, plus retained checked
modules. It contains 178 project proof modules and 2,371 vendor modules. It is
a partial cache: the full aggregate and all vendor modules are not included.
The stale prior aggregate was explicitly excluded.

Extract the checkpoint-29 source ZIP, then extract this cache **from the project
directory**. Install the pinned Lean toolchain and fetch the exact external
package revisions in `lake-manifest.json`. Obtain their cache with
`lake exe cache get`, then run `bash verification/verify_checkpoint29.sh`.
`lake build` for the full aggregate will compile the remaining modules.

The archive does not contain external dependencies or the compiler. It omits
reproducible Lake setup JSON. Its platform is Linux x86_64, with Lean
4.34.0-rc2 and Mathlib commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0`.

`checkpoint-29-build-cache-manifest.json` records every included file's hash
and each compiled module's proof-source hash. The separate
`checkpoint-29-build-cache-record.json` records the archive hash. Proof sources
and fresh checking remain authoritative; the cache only saves rebuild time.

## Historical checkpoint-19 cache baseline

Reuse `supersingular-mini-checkpoint-17-build-cache.tar.zst` from checkpoint 17 if desired. Its 71 project proof modules and 1502 vendor sources are byte-identical to the retained sources here. The archive is optional; proof sources are sufficient with the pinned toolchain and dependencies.

Extract the checkpoint-19 source ZIP. From its project directory, extract the checkpoint-17 cache archive, obtain the pinned external dependency cache with `lake exe cache get`, and run `lake build`. Lake compiles the seven project modules added since checkpoint 17, the 17 vendor modules added in checkpoint 19, and the changed aggregate import. A workspace already compiled through checkpoint 18 only needs the four newest project modules, the 17 vendor modules, and the aggregate import.

`build-cache-manifest.json` and `build-cache-record.json` describe the unchanged checkpoint-17 cache baseline; they are not a checkpoint-19 cache manifest. This checkpoint does not claim a clean recompilation of every retained dependency.

Lean: 4.34.0-rc2. Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0. Platform of the optional cache: Linux x86_64. The compiler distribution and external dependency caches are not in that archive.
