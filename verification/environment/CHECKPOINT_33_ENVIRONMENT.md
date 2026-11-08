# Checkpoint 33 build environment

The compiler is the unmodified official Lean 4.34.0-rc2 executable, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. The verified release archive SHA-256 is
`3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8`.
Mathlib is pinned to `85e3a25e006c35636f0e53b0e9296caca2685bc0`; the vendored FLT
subset is pinned to `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef` with documented,
reversible proof ports. The ten external git packages retain their exact
`lake-manifest.json` revisions.

The checkpoint-32 source and partial project/vendor cache were restored and
all archived source/artifact hashes checked. The pinned Mathlib cache was
restored (8,747 entries). Focused `lake --old build +Module` invocations reused
these verified artifacts. `--old` is appropriate only after those source,
artifact and dependency checks; it is not a way to ignore changed proofs.
The new `verification/build_incremental.py` performs those checks before
restoring source timestamps changed by archive extraction. It rejects a
mismatched cached source. No Lake trace or compiled proof object was forged.

A separate launcher serializes Lean source invocations (`-j1`,
`-DElab.async=false`) in the 8 GiB environment. The previous `/proc/self/exe`
readlink accommodation and OS paging hints were retained. These do not change
kernel checking. The two older graph/product builds retained their supported
Lean header snapshots. The faithfully-flat repair used the official Lean
incremental snapshot facility for its byte-identical, already kernel-checked
prefix; the changed tail and final theorem were checked normally. Snapshots
are machine-specific and are not part of the portable compiled cache.

The earlier checkpoint-32 explanation that the density dependency was blocked
merely by imports was incomplete. Imports succeeded in the present diagnostic;
implicit morphism/subtype conversion in the kernel caused the blow-up.
Explicit point-value congruences and checked auxiliary lemmas repaired it.
The analogous descent bottleneck was removed by proving the commuting square
with abstract coefficient rings before specialization. The final upstream
effective-descent theorem and its proof remain byte-for-byte unchanged.
A project Tate pullback proof also received a statement-preserving rewrite.
Full old/new text and hashes are recorded in the port and repair manifests.

The compiled archive remains partial. It contains completed project/vendor
modules, their ordinary `.olean` companions and successful traces. It excludes
exploratory diagnostic copies, unchecked drafts, the compiler, and external
package caches. Extract it over the matching source tree; install the exact
external revisions and their matching cache before running the incremental
verifier. The full aggregate and historical examples were not rebuilt.
