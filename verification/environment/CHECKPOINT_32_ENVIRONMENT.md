# Checkpoint 32 environment and build scope

Lean is pinned to 4.34.0-rc2, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`.
The official Linux x86_64 release archive SHA-256 was verified as
`3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8`.
The original compiler executable was retained without modification as
`lean.bin`; a separate launcher serialized compiler invocations with `-j1`.
Synchronous elaboration (`-DElab.async=false`) was used in later invocations.
The two early graph and binary-product module builds used Lean's supported
header-snapshot save/load flags. No proof or kernel checking was disabled.

The environment required the previously documented `/proc/<pid>/exe` to
`/proc/self/exe` readlink accommodation. The build-only interposer also applied
`MADV_RANDOM`, later `MADV_NOHUGEPAGE`, to mapped `.olean` files to reduce paging
and private huge-page pressure. These are OS paging hints; proof sources and
compiler bytes were not altered. Its source is
`verification/environment/checkpoint32-runtime-compat.c`. The exact
workspace-specific launcher is retained alongside it as a historical record;
it is not a portable installation script.

The ten external packages were checked out at their exact saved
`lake-manifest.json` revisions. The retained checkpoint-31 Mathlib hash cache
was unpacked successfully (8,747 archive entries). Mathlib remains pinned to
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. The FLT subset remains pinned to
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`, with its existing recorded ports only.

All five new checked modules passed normal focused Lake compilation, and all
19 stored declaration entries passed the transitive axiom audit. Prior
checked sources/caches were reused. The full aggregate and historical example
suite were NOT rerun. The aggregate imports only checked modules.

The broader numerical build failed before reaching the seven continuation
drafts: loading the pinned torsion-density dependency exhausted the 8 GiB
memory limit. Synchronous elaboration and direct compiler invocation also
failed. Low-memory diagnostics failed during import/initialization; no result
from a diagnostic copy is included in the cache or certified as a theorem.
A trial using Lean's newer module header was rejected because the dependencies
use legacy modules. No vendor source was changed by these trials.

The separate checkpoint-32 compiled cache preserves completed project/vendor
artifacts, including the additional old dependencies rebuilt this turn. It
is still partial, excludes unchecked drafts, and does not include the compiler
or external package checkout/cache. Use the checkpoint-31 Mathlib cache with
it, or obtain the pinned external cache through Mathlib's supported tool.
Proof sources and verification remain authoritative.
