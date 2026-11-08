# Checkpoint 31 environment restoration

The checkpoint-30 source ZIP was recovered unchanged (SHA-256
`d33ae850744d28d1ae01243188634cd546f91cc4cc410922e16b8c4135ac45fe`).
The complete checkpoint-30 partial compiled cache was recovered separately
(SHA-256 `2a3ee84d4208b7dca4349149827cb6d38628d45c030f9083a66aa8f332eb0cac`).

The official Linux Lean 4.34.0-rc2 archive was downloaded from the Lean release.
Its SHA-256 is `3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8`;
the compiler reports commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
All external packages were restored at the exact revisions in lake-manifest.json.
Mathlib's official hash-indexed cache was restored for the pinned revision.

This executor runs in a PID namespace while /proc exposes host process IDs.
Consequently Lean's /proc/getpid()/exe discovery can look up the wrong process.
The accompanying self-exe-compat.c redirects only that exact self lookup to
/proc/self/exe, the ordinary permitted alias for the running executable.
The compiler binary and proof checker were not modified. The local launcher
limits simultaneous Lean processes to four and uses one worker per process.
Neither adjustment is needed in an ordinary Lean installation.

No old proof source, vendor theorem, definition, or package revision was changed.
The verification report records the focused targets, audit and source checks.

## Build scope and recovery

The restored project/vendor cache was partial. The first broad build encountered
more than 1,500 missing compiled dependencies for the proposed root/descent
continuation. It was interrupted before checking those five draft modules. A
combined-source experiment encountered upstream module-isolation conflicts and
was abandoned; none of its output is used as a checked artifact. The final
checkpoint uses the ordinary Lake build and standalone axiom audit for the
three new quotient/graph modules only.

Paging hints (MADV_RANDOM and MADV_WILLNEED) were tried during restoration, with
no claimed improvement. The final compiler launcher uses only the self-executable
lookup shim. For the two new pairing/graph files it also uses Lean's official
`--incr-header-save`/`--incr-load` flags to reuse import state between local edits.
These are performance settings; the original Lean compiler and kernel are used.
The ordinary verification script does not require the launcher or snapshots.

The accompanying `supersingular-curves-checkpoint-31-mathlib-cache.tar.zst`
contains all 8,747 official hash-indexed Mathlib cache archives and a hash manifest
for the pinned package revisions. Restore that cache before asking Lake to
rebuild missing project/vendor modules. The separate checkpoint-31 build cache
contains the retained and newly completed project/vendor artifacts and remains
partial; it does not certify the draft modules or the full aggregate.
