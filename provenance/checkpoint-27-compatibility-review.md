# Checkpoint 27 compatibility review

The original ten ports are unchanged. Seven newly imported proof files need compatibility updates for the pinned Mathlib version; no theorem statement changes.

- `S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat`: eight `Ideal.bot_prime` references become `Ideal.isPrime_bot`.
- `S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one`: TFAE `.out 0 3` becomes `.out 1 4`.
- `S_AlgebraicGeometry_exists_smoothProperCurve_opens_hom_comp_eq_of_ringKrullDim_eq_one`: TFAE `.out 4 1` becomes `.out 5 2`, and `.out 1 0` becomes `.out 2 1`.
- `S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_comap_eq_of_base_eq_of_ringKrullDim_le_one`: TFAE `.out 3 6` becomes `.out 4 7`. The apparent Dedekind constructor error came from selecting the wrong TFAE entry; the constructor is unchanged.
- `S_AlgebraicGeometry_geometricallyConnected_of_isConnected_preimage_of_section_of_isArtinianRing`: two `Ideal.bot_prime` references become `Ideal.isPrime_bot`.
- `S_GoodReductionJacobian_exists_relativeGroupLaw_baseChange_adicCompletion_one_eq_of_forall_nonempty_relativeGroupLaw_geometricFibre`: one `Ideal.bot_prime` reference becomes `Ideal.isPrime_bot`.

TFAE indices changed from zero-based to one-based, so incrementing both indices selects exactly the same mathematical assertions and direction. The primality theorem was renamed. All files are under `vendor/flt/P2M/Sol/` with `.lean` suffix.

The independent reviewer compiled scratch copies of the first five files with the existing vendor options. The sixth was detected by the same identifier scan before its dependencies finished. Final build and transitive-axiom evidence for all retained modules belongs to `verification/checkpoint-27-run.json`; this review alone is not a whole-project certificate.

Every exact replacement, upstream Git blob/SHA256 and current SHA256 is recorded in the upstream and port manifests. The source checker reverses the recorded replacements and re-verifies the original pinned upstream bytes.

A seventh dependency failure exposed the same TFAE migration in `S_AlgebraicGeometry_exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle`: `(tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk x)).out 3 1` becomes `.out 4 2`. The actual list in Mathlib has the integrally-closed/unique-nonzero-prime condition at entry 4 and ValuationRing at entry 2. A read-only scan of all retained new vendor files with missing or stale object files found no further numeric TFAE.out occurrences awaiting correction. Final combined build/audit evidence remains authoritative.
