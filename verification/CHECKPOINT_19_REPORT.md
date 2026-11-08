# Checkpoint 19: Jacobian cotangents and global forms through residues

20 September 2026 · Lean 4.34.0-rc2

**The actual Jacobian cotangent space is now identified with the actual curve's global differential forms over an algebraically closed field. The comparison is fixed by residue evaluation and the Poincare pairing, and its uniqueness is proved. The Cartier–Verschiebung identity and the two general geometric classification criteria remain open.**

## What was completed

For an actual smooth proper integral curve C over an algebraically closed field K, a specified two-affine differential chart, and a genuine Picard-representing Jacobian J, the new code constructs

\[
H^0(C,\Omega^1_{C/K})\simeq_K H^1_{\mathrm{rep}}(K(C),0)^\vee,
\qquad
\operatorname{Cot}_0(J)\simeq_K H^0(C,\Omega^1_{C/K}).
\]

Here global forms are compatible actual differential-sheaf sections on the affine cover. The cotangent is the actual maximal ideal modulo its square at the Jacobian identity. Repartition H¹ is the actual quotient by integral and principal repartitions. The caller supplies neither a residue theorem nor a duality theorem as an assumption.

The first map is characterized on every repartition a by

\[
\langle\omega,[a]\rangle
=\sum_v\operatorname{Tr}_{k(v)/K}\operatorname{Res}_v(a_v\omega).
\]

The code proves this formula for zero and nonzero differentials, proves agreement with the existing Cech/off-chart residue pairing, and proves uniqueness. It then uses the established generic-restriction map to obtain the formula for actual global forms.

The second comparison composes this residue duality with the existing Poincare-normalized cotangent/dual-cohomology map. For x in Cot₀(J) and a tangent functional l, its image ωₓ satisfies

\[
\langle\omega_x,\operatorname{PoincareClass}(l)\rangle=l(x).
\]

This normalization uniquely determines the comparison. A separate theorem gives its residue formula on every actual overlap section of the curve's structure sheaf.

## How its hypotheses were supplied

The proof uses the existing completion/coefficient-field construction of local residues. The pinned residue theorem is stated for every allowed canonical residue family; the new code specializes it to the exact family used by the pairing.

Over an algebraically closed field, a separating transcendental element supplies a finite separable extension of a rational function field. The code transports the algebra structures and proves the hypotheses needed to apply that residue theorem. For the actual scheme, one-variable function-field structure, essential finite type, the differential-coordinate conditions, the canonical-divisor data and the constants condition are all supplied from previously proved curve results.

The deep residue theorem and regular/Weil/dual-cohomology equivalences are reused from the pinned FLT sources. The new contribution here is their specified composition, hypothesis discharge on the actual curve, evaluation/uniqueness proofs, and integration with the independently constructed Jacobian. This is not presented as a new foundational proof of Serre duality.

## What this gives for Verschiebung

The new comparison also transports the already proved evaluation formula for actual Frobenius-pulled-back Poincare deformations:

\[
\langle\omega_x,\operatorname{FrobeniusDeformationClass}(l)\rangle
=l(V^*x).
\]

V remains the independently constructed Jacobian Verschiebung. The functional l has the genuine Frobenius-twisted cotangent space as its domain; the scalar twist is retained.

**This still does not prove Cartier = V*.** Two connecting statements remain: identify the actual pulled-back deformation cocycle with the corresponding Frobenius action on cochains, and prove that this action is adjoint to the existing differential Cartier operator under the residue pairing. The new cotangent/global-form equivalence supplies the spaces and normalization needed for those statements.

The results are relative to a specified affine cover over an algebraically closed field. Independence under cover refinement, descent of this complete comparison to arbitrary perfect fields, and functorial compatibility beyond the displayed deformation formula are not asserted here.

## Match to the sheet and IKO §1

| Requested part | Status after this checkpoint |
|---|---|
| Elliptic curves, supersingularity, Legendre examples | Retained geometric p-torsion definition, odd-characteristic Hasse criterion, field-extension invariance, Legendre polynomial and examples. Separate scheme/Weierstrass and isogeny-definition comparisons remain. |
| Superspecial and supersingular definitions | Both exist independently: geometric product isomorphism and product isogeny. Superspecial implies supersingular. |
| Cartier matrix on dx/y, x dx/y | Retained full regular/global bases, actual Cartier formulas, and zero/twisted-square-zero criteria for every presented separable quintic/sextic model. |
| Actual cotangent/global-differential comparison | **Completed over algebraically closed fields for a specified chart.** The map is specified by residues and the Poincare pairing, with hypotheses supplied and uniqueness proved. |
| Cartier compared with Jacobian Verschiebung | Partial. Independent V, curve-Frobenius Picard pullback = V, actual cotangent/global-form comparison and deformation evaluation are proved. Cochain compatibility and residue/Cartier adjointness remain. |
| IKO Lemma 1.1(i), supersingularity | General geometric equivalence remains open. The retained matrix and p-rank results do not prove a product isogeny. |
| IKO Lemma 1.1(ii), superspeciality | General geometric equivalence remains open. Necessary Cartier/root conditions are proved for both explicit families; the converse product-isomorphism result remains open. |
| IKO families and parameter polynomials | Retained actual models/Jacobians, matrices, root and p-rank criteria, ordinary loci, and the main differential-equation proof of Proposition 1.14. Further geometric and isomorphism/quotient classifications remain. |
| Newton polygon | Retained coefficient-hull and finite-field Witt-isocrystal definitions/examples. Attachment to the actual curve/Jacobian and the geometric supersingularity comparison remain open. |

`SECTION1_COVERAGE.md` contains the full proposition-by-proposition ledger. This checkpoint closes a comparison step required for the operator interpretation in §1.1; it does not finish another geometric classification proposition or all of §1. No separately specified Oort conjecture is claimed proved.

## Verification

**All current checks passed.** The full project build succeeded (10,362 jobs), all four new proof modules and all 17 added dependency modules compiled, and the four actual-curve integration examples passed. Source verification checked 142 source/provenance hashes, exact dependency closure and all prior proof bytes. The comment-stripped scan of 1,598 project/vendor Lean sources found no admitted-proof, added-axiom or native-evaluation markers.

The new-proof audit checked **359 module declaration entries**: 50 in the new project modules and 309 in the new dependency modules. Their transitive axiom dependencies use only `propext`, `Classical.choice` and `Quot.sound`. One shared generated equation entry was also checked by its stored type/body. Execution details and log hashes are recorded in `verification/checkpoint-19-run.json`, completed 2026-09-20T00:21:52.045168+00:00.

The concrete integration suite uses the genuine genus-two curve y² = x⁵ − 1 over the algebraic closure of F₃. It instantiates the new cotangent/global-form equivalence without added duality assumptions, proves the global-form space has dimension two through that equivalence, and checks the representative residue and independent-V deformation formulas.

The current verification route builds the full project, verifies pinned source provenance and preservation of previous proofs, scans project/vendor sources for admissions, compiles the new integration suite, and audits every declaration entry in the four new project modules and all 17 new vendor modules, including transitive axiom dependencies. Shared generated equation entries are also inspected through their stored types and bodies; they are not skipped.

The earlier full audit and eight earlier integration suites are retained as historical evidence for byte-identical sources. They are not claimed to have been rerun. Checkpoint 17's full audit covered 1,631 project and 26,817 imported FLT declarations; checkpoint 18 separately audited all 56 declarations from its three new modules.

To reproduce the current focused route:

```sh
lake exe cache get
bash verification/verify_checkpoint19.sh
```

The comprehensive historical route, including all integration suites and `Audit.lean`, remains available as `bash verification/verify.sh`.

## Files and provenance

The four new modules are:

- `Geometry/ResidueFoundation.lean`: selected-family residue theorem and supplied rational-subfield hypotheses.
- `Geometry/ResiduePairing.lean`: specified regular-form/dual-repartition equivalence, residue formula, uniqueness and Cech compatibility.
- `Geometry/SchemeResidueDuality.lean`: discharge of all auxiliary hypotheses on the actual scheme, with explicit representative formulas.
- `Geometry/JacobianResidue.lean`: actual global-form and Jacobian cotangent comparisons, uniqueness and V deformation evaluation.

Paths are relative to `SupersingularCurves/`. Attribution is recorded in `provenance/residue-duality-comparison.json`.

There are now 78 proof modules and 584 public theorem declarations, including 19 new declarations in this checkpoint; the retained private supporting lemma count is nine. These are code inventory counts, not measures of novelty or completion. All 74 prior proof modules and all 1,502 prior vendor modules are byte-identical. The 17 new vendor modules match the pinned upstream bytes exactly; no compatibility port was added.

Pins remain Lean `leanprover/lean4:v4.34.0-rc2`, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and FLT `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. The proof checker is unmodified. The source ZIP includes the dependency sources, licenses, provenance, coverage ledger, and verification evidence. The optional checkpoint-17 compiled cache can be reused as a baseline; it does not contain the newly added modules, which `lake build` compiles.

The next mathematical milestone is the Frobenius/cochain and residue/Cartier compatibility needed to prove the actual Cartier–Verschiebung identity. The geometric superspecial and supersingular classification theorems remain substantial separate goals after that comparison.
