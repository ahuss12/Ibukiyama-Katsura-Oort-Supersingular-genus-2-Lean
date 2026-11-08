# Checkpoint 21 — Cartier/Verschiebung and the general genus-two p-rank criterion

20 September 2026 · Lean 4.34.0-rc2

**Two substantial gaps are closed.** The existing Cartier operator is now compared with actual Jacobian Verschiebung under a specified cohomological scalar identification. The general p-rank-zero converse is also proved for every presented separable quintic/sextic genus-two model. **The complete professor's sheet and all of IKO Section 1 are not finished.**

## Scope recovered

The continuation starts from the attached checkpoint-20 ZIP. Decisions from the “Scope supersingular curves” conversation were recovered, and the original sheet photograph, `IMG_1047.jpeg`, was found and visually checked. A copy is included as `references/ProfessorSheet.jpeg`.

The sheet covers elliptic supersingularity, equivalent properties, the Legendre family and examples, higher-genus definitions, superspeciality, Newton polygons, the two genus-two families, IKO parameter polynomials, and the Section 1 matrix calculation. It names Ibukiyama–Katsura–Oort; it does not state a separate Oort conjecture. The user's explicit instruction to cover **all** of IKO Section 1 remains the target. `SECTION1_COVERAGE.md` records every item against [the paper](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf).

## Newly verified results

### 1. Cartier, residues, and actual Verschiebung

The local identity

\[
\operatorname{Res}(fC\omega)^p=\operatorname{Res}(f^p\omega)
\]

is proved for arbitrary pole order using the existing Cartier operator and canonical local residues. Summing the local identities gives adjointness to actual Frobenius on structure-sheaf cohomology.

Let \(\alpha\) be the Poincare/residue-normalized equivalence from the Jacobian cotangent space to global forms, \(dV\) the actual cotangent map of independently constructed Verschiebung, and \(u\) the inverse-Frobenius scalar identification fixed independently through actual curve-projection pullback on cohomology. The theorem is

\[
\alpha\bigl(u(dV(z))\bigr)=C(\alpha(z)).
\]

In particular, **\(dV=0\iff C=0\)**. The coefficient matrix and both IKO parameter polynomials now detect vanishing of this actual cotangent map. For the characteristic-three curve \(y^2=x^5-1\), the actual Jacobian has p-rank zero and \(dV\ne0\).

Main declarations: `Jacobian.cotangentGlobalEquiv_verschiebung`, `Jacobian.verschiebungCotangent_eq_zero_iff`, `SimpleRootModel.jacobian_verschiebungCotangent_zero_iff_matrix`, and the two family `verschiebungCotangent_zero_iff` theorems.

**Precise remaining limitation:** the cohomological identification \(u\) has not yet been identified with cotangent pullback along the actual Jacobian scheme projection. The comparison above and its vanishing criterion do not assume that further naturality theorem. They are not a proof of geometric superspeciality.

### 2. General genus-two p-rank equivalence

For any two-by-two matrix over an algebraically closed field of characteristic \(p\), the inverse-Frobenius action \(v\mapsto\operatorname{Frob}^{-1}(Mv)\) has only zero fixed vector exactly when \(M^{(p)}M=0\). This new proof uses elementary polynomial elimination; it does not invoke an assumed classification theorem.

Combining this with the existing full differential basis and actual Picard/Jacobian torsion correspondence proves

\[
\operatorname{p\text{-}rank}(J)=0
\iff C^2=0
\iff M^{(p)}M=0.
\]

The scope is **every separable quintic or sextic model over an algebraically closed field of odd characteristic, for any genuine representing Jacobian and base point**. The Cartier statement is proved on both the entire regular-differential space and the actual global-differential space. It is no longer limited to the two IKO families.

Main declarations: `IKO.semilinear_fixed_trivial_iff_twisted_square_zero` and the three `SimpleRootModel.jacobian_hasPRankOver_zero_iff_...` theorems for matrix, regular Cartier square, and global Cartier square.

This does **not** yet prove that an arbitrary abstract genus-two curve has one of these presentations, or that p-rank zero supplies a geometric product isogeny.

## Verification

- All 85 prior project proof modules and all vendor Lean files remain byte-identical to the attachment. No new vendor dependency, axiom, or compatibility port was added.
- Ten additional draft modules were recovered from the previous workspace, reviewed and repaired. Every one was freshly recompiled. Two further modules were written in this continuation and compiled.
- The full aggregate build passed: **10,389 jobs**. Retained dependency artifacts were reused; this is not a clean recompilation of every dependency.
- **196 declaration entries** across all 12 added modules were transitively audited, including stored types/bodies and private/generated entries. Only `propext`, `Classical.choice`, and `Quot.sound` occur as axiom dependencies.
- **14 integration examples** passed. They include actual curves in characteristics 3, 5 and 7, both IKO families, and a nontrivial Frobenius-twist regression with \(M^{(3)}M=0\) but \((M^2)_{00}=1\).
- Source checks verify the attachment-preservation manifest, the pinned vendor import closure, and hashes of all current proof/verification sources. The project/vendor source scan rejects proof admissions and native-evaluation markers. Exact outcomes and log hashes are in `verification/checkpoint-21-run.json`.

There are now **97 project proof modules, 708 public theorem declarations, and 13 private supporting lemmas**. This checkpoint adds 79 public theorems from recovered drafts and seven newly written public theorems, plus three new private lemmas. These are inventory figures, not completion percentages or novelty claims.

Reproduce with the pinned toolchain:

```sh
lake exe cache get
bash verification/verify_checkpoint21.sh
```

The unchanged historical full audit and prior integration suites remain documented evidence; they were not all rerun. Sources, licenses, provenance, the original sheet, logs, and the complete scope ledger are in the ZIP. Compiled caches are omitted.

## Still required for the agreed scope

1. **Geometric Cartier criteria:** Cartier zero iff geometric superspeciality, and Cartier square zero iff geometric supersingularity. In particular, the product-isomorphism and product-isogeny constructions/classifications remain missing.
2. **Remaining naturality:** identify the cohomological scalar untwist with the Jacobian scheme-projection cotangent map; address the necessary cover/base-change comparisons.
3. **Newton polygons of the actual objects:** attach the isocrystal to the actual curves/Jacobians and prove the geometric supersingularity comparison. Existing standalone Newton-polygon examples do not supply this.
4. **Remaining IKO Section 1:** abstract genus-two presentation, automorphism/reduced-group classification, elliptic quotients, parameter-isomorphism classification, and the unfinished congruence/geometric statements listed proposition by proposition in `SECTION1_COVERAGE.md`.
5. **Sheet-specific identifications and field scope:** prove the birational changes between the handwritten cyclic-cover equations and the implemented hyperelliptic models; complete the outstanding elliptic implementation comparisons and descent where required.

The bounded search of the available pinned source index and inspected Dieudonne files did not supply the missing geometric classification theorems. Their absence from this checkpoint is explicit, rather than hidden in a definition or assumed hypothesis.
