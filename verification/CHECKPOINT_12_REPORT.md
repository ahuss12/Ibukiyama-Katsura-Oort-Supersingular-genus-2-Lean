# Supersingular curves mini-project — checkpoint 12

**Author:** Ameen Hussain  
**Date:** 18 September 2026  
**Verification:** fresh project compilation, source audit, all six example suites, and transitive axiom audit passed

This checkpoint completes the basis and Cartier-matrix calculation in IKO §1.1 for **every presented separable quintic or sextic**, extending the previous two-family results. It supplies actual curve/global-form/Jacobian constructions and a genuine characteristic-three example. The geometric supersingular/superspecial classification and crystalline Newton comparison are still unfinished.

## New results

Let k be algebraically closed of odd prime characteristic p, and let f ∈ k[x] be separable of degree five or six. Lean constructs the quadratic function field and a smooth proper genus-two model of y² = f(x). It proves that

\[
\omega_0=dx/y,\qquad \omega_1=x\,dx/y
\]

form a basis of **all** regular differentials and, through the canonical generic-restriction equivalence, of the actual scheme-global differential space.

Writing f(x)^((p−1)/2) = Σ c_j x^j, the raw coefficient matrix is

\[
M=\begin{pmatrix}c_{p-1}&c_{p-2}\\c_{2p-1}&c_{2p-2}\end{pmatrix}.
\]

For coordinates v, the Cartier operator sends v to Frob⁻¹(Mv), with inverse Frobenius applied entrywise. Consequently Lean proves, on both full differential spaces,

\[
\mathcal C=0\iff M=0,\qquad
\mathcal C^2=0\iff M^{(p)}M=0.
\]

It also proves

\[
M^{(p)}M=0\Longrightarrow f(\operatorname{Jac}(C))=0
\]

for **every representing Jacobian and every base point** of the constructed curve. The p-rank is defined through actual geometric p-torsion points. This is one implication; the general converse and the geometric product-isogeny interpretation are not asserted.

### Why this removes assumptions

The input is the polynomial, separability, degree, and base-field hypotheses. A simple root is obtained from algebraic closure. The independent Riemann–Hurwitz theorem proves genus two and the dimension of regular forms. The new reciprocal chart uses u = 1/x and z = y/x³, with z² = u⁶ f(1/u). Its separability is proved, including the possible root at infinity. This supplies all-place regularity; independence and dimension then prove spanning. A full basis or genus assertion is never an input assumption.

The Jacobian implication uses the proved divisor-class logarithm: Cartier-fixed forms coming from p-torsion must vanish if Cartier has square zero. The group-compatible Picard correspondence then makes the actual Jacobian p-torsion trivial. No classification theorem is assumed.

### Characteristic-three example

For **y² = x⁵ − 1 in characteristic three**, Lean now constructs the curve and proves

\[
g(C)=2,\qquad M=\begin{pmatrix}0&0\\1&0\end{pmatrix},\qquad
\mathcal C\ne0,\quad \mathcal C^2=0,\quad f(\operatorname{Jac}(C))=0.
\]

The Cartier statements concern the full regular space and the full scheme-global space. The previous checkpoint only had this particular distinction on a rational two-form span under function-field hypotheses. This result does **not** yet prove the geometric supersingular/non-superspecial classification of the example.

## New code

All paths below are relative to `SupersingularCurves/Hyperelliptic/`.

| Module | Main result |
|---|---|
| `Reciprocal.lean` | Reflection identities, reciprocal separability, all-place regularity |
| `GenusTwoBasis.lean` | Model from any separable quintic/sextic; full regular basis |
| `GenusTwoCartier.lean` | General full-space Cartier coordinates and two matrix criteria |
| `GenusTwoGlobalForms.lean` | Actual global basis and transported matrix/operator criteria |
| `GenusTwoJacobian.lean` | Representing Jacobian and square-zero Cartier ⇒ p-rank zero |
| `CharacteristicThree.lean` | Actual y² = x⁵ − 1 example, global distinction, Jacobian p-rank |

**31 public theorem declarations** are added. The project contains **428 public theorem declarations in 56 proof modules**, plus nine private supporting lemmas. These are declaration counts, not counts of independent discoveries. All **50 checkpoint-11 proof modules are byte-for-byte unchanged**. There are no new or modified vendor modules. Reuse and scope are recorded in `provenance/general-genus-two.json`; preservation hashes are in `provenance/checkpoint-11.json`.

## Verification

Completed at **2026-09-18T05:58:01.395169+00:00**. The project build directory was cleared before verification. Lake freshly compiled all **56 proof modules and the aggregate import** (57 project compile units); pinned external/vendor dependencies were reused. All **98 checked source hashes** remained unchanged during the gate. The initial execution session became unavailable after the completed fresh build; the source checks, six example suites, and axiom audit were then resumed. The completed build log was preserved and no proof source changed.

| Check | Result |
|---|---|
| Fresh full project compilation | Passed |
| Source provenance, exact vendor closure, and checkpoint-11 preservation | Passed |
| Full-basis example suite | Passed |
| Actual divisor-class torsion example suite | Passed |
| Jacobian/global-differential example suite | Passed |
| Simple-root and degree-bound example suite | Passed |
| Geometric superspecial obstruction example suite | Passed |
| General genus-two model and Cartier distinction example suite | Passed |
| Transitive axiom audit | Passed |

The audit checked **1267 project declarations and 24884 imported FLT declarations**, permitting only `propext`, `Classical.choice`, and `Quot.sound`. The source scan found no admitted-proof, extra-axiom, or native-evaluation markers in **1490 project/vendored Lean source files**. The exact run and log hashes are in `verification/checkpoint-12-run.json`; scan evidence is in `verification/source-scan.json`. Retained upstream style/deprecation warnings do not indicate unproved goals. No new proof module emitted a warning in the final build.

The new example suite specializes the actual characteristic-three curve, global operator distinction, and Jacobian p-rank; checks the full global dimension for a sextic in characteristic five; and checks reciprocal separability for a sextic having a root at zero. All five earlier example suites are retained.

The toolchain remains Lean **4.34.0-rc2**, Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`, and selected FLT sources at `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`. The vendor selection has 1433 modules, 1427 unchanged and six documented compatibility ports.

To rebuild with the pinned toolchain installed:

```sh
lake exe cache get
bash verification/verify.sh
```

An optional build cache, `supersingular-mini-checkpoint-12-build-cache.tar.zst`, preserves 10430 compiled artifacts (220.1 MiB compressed). Its checksum and restoration instructions are in `verification/build-cache-record.json` and `verification/BUILD_CACHE.md`. It omits the compiler, external package caches, and generated setup JSON files; the source archive builds independently of it.

The hosted verification uses the included executable-path compatibility shim, documented in `verification/lean_app_path_compat.c`, to locate the installed compiler. It does not change Lean's proof checker. Pinned external/vendor dependencies are reused; all project build artifacts are cleared before the final run.

## Match to the professor's sheet

**Status key:** “proved” means a Lean theorem within the stated assumptions; “defined” means the mathematical object or predicate exists; “partial” means part of the requested result is still missing. None of the pending statements is an assumed theorem in this project.

| Sheet item | Verified in checkpoint 12 | Still required |
|---|---|---|
| **0. Elliptic curve E over a finite/perfect field** | Actual Weierstrass curves over a general field; finite and perfect fields are included. Nonsingularity is required in the supersingularity predicate. | Identification of the separate Weierstrass-point and scheme-group implementations. |
| **1. Definition of E supersingular** | **Defined geometrically:** after extension to an algebraic closure, the only point killed by p is the identity. | No missing definition. |
| **2. Equivalent elliptic properties** | **Proved in odd characteristic:** equivalence with Hasse-invariant vanishing, and invariance under extending the field. | The complete collection of elliptic characterizations, including comparison with the isogeny definition. |
| **3–4. Legendre family and examples** | **Proved:** ellipticity for t ≠ 0,1; supersingularity iff the Deuring/Hasse polynomial vanishes; separability of that polynomial; concrete examples. | Connection to the separate genus-five project's construction, if included in the eventual manuscript. |
| **0–1. Curves of genus g and C supersingular** | Actual curve/Jacobian framework and independent geometric product-isogeny predicate. **New:** every separable quintic/sextic input over an algebraically closed field of odd characteristic supplies an actual genus-two model and representing Jacobian. | General geometric Cartier criteria; descent of the complete results to arbitrary perfect ground fields; the hyperelliptic presentation theorem for every abstract genus-two curve. |
| **Circled superspecial / product isomorphism** | **Defined independently:** geometric unpolarized product isomorphism. Superspecial ⇒ supersingular and trivial p-torsion are proved. For both IKO curves, superspeciality implies parameter vanishing and Cartier zero. | The converse Cartier zero ⇒ product isomorphism; the general Cartier/superspecial criterion. |
| **Boxed Newton polygon** | **Defined:** lower coefficient hulls, normalized valuations, and the polygon of a finite-field Witt-vector F-isocrystal. Isomorphism invariance and a genuine rank-two half-slope example over every prime field are proved. | Construct the isocrystal of the actual curves/Jacobians and prove the geometric supersingularity comparison. |
| **2. Higher-genus equivalent properties** | Both IKO families retain root ⇔ Cartier zero ⇔ Cartier square zero ⇔ geometric p-rank zero. **New:** for every separable quintic/sextic, matrix zero ⇔ Cartier zero, twisted-matrix square zero ⇔ Cartier square zero, and this last condition implies actual Jacobian p-rank zero. | General converse from p-rank zero; geometric superspecial/supersingular equivalences. No genus-five classification follows. |
| **3. Families A and B** | Both IKO hyperelliptic presentations have actual function fields, smooth proper models, full regular/global differential bases, Cartier matrices, and representing Jacobians. | The handwritten cyclic-cover presentations have not been related to these models by proved birational transformations. |
| **4. IKO parameter polynomial** | g_p and h_p characterize Cartier zero and p-rank zero in the two families; complements are ordinary. Separability, endpoints, degrees, root counts, and finite upper bounds for geometric superspecial parameter sets are proved. | Equality of superspecial parameter sets with root sets; supersingular interpretation; isomorphism-class counts. |
| **Boxed §1: matrix on dx/y, x dx/y** | **Proved for every separable quintic/sextic equation:** all-place regularity, full basis, actual Cartier coordinates with the correct Frobenius twist, and the corresponding basis/operator on scheme-global forms. | Present every abstract genus-two curve by such an equation; compare the operator with Jacobian Verschiebung/cotangent data. |
| **“Oort conjecture”** | The explicit source being followed is the IKO paper. | No separate, precise conjecture statement has been fixed or proved. |

The sheet's operator notation is handled through Cartier on differential forms. The comparison to the independently constructed Jacobian's Verschiebung has not been proved. “Superspecial” and “supersingular” remain separate geometric definitions; only the forward implication is currently established in general.

## Match to IKO §1, item by item

Source: Ibukiyama–Katsura–Oort, [*Supersingular curves of genus two and class numbers*, §1, printed pp. 128–139](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf). This ledger covers the whole section, not just its matrix calculation.

| IKO item | Status | Exact scope of the formalization |
|---|---|---|
| **§1.1, equations (1.1)–(1.5)** | **Proved for every presented separable quintic/sextic model** | Smooth proper model, genus two, full regular/global basis dx/y and x dx/y, actual Cartier coefficient matrix, and both zero/twisted-square-zero criteria. The assertion that every abstract genus-two curve admits such a presentation and the comparison with Jacobian Verschiebung are pending. |
| **Lemma 1.1(i)** | **Partial** | General presented models: Cartier square zero ⇔ M^(p) M = 0 ⇒ actual Jacobian p-rank zero. Both explicit families retain equivalence with p-rank zero. The geometric supersingularity equivalence remains open. |
| **Lemma 1.1(ii)** | **Forward implication proved for both families; partial generally** | Geometric superspeciality ⇒ Cartier zero on the full regular/global differential space, derived via actual p-torsion and the family calculations. The converse and the general genus-two lemma remain open. |
| **Lemma 1.1(iii)** | **Proved for the two families; partial generally** | Exact finite geometric p-torsion counts prove p-rank two precisely when the parameter polynomial is nonzero; the determinant criterion is also proved. The general genus-two theorem is pending. |
| **§1.2: reduced automorphisms and classes (1)–(6)** | **Pending** | The automorphism/quotient classification has not been formalized. |
| **Definition 1.2** | **Defined** | The paper's Legendre polynomial is implemented as the Deuring/Hasse polynomial, with separability available. |
| **Proposition 1.3** | **Pending** | The elliptic-quotient construction and the full geometric equivalences are missing. |
| **Remark 1.4** | **Pending** | The explicit elliptic-quotient equations are missing. |
| **§1.3 family setup** | **Proved for the explicit models; partial as classification** | Both branch polynomials are separable for admissible parameters; their function fields, smooth proper models, and representing Jacobians exist. Identification with the automorphism classes is pending. |
| **Proposition 1.5** | **Pending** | Classification of isomorphic parameters has not been proved. |
| **Definition 1.6** | **Defined** | `gPolynomial`; uniform family-A matrix formulas are proved from it. |
| **Definition 1.7** | **Defined** | `hPolynomial`; uniform family-B matrix formulas are proved from it. |
| **Proposition 1.8** | **Partial** | Family-A matrix formulas, global Cartier criteria, geometric p-torsion counts, p-ranks and the ordinary locus for p ≥ 5; now also the necessary root condition for geometric superspeciality. The supersingular equivalence remains open. |
| **Proposition 1.9** | **Partial** | Corresponding family-B results for odd primes, including the necessary superspecial root condition and exclusion of the entire admissible family from superspeciality when p = 3. The supersingular equivalence remains open. |
| **Proposition 1.10** | **Partial** | Cartier zero ⇔ Cartier square zero ⇔ p-rank zero for the two families; geometric superspeciality now implies these conditions. The converse, supersingularity equivalence, and elliptic-quotient statements remain open. |
| **Example following Proposition 1.10** | **Pending** | The characteristic-13 quotient example has not been formalized. |
| **Proposition 1.11** | **Pending** | The full class-(4) congruence statement and its geometric conclusion are missing. |
| **Proposition 1.12** | **Pending** | The full class-(5) congruence statement and its geometric conclusion are missing. |
| **Proposition 1.13** | **Characteristic-three full-space example proved; geometric classification pending** | Actual curve y² = x⁵ − 1, genus two, full regular/global spaces, nonzero square-zero Cartier, and actual Jacobian p-rank zero. The supersingular/non-superspecial geometric interpretation and remaining congruence cases are not proved. |
| **§1.4 / Proposition 1.14** | **Proved** | Separability of g_p for p ≥ 5 and h_p for p ≥ 3 over every field of characteristic p, using the main differential-equation proof. The four equations of (1.34), endpoint exclusions, degrees, and distinct geometric root counts are also proved. The analytic gamma-function presentation is replaced by an algebraic coefficient recurrence. |
| **Remark 1.15** | **Optional alternative, not implemented** | Proposition 1.14 is already proved by the main argument. This suggested geometric alternative is not an additional missing conclusion of Proposition 1.14. |


## Remaining work and preprint scope

The main remaining geometric bridge is **Cartier zero ⇒ Jacobian geometrically isomorphic to a product of supersingular elliptic curves**. This requires the curve/Jacobian Cartier–Verschiebung or Dieudonné comparison and a proved classification theorem. The full Lemma 1.1 supersingularity equivalence needs its own product-isogeny comparison. The existing geometric definitions have not been replaced by the matrix criteria.

The new general setup starts with a separable quintic/sextic equation. It does not prove that **every abstract genus-two curve** admits such an equation. Cartier formulas also have not yet been identified with an independently constructed Jacobian Verschiebung map. These are explicit boundaries of the §1.1 claim.

Newton polygons remain defined for valued polynomials and actual finite-field Witt-vector F-isocrystals, with invariance and a half-slope example proved. Attaching the relevant crystalline/F-isocrystal object to these curves or Jacobians and proving its geometric supersingularity comparison remain open. This checkpoint preserves the Newton work unchanged.

The complete §1 target still includes automorphisms, elliptic quotients, parameter-isomorphism classification, the remaining special congruence statements, and geometric interpretations. The handwritten cyclic-cover presentations still need proved birational maps to the implemented hyperelliptic models. No separately specified “Oort conjecture” is proved.

This checkpoint broadens the verified computational foundation substantially. A focused preprint can describe that bounded formalization, with substantial upstream reuse attributed. It would still be inaccurate to title or summarize the result as a complete formalization of IKO §1 or of all the professor's sheet.
