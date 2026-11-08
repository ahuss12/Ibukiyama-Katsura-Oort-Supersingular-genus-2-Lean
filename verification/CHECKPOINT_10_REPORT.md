# Supersingular curves mini-project — checkpoint 10

**Author:** Ameen Hussain  
**Report date:** 18 September 2026  
**Verification:** full build, source checks, all four example suites, and transitive axiom audit passed  
**Change in this delivery:** IKO Proposition 1.14 proved by the main differential-equation argument, with the four explicit equations, endpoint exclusions, exact degrees, and distinct-root counts.

Checkpoint 10 preserves the chain from the two explicit IKO equations to actual smooth proper curves, global differential forms, Picard-representing Jacobians, Cartier matrices, and geometric p-ranks. It adds the simple-root theorem for both parameter polynomials. **The complete professor's sheet and all of IKO §1 remain unfinished.**

## New in checkpoint 10: IKO Proposition 1.14

For every prime p ≥ 5, g_p is separable over any field of characteristic p. For every odd prime p ≥ 3, h_p is separable over any field of characteristic p. Lean also proves that neither polynomial vanishes at 0 or 1 and that their degrees are floor(p/3) and floor(p/4), respectively. Consequently, over an algebraically closed field, they have exactly those numbers of distinct roots. The h_3 boundary case is included: its degree and number of roots are both zero.

This follows the **main proof in IKO §1.4**, using the hypergeometric differential equation (1.31), with the parameters of (1.34). The optional geometric argument in Remark 1.15 is not needed to complete Proposition 1.14.

The common binomial family is

\[
B_{m,s}(x)=\sum_{j=0}^{m-s}\binom{m}{s+j}\binom{m}{j}x^j.
\]

The code proves its coefficient recurrence and the differential equation with a = −m, b = s−m, c = s+1:

\[
x(1-x)f''+[c-(a+b+1)x]f'-abf=0.
\]

With m = (p−1)/2, taking s = floor((p+1)/6) gives g_p, and taking s = floor((p+1)/4) gives h_p. The endpoint identities B(0) = binom(m,s) and B(1) = binom(2m,m−s), together with 2m < p, prove that those values are nonzero. This supplies all assumptions of the general separability lemma for these polynomials.

The crucial root argument is explicit: if both f(t) and f′(t) vanish at t ≠ 0,1, repeated differentiation of the differential equation forces every derivative to vanish at t. But for n = degree(f) < p, the n-th derivative is the nonzero constant n! times the leading coefficient. The contradiction excludes repeated roots. The degree bound is essential; a compiled characteristic-five example uses f = x^5−2 to show why it cannot be omitted.

The four equations are proved as polynomial identities, with denominators cleared:

| Polynomial and prime class | Verified differential equation |
|---|---|
| g_p, p ≡ 1 mod 6 | 6x(1−x)g″ + (5−11x)g′ − g = 0 |
| g_p, p ≡ 5 mod 6 | 6x(1−x)g″ + (7−13x)g′ − 2g = 0 |
| h_p, p ≡ 1 mod 4 | 8x(1−x)h″ + (6−14x)h′ − h = 0 |
| h_p, p ≡ 3 mod 4 | 8x(1−x)h″ + (10−18x)h′ − 3h = 0 |

The development uses the original, unnormalized polynomials. This is valid because the equations are homogeneous. It proves the algebraic coefficient identities directly; it does not formalize the paper's analytic gamma-function presentation or infinite hypergeometric series.

The root counts concern **parameter values**, not isomorphism classes of curves. Combined mathematically with the retained family criteria, they describe the finite parameter loci with Cartier zero and geometric p-rank zero. Their interpretation as geometrically superspecial or supersingular Jacobians still needs the comparison theorems listed below.

Four new modules add 39 public theorem declarations: 31 new supporting/specialization declarations and eight generalized/adapted declarations. The derivative-propagation proof structure and distinct-root cardinality argument generalize the already vendored Deuring-polynomial proof from Anthropic's pinned FLT repository. Exact attribution is in `provenance/hypergeometric-generalization.json`; all upstream notices remain included. These counts describe declarations, not independent mathematical discoveries.

## What is proved for the two families

The implemented presentations are

\[
C^A_t:\quad y^2=(x^3-1)(x^3-t),\qquad
C^B_t:\quad y^2=x(x^2-1)(x^2-t).
\]

For the complete geometric family results, K is algebraically closed of prime characteristic p, t ≠ 0,1, with p ≥ 5 for A and p ≥ 3 for B. The code also carries the corresponding nonzero-characteristic witnesses explicitly.

For each admissible parameter, Lean constructs a smooth proper integral curve and a genuine Picard-representing Jacobian of dimension two. Its group law comes from tensoring line bundles. There is an Abel–Jacobi morphism taking the chosen base point to the identity, an additive equivalence between degree-zero divisor classes and Jacobian points, and an equivalence of their independently defined n-torsion groups.

The differential basis consists of dx/y and x dx/y. Both regularity at every place and completeness of the basis are proved. The global-form representation uses compatible Kähler forms on a two-affine cover of the actual curve. Its correspondence with regular function-field differentials is proved to be generic restriction followed by the specified field isomorphism.

Write P(t) for g_p(t) in A and h_p(t) in B. The proved conclusions are:

| Parameter condition | Geometric Jacobian p-torsion cardinality | p-rank | Ordinary | Cartier on all global forms |
|---|---:|---:|---|---|
| P(t) = 0 | 1 | 0 | No | Zero; its square is zero |
| P(t) ≠ 0 | p² | 2 | Yes | Nonzero; its square is nonzero |

Finiteness of the torsion sets is proved explicitly. These counts concern geometric points over the algebraically closed base, not rational points over a smaller finite field. Ordinary is defined by p-rank equal to dimension. The root condition is not used as the definition of superspeciality or supersingularity.

For the raw coefficient matrix M and Frobenius σ, the coordinate action is C(v) = σ⁻¹(Mv), entrywise. The square-zero criterion uses σ(M)M, with the order and twist proved in Lean.

## Where to inspect the proofs

Paths in this table are relative to `SupersingularCurves/` inside the archive. The complete declaration inventory is `verification/proved-theorems.json`.

| Result | File and representative declaration |
|---|---|
| Geometric elliptic definition and Hasse criterion | `Elliptic/Supersingular.lean`: `IsSupersingular`, `isSupersingular_iff_hasseInvariant_eq_zero` |
| Legendre criterion and separability | `Elliptic/Legendre.lean`: `legendre_isSupersingular_iff`, `hassePolynomial_separable` |
| Independent geometric product predicates | `Geometry/Superspecial.lean`: `IsSuperspecialOver`, `IsSupersingularOver`, `IsSuperspecial.isSupersingular` |
| Genuine Jacobian existence | `Geometry/JacobianConstruction.lean`: `jacobianRealization_nonempty`, `constructJacobian` |
| Family p-torsion, p-rank, and ordinarity | `IKO/Jacobians.lean`: `card_familyAJacobian_torsion`, `familyAJacobian_pRank`, `familyAJacobian_ordinary_iff`, and their B counterparts |
| Global basis and Cartier root criteria | `IKO/GlobalForms.lean`: `familyAGlobalBasis_restrict`, `familyA_globalCartier_coordinates`, `familyA_all_globalCartier_zero_iff`, `familyA_all_globalCartier_square_zero_iff`, and B counterparts |
| Polynomial Newton polygon | `NewtonPolygon/Basic.lean`: `ofPolynomial`, `padic` |
| Actual finite-field isocrystal polygon | `NewtonPolygon/Isocrystal.lean`: `ofIsocrystal`, `ofIsocrystal_eq_of_equiv` |
| Genuine half-slope example | `NewtonPolygon/HalfSlope.lean`: `halfSlope_newton` |
| General differential-equation root argument | `IKO/Hypergeometric.lean`: `not_isRoot_derivative_of_hypergeometric`, `separable_of_hypergeometric` |
| Binomial recurrence and endpoint values | `IKO/BinomialPolynomial.lean`: `binomialPolynomial_coeff_recurrence`, `eval_one_binomialPolynomial`, `binomialPolynomial_separable` |
| IKO Proposition 1.14 and distinct-root counts | `IKO/SimpleRoots.lean`: `gPolynomial_separable`, `hPolynomial_separable`, `card_roots_gPolynomial`, `card_roots_hPolynomial` |
| The four equations from IKO (1.34) | `IKO/HypergeometricEquations.lean`: `gPolynomial_equation_mod_six_one`, `gPolynomial_equation_mod_six_five`, `hPolynomial_equation_mod_four_one`, `hPolynomial_equation_mod_four_three` |

For a finite field of size p^r, the isocrystal construction proves that the r-th Frobenius iterate is linear, takes its reversed characteristic polynomial, and normalizes the Witt valuation by r, with v_W(p) = 1. The rank-two block F(x,y) = (σ(y), pσ(x)) is constructed over perfect fields; its Newton polygon is computed over every prime field as the segment from (0,0) to (2,1). No crystalline/isocrystal realization of either family Jacobian has yet been constructed.

## Match to the professor's sheet

**Status key:** “proved” means a Lean theorem within the stated assumptions; “defined” means the mathematical object or predicate exists; “partial” means part of the requested result is still missing. None of the pending statements is an assumed theorem in this project.

| Sheet item | Verified in checkpoint 10 | Still required |
|---|---|---|
| **0. Elliptic curve E over a finite/perfect field** | Actual Weierstrass curves over a general field; finite and perfect fields are included. Nonsingularity is required in the supersingularity predicate. | Identification of the separate Weierstrass-point and scheme-group implementations. |
| **1. Definition of E supersingular** | **Defined geometrically:** after extension to an algebraic closure, the only point killed by p is the identity. | No missing definition. |
| **2. Equivalent elliptic properties** | **Proved in odd characteristic:** equivalence with Hasse-invariant vanishing, and invariance under extending the field. | The complete collection of elliptic characterizations, including comparison with the isogeny definition. |
| **3–4. Legendre family and examples** | **Proved:** ellipticity for t ≠ 0,1; supersingularity iff the Deuring/Hasse polynomial vanishes; separability of that polynomial; concrete examples. | Connection to the separate genus-five project's construction, if included in the eventual manuscript. |
| **0–1. Curves of genus g and C supersingular** | Actual curve/Jacobian framework. Over an algebraically closed base, the curve predicate uses a Picard-representing Jacobian and the geometric product-isogeny predicate. Both IKO family curves and their Jacobians are constructed, with genus/dimension two proved. | General geometric Cartier criteria; descent of the complete family results to arbitrary perfect ground fields. |
| **Circled superspecial / product isomorphism** | **Defined independently:** the Jacobian is isomorphic, as an unpolarized abelian variety, to a product of supersingular elliptic curves. Superspecial ⇒ supersingular is proved. | Prove that Cartier vanishing is equivalent to this geometric isomorphism condition. |
| **Boxed Newton polygon** | **Defined:** lower coefficient hulls, normalized valuations, and the polygon of a finite-field Witt-vector F-isocrystal. Isomorphism invariance and a genuine rank-two half-slope example over every prime field are proved. | Construct the isocrystal of the actual curves/Jacobians and prove the geometric supersingularity comparison. |
| **2. Higher-genus equivalent properties** | For the two IKO families, the parameter-root, Cartier-zero, Cartier-square-zero, and geometric p-rank-zero conditions are proved equivalent. | The links to geometric superspeciality and supersingularity; the corresponding general genus-two results. No genus-five classification follows from these family results. |
| **3. Families A and B** | Both IKO hyperelliptic presentations have actual function fields, smooth proper models, full regular/global differential bases, Cartier matrices, and representing Jacobians. | The handwritten cyclic-cover presentations have not been related to these models by proved birational transformations. |
| **4. IKO parameter polynomial** | g_p and h_p are defined. Their roots characterize Cartier vanishing and p-rank zero for the corresponding actual Jacobians; their complements are exactly the ordinary loci. **New:** both polynomials are separable, their roots avoid 0 and 1, and their exact degrees and distinct geometric root counts are proved. | Their geometric superspecial/supersingular interpretation and the count after identifying isomorphic parameters. |
| **Boxed §1: matrix on dx/y, x dx/y** | **Proved for both families:** these form a full basis; the actual Cartier operator has the calculated semilinear matrix, including the correct Frobenius twist under iteration. The basis is connected to global forms on the curve. | General setup for an arbitrary genus-two curve and comparison with Jacobian Verschiebung/cotangent data. |
| **“Oort conjecture”** | The explicit source being followed is the IKO paper. | No separate, precise conjecture statement has been fixed or proved. |

The sheet's operator notation is handled through Cartier on differential forms. The comparison to the independently constructed Jacobian's Verschiebung has not been proved. “Superspecial” and “supersingular” remain separate geometric definitions; only the forward implication is currently established in general.

## Match to IKO §1, item by item

Source: Ibukiyama–Katsura–Oort, [*Supersingular curves of genus two and class numbers*, §1, printed pp. 128–139](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf). This ledger covers the whole section, not just its matrix calculation.

| IKO item | Status | Exact scope of the formalization |
|---|---|---|
| **§1.1, equations (1.1)–(1.5)** | **Proved for the two families; partial generally** | Actual smooth proper curves, genus two, full basis dx/y and x dx/y, actual Cartier and coefficient matrices, and canonical passage to global forms. The assertion for every genus-two curve is pending. |
| **Lemma 1.1(i)** | **Partial** | Cartier-square-zero matrix/root criteria and geometric p-rank-zero criteria are proved for both families. The equivalence with geometric supersingularity is pending. |
| **Lemma 1.1(ii)** | **Partial** | Cartier-zero matrix/root criteria are proved for both families. The equivalence with a product isomorphism of the Jacobian is pending. |
| **Lemma 1.1(iii)** | **Proved for the two families; partial generally** | Exact finite geometric p-torsion counts prove p-rank two precisely when the parameter polynomial is nonzero; the determinant criterion is also proved. The general genus-two theorem is pending. |
| **§1.2: reduced automorphisms and classes (1)–(6)** | **Pending** | The automorphism/quotient classification has not been formalized. |
| **Definition 1.2** | **Defined** | The paper's Legendre polynomial is implemented as the Deuring/Hasse polynomial, with separability available. |
| **Proposition 1.3** | **Pending** | The elliptic-quotient construction and the full geometric equivalences are missing. |
| **Remark 1.4** | **Pending** | The explicit elliptic-quotient equations are missing. |
| **§1.3 family setup** | **Proved for the explicit models; partial as classification** | Both branch polynomials are separable for admissible parameters; their function fields, smooth proper models, and representing Jacobians exist. Identification with the automorphism classes is pending. |
| **Proposition 1.5** | **Pending** | Classification of isomorphic parameters has not been proved. |
| **Definition 1.6** | **Defined** | `gPolynomial`; uniform family-A matrix formulas are proved from it. |
| **Definition 1.7** | **Defined** | `hPolynomial`; uniform family-B matrix formulas are proved from it. |
| **Proposition 1.8** | **Partial** | All family-A matrix formulas, global Cartier root criteria, geometric p-torsion counts, p-ranks, and the ordinary locus are proved for primes p ≥ 5. The supersingular conclusion is pending. |
| **Proposition 1.9** | **Partial** | Corresponding family-B results are proved for all odd primes, including p = 3. The supersingular conclusion is pending. |
| **Proposition 1.10** | **Partial prerequisites only** | For the two explicit families, Cartier zero and square zero have the same parameter-root criterion, and p-rank is either zero or two. The geometric equivalences and elliptic-quotient statements are pending. |
| **Example following Proposition 1.10** | **Pending** | The characteristic-13 quotient example has not been formalized. |
| **Proposition 1.11** | **Pending** | The full class-(4) congruence statement and its geometric conclusion are missing. |
| **Proposition 1.12** | **Pending** | The full class-(5) congruence statement and its geometric conclusion are missing. |
| **Proposition 1.13** | **Partial calculation only** | In characteristic three, the fifth-power example distinguishes Cartier zero from square zero under explicit function-field hypotheses. Its full regular basis, geometric interpretation, and remaining congruence cases are missing. |
| **§1.4 / Proposition 1.14** | **Proved** | Separability of g_p for p ≥ 5 and h_p for p ≥ 3 over every field of characteristic p, using the main differential-equation proof. The four equations of (1.34), endpoint exclusions, degrees, and distinct geometric root counts are also proved. The analytic gamma-function presentation is replaced by an algebraic coefficient recurrence. |
| **Remark 1.15** | **Optional alternative, not implemented** | Proposition 1.14 is already proved by the main argument. This suggested geometric alternative is not an additional missing conclusion of Proposition 1.14. |

## Compilation and verification evidence

Completed at **2026-09-18T02:51:30.759244+00:00**. The restored baseline was rebuilt from its saved sources, including the selected FLT dependencies. After integrating the four new proof modules, the complete verification script passed. The new modules were compiled through Lake in that final gate; previously built dependencies were reused. All 80 recorded checked source hashes remained unchanged during verification.

| Check | Result |
|---|---|
| Full project build with all 45 proof modules and aggregate import | **Passed** |
| Source hashes, pinned provenance, exact vendor closure, and prior-checkpoint preservation | **Passed** |
| Full-basis examples | **Passed** |
| Divisor-class torsion examples | **Passed** |
| Actual Jacobian/global-form examples | **Passed** |
| Eight simple-root/degree-bound examples | **Passed** |
| Transitive axiom audit | **Passed** |

The axiom audit inspected **1130 project declarations and 24884 imported FLT declarations**, permitting only `propext`, `Classical.choice`, and `Quot.sound`. The source scan found no admitted-proof, nonstandard-axiom, or native-evaluation markers in 1479 project/vendored Lean source files. `verification/checkpoint-10-run.json` records the run and log hashes; `verification/source-scan.json` records the scan. Compiler style warnings in retained upstream code do not indicate unproved goals or failed gates.

Lean is pinned to 4.34.0-rc2 and Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`. The source archive contains the package lock, proof inventory, source hashes, provenance records, and final verification logs. It excludes dependency caches and binary build products.

The project contains **370 public theorem declarations in 45 proof modules**, plus nine private supporting lemmas. All 41 checkpoint-9 proof modules are byte-for-byte unchanged. The selected vendored dependency closure still contains 1433 modules: 1427 unchanged and six documented statement-preserving compatibility ports. No additional vendor module was needed for this milestone.

On a normal Lean installation, extract the archive and run from its project directory:

```sh
lake exe cache get
bash verification/verify.sh
```

An optional separate build cache, `supersingular-mini-checkpoint-10-build-cache.tar.zst`, preserves 10353 compiled artifacts from this verified run (219.4 MiB compressed). It excludes compiler binaries, external package caches, and large generated setup JSON files. See `verification/BUILD_CACHE.md` for restoration instructions and `verification/build-cache-record.json` for its checksum. It is a convenience for the pinned Linux environment; the source archive remains independently buildable.

The hosted verification uses the included executable-path compatibility shim to resolve the compiler's own `/proc` executable lookup. It changes no proof checking and is unnecessary for a normal local installation.

## Remaining mathematical work

The central missing theorem is the comparison of Cartier conditions with the independently defined geometric product-isomorphism and product-isogeny conditions. Actual Jacobians and their point groups now exist in the development, but the required geometric classification is not yet proved.

A separate missing bridge attaches a crystalline/isocrystal object to these actual curves or Jacobians and relates its Newton polygon to geometric supersingularity. The other pending IKO §1 rows—automorphisms, quotients, parameter isomorphisms, and the remaining congruence examples—also remain part of the requested work. Proposition 1.14 is now complete.

A defensible manuscript scope now includes the actual family Cartier and p-rank calculations together with the simple-root theorem and its differential-equation proof. A manuscript claiming all of IKO §1, the entire sheet, a genus-five supersingularity theorem, or an Oort conjecture would still exceed the verified results. The next central mathematical milestone is the geometric Cartier–superspeciality comparison.
