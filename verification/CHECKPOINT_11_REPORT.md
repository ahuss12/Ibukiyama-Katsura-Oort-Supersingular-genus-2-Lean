# Supersingular curves mini-project — checkpoint 11

**Author:** Ameen Hussain  
**Report date:** 18 September 2026  
**Verification:** fresh project compilation, source audit, all five example suites, and transitive axiom audit passed  
**New result:** geometric superspeciality implies the polynomial-root and Cartier-zero conditions for both actual IKO curves; finite superspecial parameter bounds follow.

This checkpoint proves a genuine forward link from the independent product-isomorphism definition to the calculations already formalized. It handles every representing Jacobian and every base point. **The converse, the full IKO §1 classification, and the geometric Newton comparison remain unfinished.** No percentage of completion is assigned: the remaining classification bridges are substantial theorems.

## The new mathematical result

Let k be algebraically closed of prime characteristic p, and let t be different from 0 and 1. The actual smooth proper genus-two models have function fields given by

\[
A_t:\quad y^2=(x^3-1)(x^3-t),\qquad
B_t:\quad y^2=x(x^2-1)(x^2-t).
\]

Use p ≥ 5 for A and p ≥ 3 for B. Write P = g_p or h_p respectively. Lean now proves

\[
C_t\text{ geometrically superspecial}
\ \Longrightarrow\ f(\operatorname{Jac}(C_t))=0
\ \Longleftrightarrow\ P(t)=0
\ \Longleftrightarrow\ \mathcal C|_{H^0(C_t,\Omega^1)}=0.
\]

Here geometric superspeciality means that the actual Jacobian, after scalar extension to an algebraic closure, is isomorphic **as an unpolarized group scheme** to a product of supersingular elliptic curves. It is not defined by Cartier zero. The p-rank uses the actual group of geometric p-torsion points. The global differential space is the previously constructed scheme-global space, with its proved identification with regular function-field differentials.

The first implication is new. The subsequent equivalences were proved earlier for these two families. No converse from the root condition to geometric superspeciality is claimed.

For the sets of admissible geometric superspecial parameters, Lean further proves

\[
\#\{t:A_t\text{ superspecial}\}\leq\lfloor p/3\rfloor,
\qquad
\#\{t:B_t\text{ superspecial}\}\leq\lfloor p/4\rfloor.
\]

Finiteness is proved separately, so these inequalities are not relying on the convention that the natural cardinal of an infinite set is zero. These are counts of parameter values, not isomorphism classes. Equality is not established. In characteristic three every admissible family-B curve is proved not superspecial, since h_3 = 1.

## How the bridge is proved

1. **Faithful extension of scalars on points.** For an actual abelian variety A/k and any field extension L/k in the same universe, the pullback construction gives a group homomorphism A(k) → A_L(L). It is injective by faithfully flat descent. This works without assuming that k is algebraically closed or perfect.
2. **Product projections kill p-torsion.** If an abelian variety is isomorphic to a product of supersingular elliptic curves, each projection of a p-torsion point is the identity. The categorical product property makes the point itself the identity. The scalar-extension injection yields the same necessary condition for geometric superspeciality over any ground field. Over an algebraically closed base this gives p-rank zero. Positive-dimensional ordinary abelian varieties are consequently not superspecial.
3. **Every representing Jacobian has the right point group.** The already vendored Picard theorem supplies a group-compatible divisor-class correspondence for any representation and base point. Thus torsion cardinality and p-rank do not depend on the chosen construction. This is a point-group result, not a newly proved uniqueness theorem for group schemes.
4. **Apply the existing family calculations.** The curve predicate existentially quantifies a representing Jacobian. Step 3 transfers its p-rank-zero consequence to the constructed family Jacobian, where the polynomial and Cartier criteria were already proved. A nonroot therefore excludes superspeciality of the curve for every possible witness.
5. **Use the proved root counts.** The actual superspecial parameter set lies in the finite root set of g_p or h_p. Checkpoint 10's degree/separability results give the displayed upper bounds.

This is the forward implication of IKO Lemma 1.1(ii) **for these two explicit families**, obtained through their special p-rank computations. It is not the proof of the full general lemma cited by IKO. The earlier proof of Proposition 1.14 still follows IKO's main differential-equation argument and is unchanged; the optional alternative in Remark 1.15 is still not needed.

## Code added

All paths below are relative to the archive's project directory.

| New module | Main declarations |
|---|---|
| `SupersingularCurves/Geometry/PointBaseChange.lean` | `pointsBaseChange`, `pointsBaseChange_injective` |
| `SupersingularCurves/Geometry/SuperspecialTorsion.lean` | `IsSuperspecial.torsion_trivial`, `IsSuperspecial.hasPRankOver_zero`, `IsOrdinaryOver.not_isSuperspecial` |
| `SupersingularCurves/Geometry/JacobianIndependence.lean` | `Jacobian.picardPoints_nonempty`, `Jacobian.hasPRankOver_iff`, `CurveModel.IsSuperspecial.hasPRankOver_zero` |
| `SupersingularCurves/IKO/GeometricObstructions.lean` | `familyA_anyJacobian_pRank_zero_iff`, `familyA_isSuperspecial_imp_root`, `familyA_isSuperspecial_imp_globalCartier_zero`, B counterparts, and nonroot exclusions |
| `SupersingularCurves/IKO/SuperspecialParameters.lean` | actual parameter sets, root-set containments, finiteness, `ncard_familyASuperspecialParameters_le` and B counterpart |

There are **27 added public theorem declarations**, bringing the project to **397 public theorem declarations across 50 proof modules**, plus nine private supporting lemmas. These are supporting and integration declarations, not counts of independent discoveries. All **45 checkpoint-10 proof modules are byte-for-byte unchanged**, including the Newton-polygon work and Proposition 1.14.

## Verification

Completed at **2026-09-18T04:30:45.958705+00:00**. The project build directory was cleared before verification. Lake freshly compiled all **50 proof modules and the aggregate import** (51 project compile units); pinned external/vendor dependencies were reused. All **89 checked source hashes** remained unchanged during the gate.

| Check | Result |
|---|---|
| Fresh full project compilation | Passed |
| Source provenance, exact vendor closure, and checkpoint-10 preservation | Passed |
| Full-basis example suite | Passed |
| Actual divisor-class torsion example suite | Passed |
| Jacobian/global-differential example suite | Passed |
| Simple-root and degree-bound example suite | Passed |
| New geometric superspecial obstruction example suite | Passed |
| Transitive axiom audit | Passed |

The audit checked **1172 project declarations and 24884 imported FLT declarations**, permitting only `propext`, `Classical.choice`, and `Quot.sound`. The source scan found no admitted-proof, extra-axiom, or native-evaluation markers in **1484 project/vendored Lean source files**. The exact run and log hashes are in `verification/checkpoint-11-run.json`; scan evidence is in `verification/source-scan.json`. Retained upstream style/deprecation warnings do not indicate unproved goals. No new proof module emitted a warning in the final build.

The new example suite checks four cases: every admissible family-B parameter in characteristic three is excluded from geometric superspeciality; family A at t = 2 in characteristic five is excluded; every representing Jacobian of family A at t = 4 in characteristic five has p-rank zero; and both parameter-count bounds specialize correctly in characteristic seven. The root example does **not** assert geometric superspeciality.

The pinned environment remains Lean 4.34.0-rc2 and Mathlib `85e3a25e006c35636f0e53b0e9296caca2685bc0`. The selected FLT source commit is `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`: 1433 modules, of which 1427 are unchanged and six have documented compatibility ports. No vendor module was added or modified in this checkpoint. The new reuse/provenance record is `provenance/geometric-obstructions.json`.

To rebuild with the pinned toolchain installed:

```sh
lake exe cache get
bash verification/verify.sh
```

An optional build cache, `supersingular-mini-checkpoint-11-build-cache.tar.zst`, preserves 10388 compiled artifacts (219.6 MiB compressed). Its checksum and restoration instructions are in `verification/build-cache-record.json` and `verification/BUILD_CACHE.md`. It omits the compiler, external package caches, and generated setup JSON files; the source archive builds independently of it.

The hosted verification uses the included executable-path compatibility shim, documented by its source in `verification/lean_app_path_compat.c`, to locate the installed compiler. It does not change Lean's proof checker. Previously compiled external package/vendor dependencies are reused; the project's generated build directory was cleared before the final run so all 50 proof modules and the aggregate import are recompiled.

## Match to the professor's sheet

**Status key:** “proved” means a Lean theorem within the stated assumptions; “defined” means the mathematical object or predicate exists; “partial” means part of the requested result is still missing. None of the pending statements is an assumed theorem in this project.

| Sheet item | Verified in checkpoint 11 | Still required |
|---|---|---|
| **0. Elliptic curve E over a finite/perfect field** | Actual Weierstrass curves over a general field; finite and perfect fields are included. Nonsingularity is required in the supersingularity predicate. | Identification of the separate Weierstrass-point and scheme-group implementations. |
| **1. Definition of E supersingular** | **Defined geometrically:** after extension to an algebraic closure, the only point killed by p is the identity. | No missing definition. |
| **2. Equivalent elliptic properties** | **Proved in odd characteristic:** equivalence with Hasse-invariant vanishing, and invariance under extending the field. | The complete collection of elliptic characterizations, including comparison with the isogeny definition. |
| **3–4. Legendre family and examples** | **Proved:** ellipticity for t ≠ 0,1; supersingularity iff the Deuring/Hasse polynomial vanishes; separability of that polynomial; concrete examples. | Connection to the separate genus-five project's construction, if included in the eventual manuscript. |
| **0–1. Curves of genus g and C supersingular** | Actual curve/Jacobian framework. Over an algebraically closed base, the curve predicate uses a Picard-representing Jacobian and the geometric product-isogeny predicate. Both IKO family curves and their Jacobians are constructed, with genus/dimension two proved. | General geometric Cartier criteria; descent of the complete family results to arbitrary perfect ground fields. |
| **Circled superspecial / product isomorphism** | **Defined independently:** geometric unpolarized product isomorphism. Superspecial ⇒ supersingular is proved. **New:** superspecial abelian varieties have trivial p-torsion; for both IKO curves geometric superspeciality implies polynomial vanishing and Cartier zero. | The converse Cartier zero ⇒ product isomorphism; the general Cartier/superspecial criterion. |
| **Boxed Newton polygon** | **Defined:** lower coefficient hulls, normalized valuations, and the polygon of a finite-field Witt-vector F-isocrystal. Isomorphism invariance and a genuine rank-two half-slope example over every prime field are proved. | Construct the isocrystal of the actual curves/Jacobians and prove the geometric supersingularity comparison. |
| **2. Higher-genus equivalent properties** | For both IKO families, parameter root ⇔ Cartier zero ⇔ Cartier square zero ⇔ geometric p-rank zero. **New:** p-rank is independent of the representing Jacobian and base point, and geometric superspeciality implies these conditions. | The reverse superspecial implication; links to geometric supersingularity; general genus-two criteria. No genus-five classification follows. |
| **3. Families A and B** | Both IKO hyperelliptic presentations have actual function fields, smooth proper models, full regular/global differential bases, Cartier matrices, and representing Jacobians. | The handwritten cyclic-cover presentations have not been related to these models by proved birational transformations. |
| **4. IKO parameter polynomial** | g_p and h_p are defined; their roots characterize Cartier zero and p-rank zero, and their complements are the ordinary loci. Separability, endpoint exclusions, exact degrees and root counts are proved. **New:** actual superspecial parameter sets lie in these root sets, are finite, and have sizes at most floor(p/3) and floor(p/4). | Equality of the superspecial parameter sets with the root sets; supersingular interpretation; isomorphism-class counts. |
| **Boxed §1: matrix on dx/y, x dx/y** | **Proved for both families:** these form a full basis; the actual Cartier operator has the calculated semilinear matrix, including the correct Frobenius twist under iteration. The basis is connected to global forms on the curve. | General setup for an arbitrary genus-two curve and comparison with Jacobian Verschiebung/cotangent data. |
| **“Oort conjecture”** | The explicit source being followed is the IKO paper. | No separate, precise conjecture statement has been fixed or proved. |

The sheet's operator notation is handled through Cartier on differential forms. The comparison to the independently constructed Jacobian's Verschiebung has not been proved. “Superspecial” and “supersingular” remain separate geometric definitions; only the forward implication is currently established in general.

## Match to IKO §1, item by item

Source: Ibukiyama–Katsura–Oort, [*Supersingular curves of genus two and class numbers*, §1, printed pp. 128–139](https://www.numdam.org/item/CM_1986__57_2_127_0.pdf). This ledger covers the whole section, not just its matrix calculation.

| IKO item | Status | Exact scope of the formalization |
|---|---|---|
| **§1.1, equations (1.1)–(1.5)** | **Proved for the two families; partial generally** | Actual smooth proper curves, genus two, full basis dx/y and x dx/y, actual Cartier and coefficient matrices, and canonical passage to global forms. The assertion for every genus-two curve is pending. |
| **Lemma 1.1(i)** | **Partial** | Cartier-square-zero matrix/root criteria and geometric p-rank-zero criteria are proved for both families. The equivalence with geometric supersingularity is pending. |
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
| **Proposition 1.13** | **Partial calculation only** | In characteristic three, the fifth-power example distinguishes Cartier zero from square zero under explicit function-field hypotheses. Its full regular basis, geometric interpretation, and remaining congruence cases are missing. |
| **§1.4 / Proposition 1.14** | **Proved** | Separability of g_p for p ≥ 5 and h_p for p ≥ 3 over every field of characteristic p, using the main differential-equation proof. The four equations of (1.34), endpoint exclusions, degrees, and distinct geometric root counts are also proved. The analytic gamma-function presentation is replaced by an algebraic coefficient recurrence. |
| **Remark 1.15** | **Optional alternative, not implemented** | Proposition 1.14 is already proved by the main argument. This suggested geometric alternative is not an additional missing conclusion of Proposition 1.14. |


## What should happen next

The principal remaining superspecial bridge is **Cartier zero ⇒ geometric product isomorphism** for the actual Jacobian. A defensible route needs the comparison between the curve's Cartier action and the Jacobian's cotangent/Dieudonné data, and a proved theorem turning maximal a-number into superspeciality. For the published comparison with product isomorphisms, see [Achter–Pries, Theorem 1.1, §2.3, and Lemma 3.7](https://arxiv.org/pdf/1403.0023). Their principally polarized formulation would also require supplying the canonical principal polarization of the constructed Jacobian. The current imported foundations do not supply that classification theorem. It must be implemented or imported with a verified proof; it cannot be substituted by the desired equivalence as a hypothesis.

A separate bridge is still needed between p-rank zero and the geometric product-isogeny definition of supersingularity in dimension two. P-rank zero must not be used as the definition of supersingularity in arbitrary genus. The Newton-polygon definitions, valuation normalization, isocrystal invariance, and rank-two half-slope example are already proved, but no crystalline/F-isocrystal realization of either family Jacobian has yet been attached to them.

For the complete IKO §1 target, automorphisms and elliptic quotients, isomorphic-parameter classification, and the remaining special congruence results also remain. The handwritten cyclic-cover presentations have not yet been related to these hyperelliptic models by proved birational maps. No separately specified “Oort conjecture” or genus-five supersingularity classification is proved here.

A preprint can eventually present a focused, precisely bounded formalization. This checkpoint adds a substantive geometric implication, but it does not justify describing the entire professor's sheet or IKO §1 as completed. A manuscript should distinguish the new integration proofs from the substantial reused Mathlib/FLT foundations and list the missing comparisons explicitly.
