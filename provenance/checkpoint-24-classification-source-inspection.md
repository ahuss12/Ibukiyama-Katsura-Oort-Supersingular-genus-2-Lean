# Bounded reverse-classification source inspection

Pinned source: `anthropics/fermats-last-theorem`, commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`.

This inspection did not identify a directly applicable theorem constructing an
elliptic-product isogeny from p-rank zero for an arbitrary abelian surface, or an
elliptic-product isomorphism from vanishing Verschiebung differential. This is a
bounded result, not a claim that every proof body in the repository lacks such
a theorem.

## Scope and reproducible evidence

The complete, untruncated Definitions and Theorems tree indices contain 30,961
Lean filenames (1,450 definitions and 29,511 theorem files). The selection
includes every filename matching the following case-insensitive rules:

1. One of `abelianscheme`, `abelianvar`, `goodreductionjacobian`,
   `relativegrouplaw`, `fakeelliptic`, together with one of `isogen`, `prod`,
   `decomp`, `froben`, `dieudonn`, `honda`, `split`, `quotient`, `pdivisible`.
2. Any of `dieudonn`, `honda`, `isocrystal`.
3. General p-divisible-group definitions and the `Thm_PDivisibleGroup` or
   `Thm_MvFormalGroup` theorem families with `pdivisible` in the filename.
4. `superspecial`, `complete_reducibility`, or `completereducibility`.

The resulting 359 sources consist of 12 definition files and 347 theorem files.
167 overlap the earlier checkpoint-22 content inspection; 192 are additional
sources (45 outside the FakeElliptic family and 147 within that family).
All 359 source byte strings were retrieved and verified against the pinned Git
blob hashes, with zero retrieval failures. `checkpoint-24-classification-content-audit.json` records those
hashes, independent SHA-256 hashes, sizes, and extracted declarations.

The complete additional non-FakeElliptic declarations were read. Within the
FakeElliptic family, filenames and candidate conclusions were screened, and the
concrete product, formal-algebraization, and double-Frobenius candidates below
were read in detail. The entire proof body of the double-Frobenius candidate was
also fetched and read; its separate hash record is retained in the inspection index. This does not constitute a full read of every
FakeElliptic proof body, every unnamed helper, or every unselected source.

The retained `checkpoint-24-classification-source-inspection.json` records all pinned source identities and hashes; `checkpoint-24-classification-content-audit.json` preserves extracted declarations. The downloaded full source bodies are reproducible from the repository pin. Retrieval and statement inspection do not constitute a successful Lean build of all selected sources.

## Concrete candidates and their exact limits

| Candidate | What its actual statement provides | Why it does not finish reverse classification |
|---|---|---|
| `RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup` | An actual abelian-scheme quotient, finite flat surjective quotient map, specified scheme kernel, and fppf quotient property | It takes the finite flat closed subgroup and its group closure laws as input; it also assumes an affine neighborhood of every finite point set. It does not construct the special subgroup or identify the quotient as an elliptic product. |
| Its `_of_affineOrbit_of_commRing` variant | The same construction over a general commutative ring, with an affine-orbit hypothesis | The subgroup remains an input. |
| `RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed` | A smooth quotient of dimension `g - h` by a given smooth closed normal subgroup of dimension `h` | It does not construct an elliptic subgroup of the original surface. |
| `FakeEllipticCurve.exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod` | Transports an existing product diagram and quaternion action across an isomorphism | Both a product pullback and an isomorphism to it are assumptions. It cannot establish the first product decomposition. |
| `FakeEllipticCurve.exists_iso_comp_eq_of_formalIso_comp_germ_eq_of_isIsogenyPair_of_hasHeight_four_of_isAlgClosed_of_constantCoeff_eq_zero` | Algebraizes a compatible formal isomorphism between two quaternionic fake elliptic curves already isogenous to a common object | Requires the quaternionic structures, actual isogeny pairs, formal coordinates, and compatible formal isomorphism as inputs. |
| `FakeEllipticCurve.iso_frobeniusTwist_frobeniusTwist_of_forall_nsmulPt_eq_one` | A double-Frobenius-twist isomorphism under trivial rational p-torsion | Requires a maximal quaternion order, an indefinite quaternion algebra ramified at two prescribed primes different from p, level prime to p, and given quaternionic Frobenius/Verschiebung data. Its proof invokes the specialized level-isogeny theorem; its auxiliary lemmas are inverse-isomorphism transport, preservation of the identity, and surjectivity of Frobenius on rational points. There is no general product-splitting helper in this proof. |
| `RelativeGroupLaw.exists_pDivisibleGroup_closedImmersion_isIso_torsion_of_abelianSchemePropertyBundle` (previously inspected, rechecked) | An attached p-divisible group with actual torsion-level closed immersions and exact torsion identification | This statement assumes an algebra from the local base ring into an algebraically closed characteristic-zero field. It cannot be directly instantiated with a characteristic-p field as base. Its more general construction predecessors may be reusable after separately supplying all hypotheses. |
| `DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent` and the p-divisible-tower realization theorem | Genuine realization of suitable Dieudonne data as finite Hopf algebras or towers over `ZMod p` | These are not realization as abelian varieties, and their base is not an arbitrary algebraically closed field. |
| Honda realization and finite Dieudonne full-faithfulness candidates | Finite Hopf-algebra and mixed-characteristic lifting constructions, with explicit F/V compatibility | They do not produce the required abelian-variety product isomorphism or isogeny. |
| Generic abelian-scheme analytic uniformization candidates | Complex lattices, quotient point equivalences, and associated analytic/algebraic homomorphisms | The base is the complex numbers; they are not a positive-characteristic surface classification. |

The last table is a statement-level applicability assessment. Existing genuine
quotient, finite-group realization, and specialized algebraization machinery
must not be described as wholly absent.

## Next foundational theorems, still requiring proofs

For the superspecial converse, a concrete next step is to pass from vanishing
of the actual Verschiebung differential at the identity to global vanishing by
translation, and then factor that actual morphism through relative Frobenius.
The section p-power-root and normality work being developed in checkpoint 24
addresses the local algebra for this step. The completed degree theorems give
both Frobenius and Verschiebung rank `p^g`, so an appropriate finite residual
factor can then have rank one. This does not by itself prove an elliptic-product
decomposition: a geometric splitting theorem remains necessary.

For p-rank-zero surfaces, a possible geometric route is to construct a suitable
finite flat subgroup with a superspecial quotient, apply the existing genuine
quotient theorem, and prove the superspecial product splitting. The subgroup
construction and the quotient's required differential property are new
mathematical obligations, not established results of this inspection. An
alternative p-divisible/isocrystal route likewise requires an actual attachment,
the needed rank-four classification, and an abelian isogeny realization theorem.

No classification conclusion was introduced as an axiom, a replacement
definition, or a hypothesis in a purported completion. This inspection itself
changes no project proof sources or manifests.
