# Checkpoint 26 scope review

The completed reduction is an actual geometric construction. For every represented separable genus-two quintic or sextic over an algebraically closed field of odd characteristic, full-space Cartier squared zero gives an actual isogeny from the original representing Jacobian to an actual abelian surface with zero Verschiebung cotangent differential. All scalar extension, degree, kernel, group-law, rank and twice-V hypotheses on the nonzero branch are proved in the new modules.

## Reviewed interfaces

- `SimpleRootModel.jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier` in `Hyperelliptic/GenusTwoQuotientVanishing.lean` requires only the model's separability/degree/odd-characteristic hypotheses, an actual representing Jacobian, and Cartier squared zero. It covers the zero Cartier branch with the identity isogeny and the nonzero branch with relative Frobenius followed by the actual quotient.
- `QuotientData` contains quotient properties, but its inhabitance is proved from the actual simultaneous finite-flat subgroup and the pinned quotient theorem. Quotient existence is not a new premise for the final existence result.
- The actual quotient map of degree p has source A^(p). The map from the original A includes F_A; it is an isogeny, and is not advertised as degree p.
- The actual zero differential statement is about independently constructed Verschiebung on the actual quotient group scheme, not an operator named after it.
- The Cartier-square bridge uses `CartierCechSquare`, `FrobeniusCechSquare`, `PicardFrobeniusCotangent` and `JacobianVerschiebungSquare`. Two actual relative Cech pullbacks and their independently identified Picard pullbacks reach the actual V^(p) followed by V. No missing scheme-projection cotangent normalization is assumed.
- The matrix statement uses `(M.map (fun c => c^p)) * M = 0`, the correct semilinear twisted product.
- Actual finite group schemes of order p have cotangent dimension one by a proved local power-basis argument using derivations constructed from the group law. No classification of finite group schemes is assumed.

## Independent review and remaining boundary

A separate read-only review checked quotient existence and abelian properties, residual factor degrees, the actual twice-V comparison, and factor identities. It found no geometric classifier premise and no weakened geometric definitions. All 152 preceding proof modules and 1,936 preceding vendor Lean files retain their exact hashes. The complete new declaration audit and source integrity checks are recorded separately in the verification logs.

The remaining global theorem is: an actual abelian surface over an algebraically closed field with zero actual Verschiebung cotangent map is isomorphic as a group scheme to a product of supersingular elliptic curves. Neither Frobenius² periodicity nor the zero-dV quotient is this product. The independently defined superspecial/supersingular predicates are unchanged. This one missing product theorem would close the Cartier-zero implication and, by composing with the constructed isogeny, the Cartier-square-zero implication.

The actual residual Frobenius isomorphism also has a proved symmetric line-bundle compatibility: for any actual symmetric invertible L, its pullback of L^(p²) agrees by an actual sheaf isomorphism with pullback along the actual double Frobenius projection. This is supplied by `FrobeniusSquareLineBundle` and `FrobeniusFactorSymmetricBundle`. `SymmetricProjectiveBundle` also constructs the symmetric invertible sheaf with an actual finite projective presentation and combines these results, discharging caller-supplied bundle existence. No moduli point or product-decomposition premise is introduced.

Finite-field fixed-point descent, a compatible polarized moduli point, Tate/isogeny or endomorphism realization, and integral product splitting have not been supplied as a complete arithmetic route. No completed finite-field descent or elliptic product is claimed here. The wider sheet/IKO §1 ledger remains separate in `SECTION1_COVERAGE.md`.
