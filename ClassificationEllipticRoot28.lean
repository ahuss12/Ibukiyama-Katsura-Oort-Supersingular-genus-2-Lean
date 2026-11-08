import SupersingularCurves.Elliptic.Legendre
set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Elliptic

open Polynomial WeierstrassCurve

theorem exists_supersingular_legendre {K : Type*} [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) :
    ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ IsSupersingular p (legendreCurve t) := by
  let H : K[X] := hassePolynomial p
  have hdeg : H.natDegree = (p - 1) / 2 :=
    P2MW.S_Polynomial_separable_deuringPolynomial_map.Polynomial.natDegree_deuringPolynomial_map p
  have hp := (Fact.out : p.Prime).two_le
  have hpos : 0 < H.natDegree := by rw [hdeg]; omega
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root H (by
    intro h
    have hz : H.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some (n := 0) h
    omega)
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    have he : H.eval 0 = 1 :=
      P2MW.S_Polynomial_separable_deuringPolynomial_map.Polynomial.eval_zero_deuringPolynomial_map p
    exact one_ne_zero (he.symm.trans ht)
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    have he : H.eval 1 = (-1 : K) ^ ((p - 1) / 2) :=
      P2MW.S_Polynomial_separable_deuringPolynomial_map.Polynomial.eval_one_deuringPolynomial_map p
    exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) (he.symm.trans ht)
  exact ⟨t, ht0, ht1, (legendre_isSupersingular_iff p hp2 t ht0 ht1).mpr ht⟩

end SupersingularCurves.Elliptic

