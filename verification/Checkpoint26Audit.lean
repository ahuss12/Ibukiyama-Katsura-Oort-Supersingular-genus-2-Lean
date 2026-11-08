import SupersingularCurves.Geometry.AffineInvariantDerivation
import SupersingularCurves.Geometry.CartierCechSquare
import SupersingularCurves.Geometry.FiniteIsogenyCotangentRank
import SupersingularCurves.Geometry.FiniteLocalGroupPrimeCotangent
import SupersingularCurves.Geometry.FiniteLocalGroupScheme
import SupersingularCurves.Geometry.FiniteQuotientGeometry
import SupersingularCurves.Geometry.FiniteSurjectivePoints
import SupersingularCurves.Geometry.FrobeniusBaseChangeDegree
import SupersingularCurves.Geometry.FrobeniusCechSquare
import SupersingularCurves.Geometry.FrobeniusFactorSymmetricBundle
import SupersingularCurves.Geometry.FrobeniusSquareLineBundle
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotient
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDegree
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDescent
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangent
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangentRank
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorHom
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorPoints
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorization
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorsDegree
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientPoints
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientVanishing
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupGroup
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupHeightOne
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupIdentity
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupOrder
import SupersingularCurves.Geometry.GroupHomFibre
import SupersingularCurves.Geometry.JacobianQuotientCotangent
import SupersingularCurves.Geometry.JacobianQuotientVerschiebung
import SupersingularCurves.Geometry.JacobianVerschiebungSquare
import SupersingularCurves.Geometry.JacobianVerschiebungTwistVanishing
import SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder
import SupersingularCurves.Geometry.LocalAlgebraPrimeLength
import SupersingularCurves.Geometry.LocalGroupInvariantDerivation
import SupersingularCurves.Geometry.PicardFrobeniusCotangent
import SupersingularCurves.Geometry.RankOneFactorCancellation
import SupersingularCurves.Geometry.SmoothFiniteQuotientDimension
import SupersingularCurves.Geometry.SymmetricProjectiveBundle
import SupersingularCurves.Geometry.VerschiebungZeroKernel
import SupersingularCurves.Hyperelliptic.GenusTwoQuotient
import SupersingularCurves.Hyperelliptic.GenusTwoQuotientVanishing
import SupersingularCurves.Hyperelliptic.GenusTwoSubgroupOrder
import SupersingularCurves.Hyperelliptic.GenusTwoVerschiebungSquare
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict
import P2M.Sol.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback
import P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
import P2M.Sol.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_smooth_of_field
import P2M.Sol.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict
import Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType

set_option autoImplicit false
set_option maxHeartbeats 0

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let modules : Array Lean.Name := #[
    `SupersingularCurves.Geometry.AffineInvariantDerivation,
    `SupersingularCurves.Geometry.CartierCechSquare,
    `SupersingularCurves.Geometry.FiniteIsogenyCotangentRank,
    `SupersingularCurves.Geometry.FiniteLocalGroupPrimeCotangent,
    `SupersingularCurves.Geometry.FiniteLocalGroupScheme,
    `SupersingularCurves.Geometry.FiniteQuotientGeometry,
    `SupersingularCurves.Geometry.FiniteSurjectivePoints,
    `SupersingularCurves.Geometry.FrobeniusBaseChangeDegree,
    `SupersingularCurves.Geometry.FrobeniusCechSquare,
    `SupersingularCurves.Geometry.FrobeniusFactorSymmetricBundle,
    `SupersingularCurves.Geometry.FrobeniusSquareLineBundle,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotient,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDegree,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDescent,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangent,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangentRank,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorHom,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorPoints,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorization,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorsDegree,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientPoints,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientVanishing,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupGroup,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupHeightOne,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupIdentity,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupOrder,
    `SupersingularCurves.Geometry.GroupHomFibre,
    `SupersingularCurves.Geometry.JacobianQuotientCotangent,
    `SupersingularCurves.Geometry.JacobianQuotientVerschiebung,
    `SupersingularCurves.Geometry.JacobianVerschiebungSquare,
    `SupersingularCurves.Geometry.JacobianVerschiebungTwistVanishing,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder,
    `SupersingularCurves.Geometry.LocalAlgebraPrimeLength,
    `SupersingularCurves.Geometry.LocalGroupInvariantDerivation,
    `SupersingularCurves.Geometry.PicardFrobeniusCotangent,
    `SupersingularCurves.Geometry.RankOneFactorCancellation,
    `SupersingularCurves.Geometry.SmoothFiniteQuotientDimension,
    `SupersingularCurves.Geometry.SymmetricProjectiveBundle,
    `SupersingularCurves.Geometry.VerschiebungZeroKernel,
    `SupersingularCurves.Hyperelliptic.GenusTwoQuotient,
    `SupersingularCurves.Hyperelliptic.GenusTwoQuotientVanishing,
    `SupersingularCurves.Hyperelliptic.GenusTwoSubgroupOrder,
    `SupersingularCurves.Hyperelliptic.GenusTwoVerschiebungSquare,
    `Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict,
    `P2M.Sol.S_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback,
    `P2M.Sol.S_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective,
    `P2M.Sol.S_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp,
    `P2M.Sol.S_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace,
    `P2M.Sol.S_AlgebraicGeometry_isReduced_of_smooth_of_field,
    `P2M.Sol.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed,
    `P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType,
    `Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation,
    `Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation,
    `Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict,
    `Theorems.Thm_AlgebraicGeometry_Scheme_quotient_baseChange_of_finiteLocallyFree_of_isPullback,
    `Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective,
    `Theorems.Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp,
    `Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace,
    `Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field,
    `Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_quotient,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finiteLocallyFree_equivalenceRelation_action,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed,
    `Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType]
  let advertised : Array Lean.Name := #[
    `SupersingularCurves.Geometry.AffineInvariantDerivation.point_coordinates,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.coordinates_point,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.point_injective,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.point_comp,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.point_pointMul,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.pointMul_natural,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.point_unit,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.pointMul_one_left,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.pointMul_one_right,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.translationLift_fst,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.translationLift_augmentation,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.exists_derivation,
    `SupersingularCurves.Geometry.AffineInvariantDerivation.exists_derivation_isUnit,
    `SupersingularCurves.Geometry.DifferentialChart.globalCartier_square_residue_adjoint,
    `SupersingularCurves.Geometry.DifferentialChart.absoluteCech_square_zero_of_globalCartier_square_zero,
    `SupersingularCurves.Geometry.GroupHomFibre.subsingleton_of_kernel_trivial,
    `SupersingularCurves.Geometry.GroupHomFibre.fibre_cotangent_finrank_eq_one,
    `SupersingularCurves.Geometry.GroupHomFibre.differential_finrank_eq_one,
    `SupersingularCurves.Geometry.FiniteLocalGroupScheme.cotangent_finrank_eq_one_of_finrank_eq_prime,
    `SupersingularCurves.Geometry.FiniteLocalGroupScheme.pointEquiv_comp,
    `SupersingularCurves.Geometry.FiniteLocalGroupScheme.fromSpecStalk_isIso,
    `SupersingularCurves.Geometry.FiniteLocalGroupScheme.fromSpecStalk_over,
    `SupersingularCurves.Geometry.FiniteLocalGroupScheme.stalkLaw_one,
    `SupersingularCurves.Geometry.FiniteQuotientGeometry.geometricallyConnected_of_surjective,
    `SupersingularCurves.Geometry.FiniteSurjectivePoints.pointMap_surjective,
    `SupersingularCurves.Geometry.SchemeFrobenius.map_isPullback,
    `SupersingularCurves.Geometry.SchemeFrobenius.map_finrank,
    `SupersingularCurves.Geometry.SchemeFrobenius.map_finrank_eq_const,
    `SupersingularCurves.Geometry.SchemeFrobenius.absoluteCech_projectionCech,
    `SupersingularCurves.Geometry.SchemeFrobenius.absoluteCech_projectionCechEquiv,
    `SupersingularCurves.Geometry.SchemeFrobenius.cechPullback_twice_projectionCechEquiv,
    `SupersingularCurves.Geometry.SchemeFrobenius.cechPullback_twice_eq_zero_of_absoluteCech_square_zero,
    `SupersingularCurves.Geometry.AbelianVariety.exists_frobenius_factor_iso_symmetric_bundle,
    `SupersingularCurves.Geometry.SchemeFrobenius.absolute_square_natural,
    `SupersingularCurves.Geometry.SchemeFrobenius.doubleRelative_projection,
    `SupersingularCurves.Geometry.SchemeFrobenius.doubleProjection_relative,
    `SupersingularCurves.Geometry.SchemeFrobenius.factor_absolute_square,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.nonempty_quotientData,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.relativeFrobeniusHom_isIsogeny,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.map_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientHom_left,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientHom_isIsogeny,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.isogenyFromOriginal_isIsogeny,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.finrank_eq_subgroup,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.finrank_eq_prime_of_dimension_two,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.finrank_of_verschiebungCotangent_eq_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.existsUnique_desc,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientMap_desc,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.desc_mul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientMap_frobeniusFactor,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.frobeniusFactor_mul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientMap_verschiebungFactor,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactor_mul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientMap_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactor_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientTwistMap_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorTwist_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungTwist_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungCotangent_eq_quotient_comp_factor,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungTwistCotangent_eq_quotientTwist_comp_factorTwist,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotient_verschiebungCotangent_eq_factorTwist_comp_quotient,
    `SupersingularCurves.Geometry.SchemeFrobenius.twistPointsEquiv_pointMap,
    `SupersingularCurves.Geometry.SchemeFrobenius.map_mul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientCotangent_finrank_eq_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorCotangent_finrank_eq_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorTwistCotangent_finrank_eq_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.frobeniusFactor_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactor_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.frobeniusFactorHom_left,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorHom_left,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.frobeniusFactorHom_isIsogeny,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorHom_isIsogeny,
    `SupersingularCurves.Geometry.SchemeFrobenius.relativePoint_mapPoint,
    `SupersingularCurves.Geometry.SchemeFrobenius.pointMap_map_injective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorPoint_kernel_trivial,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorPoint_injective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactorTwistPoint_injective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientMap_nsmul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientTwistMap_over,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.frobenius_eq_factor_comp_quotientTwist,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebung_eq_factorTwist_comp_quotient,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.subgroup_order_mul_frobeniusFactor_finrank,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.subgroup_order_mul_verschiebungFactor_finrank,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.frobeniusFactor_finrank_eq_prime,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungFactor_finrank_eq_prime,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.quotientPoint_kernel_trivial,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.pointsMap_injective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.pointsMap_surjective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.frobeniusPointsMap_bijective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.hasPRankOver_iff,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.hasPRankOver_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData.verschiebungCotangent_eq_zero_of_factor_ranks,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusionPoint_injective,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusionPoint_natural,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusionPoint_subgroupLaw_mul,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusionPoint_subgroupLaw_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusionPoint_subgroupLaw_inv,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.subgroupLaw_commutative,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusionHom_left,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.subgroupGroup_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusion_mul_map,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.inclusion_inv_map,
    `SupersingularCurves.Geometry.PointedCotangent.augmentation_globalGerm,
    `SupersingularCurves.Geometry.PointedCotangent.pow_eq_zero_of_absolute_eq_constant,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.absolute_eq_identity_constant,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.maximalIdeal_pow_eq_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.augmentationIdeal_pow_eq_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.subgroupLaw_one_eq_identityPoint,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.structure_eq_fibreToBase,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.identityPoint_coe_eq_fibreIdentityPoint,
    `SupersingularCurves.Geometry.FiniteGeometricPoints.finrank_eq_stalk_finrank,
    `SupersingularCurves.Geometry.FiniteLocalGroupScheme.finrank_eq_prime_of_cotangent_dimension_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.finrank_eq_prime_of_cotangent_dimension_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.cotangent_finrank_toBase_eq_fibre,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.finrank_eq_prime_of_fibre_cotangent_dimension_one,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.finrank_eq_prime_of_dimension_two,
    `SupersingularCurves.Geometry.GroupHomFibre.map_one,
    `SupersingularCurves.Geometry.GroupHomFibre.map_inv,
    `SupersingularCurves.Geometry.GroupHomFibre.inclusionPoint_injective,
    `SupersingularCurves.Geometry.GroupHomFibre.inclusionPoint_kernel,
    `SupersingularCurves.Geometry.GroupHomFibre.inclusionPoint_liftPoint,
    `SupersingularCurves.Geometry.GroupHomFibre.inclusionPoint_natural,
    `SupersingularCurves.Geometry.GroupHomFibre.law_one_eq_point,
    `SupersingularCurves.Geometry.Jacobian.groupScheme_twiceTwistZero_eq,
    `SupersingularCurves.Geometry.Jacobian.quotient_twistedVerschiebungCotangent_eq_zero_iff,
    `SupersingularCurves.Geometry.Jacobian.quotient_twistedVerschiebungCotangent_ne_zero,
    `SupersingularCurves.Geometry.Jacobian.quotient_twistedVerschiebungCotangent_comp_eq_zero_of_globalCartier_square_zero,
    `SupersingularCurves.Geometry.Jacobian.quotient_verschiebungCotangent_eq_zero_of_globalCartier_square_zero,
    `SupersingularCurves.Geometry.Jacobian.exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier_square_zero,
    `SupersingularCurves.Geometry.Jacobian.map_verschiebung_zero,
    `SupersingularCurves.Geometry.Jacobian.twistedPicardPullback_eq_map_verschiebung,
    `SupersingularCurves.Geometry.Jacobian.frobeniusCotangent_twist_eq_twistedVerschiebungCotangent,
    `SupersingularCurves.Geometry.Jacobian.frobeniusCotangent_eq_verschiebungCotangent,
    `SupersingularCurves.Geometry.Jacobian.verschiebungCotangent_twice_eq_zero_of_absoluteCech_square_zero,
    `SupersingularCurves.Geometry.Jacobian.differential_verschiebung_twice_eq_zero_of_absoluteCech_square_zero,
    `SupersingularCurves.Geometry.Jacobian.verschiebungCotangent_twice_eq_zero_of_globalCartier_square_zero,
    `SupersingularCurves.Geometry.Jacobian.differential_verschiebung_twice_eq_zero_of_globalCartier_square_zero,
    `SupersingularCurves.Geometry.PicardCohomology.frobeniusCotangent_eq_zero_iff_cechPullback_eq_zero,
    `SupersingularCurves.Geometry.SchemeFrobenius.cechPullback_twist_eq_zero_iff,
    `SupersingularCurves.Geometry.Jacobian.twistedVerschiebungCotangent_eq_zero_iff,
    `SupersingularCurves.Geometry.Jacobian.twistedVerschiebungCotangent_ne_zero,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.exists_generator_of_cotangent_finrank_one,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.span_powers_eq_top,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.finrank_le_of_pow_eq_zero,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.isUnit_of_augmentation_ne_zero,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.nilpotencyClass_eq_prime,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.minpoly_eq_X_pow_prime,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.finrank_eq_prime,
    `SupersingularCurves.Geometry.LocalAlgebraFrobeniusOrder.finrank_eq_prime_of_cotangent_dimension_one,
    `SupersingularCurves.Geometry.LocalAlgebraPrimeLength.nilpotent_pow_finrank,
    `SupersingularCurves.Geometry.LocalAlgebraPrimeLength.ker_eq_span_of_span_powers,
    `SupersingularCurves.Geometry.LocalAlgebraPrimeLength.cotangent_finrank_eq_one_of_generator,
    `SupersingularCurves.Geometry.LocalAlgebraPrimeLength.cotangent_finrank_eq_one,
    `SupersingularCurves.Geometry.LocalGroupInvariantDerivation.exists_derivation_augmentation_ne_zero,
    `SupersingularCurves.Geometry.LocalGroupInvariantDerivation.exists_derivation_isUnit,
    `SupersingularCurves.Geometry.PicardCohomology.frobeniusCotangent_cochain,
    `SupersingularCurves.Geometry.PicardCohomology.tangentCechEquiv_frobeniusCotangent,
    `SupersingularCurves.Geometry.PicardCohomology.frobeniusCotangent_twice_eq_zero,
    `SupersingularCurves.Geometry.PicardCohomology.picardPullback_eq_verschiebung,
    `SupersingularCurves.Geometry.PerfectFieldVerschiebung.map_verschiebung,
    `SupersingularCurves.Geometry.RankOneFactorCancellation.range_comp_eq_of_rank_one,
    `SupersingularCurves.Geometry.RankOneFactorCancellation.eq_zero_of_mem_rank_one_range,
    `SupersingularCurves.Geometry.RankOneFactorCancellation.middle_comp_eq_zero,
    `SupersingularCurves.Geometry.FiniteQuotientGeometry.topologicalKrullDim_eq_of_finite_surjective,
    `SupersingularCurves.Geometry.FiniteQuotientGeometry.smoothOfRelativeDimension_of_finite_surjective,
    `SupersingularCurves.Geometry.AbelianVariety.exists_symmetric_finiteBySections,
    `SupersingularCurves.Geometry.AbelianVariety.exists_frobenius_factor_iso_symmetric_projective_bundle,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.frobenius_eq_zero_iff_verschiebung_eq_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.vInclusion_frobenius_of_verschiebungCotangent_eq_zero,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.simultaneousKernelIsoVKernel_hom_inclusion,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.simultaneousKernelIsoVKernel_hom_toBase,
    `SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.simultaneousKernel_finrank_of_verschiebungCotangent_eq_zero,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_quotient_finrank_eq_prime_of_matrix,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_exists_degree_prime_quotient_of_globalCartier,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_quotient_verschiebungCotangent_eq_zero_of_globalCartier,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_quotient_verschiebungCotangent_eq_zero_of_matrix,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_exists_isogeny_to_zero_verschiebungCotangent_of_matrix,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_subgroup_order_eq_prime_of_matrix,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_subgroup_order_eq_prime_of_globalCartier,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_subgroup_order_eq_prime_of_regularCartier,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_verschiebungCotangent_twice_eq_zero_of_globalCartier,
    `SupersingularCurves.Hyperelliptic.SimpleRootModel.jacobian_verschiebungCotangent_twice_eq_zero_of_matrix]
  for name in advertised do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Advertised theorem missing or not a theorem: {name}"
  let mut counts : Array Nat := Array.replicate modules.size 0
  let mut sharedEntries : Nat := 0
  for j in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[j]!
    if modules.contains mod then
      let data := env.header.moduleData[j]!
      unless data.constNames == data.constants.map (·.name) do
        throwError "Inconsistent declaration table for {mod}"
      for info in data.constants do
        let name := info.name
        unless (env.checked.get.find? name).isSome do
          throwError "Missing checked declaration {name} from module {mod}"
        let origin := match env.getModuleIdxFor? name with
          | none => Lean.Name.anonymous
          | some idx => env.header.moduleNames[idx.toNat]!
        if origin != mod then sharedEntries := sharedEntries + 1
        if info.isAxiom && !allowed.contains name then
          throwError "Nonstandard axiom declaration {name} in {mod}"
        for i in [:modules.size] do
          if mod == modules[i]! then counts := counts.set! i (counts[i]! + 1)
        for ax in ← Lean.collectAxioms name do
          unless allowed.contains ax do
            throwError "Nonstandard axiom {ax} in {name} from module {mod}"
        let deps := info.type.getUsedConstants ++
          ((info.value? true).map (·.getUsedConstants)).getD #[]
        for dep in deps do
          unless (env.checked.get.find? dep).isSome do
            throwError "Missing dependency {dep} of {name} in {mod}"
          for ax in ← Lean.collectAxioms dep do
            unless allowed.contains ax do
              throwError "Nonstandard axiom {ax} in stored declaration {name} from {mod}"
  for i in [:modules.size] do
    unless counts[i]! > 0 do
      throwError "No declarations inspected in module {modules[i]!}"
    Lean.logInfo m!"Audited {counts[i]!} declarations from {modules[i]!}."
  Lean.logInfo m!"Inspected {sharedEntries} shared generated entries by stored type/body as well as resolved declaration."
  Lean.logInfo m!"Checkpoint 26 transitive axiom audit passed: {counts.foldl (· + ·) 0} new project/vendor declaration entries."
