import EllipticCurves.WeakMordellWeil

set_option pp.universes false

#check @WeierstrassCurve.Affine.f
#check @WeierstrassCurve.Affine.fCofactor
#check @WeierstrassCurve.Affine.fCofactor_eq_of_f_eq
#check @WeierstrassCurve.Affine.A
#check @WeierstrassCurve.Affine.M
#check @WeierstrassCurve.Affine.μX
#check @WeierstrassCurve.Affine.μX_of_eval_f_ne_zero
#check @WeierstrassCurve.Affine.μX_of_eval_f_eq_zero
#check @WeierstrassCurve.Affine.μ₀
#check @WeierstrassCurve.Affine.μ₀_zero
#check @WeierstrassCurve.Affine.μ₀_some
#check @WeierstrassCurve.Affine.μ
#check @WeierstrassCurve.Affine.μ_apply
#check @WeierstrassCurve.Affine.μ₀_two_nsmul
#check @WeierstrassCurve.Affine.eq_two_smul_of_μ_eq_one
#check @WeierstrassCurve.Affine.ker_μ_eq
#check @WeierstrassCurve.Affine.card_ker_nsmul_two
#check @WeierstrassCurve.Affine.projFactor_mk_C_sub_X
#check @WeierstrassCurve.Affine.projFactor_mk_C_sub_X_add_fCofactor
#check @WeierstrassCurve.Affine.mk_fCofactor_eq_zero
#check @WeierstrassCurve.Affine.normM
#check @WeierstrassCurve.Affine.range_μ_le_ker_normM
#check @AdjoinRoot.equivPiFactors
#check @AdjoinRoot.projFactor
#check @AdjoinRoot.projFactor_mk
#check @AdjoinRoot.modPowEquivPiFactors
#check @AdjoinRoot.modPowEquivPiFactors_unit
#check @AdjoinRoot.modPowEquivPiFactors_mk
#check @AdjoinRoot.modPow_mk_eq_one_iff_forall_factors
#check @Units.modPow.unit_eq_one_iff
#check @Units.modPow.mk_eq_mk_iff
#check @Units.modPow.mk_eq_one_iff_isSquare
#check @Units.modPow.map_unit
#check @Units.modPow.congr
#check @Units.modPow.piEquiv
#check @Polynomial.quotientSpanXSubCAlgEquiv
#check @QuotientGroup.quotientKerEquivRange

namespace SplitKummerAudit
open WeierstrassCurve.Affine

theorem mu_zero_iff_double {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)
    [DecidableEq K] [W.IsCharNeTwoNF] [W.IsElliptic] (P : W.Point) :
    W.μ₀ P = 1 ↔ ∃ Q : W.Point, 2 • Q = P := by
  change Multiplicative.ofAdd P ∈ (μ (W := W)).ker ↔ _
  rw [ker_μ_eq]
  change P ∈ (nsmulAddMonoidHom (α := W.Point) 2).range ↔ _
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]

#print axioms mu_zero_iff_double
#print axioms WeierstrassCurve.Affine.ker_μ_eq
#print axioms AdjoinRoot.modPowEquivPiFactors
end SplitKummerAudit
