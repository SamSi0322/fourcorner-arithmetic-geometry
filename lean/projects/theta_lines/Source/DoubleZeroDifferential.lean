import ThetaRegularFunctionDifferential

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicCurve KaehlerDifferential
namespace FourCorner.ThetaDoubleZeroDifferential
open ThetaRegularFunctionDifferential
variable {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]
local instance : ∀w : Place K F,w.DCoordGenerates := dCoordGenerates_of_isCurveOver

/-- The existing F-linear coefficient is the SAME native actual Place
coefficient, not a separately selected comparison or an assumed equality. -/
theorem coefficient_is_native (w : Place K F) (ω : Ω[F⁄K]) :
    coefficient w ω=w.differentialCoeff ω := rfl

/-- Every zero of order at least two has an actual differential coefficient
in the actual DVR maximal ideal. All Places and depths are retained; no
regularity/maximal-ideal assumption on Df and no characteristic-zero or
nonvanishing integer coefficient assumption is used. -/
theorem derivative_in_maximalIdeal_of_order_ge_two (w : Place K F) (f : F) (hf : f≠0)
    (ho : 2≤w.ord f) :
    ∃c : w.toValuationSubring,(c:F)=w.differentialCoeff (D K F f) ∧
      c∈IsLocalRing.maximalIdeal w.toValuationSubring := by
  let A := w.toValuationSubring
  let π : A := (IsDiscreteValuationRing.exists_irreducible A).choose
  have hπ : Irreducible π := (IsDiscreteValuationRing.exists_irreducible A).choose_spec
  have hπF : (π:F)≠0 := by
    intro hh
    exact hπ.ne_zero (Subtype.ext hh)
  have hπ2 : (π:F)^2≠0 := pow_ne_zero 2 hπF
  have hπord : w.ord ((π:F)^2)=2 := by
    rw [pow_two,w.ord_mul hπF hπF,w.ord_coe_irreducible hπ]
    norm_num
  let u : F := f/(π:F)^2
  have hu0 : u≠0 := div_ne_zero hf hπ2
  have huord : w.ord u=w.ord f-2 := by
    dsimp [u]
    rw [div_eq_mul_inv,w.ord_mul hf (inv_ne_zero hπ2),w.ord_inv,hπord]
    ring
  have hu : u∈A := w.mem_of_ord_nonneg hu0 (by rw [huord];omega)
  have hfac : f=(π:F)^2*u := by
    dsimp [u]
    field_simp
  let d : A := ⟨coefficient w (D K F u),coefficient_D_mem w u hu⟩
  have hcoefπ : coefficient w (D K F (π:F))=1 := by
    change w.differentialCoeff _=1
    have hcoord : w.dCoord=D K F (π:F) := rfl
    rw [←hcoord,w.differentialCoeff_dCoord]
  let c : A := π*(π*d+(2:A)*⟨u,hu⟩)
  refine ⟨c,?_,?_⟩
  · change (π:F)*((π:F)*(d:F)+(2:F)*u)=coefficient w (D K F f)
    rw [hfac,Derivation.leibniz,Derivation.leibniz_pow,map_add]
    simp only [map_smul,map_nsmul,nsmul_eq_mul,smul_eq_mul,hcoefπ,
      Nat.reduceSub,pow_one,mul_one]
    change (π:F)*((π:F)*coefficient w (D K F u)+(2:F)*u)=_
    ring
  · have hpmax : π∈IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
    exact (IsLocalRing.maximalIdeal A).mul_mem_right (π*d+(2:A)*⟨u,hu⟩) hpmax

#print axioms coefficient_is_native
#print axioms derivative_in_maximalIdeal_of_order_ge_two
end FourCorner.ThetaDoubleZeroDifferential
