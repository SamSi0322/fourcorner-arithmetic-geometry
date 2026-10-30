import ThetaCoverClassPortable.ThetaDChartNaturality

namespace FourCorner.ThetaDNativeProjRatios
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open ThetaLiteralModels ThetaProjectiveModel ThetaDGeometricModel ThetaDPlaneChartSections ThetaDChartNaturality
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance : IsIntegral (D ℚ) := original_integral

abbrev G := grading (targetEquation ℚ) (target_homogeneous ℚ)
abbrev hcoordinate (j : Fin 3) := ThetaProjectiveModel.coordinate (targetEquation ℚ) (target_homogeneous ℚ) j
abbrev B (j : Fin 3) := Proj.basicOpen G (hcoordinate j)

 theorem U_eq_basic (j : Fin 3) : U j=B j := by
  rw [U,Scheme.Hom.image_top_eq_opensRange]
  change ((chartIso (targetEquation ℚ) (target_homogeneous ℚ) j).inv ≫ (B j).ι).opensRange=B j
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (B j).opensRange_ι

 theorem basic_nonempty (j : Fin 3) : Nonempty (B j) := by
  rw [←U_eq_basic]
  exact U_nonempty j

 theorem coordinate_not_mem_generic (j : Fin 3) :
    hcoordinate j ∉ (genericPoint (D ℚ)).asHomogeneousIdeal := by
  have hh : genericPoint (D ℚ)∈B j :=
    ((genericPoint_spec (D ℚ)).mem_open_set_iff (B j).isOpen).mpr (by simpa using basic_nonempty j)
  exact hh

/-- The original Proj generic stalk, with its actual native homogeneous
localization description. No replacement function field is introduced. -/
def stalkEquiv : (D ℚ).functionField ≃+* HomogeneousLocalization.AtPrime G
    (genericPoint (D ℚ)).asHomogeneousIdeal.toIdeal :=
  Proj.stalkIso' G (genericPoint (D ℚ))

/-- The ratio X_a/X_j inside the original curve's actual generic stalk. -/
def ratio (j a : Fin 3) : (D ℚ).functionField :=
  stalkEquiv.symm (.mk ⟨1,⟨hcoordinate a,coordinate_degree _ _ a⟩,
    ⟨hcoordinate j,coordinate_degree _ _ j⟩,coordinate_not_mem_generic j⟩)

 theorem ratio_self (j : Fin 3) : ratio j j=1 := by
  apply stalkEquiv.injective
  simp only [ratio,RingEquiv.apply_symm_apply,map_one]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk,HomogeneousLocalization.val_one]
  rw [←Localization.mk_one,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  exact ⟨1,by simp⟩

 theorem ratio_mul (i j a : Fin 3) : ratio i a*ratio j i=ratio j a := by
  apply stalkEquiv.injective
  simp only [map_mul,ratio,RingEquiv.apply_symm_apply]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk,HomogeneousLocalization.val_mul,Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,Submonoid.coe_mul,Subtype.coe_mk,OneMemClass.coe_one,one_mul]
  ring

 theorem ratio_ne_zero (i j : Fin 3) : ratio i j≠0 := by
  intro h
  have hh := ratio_mul i j j
  rw [h,zero_mul,ratio_self] at hh
  exact zero_ne_one hh

 theorem ratio_div (i j a : Fin 3) : ratio i a=ratio j a/ratio j i := by
  apply (eq_div_iff (ratio_ne_zero j i)).mpr
  exact ratio_mul i j a

/-- All three literal projective chart transitions in the TRUE rational
function field, with their genuine nonzero denominators. -/
 theorem transition_XZ : ratio 0 1=ratio 2 1/ratio 2 0 ∧ ratio 0 2=(ratio 2 0)⁻¹ := by
  refine ⟨ratio_div 0 2 1,?_⟩
  rw [ratio_div 0 2 2,ratio_self,one_div]

 theorem transition_YZ : ratio 1 0=ratio 2 0/ratio 2 1 ∧ ratio 1 2=(ratio 2 1)⁻¹ := by
  refine ⟨ratio_div 1 2 0,?_⟩
  rw [ratio_div 1 2 2,ratio_self,one_div]

#print axioms U_eq_basic
#print axioms stalkEquiv
#print axioms ratio_mul
#print axioms transition_XZ
#print axioms transition_YZ
end
end FourCorner.ThetaDNativeProjRatios
