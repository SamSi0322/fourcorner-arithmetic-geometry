import HpConstantFieldComparison
import GeometricFrobeniusTransport
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import SharpPointBound
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one

namespace FourCorner.HpFiniteBaseGenus

open HpLiteralField HpFieldGeometry AlgebraicCurve
open scoped TensorProduct
noncomputable section
variable (k : Type*) [Field k] [Fintype k] [NeZero (2 : k)]
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
local instance constantAlgebra (p : k) : Algebra k (field k p) := HpFieldGeometry.constantAlgebra k p
local instance constantModule (p : k) : Module k (field k p) := Algebra.toModule

/-- The actual finite-base Hasse field has genus five. Its constant tensor,
Frobenius square, full constants and geometric genus are proved inputs. -/
theorem genus_five (p : k) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) : genusFF k (field k p)=5 := by
  let L := AlgebraicClosure k
  let F0 := field k p
  let F := field L (algebraMap k L p)
  letI : Algebra k F0 := HpFieldGeometry.constantAlgebra k p
  letI : Module k F0 := Algebra.toModule
  letI : PerfectField k := PerfectField.ofFinite
  letI : PerfectField L := IsAlgClosed.perfectField L
  letI : NeZero (2 : L) := ⟨by simpa only [map_ofNat] using
    (map_ne_zero (algebraMap k L)).mpr (NeZero.ne (2 : k))⟩
  letI : IsDomain (L ⊗[k] F0) := HpTensorComparison.all_constants_domain k L p hp ha hb
  let e : FractionRing (L ⊗[k] F0) ≃ₐ[L] F := HpConstantFieldComparison.fractionFieldEquiv k L p hp ha hb
  letI : Algebra F0 F := GeometricTensorFrobenius.imageAlgebra k L F0 F e
  letI : IsCurveOver k F0 := isCurveOver k p
  letI : IsCurveOver L F := isCurveOver L (algebraMap k L p)
  have hfg : ∃ s : Finset F0,IntermediateField.adjoin k (s : Set F0)=⊤ := by
    letI : FiniteDimensional (RatFunc k) F0 := finite_over_line k p
    haveI : Algebra.EssFiniteType k F0 := RatFuncFiniteExtension.essFiniteType k F0
    change (⊤ : IntermediateField k F0).FG
    exact IntermediateField.fg_top_iff.mpr inferInstance
  have hgen := GeometricTensorFrobenius.image_algebra_generates k L F0 F e
  let phi : F →ₐ[L] F := GeometricTensorFrobenius.transportedFrobenius k L F0 F e
  have hphi := GeometricTensorFrobenius.transportedFrobenius_algebraMap k L F0 F e
  have hC : ConstantsAreBase k F0 := HpConstantFieldComparison.constantsAreBase k p hp ha hb
  have hdesc := genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed k L F0 F hfg hgen phi hphi hC
  have hp' : algebraMap k L p ≠ 0 := (map_ne_zero _).mpr hp
  have ha' : algebraMap k L p-1 ≠ 0 := by simpa only [map_sub,map_one] using (map_ne_zero (algebraMap k L)).mpr ha
  have hb' : algebraMap k L p+1 ≠ 0 := by simpa only [map_add,map_one] using (map_ne_zero (algebraMap k L)).mpr hb
  have hg : genusFF L F=5 := HpGeometricGenus.genus_five L (algebraMap k L p) hp' ha' hb'
  exact hdesc.symm.trans hg

theorem genus5_lower_bound_positive (q : ℕ) (hq : 101≤q) :
    0<(q : ℝ)+1-10*Real.sqrt (q : ℝ) := by
  have hqR : (101 : ℝ)≤q := by exact_mod_cast hq
  have hs := Real.sq_sqrt (Nat.cast_nonneg q : (0 : ℝ)≤q)
  have hsp := Real.sqrt_nonneg (q : ℝ)
  have hprod : 0≤((q : ℝ)-101)*((q : ℝ)+3) := mul_nonneg (by linarith) (by positivity)
  have hpositive : 0<(q : ℝ)+1 := by positivity
  nlinarith

/-- The sharp proved Hasse--Weil bound supplies an actual rational place of
this literal residue field at every ordinary prime of size at least101. -/
theorem exists_degree_one (p : k) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hq : 101≤Nat.card k) : ∃ w : Place k (field k p),w.deg=1 := by
  let F := field k p
  letI : PerfectField k := PerfectField.ofFinite
  letI : IsCurveOver k F := isCurveOver k p
  letI : FiniteDimensional (RatFunc k) F := finite_over_line k p
  letI : Algebra.EssFiniteType k F := RatFuncFiniteExtension.essFiniteType k F
  have hC := HpConstantFieldComparison.constantsAreBase k p hp ha hb
  have hcount := finite_degree_one_places_and_hasseWeil_bound k F hC
  have hbound := hcount.2
  rw [genus_five k p hp ha hb] at hbound
  norm_num only [Nat.cast_ofNat] at hbound
  have hlower := (abs_le.mp hbound).1
  have hpositive := genus5_lower_bound_positive (Nat.card k) hq
  by_contra hnone
  let S : Set (Place k F) := {w | w.deg=1}
  letI : IsEmpty S := ⟨by rintro ⟨w,hw⟩;exact hnone ⟨w,hw⟩⟩
  have hz : Nat.card S=0 := Nat.card_eq_zero.mpr (Or.inl inferInstance)
  change -(10*Real.sqrt (Nat.card k : ℝ))≤(Nat.card S : ℝ)-((Nat.card k : ℝ)+1) at hlower
  rw [hz,Nat.cast_zero] at hlower
  linarith

theorem exists_rational_place (p : k) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (hq : 101≤Nat.card k) : ∃ w : Place k (field k p),w.IsRational := by
  obtain ⟨w,hw⟩ := exists_degree_one k p hp ha hb hq
  exact ⟨w,w.isRational_iff_deg_eq_one.mpr hw⟩

#print axioms genus_five
#print axioms exists_degree_one
#print axioms exists_rational_place

end
end FourCorner.HpFiniteBaseGenus
