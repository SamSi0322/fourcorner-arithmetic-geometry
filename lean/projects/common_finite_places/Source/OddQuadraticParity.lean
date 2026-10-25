import OddQuadraticUnit
import RadicalSeparable
import geometry.QuadraticRescaledUnit
import geometry.QuadraticPlaceRamification

noncomputable section
namespace FourCorner.OddQuadraticParity
open AlgebraicCurve
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [NeZero (2:K)]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000

theorem rescaled (w : Place K E) {a t : F} {r : E}
    (hroot : r^2=algebraMap F E a) (hgen : Algebra.adjoin F {r}=⊤)
    (ha : a≠0) (ht : t≠0) (hord : (w.restrict F).ord a = 2*(w.restrict F).ord t) :
    differentIdeal (w.restrict F).toValuationSubring (Place.integralClosureAt E (w.restrict F))=⊤ ∧
      w.ramificationIndex F=1 := by
  have hr : (r/algebraMap F E t)^2 = algebraMap F E (a/t^2) := by
    rw [div_pow,hroot,map_div₀,map_pow]
  have hg := QuadraticRescaledUnit.adjoin_div_algebraMap_eq_top r ht hgen
  have hpow : (w.restrict F).ord (t^2) = 2*(w.restrict F).ord t := by
    simpa only [zpow_ofNat] using (w.restrict F).ord_zpow t (2:ℤ)
  have ho : (w.restrict F).ord (a/t^2)=0 := by
    rw [QuadraticRescaledUnit.ord_div _ ha (pow_ne_zero _ ht),hpow,hord,sub_self]
  exact OddQuadraticUnit.unit_radicand w hr hg (div_ne_zero ha (pow_ne_zero _ ht)) ho

/-- Every even valuation order is removed by an actual power of an actual
uniformizer; the different of the original field extension is the unit ideal. -/
theorem even_order (w : Place K E) {a : F} {r : E}
    (hroot : r^2=algebraMap F E a) (hgen : Algebra.adjoin F {r}=⊤)
    (ha : a≠0) (heven : Even ((w.restrict F).ord a)) :
    differentIdeal (w.restrict F).toValuationSubring (Place.integralClosureAt E (w.restrict F))=⊤ ∧
      w.ramificationIndex F=1 := by
  obtain ⟨n,hn⟩ := heven
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible (w.restrict F).toValuationSubring
  have hπ0 : (π:F)≠0 := by simpa [ne_eq,ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  apply rescaled w hroot hgen ha (zpow_ne_zero n hπ0)
  rw [(w.restrict F).ord_zpow,(w.restrict F).ord_coe_irreducible hπ,mul_one,hn]
  ring

theorem index_formula (w : Place K E) {a : F} {r : E}
    (hroot : r^2=algebraMap F E a) (hgen : Algebra.adjoin F {r}=⊤)
    (ha : a≠0) (hdegree : Module.finrank F E≤2) :
    w.ramificationIndex F = if Even ((w.restrict F).ord a) then 1 else 2 := by
  classical
  split_ifs with he
  · exact (even_order w hroot hgen ha he).2
  · exact QuadraticPlaceRamification.ramificationIndex_eq_two_of_odd_ord w hroot
      (Int.not_even_iff_odd.mp he) hdegree
end FourCorner.OddQuadraticParity
#print axioms FourCorner.OddQuadraticParity.even_order
#print axioms FourCorner.OddQuadraticParity.index_formula
