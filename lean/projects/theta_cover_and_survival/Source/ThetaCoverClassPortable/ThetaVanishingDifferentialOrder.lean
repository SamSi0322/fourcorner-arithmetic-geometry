import ThetaCoverClassPortable.ThetaDHyperplaneLocalOrders

namespace FourCorner.ThetaVanishingDifferentialOrder
open AlgebraicCurve ThetaRegularFunctionDifferential
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]
local instance : ∀w : Place K F,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- A simple zero has nonvanishing actual differential in the actual DVR
cotangent direction. This is proved using the actual uniformizer, unit factor,
and regularity of derivatives of true regular functions. -/
theorem derivative_unit_of_order_one (w : Place K F) (f : F) (hf : f≠0)
    (ho : w.ord f=1) :
    ∃c : w.toValuationSubring,(c:F)=coefficient w (KaehlerDifferential.D K F f) ∧ IsUnit c := by
  let A := w.toValuationSubring
  let π : A := (IsDiscreteValuationRing.exists_irreducible A).choose
  have hπ : Irreducible π := (IsDiscreteValuationRing.exists_irreducible A).choose_spec
  obtain ⟨u,hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [ho,zpow_one] at hu
  let d : A := ⟨coefficient w (KaehlerDifferential.D K F ((u:A):F)),
    coefficient_D_mem w ((u:A):F) (u:A).property⟩
  have hp : coefficient w (KaehlerDifferential.D K F (π:F))=1 := by
    change w.differentialCoeff _=1
    have hh : w.dCoord=KaehlerDifferential.D K F (π:F) := rfl
    rw [←hh,w.differentialCoeff_dCoord]
  refine ⟨(u:A)+π*d,?_,?_⟩
  · rw [hu,Derivation.leibniz,map_add,map_smul,map_smul,hp]
    change ((u:A):F)+(π:F)*(d:F)=((u:A):F)*1+(π:F)*coefficient w (KaehlerDifferential.D K F ((u:A):F))
    simp only [mul_one]
    rfl
  · rw [←IsLocalRing.notMem_maximalIdeal]
    intro hm
    have hpmax : π∈IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit
    have hpd : π*d∈IsLocalRing.maximalIdeal A := (IsLocalRing.maximalIdeal A).mul_mem_right d hpmax
    have hum : (u:A)∈IsLocalRing.maximalIdeal A := by
      simpa only [add_sub_cancel_right] using (IsLocalRing.maximalIdeal A).sub_mem hm hpd
    exact (IsLocalRing.notMem_maximalIdeal.mpr u.isUnit) hum

/-- Simultaneous actual vanishing of f and df at a place forces order ≥2.
These are local-ring vanishing conditions that the geometric contact proof
must establish; no bitangent/contact divisor statement is assumed here. -/
theorem order_ge_two_of_vanishing (w : Place K F) (f : F) (hf : f≠0)
    (hr : f∈w.toValuationSubring)
    (hm : (⟨f,hr⟩ : w.toValuationSubring)∈IsLocalRing.maximalIdeal w.toValuationSubring)
    (hd : (⟨coefficient w (KaehlerDifferential.D K F f),coefficient_D_mem w f hr⟩ :
      w.toValuationSubring)∈IsLocalRing.maximalIdeal w.toValuationSubring) : 2≤w.ord f := by
  have hn : (⟨f,hr⟩ : w.toValuationSubring)≠0 := by intro h;exact hf (congrArg Subtype.val h)
  have hp := (Place.mem_maximalIdeal_iff_ord_pos' hn).mp hm
  change 0<w.ord f at hp
  have hnot : w.ord f≠1 := by
    intro ho
    obtain ⟨c,hc,hcu⟩ := derivative_unit_of_order_one w f hf ho
    have he : c=(⟨coefficient w (KaehlerDifferential.D K F f),coefficient_D_mem w f hr⟩ :
      w.toValuationSubring) := Subtype.ext hc
    rw [←he] at hd
    exact (IsLocalRing.notMem_maximalIdeal.mpr hcu) hd
  omega

#print axioms derivative_unit_of_order_one
#print axioms order_ge_two_of_vanishing
end
end FourCorner.ThetaVanishingDifferentialOrder
