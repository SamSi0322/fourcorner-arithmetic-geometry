import ThetaCoverClassPortable.ThetaActualLineDifferentials

namespace FourCorner.ThetaValuationTangencyOrder
open AlgebraicCurve ThetaRegularFunctionDifferential ThetaVanishingDifferentialOrder
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K F : Type*} [Field K] [PerfectField K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]
local instance : ∀w : Place K F,w.DCoordGenerates := dCoordGenerates_of_isCurveOver
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

 theorem inverse_mem {A : ValuationSubring F} {q : A} (hq : IsUnit q) : (q:F)⁻¹∈A := by
  rcases hq with ⟨u,rfl⟩
  have hm : (((u⁻¹:Aˣ):A):F)*((u:A):F)=1 :=
    congrArg (fun z : A=>(z:F)) u.inv_val
  have he : (((u⁻¹:Aˣ):A):F)=((u:A):F)⁻¹ := eq_inv_of_mul_eq_one_left hm
  rw [←he]
  exact ((u⁻¹:Aˣ):A).property

/-- Normal-form tangency in the ACTUAL DVR gives order at least two.
Every premise is an actual ring membership or actual Kähler identity; the
geometric cases establish them from their literal original contact data. -/
theorem order_ge_two_of_normal_form (w : Place K F)
    (f u n q : w.toValuationSubring) (hf : (f:F)≠0)
    (hfm : f∈IsLocalRing.maximalIdeal w.toValuationSubring)
    (hnm : n∈IsLocalRing.maximalIdeal w.toValuationSubring) (hq : IsUnit q)
    (hD : KaehlerDifferential.D K F (f:F)=
      (-(n:F)/(q:F)) • KaehlerDifferential.D K F (u:F)) :
    2≤w.ord (f:F) := by
  let A := w.toValuationSubring
  let iq : A := ⟨(q:F)⁻¹,inverse_mem hq⟩
  let d : A := ⟨coefficient w (KaehlerDifferential.D K F (u:F)),coefficient_D_mem w (u:F) u.property⟩
  let c : A := -n*iq*d
  have hc : (c:F)=coefficient w (KaehlerDifferential.D K F (f:F)) := by
    rw [hD,map_smul]
    change -(n:F)*(q:F)⁻¹*coefficient w (KaehlerDifferential.D K F (u:F))=
      (-(n:F)/(q:F))*coefficient w (KaehlerDifferential.D K F (u:F))
    rw [div_eq_mul_inv]
  have hcm : c∈IsLocalRing.maximalIdeal A :=
    (IsLocalRing.maximalIdeal A).mul_mem_right d
      ((IsLocalRing.maximalIdeal A).mul_mem_right iq ((IsLocalRing.maximalIdeal A).neg_mem hnm))
  have hd : (⟨coefficient w (KaehlerDifferential.D K F (f:F)),coefficient_D_mem w (f:F) f.property⟩:A)∈
      IsLocalRing.maximalIdeal A := by
    have he : (⟨coefficient w (KaehlerDifferential.D K F (f:F)),coefficient_D_mem w (f:F) f.property⟩:A)=c :=
      Subtype.ext hc.symm
    rw [he]
    exact hcm
  exact order_ge_two_of_vanishing w (f:F) hf f.property hfm hd

#print axioms inverse_mem
#print axioms order_ge_two_of_normal_form
end
end FourCorner.ThetaValuationTangencyOrder
