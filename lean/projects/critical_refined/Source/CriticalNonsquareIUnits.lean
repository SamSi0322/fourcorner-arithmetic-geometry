import CriticalProjectiveBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace FourCorner.CriticalNonsquareIUnits
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation CriticalProjectiveResidues
variable {k:Type*} [Field k]

/-- Any zero coordinate on the original V0=1 intersection forces i square. -/
theorem normalized_zero (i a b c:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (hb:b^2-1=i*(a^2-1)) (hc:c^2-1=(1+i)*(a^2-1))
    (hz:a=0 ∨ b=0 ∨ c=0) : IsSquare i := by
  rcases hz with ha0|hb0|hc0
  · have hcsq:c^2= -i := by rw [ha0] at hc;linear_combination hc
    have hr:(i*c)^2=i := by rw [mul_pow,hi,hcsq];ring
    exact ⟨i*c,by simpa only [pow_two] using hr.symm⟩
  · have hcsq:c^2=i := by
      rw [hb0] at hb
      linear_combination (norm:=ring_nf) hc-(1-i)*hb
      simp only [hi] <;> ring
    exact ⟨c,by simpa only [pow_two] using hcsq.symm⟩
  · have he:a^2=i*b^2 := by
      rw [hc0] at hc
      linear_combination -i*hb-(1-i)*hc
    have hbN:b≠0 := by
      intro hb0
      have haSq:a^2=0 := by simpa [hb0] using he
      have ha0:a=0 := sq_eq_zero_iff.mp haSq
      have hI:i=1 := by rw [ha0,hb0] at hb;linear_combination hb
      exact CriticalElliptic23.iota_ne_one i hi h2 hI
    have hr:(a/b)^2=i := by rw [div_pow,he,mul_div_cancel_right₀ _ (pow_ne_zero 2 hbN)]
    exact ⟨a/b,by simpa only [pow_two] using hr.symm⟩

/-- A genuine original projective point with V0=0 also forces i square. -/
theorem projective_zero (i:k) (V:Fin 4→k)
    (hn:V≠0) (hc:CriticalElliptic23.CriticalCoordinates i V) (h0:V 0=0) : IsSquare i := by
  have hex:∃j,V j≠0 := by
    by_contra h
    apply hn
    funext j
    by_contra hj
    exact h ⟨j,hj⟩
  have h1:V 1≠0 := by
    intro hz
    have hs:CriticalElliptic23.Shift V=0 := by simp [CriticalElliptic23.Shift,h0,hz]
    exact CriticalElliptic23.boundary_zero_nonzero i V hc hs hex h0
  have he:V 2^2=i*V 1^2 := by simpa [CriticalElliptic23.Shift,h0] using hc.1
  have hr:(V 2/V 1)^2=i := by rw [div_pow,he,mul_div_cancel_right₀ _ (pow_ne_zero 2 h1)]
  exact ⟨V 2/V 1,by simpa only [pow_two] using hr.symm⟩

/-- When i is nonsquare, EVERY actual rational base place has all three
original normalized coordinates units. There are no omitted poles or zeros. -/
theorem all_units (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) (hns:¬IsSquare i)
    (v:Place k (field k i)) (hv:v.IsRational) :
    v.ord (a k i)=0 ∧ v.ord (b k i)=0 ∧ v.ord (c k i)=0 := by
  have ha:0≤v.ord (a k i) := by
    by_contra h
    have hn:v.ord (a k i)<0 := by omega
    have hz:vector i hi h2 v hv 0=0 := by
      rw [vector,dif_neg h]
      simpa only [poleVector,Matrix.cons_val_zero] using CriticalProjectiveBoundary.pole_zero_residue i hi h2 v hv hn
    exact hns (projective_zero i (vector i hi h2 v hv) (vector_nonzero i hi h2 v hv) (vector_critical i hi h2 v hv) hz)
  let aa:=regularA i hi h2 v ha
  let bb:=regularB i hi h2 v ha
  let cc:=regularC i hi h2 v ha
  have hq:(evaluate v hv bb)^2-1=i*((evaluate v hv aa)^2-1) ∧
      (evaluate v hv cc)^2-1=(1+i)*((evaluate v hv aa)^2-1) := by
    simpa [finiteVector,CriticalElliptic23.CriticalCoordinates,CriticalElliptic23.Shift,aa,bb,cc]
      using finite_critical i hi h2 v hv ha
  have haz:evaluate v hv aa≠0 := fun h=>hns (normalized_zero i _ _ _ hi h2 hq.1 hq.2 (Or.inl h))
  have hbz:evaluate v hv bb≠0 := fun h=>hns (normalized_zero i _ _ _ hi h2 hq.1 hq.2 (Or.inr (Or.inl h)))
  have hcz:evaluate v hv cc≠0 := fun h=>hns (normalized_zero i _ _ _ hi h2 hq.1 hq.2 (Or.inr (Or.inr h)))
  have hn:=CriticalBadUnits.ordered_nonzero i hi h2
  have hm:=CriticalProductValuation.integral_of_nonnegative i v hi h2 ha
  have na:¬0<v.ord (a k i) := fun h=>haz ((ResidueValuationFacts.evaluate_zero_iff_ord_pos v hv aa hn.1).mpr h)
  have nb:¬0<v.ord (b k i) := fun h=>hbz ((ResidueValuationFacts.evaluate_zero_iff_ord_pos v hv bb hn.2.1).mpr h)
  have nc:¬0<v.ord (c k i) := fun h=>hcz ((ResidueValuationFacts.evaluate_zero_iff_ord_pos v hv cc hn.2.2.1).mpr h)
  omega

end FourCorner.CriticalNonsquareIUnits
#print axioms FourCorner.CriticalNonsquareIUnits.normalized_zero
#print axioms FourCorner.CriticalNonsquareIUnits.projective_zero
#print axioms FourCorner.CriticalNonsquareIUnits.all_units
