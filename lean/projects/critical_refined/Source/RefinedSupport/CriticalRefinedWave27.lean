import FourCorner.CriticalSeventeenFinite
set_option autoImplicit false
namespace FourCorner.CriticalRefinedWave27
/-- Signed critical equations, permitting every zero pattern. -/
def SignedPattern {K : Type*} [CommRing K] (i b a₀ a₁ a₂ a₃ : K) : Prop :=
  i^2 = -1 ∧ b ≠ 0 ∧ a₁^2 = a₀^2+b ∧ a₂^2 = a₀^2+i*b ∧
    a₃^2 = a₀^2+(1+i)*b

theorem signed_product_identity {K : Type*} [CommRing K]
    {i b a₀ a₁ a₂ a₃ : K} (h : SignedPattern i b a₀ a₁ a₂ a₃) :
    (a₀*a₃+a₁*a₂)*(a₀*a₃-a₁*a₂) = -i*b^2 := by
  rcases h with ⟨_,_,h₁,h₂,h₃⟩
  calc
    _ = a₀^2*a₃^2-a₁^2*a₂^2 := by ring
    _ = -i*b^2 := by rw [h₁,h₂,h₃]; ring

/-- No sign choice or vanishing normalized coordinate makes either product zero. -/
theorem signed_product_nonzero {K : Type*} [Field K]
    {i b a₀ a₁ a₂ a₃ : K} (h : SignedPattern i b a₀ a₁ a₂ a₃) :
    a₀*a₃+a₁*a₂ ≠ 0 ∧ a₀*a₃-a₁*a₂ ≠ 0 := by
  have hi : i ≠ 0 := by
    intro hz
    have hh := h.1
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at hh
    exact neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0) hh.symm
  have hn : -i*b^2 ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hi) (pow_ne_zero _ h.2.1)
  have hm : (a₀*a₃+a₁*a₂)*(a₀*a₃-a₁*a₂) ≠ 0 := by
    rw [signed_product_identity h]; exact hn
  exact ⟨left_ne_zero_of_mul hm, right_ne_zero_of_mul hm⟩

/-- Exact product formula for original roots and a denominator at arbitrary depth. -/
theorem original_product_normalization {K : Type*} [Field K]
    (v₀ v₁ v₂ v₃ d M : K) (hd : d ≠ 0) (hM : M ≠ 0) :
    ((d*v₀)*(d*v₃)+(d*v₁)*(d*v₂))/(d^2*M)^2 =
      (v₀*v₃+v₁*v₂)/(d^2*M^2) := by
  field_simp
  <;> ring

def RefinedPattern (p : ℕ) : Prop :=
  ∃ i b a₀ a₁ a₂ a₃ : ZMod p,
    SignedPattern i b a₀ a₁ a₂ a₃ ∧ a₀ ≠ 0 ∧ a₁ ≠ 0 ∧ a₂ ≠ 0 ∧ a₃ ≠ 0 ∧
    IsSquare (2*(a₀*a₃+a₁*a₂))

private theorem table5 : ∀ i c b : ZMod 5, i^2 = -1 → b ≠ 0 →
    IsSquare c → IsSquare (c+b) → IsSquare (c+i*b) →
    ¬ IsSquare (c+(1+i)*b) := by decide
private theorem table13 : ∀ i c b : ZMod 13, i^2 = -1 → b ≠ 0 →
    IsSquare c → IsSquare (c+b) → IsSquare (c+i*b) →
    ¬ IsSquare (c+(1+i)*b) := by decide

theorem refined_excludes5 : ¬ RefinedPattern 5 := by
  rintro ⟨i,b,a₀,a₁,a₂,a₃,⟨hi,hb,h₁,h₂,h₃⟩,_⟩
  exact table5 i (a₀^2) b hi hb (IsSquare.sq _) (h₁ ▸ IsSquare.sq _)
    (h₂ ▸ IsSquare.sq _) (h₃ ▸ IsSquare.sq _)

theorem refined_excludes13 : ¬ RefinedPattern 13 := by
  rintro ⟨i,b,a₀,a₁,a₂,a₃,⟨hi,hb,h₁,h₂,h₃⟩,_⟩
  exact table13 i (a₀^2) b hi hb (IsSquare.sq _) (h₁ ▸ IsSquare.sq _)
    (h₂ ▸ IsSquare.sq _) (h₃ ▸ IsSquare.sq _)

theorem refined_excludes17 : ¬ RefinedPattern 17 := by
  rintro ⟨i,b,a₀,a₁,a₂,a₃,⟨hi,hb,h₁,h₂,h₃⟩,_,_,_,_,hs⟩
  exact (seventeen_square_pattern a₀ a₁ a₂ a₃ i b hi hb h₁ h₂ h₃).2.2.2.2.2.1 hs

theorem refined_necessary {p : ℕ} (h : RefinedPattern p) :
    p ≠ 5 ∧ p ≠ 13 ∧ p ≠ 17 := by
  constructor
  · rintro rfl; exact refined_excludes5 h
  constructor
  · rintro rfl; exact refined_excludes13 h
  · rintro rfl; exact refined_excludes17 h

theorem refined41 : RefinedPattern 41 := by
  refine ⟨9,1,6,18,2,13,?_,?_,?_,?_,?_,?_⟩
  · unfold SignedPattern; decide
  · decide
  · decide
  · decide
  · decide
  · exact ⟨8, by decide⟩

/-- Square denominator clearing, valid at every depth and for every signed numerator. -/
theorem twice_product_square_iff {K : Type*} [Field K]
    (a₀ a₁ a₂ a₃ D : K) (hD : D ≠ 0) :
    IsSquare (2*((a₀*a₃+a₁*a₂)/D^2)) ↔
      IsSquare (2*(a₀*a₃+a₁*a₂)) := by
  constructor
  · intro h
    have hh := h.mul (IsSquare.sq D)
    simpa only [← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hD)] using hh
  · intro h
    simpa only [mul_div_assoc] using h.div (IsSquare.sq D)

theorem twice_product_plus_one_square {K : Type*} [Field K] {t : K}
    (ht : t ≠ 0) (hs : IsSquare (2*t)) (hr : IsSquare ((t+1)/t)) :
    IsSquare (2*(t+1)) := by
  have hh := hs.mul hr
  have he : (2*t)*((t+1)/t) = 2*(t+1) := by field_simp
  exact he ▸ hh
end FourCorner.CriticalRefinedWave27
#print axioms FourCorner.CriticalRefinedWave27.signed_product_identity
#print axioms FourCorner.CriticalRefinedWave27.refined_necessary
#print axioms FourCorner.CriticalRefinedWave27.refined41
#print axioms FourCorner.CriticalRefinedWave27.twice_product_square_iff
#print axioms FourCorner.CriticalRefinedWave27.twice_product_plus_one_square

#print axioms FourCorner.CriticalRefinedWave27.signed_product_nonzero
#print axioms FourCorner.CriticalRefinedWave27.original_product_normalization
