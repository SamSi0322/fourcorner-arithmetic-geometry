import FourCorner.CommonRootRamifiedNecessity
import FourCorner.CommonRootRamifiedExistence
import FourCorner.CommonRootTwoLift
import FourCorner.CommonRootSymmetries
import FourCorner.CriticalSeventeenPadic
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace FourCorner

variable {p : ℕ} [Fact p.Prime]

/-- At an odd prime, positive odd depth of t²−1 selects exactly one of the
two branches t−1 and t+1. No restriction on the initial valuation of t is used. -/
theorem commonRoot_ramified_orientation (hp : p ≠ 2) {t : ℚ_[p]}
    (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (hdpos : 0 < (t^2-1).valuation) (hdodd : Odd (t^2-1).valuation) :
    (0 < (t-1).valuation ∧ Odd (t-1).valuation) ∨
      (0 < (t+1).valuation ∧ Odd (t+1).valuation) := by
  have hs : t-1 ≠ 0 := sub_ne_zero.mpr ht1
  have hT : t+1 ≠ 0 := by intro h; exact htm1 (eq_neg_of_add_eq_zero_left h)
  have hv : (t^2-1).valuation = (t-1).valuation + (t+1).valuation := by
    rw [show t^2-1=(t-1)*(t+1) by ring, Padic.valuation_mul hs hT]
  have hne : (t-1).valuation ≠ (t+1).valuation := by
    intro he
    obtain ⟨k,hk⟩ := hdodd
    rw [hv,he] at hk
    omega
  have hm := commonRoot_val_sub_of_ne hT hs (Ne.symm hne)
  rw [show t+1-(t-1)=2 by ring,commonRoot_val_two hp] at hm
  by_cases hpos : 0 < (t-1).valuation
  · have hT0 : (t+1).valuation=0 := by omega
    exact Or.inl ⟨hpos, by simpa [hv,hT0] using hdodd⟩
  · have hs0 : (t-1).valuation=0 := by omega
    exact Or.inr ⟨by omega, by simpa [hv,hs0] using hdodd⟩

namespace CommonRootSource

/-- The necessity half of Lemma lem:common-ramified, for the actual completed
field and the exact ordered source. -/
theorem ramified_square_classes {t : ℚ_[p]} (S : CommonRootSource ℚ_[p] t)
    (hp : p ≠ 2) (hdpos : 0 < (t^2-1).valuation)
    (hdodd : Odd (t^2-1).valuation) :
    legendreSym p 2 = 1 ∧
      (IsSquare S.ell ∨ IsSquare ((t^2-1)/S.ell)) := by
  have hlocal : IsSquare (2 : ℚ_[p]) ∧
      (IsSquare S.ell ∨ IsSquare ((t^2-1)/S.ell)) := by
    rcases commonRoot_ramified_orientation hp S.t_ne_one S.t_ne_neg_one hdpos hdodd with h | h
    · exact S.ramified_local_necessity hp h.1 h.2
    · have he : (-t)-1=-(t+1) := by ring
      have hpos : 0 < ((-t)-1).valuation := by rw [he,commonRoot_val_neg]; exact h.1
      have hodd : Odd ((-t)-1).valuation := by rw [he,commonRoot_val_neg]; exact h.2
      have hh := S.signChange.ramified_local_necessity hp hpos hodd
      simpa using hh
  have h2res : IsSquare (2 : ZMod p) := by
    simpa using isSquare_zmod_of_isSquare_padic (p := p) 2 hlocal.1
  have h2nz : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  exact ⟨(legendreSym.eq_one_iff p (by simpa using h2nz)).mpr (by simpa using h2res), hlocal.2⟩

end CommonRootSource

/-- The converse half of Lemma lem:common-ramified. Both asserted square
classes are realized by actual points of the full ordered four-root source. -/
theorem commonRoot_ramified_both_classes (hp : p ≠ 2) (t : ℚ_[p])
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (hdpos : 0 < (t^2-1).valuation) (hdodd : Odd (t^2-1).valuation)
    (hleg : legendreSym p 2 = 1) :
    ∃ S₀ S₁ : CommonRootSource ℚ_[p] t,
      IsSquare S₀.ell ∧ IsSquare ((t^2-1)/S₁.ell) := by
  have h2nz : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h2res : IsSquare (2 : ZMod p) := by
    simpa using (legendreSym.eq_one_iff p (by simpa using h2nz)).mp hleg
  have h2 := padic_isSquare_two_of_isSquare_zmod hp h2res
  have hex : ∃ S : CommonRootSource ℚ_[p] t, IsSquare S.ell := by
    rcases commonRoot_ramified_orientation hp ht1 htm1 hdpos hdodd with h | h
    · obtain ⟨S,_,hS⟩ := commonRoot_ramified_exists_square_ell hp t ht0 ht1 htm1 h.1 h2
      exact ⟨S,hS⟩
    · have hu0 : -t ≠ 0 := neg_ne_zero.mpr ht0
      have hu1 : -t ≠ 1 := by intro he; apply htm1; linear_combination -he
      have hum1 : -t ≠ -1 := by intro he; apply ht1; linear_combination -he
      have he : (-t)-1=-(t+1) := by ring
      have hpos : 0 < ((-t)-1).valuation := by rw [he,commonRoot_val_neg]; exact h.1
      obtain ⟨S,_,hS⟩ := commonRoot_ramified_exists_square_ell hp (-t) hu0 hu1 hum1 hpos h2
      refine ⟨S.signChange.reparam (neg_neg t),?_⟩
      simpa using hS
  obtain ⟨S,hS⟩ := hex
  refine ⟨S,S.reflect,hS,?_⟩
  have he : (t^2-1)/S.reflect.ell = S.ell := by
    rw [CommonRootSource.reflect_ell]
    field_simp [S.ell_ne_zero,S.d_ne_zero]
  rw [he]
  exact hS

/-- Positive odd ramification gives local points precisely when two is a
quadratic residue. -/
theorem commonRoot_ramified_nonempty_iff (hp : p ≠ 2) (t : ℚ_[p])
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (hdpos : 0 < (t^2-1).valuation) (hdodd : Odd (t^2-1).valuation) :
    Nonempty (CommonRootSource ℚ_[p] t) ↔ legendreSym p 2 = 1 := by
  constructor
  · rintro ⟨S⟩
    exact (S.ramified_square_classes hp hdpos hdodd).1
  · intro hleg
    obtain ⟨S,_,_,_⟩ := commonRoot_ramified_both_classes hp t ht0 ht1 htm1 hdpos hdodd hleg
    exact ⟨S⟩

namespace CommonRootSource

/-- The same local classification in the conventional quotient ell/d. -/
theorem ramified_square_classes_ratio {t : ℚ_[p]} (S : CommonRootSource ℚ_[p] t)
    (hp : p ≠ 2) (hdpos : 0 < (t^2-1).valuation)
    (hdodd : Odd (t^2-1).valuation) :
    legendreSym p 2 = 1 ∧
      (IsSquare S.ell ∨ IsSquare (S.ell/(t^2-1))) := by
  obtain ⟨hleg,hclass⟩ := S.ramified_square_classes hp hdpos hdodd
  refine ⟨hleg,?_⟩
  rcases hclass with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa only [inv_div] using h.inv)

end CommonRootSource

/-- The two classes in the ramified statement are genuinely distinct. -/
theorem commonRoot_ramified_d_nonsquare (t : ℚ_[p])
    (hdodd : Odd (t^2-1).valuation) : ¬ IsSquare (t^2-1) := by
  intro hs
  obtain ⟨k,hk⟩ := commonRoot_even_val_of_isSquare hs
  obtain ⟨j,hj⟩ := hdodd
  omega

/-- Both square classes are attained by distinct full-source points. -/
theorem commonRoot_ramified_both_distinct (hp : p ≠ 2) (t : ℚ_[p])
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1)
    (hdpos : 0 < (t^2-1).valuation) (hdodd : Odd (t^2-1).valuation)
    (hleg : legendreSym p 2 = 1) :
    ∃ S₀ S₁ : CommonRootSource ℚ_[p] t,
      S₀ ≠ S₁ ∧ IsSquare S₀.ell ∧ IsSquare (S₁.ell/(t^2-1)) := by
  obtain ⟨S₀,S₁,h0,h1⟩ := commonRoot_ramified_both_classes hp t ht0 ht1 htm1 hdpos hdodd hleg
  refine ⟨S₀,S₁,?_,h0,?_⟩
  · intro he
    subst S₁
    have h := h1.mul h0
    apply commonRoot_ramified_d_nonsquare t hdodd
    simpa only [div_mul_cancel₀ _ S₀.ell_ne_zero] using h
  · simpa only [inv_div] using h1.inv

end FourCorner
#print axioms FourCorner.commonRoot_ramified_orientation
#print axioms FourCorner.CommonRootSource.ramified_square_classes

#print axioms FourCorner.commonRoot_ramified_both_classes
#print axioms FourCorner.commonRoot_ramified_nonempty_iff

#print axioms FourCorner.CommonRootSource.ramified_square_classes_ratio
#print axioms FourCorner.commonRoot_ramified_both_distinct
