import OddFourTower
import OddFourPlaces
import ResidueGenerators

noncomputable section
namespace FourCorner.OddFourLiteral
open AlgebraicCurve CommonLiteralField
variable {K : Type*} [Field K] [NeZero (2:K)]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Classical.propDecidable

theorem nonzero {t : K} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1) (i : Fin 4) : radicand K t i≠0 := by
  have h := FiniteFiveIndependence.four_product_nonsquare h0 h1 hm {i} (by simp)
  simp only [Finset.prod_singleton] at h
  intro hz
  exact h (by simp [hz])

theorem root_generates (t : K) : Algebra.adjoin (RatFunc K)
    {root K t 0,root K t 1,root K t 2,root K t 3}=⊤ := by
  have he : Set.range (root K t) = {root K t 0,root K t 1,root K t 2,root K t 3} := by
    ext x
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> tauto
    · rintro (h|h|h|h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,h.symm⟩
      · exact ⟨3,h.symm⟩
  rw [← he]
  exact ResidueGenerators.four_root_generates K t

/-- All actual places, including every point over infinity and zero, have
the genuine index predicted by the six literal branch values in char!=2. -/
theorem index_formula {t : K} (h0 : t≠0) (h1 : t≠1) (hm : t≠-1)
    (w : Place K (field K t)) :
    w.ramificationIndex (RatFunc K) = if w.restrict (RatFunc K) ∈ OddFourPlaces.support t then 2 else 1 := by
  classical
  letI := ResidueRadicalField.four_finite K t
  rw [OddFourTower.index_formula w
    (radicand K t 0) (radicand K t 1) (radicand K t 2) (radicand K t 3)
    (root K t 0) (root K t 1) (root K t 2) (root K t 3)
    (root_sq K t 0) (root_sq K t 1) (root_sq K t 2) (root_sq K t 3)
    (nonzero h0 h1 hm 0) (nonzero h0 h1 hm 1) (nonzero h0 h1 hm 2) (nonzero h0 h1 hm 3) (root_generates t)]
  have hall : (∀ i : Fin 4,Even ((w.restrict (RatFunc K)).ord (radicand K t i))) ↔
      (Even ((w.restrict (RatFunc K)).ord (radicand K t 0)) ∧
       Even ((w.restrict (RatFunc K)).ord (radicand K t 1)) ∧
       Even ((w.restrict (RatFunc K)).ord (radicand K t 2)) ∧
       Even ((w.restrict (RatFunc K)).ord (radicand K t 3))) := by simp [Fin.forall_fin_succ]
  have hs := OddFourPlaces.exists_odd_iff_mem_support t h0 h1 hm (w.restrict (RatFunc K))
  by_cases hb : w.restrict (RatFunc K) ∈ OddFourPlaces.support t
  · rw [if_pos hb,if_neg]
    intro hh
    obtain ⟨i,hi⟩ := hs.mpr hb
    exact (Int.not_even_iff_odd.mpr hi) ((hall.mpr hh) i)
  · rw [if_neg hb,if_pos]
    apply hall.mp
    intro i
    by_contra h
    exact hb (hs.mp ⟨i,Int.not_even_iff_odd.mp h⟩)
end FourCorner.OddFourLiteral
#print axioms FourCorner.OddFourLiteral.index_formula
