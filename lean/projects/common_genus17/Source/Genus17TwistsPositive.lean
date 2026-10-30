import Genus17Support

namespace FourCorner.Genus17Support

theorem twist_pos {t κ : ℚ} (hκ : κ ∈ twists t) : 0 < κ := by
  obtain ⟨e,S,hS,rfl⟩ := mem_twists.mp hκ
  apply mul_pos
  · cases e <;> norm_num
  · apply Finset.prod_pos
    intro p hp
    exact_mod_cast ((mem_oddSupport _ _).mp (hS hp)).1.pos

theorem twist_ne_zero {t κ : ℚ} (hκ : κ ∈ twists t) : κ ≠ 0 :=
  ne_of_gt (twist_pos hκ)

end FourCorner.Genus17Support
#print axioms FourCorner.Genus17Support.twist_pos
#print axioms FourCorner.Genus17Support.twist_ne_zero
