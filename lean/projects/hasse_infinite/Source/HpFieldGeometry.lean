import HpLiteralField
import OddFourTower
import geometry.RatFuncFiniteExtension

namespace FourCorner.HpFieldGeometry

open HpLiteralField AlgebraicCurve
noncomputable section
variable (K : Type*) [Field K]

instance constantAlgebra (p : K) : Algebra K (field K p) :=
  ((algebraMap (RatFunc K) (field K p)).comp (algebraMap K (RatFunc K))).toAlgebra

instance constantsLineTower (p : K) : IsScalarTower K (RatFunc K) (field K p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem root_generates (p : K) : Algebra.adjoin (RatFunc K) (Set.range (root K p))=⊤ := by
  letI := finite_over_line K p
  apply (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (fun x _ =>
    (IsIntegral.of_finite (RatFunc K) x).isAlgebraic)).mp
  exact root_adjoin_eq_top K p

theorem isCurveOver [PerfectField K] (p : K) : IsCurveOver K (field K p) := by
  letI := finite_over_line K p
  exact RatFuncFiniteExtension.isCurveOver_of_perfectField K (field K p)

theorem separable [NeZero (2 : K)] (p : K) : Algebra.IsSeparable (RatFunc K) (field K p) :=
  RadicalSeparable.generated (root K p) (root_generates K p) (fun i =>
    RadicalSeparable.square_root (root_sq K p i) (by
      simpa only [map_ofNat] using (map_ne_zero (algebraMap K (RatFunc K))).mpr (NeZero.ne (2 : K))))

theorem index_formula [NeZero (2 : K)] (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (w : Place K (field K p)) :
    w.ramificationIndex (RatFunc K)=
      if (∀ i : Fin 4,Even ((w.restrict (RatFunc K)).ord (radicand K p i))) then 1 else 2 := by
  classical
  letI := finite_over_line K p
  have hgen : Algebra.adjoin (RatFunc K) {root K p 0,root K p 1,root K p 2,root K p 3}=⊤ := by
    have hrange : Set.range (root K p)={root K p 0,root K p 1,root K p 2,root K p 3} := by
      ext x
      simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> tauto
      · rintro (h | h | h | h)
        · exact ⟨0,h.symm⟩
        · exact ⟨1,h.symm⟩
        · exact ⟨2,h.symm⟩
        · exact ⟨3,h.symm⟩
    rw [← hrange]
    exact root_generates K p
  have hn (i : Fin 4) : radicand K p i ≠ 0 := by
    have hh := radicand_product_nonsquare K p hp ha hb {i} (by simp)
    simp only [Finset.prod_singleton] at hh
    intro hz
    exact hh (by simp [hz])
  rw [OddFourTower.index_formula w (radicand K p 0) (radicand K p 1) (radicand K p 2) (radicand K p 3)
    (root K p 0) (root K p 1) (root K p 2) (root K p 3) (root_sq K p 0) (root_sq K p 1)
    (root_sq K p 2) (root_sq K p 3) (hn 0) (hn 1) (hn 2) (hn 3) hgen]
  congr 1
  simp [Fin.forall_fin_succ,and_assoc]

#print axioms isCurveOver
#print axioms separable
#print axioms index_formula

end
end FourCorner.HpFieldGeometry
