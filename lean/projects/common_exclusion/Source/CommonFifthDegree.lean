import CommonFourDegree
import CommonFiveIndependence

noncomputable section
namespace FourCorner.CommonFifthDegree
open IntermediateField
open Multiquadratic
open Multiquadratic.QuadraticSquareCriterion
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem fifth_nonsquare_of_products (q : Fin 5 → F) (r : Fin 4 → L)
    (hr : ∀ i, r i ^ 2 = algebraMap F L (q i.castSucc))
    (h2 : (2 : F) ≠ 0)
    (hind : ∀ s : Finset (Fin 5), s.Nonempty → ¬ IsSquare (∏ i ∈ s, q i)) :
    ¬ IsSquare (algebraMap F (IntermediateField.adjoin F {r 0,r 1,r 2,r 3}) (q 4)) := by
  have hi : IndependentSquareclasses F (q 0) (q 1) (q 2) := by
    apply independentSquareclasses_of_products (F := F) ![q 0,q 1,q 2]
    intro s hs
    have h := hind (s.map (Fin.castLEEmb (by decide : 3 ≤ 5))) (Finset.map_nonempty.mpr hs)
    have he : (∏ i ∈ s.map (Fin.castLEEmb (by decide : 3 ≤ 5)), q i) =
        ∏ i ∈ s, ![q 0,q 1,q 2] i := by
      rw [Finset.prod_map]
      apply Finset.prod_congr rfl
      intro i _
      fin_cases i <;> rfl
    rwa [he] at h
  let J := IntermediateField.adjoin F {r 0,r 1,r 2}
  let T := IntermediateField.adjoin J {r 3}
  have hT : T.restrictScalars F = IntermediateField.adjoin F {r 0,r 1,r 2,r 3} := by
    have hh := IntermediateField.adjoin_adjoin_left (F := F) (S := {r 0,r 1,r 2}) {r 3}
    simpa only [Set.insert_union, Set.singleton_union] using hh
  have h3 : ¬ IsSquare (algebraMap F J (q 3)) := by
    intro h
    rcases CommonFourDegree.triquadratic_square_criterion (q 0) (q 1) (q 2)
      (q 3) (r 0) (r 1) (r 2) (hr 0) (hr 1) (hr 2) hi h2 h with
      h | h | h | h | h | h | h | h
    · apply hind {3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {1,3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,1,3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {2,3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,2,3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {1,2,3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,1,2,3} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
  have h4 : ¬ IsSquare (algebraMap F J (q 4)) := by
    intro h
    rcases CommonFourDegree.triquadratic_square_criterion (q 0) (q 1) (q 2)
      (q 4) (r 0) (r 1) (r 2) (hr 0) (hr 1) (hr 2) hi h2 h with
      h | h | h | h | h | h | h | h
    · apply hind {4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {1,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,1,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {2,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,2,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {1,2,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,1,2,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
  have h34 : ¬ IsSquare (algebraMap F J (q 3 * q 4)) := by
    intro h
    rcases CommonFourDegree.triquadratic_square_criterion (q 0) (q 1) (q 2)
      (q 3 * q 4) (r 0) (r 1) (r 2) (hr 0) (hr 1) (hr 2) hi h2 h with
      h | h | h | h | h | h | h | h
    · apply hind {3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {1,3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,1,3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {2,3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,2,3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {1,2,3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
    · apply hind {0,1,2,3,4} (by simp)
      simpa [Finset.prod_insert, mul_assoc] using h
  intro h
  have hInto : IsSquare (algebraMap J T (algebraMap F J (q 4))) := by
    obtain ⟨x,hx⟩ := h
    let y : T := ⟨x.val, by change x.val ∈ T.restrictScalars F; rw [hT]; exact x.property⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    have hh := congrArg (fun z : IntermediateField.adjoin F {r 0,r 1,r 2,r 3} => (z:L)) hx
    simpa [y] using hh
  have hr3 : r 3 ^ 2 = algebraMap J L (algebraMap F J (q 3)) :=
    (hr 3).trans (IsScalarTower.algebraMap_apply F J L (q 3))
  have h2J : (2 : J) ≠ 0 := by
    simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap F J)).mpr h2
  rcases square_criterion (algebraMap F J (q 3)) (algebraMap F J (q 4))
    (r 3) hr3 h3 h2J hInto with h | h
  · exact h4 h
  · exact h34 (by simpa only [map_mul] using h)

#print axioms fifth_nonsquare_of_products
end FourCorner.CommonFifthDegree
