import geometry.MultiquadraticField

noncomputable section
namespace FourCorner.CommonFourDegree
open IntermediateField
open Multiquadratic
open Multiquadratic.QuadraticSquareCriterion
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- The squareclass kernel of an actual three-radical field consists of the
eight generated squareclasses. This is a square-root theorem, not a degree
or ramification hypothesis. -/
theorem triquadratic_square_criterion (a b c d : F) (r s u : L)
    (hr : r^2 = algebraMap F L a) (hs : s^2 = algebraMap F L b)
    (hu : u^2 = algebraMap F L c)
    (hind : IndependentSquareclasses F a b c) (h2 : (2:F) ≠ 0)
    (hd : IsSquare (algebraMap F (IntermediateField.adjoin F {r,s,u}) d)) :
    IsSquare d ∨ IsSquare (a*d) ∨ IsSquare (b*d) ∨ IsSquare (a*(b*d)) ∨
    IsSquare (c*d) ∨ IsSquare (a*(c*d)) ∨ IsSquare (b*(c*d)) ∨
    IsSquare (a*(b*(c*d))) := by
  let J := IntermediateField.adjoin F {r,s}
  let T := IntermediateField.adjoin J {u}
  have hT : T.restrictScalars F = IntermediateField.adjoin F {r,s,u} := by
    have hh := IntermediateField.adjoin_adjoin_left (F := F) (S := {r,s}) {u}
    simpa only [Set.insert_union, Set.singleton_union] using hh
  have hdT : IsSquare (algebraMap J T (algebraMap F J d)) := by
    obtain ⟨x,hx⟩ := hd
    let y : T := ⟨x.val, by change x.val ∈ T.restrictScalars F; rw [hT]; exact x.property⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    have hh := congrArg (fun z : IntermediateField.adjoin F {r,s,u} => (z:L)) hx
    simpa [y] using hh
  have hcJ : ¬ IsSquare (algebraMap F J c) := by
    intro h
    rcases biquadratic_square_criterion a b c r s hr hs hind.first hind.second
      hind.first_second h2 h with h | h | h | h
    · exact hind.third h
    · exact hind.first_third h
    · exact hind.second_third h
    · exact hind.all_three (by simpa only [mul_assoc] using h)
  have huJ : u^2 = algebraMap J L (algebraMap F J c) :=
    hu.trans (IsScalarTower.algebraMap_apply F J L c)
  have h2J : (2:J) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap F J)).mpr h2
  rcases square_criterion (algebraMap F J c) (algebraMap F J d) u huJ hcJ h2J hdT with h | h
  · rcases biquadratic_square_criterion a b d r s hr hs hind.first hind.second
      hind.first_second h2 h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have hcd : IsSquare (algebraMap F J (c*d)) := by simpa only [map_mul] using h
    rcases biquadratic_square_criterion a b (c*d) r s hr hs hind.first hind.second
      hind.first_second h2 hcd with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- Actual degree sixteen for four independent square roots in any common
ambient field. The hypotheses contain no field-degree assumption. -/
theorem finrank_four_eq_sixteen (a b c d : F) (r s u v : L)
    (hr : r^2 = algebraMap F L a) (hs : s^2 = algebraMap F L b)
    (hu : u^2 = algebraMap F L c) (hv : v^2 = algebraMap F L d)
    (hind : IndependentSquareclasses F a b c) (h2 : (2:F) ≠ 0)
    (hd : ¬ (IsSquare d ∨ IsSquare (a*d) ∨ IsSquare (b*d) ∨ IsSquare (a*(b*d)) ∨
      IsSquare (c*d) ∨ IsSquare (a*(c*d)) ∨ IsSquare (b*(c*d)) ∨
      IsSquare (a*(b*(c*d))))) :
    Module.finrank F (IntermediateField.adjoin F {r,s,u,v}) = 16 := by
  have da := finrank_adjoin_square_root F hr (fun x hx =>
    hind.first ⟨x, by simpa only [sq] using hx.symm⟩)
  have hb : ∀ x : IntermediateField.adjoin F {r},
      x^2 ≠ algebraMap F (IntermediateField.adjoin F {r}) b := by
    intro x hx
    rcases square_criterion a b r hr hind.first h2
      ⟨x, by simpa only [sq] using hx.symm⟩ with h | h
    · exact hind.second h
    · exact hind.first_second h
  have db : Module.finrank (IntermediateField.adjoin F {r})
      (IntermediateField.adjoin (IntermediateField.adjoin F {r}) {s}) = 2 := by
    apply finrank_adjoin_square_root _ (a := algebraMap F _ b) _ hb
    simpa only [← IsScalarTower.algebraMap_apply] using hs
  have dab : Module.finrank F (IntermediateField.adjoin F {r,s}) = 4 := by
    have hh := finrank_adjoin_union F ({r} : Set L) {s}
    simp only [Set.singleton_union, da, db] at hh
    norm_num at hh
    exact hh
  have hc : ∀ x : IntermediateField.adjoin F {r,s},
      x^2 ≠ algebraMap F (IntermediateField.adjoin F {r,s}) c := by
    intro x hx
    rcases biquadratic_square_criterion a b c r s hr hs hind.first hind.second
      hind.first_second h2 ⟨x, by simpa only [sq] using hx.symm⟩ with h | h | h | h
    · exact hind.third h
    · exact hind.first_third h
    · exact hind.second_third h
    · exact hind.all_three (by simpa only [mul_assoc] using h)
  have dc : Module.finrank (IntermediateField.adjoin F {r,s})
      (IntermediateField.adjoin (IntermediateField.adjoin F {r,s}) {u}) = 2 := by
    apply finrank_adjoin_square_root _ (a := algebraMap F _ c) _ hc
    simpa only [← IsScalarTower.algebraMap_apply] using hu
  have dabc : Module.finrank F (IntermediateField.adjoin F {r,s,u}) = 8 := by
    have hh := finrank_adjoin_union F ({r,s} : Set L) {u}
    have he : ({r,s} : Set L) ∪ {u} = {r,s,u} := by ext x; simp; tauto
    rw [he, dab, dc] at hh
    norm_num at hh
    exact hh
  have hd' : ∀ x : IntermediateField.adjoin F {r,s,u},
      x^2 ≠ algebraMap F (IntermediateField.adjoin F {r,s,u}) d := by
    intro x hx
    exact hd (triquadratic_square_criterion a b c d r s u hr hs hu hind h2
      ⟨x, by simpa only [sq] using hx.symm⟩)
  have dd : Module.finrank (IntermediateField.adjoin F {r,s,u})
      (IntermediateField.adjoin (IntermediateField.adjoin F {r,s,u}) {v}) = 2 := by
    apply finrank_adjoin_square_root _ (a := algebraMap F _ d) _ hd'
    simpa only [← IsScalarTower.algebraMap_apply] using hv
  have hh := finrank_adjoin_union F ({r,s,u} : Set L) {v}
  have he : ({r,s,u} : Set L) ∪ {v} = {r,s,u,v} := by ext x; simp; tauto
  rw [he, dabc, dd] at hh
  norm_num at hh
  exact hh

/-- Product-form independence for four radicands gives degree sixteen for
any corresponding actual four-root field. -/
theorem finrank_four_eq_sixteen_of_products (q : Fin 4 → F) (r : Fin 4 → L)
    (hr : ∀ i, r i ^ 2 = algebraMap F L (q i)) (h2 : (2:F) ≠ 0)
    (h : ∀ S : Finset (Fin 4), S.Nonempty → ¬ IsSquare (∏ i ∈ S, q i)) :
    Module.finrank F (IntermediateField.adjoin F {r 0,r 1,r 2,r 3}) = 16 := by
  have hind : IndependentSquareclasses F (q 0) (q 1) (q 2) := by
    constructor
    · simpa using h {0} (by simp)
    · simpa using h {1} (by simp)
    · simpa using h {2} (by simp)
    · simpa using h {0,1} (by simp)
    · simpa using h {0,2} (by simp)
    · simpa using h {1,2} (by simp)
    · simpa [mul_assoc] using h {0,1,2} (by simp)
  apply finrank_four_eq_sixteen (q 0) (q 1) (q 2) (q 3)
    (r 0) (r 1) (r 2) (r 3) (hr 0) (hr 1) (hr 2) (hr 3) hind h2
  intro hh
  rcases hh with hh | hh | hh | hh | hh | hh | hh | hh
  · exact (h {3} (by simp)) (by simpa using hh)
  · exact (h {0,3} (by simp)) (by simpa using hh)
  · exact (h {1,3} (by simp)) (by simpa using hh)
  · exact (h {0,1,3} (by simp)) (by simpa [mul_assoc] using hh)
  · exact (h {2,3} (by simp)) (by simpa using hh)
  · exact (h {0,2,3} (by simp)) (by simpa [mul_assoc] using hh)
  · exact (h {1,2,3} (by simp)) (by simpa [mul_assoc] using hh)
  · exact (h {0,1,2,3} (by simp)) (by simpa [mul_assoc] using hh)

#print axioms finrank_four_eq_sixteen_of_products
#print axioms finrank_four_eq_sixteen
#print axioms triquadratic_square_criterion
end FourCorner.CommonFourDegree
