import CriticalRadicalField

noncomputable section
namespace FourCorner.QuadraticLinearNorm
open Multiquadratic.QuadraticSquareCriterion
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A square linear expression in the original quadratic adjunction has square norm.
This follows from the two literal coefficients, with no norm-map assumption. -/
theorem square_norm (B : F) (r : E) (hr : r^2 = algebraMap F E B)
    (hB : ¬ IsSquare B) (A D : F)
    (h : IsSquare (algebraMap F (IntermediateField.adjoin F {r}) D +
      algebraMap F (IntermediateField.adjoin F {r}) A *
        (⟨r, IntermediateField.subset_adjoin F {r} (by simp)⟩ :
          IntermediateField.adjoin F {r}))) :
    IsSquare (D^2 - A^2*B) := by
  obtain ⟨x,hx⟩ := h
  obtain ⟨m,n,he⟩ := coordinates B r hr x
  have heq : (algebraMap F E m + algebraMap F E n*r)^2 =
      algebraMap F E D + algebraMap F E A*r := by
    have hh := congrArg (fun z : IntermediateField.adjoin F {r} => (z:E)) hx
    simpa [he, sq] using hh.symm
  have hc : algebraMap F E (m^2+n^2*B-D) +
      algebraMap F E (2*m*n-A)*r = 0 := by
    simp only [map_sub,map_add,map_mul,map_pow,map_ofNat]
    linear_combination heq - (algebraMap F E n)^2*hr
  obtain ⟨h0,h1⟩ := map_add_mul_eq_zero B r hr hB _ _ hc
  refine ⟨m^2-n^2*B, ?_⟩
  have e0 : D=m^2+n^2*B := (sub_eq_zero.mp h0).symm
  have e1 : A=2*m*n := (sub_eq_zero.mp h1).symm
  rw [e0,e1]
  ring

#print axioms square_norm
end FourCorner.QuadraticLinearNorm
