import Genus17Support

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.Genus17PointSupport
open CommonPointSource CommonPostPointResidue CommonLiteralField

/-- The finite support certificate is attached to the original actual point's
ell germ and residue, with a single global positive kappa and rational root. -/
theorem actual_point_twist (t : ℚ) (ht : 1 < t) (a : Algebra ℚ (field ℚ t)) :
    letI := a
    ∀ (M : CurveModel ℚ (field ℚ t)) (p : Spec (.of ℚ) ⟶ M.C),
    ∃ κ ∈ Genus17Support.twists t, 0 < κ ∧ ∃ u : ℚ, 0 < u ∧
      (sourceForAlgebra t ht a M p).ell = κ*u^2 ∧
      ∃ s : M.C.presheaf.stalk (pointCenter M p).1,
        algebraMap (M.C.presheaf.stalk (pointCenter M p).1) M.C.functionField s =
          M.ffEquiv (ell ℚ t) ∧
        (Scheme.stalkClosedPointTo p).hom s = κ*u^2 ∧
        u^2 = (Scheme.stalkClosedPointTo p).hom s / κ := by
  letI := a
  intro M p
  obtain ⟨κ,hκ,hκpos,u,hupos,he,hu⟩ := Genus17Support.source_has_global_twist ht
    (sourceForAlgebra t ht a M p)
  obtain ⟨s,hs,hv⟩ := actual_point_coordinates_forAlgebra t ht a M p 0
  have hv' : (Scheme.stalkClosedPointTo p).hom s = (sourceForAlgebra t ht a M p).ell := by
    simpa only [orderedValue,Matrix.cons_val_zero] using hv
  refine ⟨κ,hκ,hκpos,u,hupos,he,s,?_,hv'.trans he,?_⟩
  · simpa only [orderedFunction,Matrix.cons_val_zero] using hs
  · rw [hv']
    exact hu

end FourCorner.Genus17PointSupport
#print axioms FourCorner.Genus17PointSupport.actual_point_twist
