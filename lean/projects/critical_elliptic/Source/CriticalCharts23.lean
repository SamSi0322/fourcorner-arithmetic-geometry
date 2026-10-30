import CriticalProj23
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! All four actual affine charts of the literal critical Proj. -/
noncomputable section
set_option autoImplicit false
namespace FourCorner.CriticalProj23
open MvPolynomial AlgebraicGeometry HomogeneousIdealQuotientGrading
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k]

def criticalGrading (i : k) := quotGrading (homogeneousSubmodule (Fin 4) k) (homogeneousIdeal i).toIdeal
instance (i : k) : GradedRing (criticalGrading i) :=
  quotGradingGradedRingOfHomogeneous _ (homogeneousIdeal i)

def coordinate (i : k) (j : Fin 4) : Ambient k ⧸ (homogeneousIdeal i).toIdeal :=
  Ideal.Quotient.mk _ (X j)

theorem positive_homogeneous_mem_span_X {d : ℕ} (hd : 0 < d)
    (p : Ambient k) (hp : p.IsHomogeneous d) :
    p ∈ Ideal.span (Set.range (X : Fin 4 → Ambient k)) := by
  show p ∈ MvPolynomial.idealOfVars (Fin 4) k
  rw [← pow_one (MvPolynomial.idealOfVars _ k), MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  rw [MvPolynomial.mem_support_iff] at hx
  have hdeg : Finsupp.degree x = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp hx
  omega

theorem critical_irrelevant_le_span (i : k) :
    (HomogeneousIdeal.irrelevant (criticalGrading i)).toIdeal ≤
      Ideal.span (Set.range (coordinate i)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd q hq
  obtain ⟨p,hp,rfl⟩ := (mem_quotGrading_iff
    (homogeneousSubmodule (Fin 4) k) (homogeneousIdeal i).toIdeal).mp hq
  have hpx := positive_homogeneous_mem_span_X hd p hp
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (homogeneousIdeal i).toIdeal) hpx
  change Ideal.Quotient.mk (homogeneousIdeal i).toIdeal p ∈
    Ideal.span (Set.range fun j : Fin 4 => Ideal.Quotient.mk (homogeneousIdeal i).toIdeal (X j))
  simpa only [Ideal.map_span,← Set.range_comp'] using hm

theorem coordinate_degree_one (i : k) (j : Fin 4) : coordinate i j ∈ criticalGrading i 1 :=
  mk_mem_quotGrading _ _ (isHomogeneous_X k j)

/-- Four affine schemes Spec((A[V_j⁻¹])₀), with genuine open immersions,
cover the actual projective critical intersection. -/
def coordinateAffineCover (i : k) : (criticalCurve i).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (criticalGrading i) (coordinate i)
    (coordinate_degree_one i) (fun _ => one_pos) (critical_irrelevant_le_span i)

theorem coordinate_opens_cover (i : k) :
    ⨆ j : Fin 4, Proj.basicOpen (criticalGrading i) (coordinate i j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (critical_irrelevant_le_span i)

#print axioms critical_irrelevant_le_span
#print axioms coordinateAffineCover
#print axioms coordinate_opens_cover
end FourCorner.CriticalProj23
