import EllipticQuarticChartBase

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
namespace FourCorner.EllipticQuarticModel
variable (K : Type u) [Field K]

def coordinateEvaluation (v : Fin 4 → K) (hv : ∀ j, eval v (equation K j) = 0) :
    homogeneousRing K →+* K :=
  Ideal.Quotient.lift (ideal K).toIdeal (eval v) (by
    change (ideal K).toIdeal ≤ RingHom.ker (eval v)
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hv j)

@[simp] theorem coordinateEvaluation_coordinate (v : Fin 4 → K)
    (hv : ∀ j, eval v (equation K j) = 0) (j : Fin 4) :
    coordinateEvaluation K v hv (projectiveCoordinate K j) = v j := by
  change eval v (X j) = v j
  simp

theorem evaluation_irrelevant (v : Fin 4 → K) (hv : ∀ j, eval v (equation K j) = 0)
    (hn : ∃ j, v j ≠ 0) :
    (HomogeneousIdeal.irrelevant (grading K)).toIdeal.map (coordinateEvaluation K v hv) = ⊤ := by
  obtain ⟨j,hj⟩ := hn
  have hm := Ideal.mem_map_of_mem (coordinateEvaluation K v hv)
    (HomogeneousIdeal.mem_irrelevant_of_mem (grading K) one_pos (coordinate_degree_one K j))
  rw [coordinateEvaluation_coordinate] at hm
  exact Ideal.eq_top_of_isUnit_mem _ hm (isUnit_iff_ne_zero.mpr hj)

def coordinateSections (v : Fin 4 → K) (hv : ∀ j, eval v (equation K j) = 0) :
    homogeneousRing K →+* Γ(Spec (.of K),⊤) :=
  (Scheme.ΓSpecIso (.of K)).inv.hom.comp (coordinateEvaluation K v hv)

theorem sections_irrelevant (v : Fin 4 → K) (hv : ∀ j, eval v (equation K j) = 0)
    (hn : ∃ j, v j ≠ 0) :
    (HomogeneousIdeal.irrelevant (grading K)).toIdeal.map (coordinateSections K v hv) = ⊤ := by
  rw [coordinateSections,← Ideal.map_map,evaluation_irrelevant K v hv hn]
  exact Ideal.map_top _

def pointOfCoordinates (v : Fin 4 → K) (hv : ∀ j, eval v (equation K j) = 0)
    (hn : ∃ j, v j ≠ 0) : Spec (.of K) ⟶ curve K :=
  Proj.fromOfGlobalSections (grading K) (coordinateSections K v hv)
    (sections_irrelevant K v hv hn)

set_option backward.isDefEq.respectTransparency false in
theorem point_preimage_chart (v : Fin 4 → K) (hv : ∀ j, eval v (equation K j) = 0)
    (hn : ∃ j, v j ≠ 0) (j : Fin 4) :
    pointOfCoordinates K v hv hn ⁻¹ᵁ Proj.basicOpen (grading K) (projectiveCoordinate K j) =
      PrimeSpectrum.basicOpen (v j) := by
  unfold pointOfCoordinates
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (grading K)
    (coordinateSections K v hv) (sections_irrelevant K v hv hn)
    one_pos (coordinate_degree_one K j)]
  simp [coordinateSections]

def overlapVector : Fin 4 → K := ![1,1,1,0]
theorem overlap_equations (j : Fin 2) : eval (overlapVector K) (equation K j) = 0 := by
  fin_cases j <;> simp [overlapVector,equation,conic,cubicClosure]
def overlapPoint : Spec (.of K) ⟶ curve K :=
  pointOfCoordinates K (overlapVector K) (overlap_equations K) ⟨0,by simp [overlapVector]⟩

theorem chart_overlap_nonempty :
    ((Proj.basicOpen (grading K) (projectiveCoordinate K 0) : Set (Proj (grading K))) ∩
      Proj.basicOpen (grading K) (projectiveCoordinate K 2)).Nonempty := by
  let p : Spec (.of K) := IsLocalRing.closedPoint K
  refine ⟨overlapPoint K p,?_,?_⟩
  · change p ∈ overlapPoint K ⁻¹ᵁ Proj.basicOpen (grading K) (projectiveCoordinate K 0)
    rw [overlapPoint,point_preimage_chart]
    simp [overlapVector]
    trivial
  · change p ∈ overlapPoint K ⁻¹ᵁ Proj.basicOpen (grading K) (projectiveCoordinate K 2)
    rw [overlapPoint,point_preimage_chart]
    simp [overlapVector]
    trivial

end FourCorner.EllipticQuarticModel
#print axioms FourCorner.EllipticQuarticModel.pointOfCoordinates
#print axioms FourCorner.EllipticQuarticModel.chart_overlap_nonempty
