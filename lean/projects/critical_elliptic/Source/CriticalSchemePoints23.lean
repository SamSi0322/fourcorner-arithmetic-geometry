import CriticalCharts23
import CriticalProjCoordinates23

/-! Actual Spec(k)-valued points from the paper's critical homogeneous coordinates.
This is a forward Scheme bridge; no converse classification is assumed. -/
noncomputable section
set_option autoImplicit false
namespace FourCorner.CriticalProj23
open MvPolynomial AlgebraicGeometry CriticalElliptic23
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type*} [Field k]

def coordinateEvaluation (i : k) (v : Fin 4 → k) (hc : CriticalCoordinates i v) :
    Ambient k ⧸ (homogeneousIdeal i).toIdeal →+* k :=
  Ideal.Quotient.lift _ (eval v) ((criticalIdeal_le_eval_kernel i v).mpr hc)

@[simp] theorem coordinateEvaluation_coordinate (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (j : Fin 4) :
    coordinateEvaluation i v hc (coordinate i j) = v j := by
  change eval v (X j) = v j
  simp

theorem coordinateEvaluation_irrelevant (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0) :
    (HomogeneousIdeal.irrelevant (criticalGrading i)).toIdeal.map
      (coordinateEvaluation i v hc) = ⊤ := by
  obtain ⟨j,hj⟩ := hn
  have hm := Ideal.mem_map_of_mem (coordinateEvaluation i v hc)
    (HomogeneousIdeal.mem_irrelevant_of_mem (criticalGrading i) one_pos
      (coordinate_degree_one i j))
  rw [coordinateEvaluation_coordinate] at hm
  exact Ideal.eq_top_of_isUnit_mem _ hm (isUnit_iff_ne_zero.mpr hj)

def coordinateSections (i : k) (v : Fin 4 → k) (hc : CriticalCoordinates i v) :
    Ambient k ⧸ (homogeneousIdeal i).toIdeal →+* Γ(Spec (.of k),⊤) :=
  (Scheme.ΓSpecIso (.of k)).inv.hom.comp (coordinateEvaluation i v hc)

theorem coordinateSections_irrelevant (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0) :
    (HomogeneousIdeal.irrelevant (criticalGrading i)).toIdeal.map
      (coordinateSections i v hc) = ⊤ := by
  rw [coordinateSections,← Ideal.map_map,coordinateEvaluation_irrelevant i v hc hn]
  exact Ideal.map_top _

/-- An actual scheme morphism Spec(k) ⟶ C_i, from every nonzero solution of
exactly the two displayed critical equations. -/
def pointOfCoordinates (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0) : Spec (.of k) ⟶ Proj (criticalGrading i) :=
  Proj.fromOfGlobalSections (criticalGrading i) (coordinateSections i v hc)
    (coordinateSections_irrelevant i v hc hn)

set_option backward.isDefEq.respectTransparency false in
theorem pointOfCoordinates_preimage_chart (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0) (j : Fin 4) :
    pointOfCoordinates i v hc hn ⁻¹ᵁ Proj.basicOpen (criticalGrading i) (coordinate i j) =
      (Spec (.of k)).basicOpen ((Scheme.ΓSpecIso (.of k)).inv.hom (v j)) := by
  unfold pointOfCoordinates
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (criticalGrading i)
    (coordinateSections i v hc) (coordinateSections_irrelevant i v hc hn)
    one_pos (coordinate_degree_one i j)]
  change (Spec (.of k)).basicOpen ((Scheme.ΓSpecIso (.of k)).inv.hom
    (coordinateEvaluation i v hc (coordinate i j))) = _
  rw [coordinateEvaluation_coordinate]

set_option backward.isDefEq.respectTransparency false in
theorem pointOfCoordinates_preimage_homogeneous (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0)
    (r : Ambient k ⧸ (homogeneousIdeal i).toIdeal) {d : ℕ}
    (hd : 0 < d) (hr : r ∈ criticalGrading i d) :
    pointOfCoordinates i v hc hn ⁻¹ᵁ Proj.basicOpen (criticalGrading i) r =
      PrimeSpectrum.basicOpen (coordinateEvaluation i v hc r) := by
  unfold pointOfCoordinates
  rw [Proj.fromOfGlobalSections_preimage_basicOpen (criticalGrading i)
    (coordinateSections i v hc) (coordinateSections_irrelevant i v hc hn) hd hr]
  simp [coordinateSections]

def signedSchemePoint (i : k) (e : Fin 3 → Bool) : Spec (.of k) ⟶ criticalCurve i :=
  pointOfCoordinates i (signedVector e) (signedVector_on_boundary i e).1
    ⟨0, by simp [signedVector]⟩

#print axioms coordinateEvaluation_irrelevant
#print axioms pointOfCoordinates
#print axioms pointOfCoordinates_preimage_chart
#print axioms signedSchemePoint
end FourCorner.CriticalProj23
