import geometry.SchemeModelFiniteExtension

noncomputable section
namespace FourCorner.NormalizationCoefficientMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
universe u
variable {K F E : Type u} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual coefficient map between the polynomial subalgebras of two function fields. -/
def coefficientMap (φ : F →ₐ[K] E) (S : Set F) (T : Set E) (h : φ '' S ⊆ T) :
    Algebra.adjoin K S →ₐ[K] Algebra.adjoin K T :=
  (φ.comp (Algebra.adjoin K S).val).codRestrict _ (by
    intro a
    have hm : φ a ∈ (Algebra.adjoin K S).map φ := ⟨a,a.2,rfl⟩
    have hle : (Algebra.adjoin K S).map φ ≤ Algebra.adjoin K T := by
      rw [AlgHom.map_adjoin]
      exact Algebra.adjoin_mono h
    exact hle hm)

lemma map_integral_mem (φ : F →ₐ[K] E) (S : Set F) (T : Set E) (h : φ '' S ⊆ T)
    (a : CurveModel.chartRing K S) : IsIntegral (Algebra.adjoin K T) (φ a) :=
  a.2.map_of_comp_eq (coefficientMap φ S T h).toRingHom φ.toRingHom (by ext x; rfl)

/-- Functoriality of the actual integral closures inside the two specified fields. -/
def chartMap (φ : F →ₐ[K] E) (S : Set F) (T : Set E) (h : φ '' S ⊆ T) :
    CurveModel.chartRing K S →+* CurveModel.chartRing K T where
  toFun a := ⟨φ a,map_integral_mem φ S T h a⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_one' := Subtype.ext (map_one φ)
  map_add' a b := Subtype.ext (map_add φ (a : F) (b : F))
  map_mul' a b := Subtype.ext (map_mul φ (a : F) (b : F))

lemma chartMap_constants (φ : F →ₐ[K] E) (S : Set F) (T : Set E) (h : φ '' S ⊆ T) (a : K) :
    chartMap φ S T h (algebraMap K (CurveModel.chartRing K S) a) =
      algebraMap K (CurveModel.chartRing K T) a := by
  apply Subtype.ext
  exact φ.commutes a

@[simp] theorem chartMap_coe (φ : F →ₐ[K] E) (S : Set F) (T : Set E) (h : φ '' S ⊆ T)
    (a : CurveModel.chartRing K S) : (chartMap φ S T h a : E) = φ a := rfl

def zeroMap (φ : F →ₐ[K] E) (s : F) :
    CurveModel.chartRing K ({s} : Set F) →+* CurveModel.chartRing K ({φ s} : Set E) :=
  chartMap φ ({s} : Set F) ({φ s} : Set E) (by simp)
def infinityMap (φ : F →ₐ[K] E) (s : F) :
    CurveModel.chartRing K ({s⁻¹} : Set F) →+* CurveModel.chartRing K ({(φ s)⁻¹} : Set E) :=
  chartMap φ ({s⁻¹} : Set F) ({(φ s)⁻¹} : Set E) (by simp)
def overlapMap (φ : F →ₐ[K] E) (s : F) :
    CurveModel.chartRing K ({s,s⁻¹} : Set F) →+* CurveModel.chartRing K ({φ s,(φ s)⁻¹} : Set E) :=
  chartMap φ ({s,s⁻¹} : Set F) ({φ s,(φ s)⁻¹} : Set E) (by
    rintro _ ⟨a,ha,rfl⟩
    rcases (show a=s ∨ a=s⁻¹ by simpa using ha) with rfl|rfl <;> simp)

@[simp] lemma zeroMap_coe (φ : F →ₐ[K] E) (s : F)
    (a : CurveModel.chartRing K ({s} : Set F)) : (zeroMap φ s a : E) = φ a :=
  chartMap_coe φ _ _ _ a
@[simp] lemma infinityMap_coe (φ : F →ₐ[K] E) (s : F)
    (a : CurveModel.chartRing K ({s⁻¹} : Set F)) : (infinityMap φ s a : E) = φ a :=
  chartMap_coe φ _ _ _ a
@[simp] lemma overlapMap_coe (φ : F →ₐ[K] E) (s : F)
    (a : CurveModel.chartRing K ({s,s⁻¹} : Set F)) : (overlapMap φ s a : E) = φ a :=
  chartMap_coe φ _ _ _ a

lemma zero_overlap_value (φ : F →ₐ[K] E) (s : F)
    (a : CurveModel.chartRing K ({s} : Set F)) :
    ((CurveModel.incl₀ K (φ s)) (zeroMap φ s a) : E) =
      (overlapMap φ s ((CurveModel.incl₀ K s) a) : E) := by
  rw [CurveModel.coe_chartIncl,zeroMap_coe,overlapMap_coe,CurveModel.coe_chartIncl]

lemma infinity_overlap_value (φ : F →ₐ[K] E) (s : F)
    (a : CurveModel.chartRing K ({s⁻¹} : Set F)) :
    ((CurveModel.inclInf K (φ s)) (infinityMap φ s a) : E) =
      (overlapMap φ s ((CurveModel.inclInf K s) a) : E) := by
  rw [CurveModel.coe_chartIncl,infinityMap_coe,overlapMap_coe,CurveModel.coe_chartIncl]

lemma zero_overlap_compatible (φ : F →ₐ[K] E) (s : F) :
    (CurveModel.incl₀ K (φ s)).toRingHom.comp (zeroMap φ s) =
      (overlapMap φ s).comp (CurveModel.incl₀ K s).toRingHom :=
  RingHom.ext fun a => Subtype.val_injective (zero_overlap_value φ s a)

lemma infinity_overlap_compatible (φ : F →ₐ[K] E) (s : F) :
    (CurveModel.inclInf K (φ s)).toRingHom.comp (infinityMap φ s) =
      (overlapMap φ s).comp (CurveModel.inclInf K s).toRingHom :=
  RingHom.ext fun a => Subtype.val_injective (infinity_overlap_value φ s a)

#print axioms zero_overlap_value
#print axioms infinity_overlap_value
#print axioms zero_overlap_compatible
#print axioms infinity_overlap_compatible
#print axioms coefficientMap
#print axioms chartMap
#print axioms chartMap_constants
#print axioms zeroMap
#print axioms infinityMap
#print axioms overlapMap
end FourCorner.NormalizationCoefficientMap
