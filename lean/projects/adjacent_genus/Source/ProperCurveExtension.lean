import Slot03HighAdjacentGenus
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint

/-! Extension of an actual generic-point map from a smooth curve to a proper target.
The local valuative argument adapts the known FiniteMapToP1 proof in
P2M/Sol/S_AlgebraicCurve_exists_isFinite_hom_proj_of_isProper.lean,
replacing its particular projective-line target by an arbitrary proper Scheme. -/
noncomputable section
namespace FourCorner.ProperCurveExtension
open CategoryTheory AlgebraicGeometry
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (cX : X ⟶ Spec (.of K)) (cY : Y ⟶ Spec (.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 cX] [IsProper cY] [Y.IsSeparated]

include cX in
theorem valuationRing_stalk (x : X) (hx : IsClosed ({x} : Set X)) :
    ValuationRing (X.presheaf.stalk x) := by
  letI := (AlgebraicCurve.baseToFunctionField cX).toAlgebra
  obtain ⟨v,hv⟩ := AlgebraicCurve.exists_place_range_stalk_eq cX x hx
  refine (ValuationRing.iff_isInteger_or_isInteger (R := X.presheaf.stalk x)
    (K := X.functionField)).mpr fun y => ?_
  have key : ∀ z : X.functionField, z ∈ v.toValuationSubring →
      IsLocalization.IsInteger (X.presheaf.stalk x) z := by
    intro z hz
    have hz' : z ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by rw [hv]; exact hz
    obtain ⟨r,hr⟩ := hz'
    exact RingHom.mem_rangeS.mpr ⟨r,hr⟩
  rcases v.toValuationSubring.mem_or_inv_mem y with h|h
  · exact Or.inl (key y h)
  · exact Or.inr (key _ h)

variable (f : Spec X.functionField ⟶ Y)
    (hf : f ≫ cY = X.fromSpecStalk (genericPoint X) ≫ cX)

abbrev rationalMap : X ⤏ Y := Scheme.RationalMap.ofFunctionField cX cY f hf

/-- Properness fills the actual map at every closed curve point. -/
theorem mem_domain (x : X) (hx : IsClosed ({x} : Set X)) :
    x ∈ (rationalMap cX cY f hf).domain := by
  haveI := valuationRing_stalk cX x hx
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  have hproper : IsProper cY := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hproper
  have hv : ValuativeCriterion.Existence cY := hproper.1.1.1.existence
  have hsq := hv
    { R := X.presheaf.stalk x
      commRing := inferInstance
      domain := inferInstance
      valuationRing := inferInstance
      K := X.functionField
      field := inferInstance
      algebra := inferInstance
      isFractionRing := inferInstance
      i₁ := f
      i₂ := X.fromSpecStalk x ≫ cX
      commSq := ⟨by rw [hf, ← hspec]; simp only [Category.assoc]⟩ }
  obtain ⟨⟨l,hl₁,hl₂⟩⟩ := hsq.exists_lift
  let gx := Scheme.PartialMap.ofFromSpecStalk (x := x) cX cY l hl₂
  have hmem : x ∈ gx.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hgx : gx.toRationalMap = rationalMap cX cY f hf := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [rationalMap, Scheme.RationalMap.fromFunctionField_ofFunctionField,
      Scheme.RationalMap.fromFunctionField_toRationalMap]
    have h1 : gx.fromSpecStalkOfMem hmem = l :=
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
    have h2 : gx.domain.fromSpecStalkOfMem (genericPoint X)
        ((genericPoint_specializes _).mem_open gx.domain.2 gx.dense_domain.nonempty.choose_spec) =
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
          gx.domain.fromSpecStalkOfMem x hmem := by
      rw [← cancel_mono gx.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι, hspec]
    change gx.domain.fromSpecStalkOfMem (genericPoint X) _ ≫ gx.hom = f
    rw [h2,Category.assoc]
    change Spec.map _ ≫ gx.fromSpecStalkOfMem hmem = f
    rw [h1,hl₁]
  rw [← hgx]
  exact gx.le_domain_toRationalMap hmem

/-- The extension domain is the whole actual smooth curve. -/
theorem domain_eq_top : (rationalMap cX cY f hf).domain = ⊤ := by
  rw [eq_top_iff]
  rintro x _
  by_cases hx : IsClosed ({x} : Set X)
  · exact mem_domain cX cY f hf x hx
  · have hgen : x = genericPoint X := by
      by_contra h
      exact hx (AlgebraicCurve.isClosed_singleton_of_ne_genericPoint cX x h)
    subst hgen
    obtain ⟨y,hy⟩ := (rationalMap cX cY f hf).dense_domain.nonempty
    exact ((genericPoint_spec X).mem_open_set_iff (rationalMap cX cY f hf).domain.isOpen).mpr ⟨y,trivial,hy⟩

def extension : X ⟶ Y :=
  X.topIso.inv ≫ (X.isoOfEq (domain_eq_top cX cY f hf)).inv ≫
    (rationalMap cX cY f hf).toPartialMap.hom

lemma inclusion_extension :
    (rationalMap cX cY f hf).toPartialMap.domain.ι ≫ extension cX cY f hf =
      (rationalMap cX cY f hf).toPartialMap.hom := by
  have h2 : ((rationalMap cX cY f hf).toPartialMap.domain.ι ≫ X.topIso.inv) ≫
      (X.isoOfEq (domain_eq_top cX cY f hf)).inv = 𝟙 _ := by
    rw [← cancel_mono (rationalMap cX cY f hf).domain.ι]
    simp only [Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι, Category.comp_id]
    rfl
  rw [extension, ← Category.assoc, ← Category.assoc,h2]
  exact Category.id_comp _

/-- The extended map agrees with the supplied genuine generic-point morphism. -/
theorem generic_extension : X.fromSpecStalk (genericPoint X) ≫ extension cX cY f hf = f := by
  have hη : genericPoint X ∈ (rationalMap cX cY f hf).toPartialMap.domain := by
    rw [show (rationalMap cX cY f hf).toPartialMap.domain = ⊤ from domain_eq_top cX cY f hf]
    trivial
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι _ _ hη, Category.assoc,inclusion_extension]
  have h : (rationalMap cX cY f hf).toPartialMap.fromFunctionField = f := by
    rw [← Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.toRationalMap_toPartialMap, rationalMap,
      Scheme.RationalMap.fromFunctionField_ofFunctionField]
  exact h

#print axioms mem_domain
#print axioms domain_eq_top
#print axioms extension
#print axioms generic_extension
end FourCorner.ProperCurveExtension
