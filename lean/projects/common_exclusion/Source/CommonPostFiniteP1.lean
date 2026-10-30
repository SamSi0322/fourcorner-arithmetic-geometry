import CommonPostGeometricGenus
import NormalizedBaseP1

noncomputable section
open AlgebraicGeometry AlgebraicCurve CategoryTheory
namespace FourCorner.CommonPostFiniteP1
open CommonSchemeModel CommonPostGeometricGenus

abbrev inclusionRingHom (K E : Type) [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] : RatFunc K →+* E :=
  (NormalizedModelCover.fieldInclusion K E).toRingHom
lemma inclusionRingHom_eq (K E : Type) [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] :
    inclusionRingHom K E = algebraMap (RatFunc K) E := rfl

abbrev literalInclusion {K : Type} [Field K] (t : K) : RatFunc K →+* CommonLiteralField.field K t :=
  algebraMap (RatFunc K) (CommonLiteralField.field K t)

abbrev commonCurve {K : Type} [Field K] [CharZero K] (t : K)
    (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) := (model t h0 h1 hm).C

/-- Native finite ell morphism to the literal standard projective-line Scheme. -/
def ellMap (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    commonCurve t h0 h1 hm ⟶ ProjectiveLineCharts.P1 ℚ := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  exact NormalizedModelCover.cover ℚ (CommonLiteralField.field ℚ t) ≫ NormalizedBaseP1.iso.hom

theorem ellMap_isFinite (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    IsFinite (ellMap t h0 h1 hm) := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  haveI := NormalizedModelCover.cover_isFinite ℚ (CommonLiteralField.field ℚ t)
  change IsFinite (NormalizedModelCover.cover ℚ (CommonLiteralField.field ℚ t) ≫ NormalizedBaseP1.iso.hom)
  exact MorphismProperty.comp_mem @IsFinite _ _
    (NormalizedModelCover.cover_isFinite ℚ (CommonLiteralField.field ℚ t)) inferInstance

lemma ellMap_overQ (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    ellMap t h0 h1 hm ≫ ProjectiveLineCharts.toBase ℚ = modelToBase t h0 h1 hm := by
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _


local instance ratFuncParameterNonzero : Fact ((RatFunc.X : RatFunc ℚ) ≠ 0) := ⟨RatFunc.X_ne_zero⟩

def genericBaseFieldPoint (K : Type) [Field K] [CharZero K] :
    Spec (.of (RatFunc K)) ⟶ NormalizedBaseP1.baseCurve (K := K) := by
  letI : Fact ((RatFunc.X : RatFunc K) ≠ 0) := ⟨RatFunc.X_ne_zero⟩
  exact NormalizationCoverField.fieldPoint K (RatFunc K) RatFunc.X ≫ (NormalizedModelCover.baseIso K).inv

def baseFieldPoint : Spec (.of (RatFunc ℚ)) ⟶ ProjectiveLineCharts.P1 ℚ :=
  genericBaseFieldPoint ℚ ≫ NormalizedBaseP1.iso.hom

def sourceFieldPoint (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Spec (.of (CommonLiteralField.field ℚ t)) ⟶ commonCurve t h0 h1 hm := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  letI : Fact (NormalizedModelCover.fieldInclusion ℚ (CommonLiteralField.field ℚ t) RatFunc.X ≠ 0) :=
    ⟨CurveModel.towerGenerator_ne_zero ℚ⟩
  exact NormalizationCoverField.fieldPoint ℚ (CommonLiteralField.field ℚ t)
    (NormalizedModelCover.fieldInclusion ℚ (CommonLiteralField.field ℚ t) RatFunc.X) ≫
      (NormalizedModelCover.sourceIso ℚ (CommonLiteralField.field ℚ t)).inv

/-- The actual finite projective-line map induces the original specified rational-function
extension, not a different choice of parameter on D_t. -/
theorem generic_ellMap (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    sourceFieldPoint t h0 h1 hm ≫ ellMap t h0 h1 hm =
      Spec.map (CommRingCat.ofHom (literalInclusion t)) ≫ baseFieldPoint := by
  letI := modelFieldAlgebra t
  letI : FiniteDimensional (RatFunc ℚ) (CommonLiteralField.field ℚ t) :=
    FiniteDimensional.of_finrank_pos (by rw [CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm]; norm_num)
  have h := NormalizedModelCover.generic_cover ℚ (CommonLiteralField.field ℚ t)
  set_option backward.isDefEq.respectTransparency false in
    simpa only [sourceFieldPoint,ellMap,baseFieldPoint,genericBaseFieldPoint,literalInclusion,NormalizedModelCover.fieldInclusion,IsScalarTower.toAlgHom,Category.assoc]
      using congrArg (fun f => f ≫ NormalizedBaseP1.iso.hom) h

/-- Exact extension degree of the native finite ell cover's supplied literal field diagram. -/
theorem ell_extension_degree_sixteen (t : ℚ) (h0 : t ≠ 0) (h1 : t ≠ 1) (hm : t ≠ -1) :
    Module.finrank (RatFunc ℚ) (CommonLiteralField.field ℚ t) = 16 :=
  CommonLiteralField.finrank_field_eq_sixteen ℚ h0 h1 hm

end FourCorner.CommonPostFiniteP1
#print axioms FourCorner.CommonPostFiniteP1.ellMap
#print axioms FourCorner.CommonPostFiniteP1.ellMap_isFinite
#print axioms FourCorner.CommonPostFiniteP1.ellMap_overQ

#print axioms FourCorner.CommonPostFiniteP1.generic_ellMap
#print axioms FourCorner.CommonPostFiniteP1.ell_extension_degree_sixteen
