import GenericStalkField
import NormalizedModelPointRestriction

noncomputable section
namespace FourCorner.CanonicalGenericField
open AlgebraicGeometry AlgebraicCurve CategoryTheory IntermediateField
universe u
variable (K E : Type u) [Field K] [CharZero K] [Field E] [Algebra K E]
  [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

abbrev parameter : E := CurveModel.towerGenerator K
local instance parameterNonzero : Fact (parameter K E ≠ 0) := ⟨CurveModel.towerGenerator_ne_zero K⟩
local instance zeroFinite : FiniteDimensional K⟮parameter K E⟯ E :=
  (CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)).1
local instance infinityFinite : FiniteDimensional K⟮(parameter K E)⁻¹⟯ E :=
  (CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)).2

def chartOpen : Spec (.of (CurveModel.chartRing K ({parameter K E} : Set E))) ⟶
    (SchemeModelFiniteExtension.model K E).C :=
  CurveModel.ι₀ K (parameter K E) ≫ (NormalizedModelCover.sourceIso K E).inv
instance : IsOpenImmersion (chartOpen K E) := by unfold chartOpen; infer_instance

def point : Spec (.of E) ⟶ (SchemeModelFiniteExtension.model K E).C :=
  FractionGenericStalk.fieldMap (CurveModel.chartRing K ({parameter K E} : Set E)) E ≫ chartOpen K E

theorem point_eq : point K E =
    NormalizationCoverField.fieldPoint K E (parameter K E) ≫ (NormalizedModelCover.sourceIso K E).inv := by
  simp only [point,chartOpen,NormalizationCoverField.fieldPoint,FractionGenericStalk.fieldMap,Category.assoc]

theorem point_generic : point K E (IsLocalRing.closedPoint E) =
    genericPoint (SchemeModelFiniteExtension.model K E).C :=
  FractionGenericStalk.open_fieldMap_generic _ _ (chartOpen K E)
theorem point_stalk_bijective : Function.Bijective (Scheme.stalkClosedPointTo (point K E)).hom :=
  FractionGenericStalk.open_stalk_eval_bijective _ _ (chartOpen K E)

/-- This is the FIELD ISOMORPHISM induced by the original fraction-field
chart point on the actual generic stalk of the actual canonical curve. -/
def equiv : (SchemeModelFiniteExtension.model K E).C.functionField ≃+* E :=
  GenericStalkField.equiv (point K E) (point_generic K E) (point_stalk_bijective K E)

theorem factor : Spec.map (CommRingCat.ofHom (equiv K E).toRingHom) ≫
    (SchemeModelFiniteExtension.model K E).C.fromSpecStalk
      (genericPoint (SchemeModelFiniteExtension.model K E).C) = point K E :=
  GenericStalkField.factor _ _ _
end FourCorner.CanonicalGenericField
#print axioms FourCorner.CanonicalGenericField.equiv
#print axioms FourCorner.CanonicalGenericField.factor
