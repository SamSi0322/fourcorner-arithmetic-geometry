import QuadraticRationalPlaceFibre

noncomputable section
namespace FourCorner.RationalPlaceTower
open AlgebraicCurve ResiduePlaceEvaluation RationalPlaceEvaluationUnique RationalPlaceFibreHom
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem restrict_isRational (w : Place K E) (hw : w.IsRational) : (w.restrict F).IsRational :=
  isRational_of_algHom (w.restrict F) ((evaluate w hw).comp (baseInclusion (w.restrict F) w rfl))

theorem baseInclusion_coe (v : Place K F) (w : Place K E) (hw : w.restrict F=v)
    (a : v.toValuationSubring) : (baseInclusion v w hw a : E)=algebraMap F E (a:F) := rfl

theorem evaluate_baseInclusion (v : Place K F) (hv : v.IsRational)
    (w : Place K E) (hw : w.restrict F=v) (hwr : w.IsRational) (a : v.toValuationSubring) :
    evaluate w hwr (baseInclusion v w hw a)=evaluate v hv a :=
  AlgHom.congr_fun (algHom_unique v ((evaluate w hwr).comp (baseInclusion v w hw)) (evaluate v hv)) a

variable {L : Type*} [Field L] [Algebra K L] [Algebra F L] [Algebra E L]
  [IsScalarTower K F L] [IsScalarTower K E L] [IsScalarTower F E L]
  [FiniteDimensional F L] [FiniteDimensional E L]
  [Algebra.IsSeparable F L] [Algebra.IsSeparable E L]

theorem restrict_trans (w : Place K L) : (w.restrict E).restrict F=w.restrict F := by
  apply Place.ext
  ext x
  change algebraMap E L (algebraMap F E x)∈w.toValuationSubring ↔
    algebraMap F L x∈w.toValuationSubring
  rw [←IsScalarTower.algebraMap_apply F E L]

/-- The actual rational fibre in a field tower is the dependent union of
actual rational fibres at its two steps. Rationality of the intermediate
place is derived from the original rational place. -/
def rationalTowerFibreEquiv (v : Place K F) :
    RationalFibre (E:=L) v ≃
      Σ w : RationalFibre (E:=E) v,RationalFibre (F:=E) (E:=L) w.val where
  toFun w := ⟨⟨w.val.restrict E,by rw [restrict_trans,w.property.1],
    restrict_isRational w.val w.property.2⟩,⟨w.val,rfl,w.property.2⟩⟩
  invFun w := ⟨w.2.val,by rw [←restrict_trans (F:=F) (E:=E) w.2.val,w.2.property.1,w.1.property.1],w.2.property.2⟩
  left_inv w := Subtype.ext rfl
  right_inv := by
    rintro ⟨⟨w,hw,hwr⟩,⟨z,hz,hzr⟩⟩
    dsimp only
    cases hz
    rfl

#print axioms restrict_isRational
#print axioms evaluate_baseInclusion
#print axioms rationalTowerFibreEquiv
end FourCorner.RationalPlaceTower
