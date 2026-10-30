import RationalPlaceFibreHom

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace FourCorner.CriticalRationalFibres
open AlgebraicCurve ResiduePlaceEvaluation
variable {K F E:Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- Rationality of the actual restricted place follows from an actual
K-algebra evaluation of its valuation ring. -/
theorem restrict_rational (w:Place K E) (hw:w.IsRational) :
    (w.restrict F).IsRational :=
  RationalPlaceEvaluationUnique.isRational_of_algHom (w.restrict F)
    ((evaluate w hw).comp (RationalPlaceFibreHom.baseInclusion (w.restrict F) w rfl))

/-- All actual rational points of a finite function-field cover are the
sigma of their actual rational fibres, without a fibre-label hypothesis. -/
def sigmaEquiv :
    {w:Place K E //w.IsRational} ≃
      Σ v:{v:Place K F //v.IsRational},
        {w:Place K E //w.restrict F=v.val ∧ w.IsRational} where
  toFun w:=⟨⟨w.val.restrict F,restrict_rational w.val w.property⟩,⟨w.val,rfl,w.property⟩⟩
  invFun x:=⟨x.2.val,x.2.property.2⟩
  left_inv w:=by cases w;rfl
  right_inv x:=by
    rcases x with ⟨⟨v,hv⟩,⟨w,hw,hwr⟩⟩
    cases hw
    rfl

/-- The same decomposition with ANY genuine base-place locus retained. -/
def sigmaOverEquiv (P:Place K F→Prop) :
    {w:Place K E //w.IsRational ∧ P (w.restrict F)} ≃
      Σ v:{v:Place K F //v.IsRational ∧ P v},
        {w:Place K E //w.restrict F=v.val ∧ w.IsRational} where
  toFun w:=⟨⟨w.val.restrict F,restrict_rational w.val w.property.1,w.property.2⟩,
    ⟨w.val,rfl,w.property.1⟩⟩
  invFun x:=⟨x.2.val,x.2.property.2,by rw [x.2.property.1];exact x.1.property.2⟩
  left_inv w:=by cases w;rfl
  right_inv x:=by
    rcases x with ⟨⟨v,hv,hP⟩,⟨w,hw,hwr⟩⟩
    cases hw
    rfl

end FourCorner.CriticalRationalFibres
#print axioms FourCorner.CriticalRationalFibres.restrict_rational
#print axioms FourCorner.CriticalRationalFibres.sigmaEquiv
#print axioms FourCorner.CriticalRationalFibres.sigmaOverEquiv
