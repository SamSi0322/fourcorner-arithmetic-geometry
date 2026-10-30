import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_CurveModelConstruction

/-!
A smooth proper integral scheme constructed from an actual finite extension of
`RatFunc K` in characteristic zero. Its function-field equivalence is constructed
by the integral-closure-chart gluing proof; no scheme model or equivalence is
assumed. This file does not assert projectivity or a sheaf-cohomology genus formula.
-/

noncomputable section

namespace FourCorner.SchemeModelFiniteExtension

open AlgebraicGeometry AlgebraicCurve

universe u

variable (K E : Type u) [Field K] [CharZero K] [Field E]
  [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
  [FiniteDimensional (RatFunc K) E]

/-- The scheme model obtained by gluing the two integral-closure charts. -/
def model : CurveModel K E := by
  have : Fact (CurveModel.towerGenerator K (L := E) ≠ 0) :=
    ⟨CurveModel.towerGenerator_ne_zero K⟩
  obtain ⟨hfin, hinv⟩ := CurveModel.finiteDimensional_adjoin_towerGenerator K (L := E)
  have := hfin
  have := hinv
  exact CurveModel.ofGenerator K (CurveModel.towerGenerator K (L := E))
    (CurveModel.transcendental_towerGenerator K)

/-- The actual constructed scheme is integral. -/
theorem model_isIntegral : IsIntegral (model K E).C := inferInstance

/-- Its structural morphism is proper. -/
theorem model_isProper : IsProper (model K E).toBase := inferInstance

/-- Its structural morphism is smooth of relative dimension one. -/
theorem model_smooth : SmoothOfRelativeDimension 1 (model K E).toBase := inferInstance

/-- The given extension is the stalk-at-generic-point function field of the constructed scheme. -/
def functionFieldEquiv : E ≃+* (model K E).C.functionField := (model K E).ffEquiv

theorem functionFieldEquiv_algebraMap (a : K) :
    functionFieldEquiv K E (algebraMap K E a) =
      AlgebraicCurve.baseToFunctionField (model K E).toBase a :=
  (model K E).ffEquiv_algebraMap a

end FourCorner.SchemeModelFiniteExtension

#check @FourCorner.SchemeModelFiniteExtension.model
#check @FourCorner.SchemeModelFiniteExtension.functionFieldEquiv
#print axioms FourCorner.SchemeModelFiniteExtension.model
#print axioms FourCorner.SchemeModelFiniteExtension.model_isIntegral
#print axioms FourCorner.SchemeModelFiniteExtension.model_isProper
#print axioms FourCorner.SchemeModelFiniteExtension.model_smooth
#print axioms FourCorner.SchemeModelFiniteExtension.functionFieldEquiv
#print axioms FourCorner.SchemeModelFiniteExtension.functionFieldEquiv_algebraMap
