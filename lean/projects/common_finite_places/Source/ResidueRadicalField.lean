import CommonGenus17Field
import geometry.RatFuncFiniteExtension

noncomputable section
open Polynomial IntermediateField
namespace FourCorner.ResidueRadicalField
variable (K : Type*) [Field K]

/-- The same literal radical definitions make sense over a finite field.
No characteristic-zero model or genus is transported by this definition. -/
abbrev field (t κ : K) := CommonGenus17Field.field K t κ

theorem four_radical_integral (t : K) (i : Fin 4) :
    IsIntegral (RatFunc K) (CommonLiteralField.radical K t i) := by
  refine ⟨X^2-C (CommonLiteralField.radicand K t i),monic_X_pow_sub_C _ (by decide),?_⟩
  simp [CommonLiteralField.radical_sq]

theorem four_finite (t : K) : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) := by
  classical
  letI : Fintype (Set.range (CommonLiteralField.radical K t)) :=
    (Set.finite_range (CommonLiteralField.radical K t)).fintype
  apply IntermediateField.finiteDimensional_adjoin
  rintro x ⟨i,rfl⟩
  exact four_radical_integral K t i

/-- The specified fifth radical satisfies its original equation in EVERY
characteristic; this is proved directly from its algebraic-closure construction. -/
theorem fifth_radical_sq (t κ : K) : CommonGenus17Field.radical K t κ ^ 2 =
    algebraMap (CommonLiteralField.field K t) (AlgebraicClosure (CommonLiteralField.field K t))
      (CommonGenus17Field.radicand K t κ) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (CommonLiteralField.field K t) (AlgebraicClosure (CommonLiteralField.field K t))
      (CommonGenus17Field.radicand K t κ)) (show 0 < (2 : ℕ) by decide))

theorem fifth_radical_integral (t κ : K) :
    IsIntegral (CommonLiteralField.field K t) (CommonGenus17Field.radical K t κ) := by
  refine ⟨X^2-C (CommonGenus17Field.radicand K t κ),monic_X_pow_sub_C _ (by decide),?_⟩
  simp [fifth_radical_sq]

theorem fifth_finite (t κ : K) : FiniteDimensional (CommonLiteralField.field K t) (field K t κ) :=
  IntermediateField.adjoin.finiteDimensional (fifth_radical_integral K t κ)

instance constants_line_tower (t κ : K) : IsScalarTower K (RatFunc K) (field K t κ) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  rfl

theorem finite_over_line (t κ : K) : FiniteDimensional (RatFunc K) (field K t κ) := by
  letI := four_finite K t
  letI := fifth_finite K t κ
  exact FiniteDimensional.trans (RatFunc K) (CommonLiteralField.field K t) (field K t κ)

/-- Finite generation of the ACTUAL residue radical function field. -/
theorem essFiniteType (t κ : K) : Algebra.EssFiniteType K (field K t κ) := by
  letI := finite_over_line K t κ
  exact RatFuncFiniteExtension.essFiniteType K (field K t κ)

/-- A genuine one-variable function field over perfect residue constants,
including finite fields. Full constants and genus seventeen remain separate goals. -/
theorem isCurveOver [PerfectField K] (t κ : K) : AlgebraicCurve.IsCurveOver K (field K t κ) := by
  letI := finite_over_line K t κ
  exact RatFuncFiniteExtension.isCurveOver_of_perfectField K (field K t κ)

end FourCorner.ResidueRadicalField
#print axioms FourCorner.ResidueRadicalField.finite_over_line
#print axioms FourCorner.ResidueRadicalField.essFiniteType
#print axioms FourCorner.ResidueRadicalField.isCurveOver
