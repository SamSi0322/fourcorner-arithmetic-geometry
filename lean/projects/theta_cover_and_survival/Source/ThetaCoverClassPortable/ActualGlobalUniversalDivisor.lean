import ThetaCoverClassPortable.GlobalUniversalDivisor
import ThetaCoverClassPortable.ActualCurveAffineNeighborhoods

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
namespace FourCorner.ThetaRationalPicardInput
open ThetaLiteralModels

/-- Every finite set in the actual original curve lying over an affine base open
has an affine neighbourhood inside that preimage. -/
theorem original_curve_relative_affines (V : (Spec (.of ℚ)).affineOpens)
    (F : Finset (C ℚ)) (hF : ∀ x ∈ F, cToBase ℚ x ∈ (V : (Spec (.of ℚ)).Opens)) :
    ∃ U : (C ℚ).Opens, IsAffineOpen U ∧
      U ≤ cToBase ℚ ⁻¹ᵁ (V : (Spec (.of ℚ)).Opens) ∧ ∀ x ∈ F, x ∈ U := by
  classical
  obtain ⟨A, hA, hFA⟩ := ActualCurveAffineNeighborhoods.original_curve F
  letI : IsAffine A.toScheme := hA
  let g : A.toScheme ⟶ Spec (.of ℚ) := A.ι ≫ cToBase ℚ
  let W : A.toScheme.Opens := g ⁻¹ᵁ (V : (Spec (.of ℚ)).Opens)
  have hW : IsAffineOpen W := V.2.preimage g
  refine ⟨A.ι ''ᵁ W, hW.image_of_isOpenImmersion A.ι, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    exact hz
  · intro x hx
    exact ⟨⟨x, hFA x hx⟩, hF x hx, rfl⟩

/-- A genuine global universal relative effective divisor on the literal original
curve C/Q, with its native all-Scheme classification. -/
theorem actual_original_curve_exists_isUniversal (r : ℕ) :
    ∃ (Y : Scheme) (y : Y ⟶ Spec (.of ℚ))
      (Duniv : RelEffCartierDiv (cToBase ℚ) r y), Duniv.IsUniversal := by
  letI : IsProper (cToBase ℚ) := source_proper
  letI : SmoothOfRelativeDimension 1 (cToBase ℚ) := source_smooth
  exact FourCorner.GlobalUniversalDivisor.exists_isUniversal
    (𝟙 _) (cToBase ℚ) original_curve_relative_affines r

/-- The literal original curve after an arbitrary actual QQ-scheme base change.
The finite-neighbourhood condition and affine chart universals are proved,
not supplied as representation assumptions. -/
theorem actual_baseChange_exists_isUniversal {B : Scheme}
    (qB : B ⟶ Spec (.of ℚ)) (r : ℕ) :
    ∃ (Y : Scheme) (y : Y ⟶ B)
      (Duniv : RelEffCartierDiv (pullback.snd (cToBase ℚ) qB) r y), Duniv.IsUniversal := by
  letI : IsProper (cToBase ℚ) := source_proper
  letI : SmoothOfRelativeDimension 1 (cToBase ℚ) := source_smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  apply FourCorner.GlobalUniversalDivisor.exists_isUniversal qB (pullback.snd _ _)
  intro V F hF
  exact ActualCurveAffineNeighborhoods.relative_affine_basechange qB V.1 V.2 F hF

/-- Every commutative QQ-algebra, including the zero ring, has the actual global
universal relative degree-r divisor of the same literal base-changed curve. -/
theorem actual_ringBase_exists_isUniversal (B : Type) [CommRing B] [Algebra ℚ B]
    (r : ℕ) :
    ∃ (Y : Scheme) (y : Y ⟶ Spec (.of B))
      (Duniv : RelEffCartierDiv (SmoothProperCurve.baseChange ℚ (cToBase ℚ) B) r y),
      Duniv.IsUniversal :=
  actual_baseChange_exists_isUniversal (SmoothProperCurve.specMap ℚ B) r

end FourCorner.ThetaRationalPicardInput
