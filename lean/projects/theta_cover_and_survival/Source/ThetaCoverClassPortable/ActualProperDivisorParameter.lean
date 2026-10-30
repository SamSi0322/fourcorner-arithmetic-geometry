import ThetaCoverClassPortable.ActualGlobalUniversalDivisor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_range_subset_iff_forall_subsingleton_H1_fibre

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
namespace FourCorner.ActualOpenChartCompletion
open ThetaLiteralModels ThetaRationalPicardInput AlgebraicGeometry.RelPicard

/-- The actual GLOBAL divisor parameter space of original C after an arbitrary
Noetherian QQ-algebra base change is proper. No Picard space or chart is assumed. -/
theorem actual_ringBase_proper_universal_divisor
    (B:Type) [CommRing B] [Algebra ℚ B] [IsNoetherianRing B] (d:ℕ) :
    ∃(Y:Scheme)(y:Y⟶Spec (.of B))
      (D:RelEffCartierDiv (SmoothProperCurve.baseChange ℚ (cToBase ℚ) B) d y),
      D.IsUniversal ∧ IsProper y := by
  letI : IsProper (cToBase ℚ) := source_proper
  letI : SmoothOfRelativeDimension 1 (cToBase ℚ) := source_smooth
  letI := smoothOfRelativeDimension_isStableUnderBaseChange (n:=1)
  obtain ⟨Y,y,D,hD⟩ := actual_ringBase_exists_isUniversal B d
  exact ⟨Y,y,D,hD,hD.isProper⟩

/-- Once an actual universal divisor is chosen, its proper structural map
supplies the exact finite-type gate for the ANY-field/ANY-cover H1 open.
The module is arbitrary invertible data on the actual pulled-back curve. -/
theorem universal_divisor_H1_open
    {R:Type} [CommRing R] [IsNoetherianRing R] {C:Scheme}
    (c:C⟶Spec (.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε:SchemeHomOver (𝟙 _) c)
    (hF:∀m0:ℕ,∃F:SmoothProperCurve.FiniteMapData c ε,m0≤F.m)
    {Y:Scheme}(y:Y⟶Spec (.of R)){d:ℕ}(D:RelEffCartierDiv c d y)(hD:D.IsUniversal)
    (M:(pullback c y).Modules)(hM:Scheme.Modules.IsInvertible M) :
    IsProper y ∧ ∃U:Y.Opens,∀(k:Type)[Field k](s:Spec (.of k)⟶Y),
      Set.range ⇑s⊆(U:Set Y) ↔ ∀(V:(pullback (pullback.snd c y) s).TwoAffineOpenCover),
      Subsingleton (V.sectionsOf (fibreAt c y s) (fibreModule c y s M)).H1 := by
  letI : IsProper y := hD.isProper
  exact ⟨inferInstance,
    AlgebraicGeometry.RelPicard.exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε hF y M hM⟩

#print axioms actual_ringBase_proper_universal_divisor
#print axioms universal_divisor_H1_open
end FourCorner.ActualOpenChartCompletion
