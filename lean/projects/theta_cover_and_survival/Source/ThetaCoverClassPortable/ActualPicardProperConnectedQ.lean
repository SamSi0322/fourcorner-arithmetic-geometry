import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_twistModule_and_nonempty_pullback_iso
import ThetaCoverClassPortable.ActualPicardSurjectivityQ
import ThetaCoverClassPortable.GlobalUniversalDivisor
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelPicard_isSeparated_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 12000000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicCurve
namespace FourCorner.ActualPicardProperties

/-- Actual universal effective divisors, their proper connected sum map, and
the genuine Poincare classification prove properness and geometric connectedness
of this represented object. The relative curve-affine input is explicit and is
already proved for every actual D/QQ algebra base change. -/
theorem proper_and_connected_of_represents_Q_and_curve_affines
    (R : Type) [CommRing R] [IsNoetherianRing R] (q : ℚ →+* R)
    {C : Scheme} (c : C ⟶ Spec (.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
    (hF : ∀ m0 : ℕ, ∃ F : SmoothProperCurve.FiniteMapData c ε, m0 ≤ F.m)
    (hcov : ∀ (V : (Spec (.of R)).affineOpens) (S : Finset C),
      (∀ x ∈ S, c x ∈ (V : (Spec (.of R)).Opens)) →
      ∃ U : C.Opens, IsAffineOpen U ∧ U ≤ c ⁻¹ᵁ (V : (Spec (.of R)).Opens) ∧ ∀ x ∈ S, x ∈ U)
    (g : ℕ)
    (hg : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of R))
      (L : Type) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ E : Divisor k L, (ell E : ℤ) - ell (Kc-E) = Divisor.degree E + 1 - g') → g'=g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] : IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  haveI : IsSeparated c := inferInstance
  haveI : GeometricallyConnected c := GeometricallyIrreducible.geometricallyConnected c
  obtain ⟨Y,y,E,hU⟩ := GlobalUniversalDivisor.exists_isUniversal
    (Spec.map (CommRingCat.ofHom q)) c hcov g
  haveI : IsProper y := hU.isProper
  haveI : GeometricallyConnected y := hU.geometricallyConnected
  let M : RigidifiedLineBundle c ε y :=
    ⟨E.twistModule c ε, (RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso c ε E).1,
      (RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso c ε E).2⟩
  have hM : (algEquivZeroCut c ε).P y M := fun k _ _ s =>
    RelEffCartierDiv.isAlgEquivZero_twistModule_fibre c ε E k s
  let aj : SchemeHomOver y D.toBase := h.classify y M hM
  have hclass : Nonempty ((h.poincare.pullbackAlong ⟨aj.1,aj.2⟩).L ≅ E.twistModule c ε) :=
    h.classify_spec y M hM
  haveI : Surjective aj.1 := P2MW.ActualPicardSurjectivityQ.solution R c ε q hF g hg D h hU aj.1 aj.2 hclass
  haveI : IsSeparated D.toBase :=
    AlgebraicGeometry.RelPicard.isSeparated_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData R c ε hF D h
  haveI : UniversallyClosed (aj.1 ≫ D.toBase) := by rw [aj.2];infer_instance
  haveI : UniversallyClosed D.toBase := UniversallyClosed.of_comp_surjective aj.1 D.toBase
  haveI : GeometricallyConnected (aj.1 ≫ D.toBase) := by rw [aj.2];infer_instance
  exact ⟨IsProper.mk,GeometricallyConnected.of_comp_of_surjective aj.1 D.toBase⟩
end FourCorner.ActualPicardProperties
