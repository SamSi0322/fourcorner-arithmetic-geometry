import QuadraticClosureEvaluation
import RationalPlacePoint
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

noncomputable section
open AlgebraicCurve IsDedekindDomain
namespace FourCorner.QuadraticPlaceExtension
open CommonRationalPlace CommonPostPointResidue
variable {F E : Type*} [Field F] [Field E] [CharZero F]
  [Algebra ℚ F] [Algebra ℚ E] [Algebra F E] [IsScalarTower ℚ F E]
  [FiniteDimensional F E]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A chosen square root in the residue of the original rational place gives
a genuine rational place of the quadratic field above that same place. -/
theorem exists_rational_place (w : Place ℚ F) (hw : w.IsRational)
    (B : PowerBasis F E) (hdim : B.dim = 2)
    (a : w.toValuationSubring) (ha : IsUnit a) (hns : ¬ IsSquare (a : F))
    (hz : B.gen^2 = algebraMap F E (a : F))
    (u : ℚ) (hu : u^2 = rationalEval w hw a) :
    ∃ v : Place ℚ E, v.restrict F = w ∧ ∃ hv : v.IsRational,
      ∃ z : v.toValuationSubring, (z : E) = B.gen ∧ rationalEval v hv z = u := by
  letI : FiniteDimensional F E := B.finite
  let A := w.toValuationSubring
  let C := Place.integralClosureAt E w
  have hzA : B.gen^2 = algebraMap A E a :=
    hz.trans (IsScalarTower.algebraMap_apply A F E a).symm
  let g : C →+* ℚ := QuadraticClosureEvaluation.evaluate B hdim a ha hns hzA
    (rationalEval w hw).toRingHom u hu
  have gbase (r : A) : g (algebraMap A C r) = rationalEval w hw r :=
    QuadraticClosureEvaluation.evaluate_algebraMap B hdim a ha hns hzA
      (rationalEval w hw).toRingHom u hu r
  have gsurj : Function.Surjective g := by
    intro q
    refine ⟨algebraMap A C (algebraMap ℚ A q),?_⟩
    rw [gbase]
    exact (rationalEval w hw).commutes q
  haveI : (RingHom.ker g).IsMaximal := RingHom.ker_isMaximal_of_surjective g gsurj
  have hker : RingHom.ker (rationalEval w hw).toRingHom = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _
      (RationalPlacePoint.valuation_eval_surjective w (rationalEval w hw).toRingHom))
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπeval : rationalEval w hw π = 0 := by
    change π ∈ RingHom.ker (rationalEval w hw).toRingHom
    rw [hker,IsLocalRing.mem_maximalIdeal,mem_nonunits_iff]
    exact hπ.not_isUnit
  have hne : RingHom.ker g ≠ ⊥ := by
    intro heq
    have hzero : algebraMap A C π = 0 := by
      apply Ideal.mem_bot.mp
      rw [← heq]
      change g (algebraMap A C π) = 0
      rw [gbase,hπeval]
    exact hπ.ne_zero (Place.algebraMap_integralClosureAt_injective (F' := E) w
      (hzero.trans (map_zero _).symm))
  let P : HeightOneSpectrum C := ⟨RingHom.ker g,inferInstance,hne⟩
  let v : Place ℚ E := Place.placeOfPrime (v := w) P
  letI : Algebra C v.toValuationSubring := by
    change Algebra C (HeightOneSpectrum.valuationSubringAtPrime E P)
    infer_instance
  letI : IsScalarTower C v.toValuationSubring E := by
    change IsScalarTower C (HeightOneSpectrum.valuationSubringAtPrime E P) E
    infer_instance
  haveI : IsLocalization P.asIdeal.primeCompl v.toValuationSubring := by
    change IsLocalization P.asIdeal.primeCompl (HeightOneSpectrum.valuationSubringAtPrime E P)
    exact Localization.subalgebra.isLocalization_ofField E P.asIdeal.primeCompl
      P.asIdeal.primeCompl_le_nonZeroDivisors
  have hg : ∀ s : P.asIdeal.primeCompl, IsUnit (g s) := by
    intro s
    apply isUnit_iff_ne_zero.mpr
    exact s.property
  let ev : v.toValuationSubring →+* ℚ := IsLocalization.lift (g := g) hg
  have hv : v.IsRational := CurveRationalPlace07.isRational_of_eval v ev
  let zC : C := ⟨B.gen,QuadraticClosureEvaluation.root_integral B a hzA⟩
  let z : v.toValuationSubring := algebraMap C v.toValuationSubring zC
  have hzcoe : (z : E) = B.gen := by
    change algebraMap v.toValuationSubring E (algebraMap C v.toValuationSubring zC) = B.gen
    rw [← IsScalarTower.algebraMap_apply C v.toValuationSubring E]
    rfl
  have hzev : ev z = u := by
    change (IsLocalization.lift hg) (algebraMap C v.toValuationSubring zC) = u
    rw [IsLocalization.lift_eq]
    exact QuadraticClosureEvaluation.evaluate_root B hdim a ha hns hzA
      (rationalEval w hw).toRingHom u hu
  refine ⟨v,Place.restrict_placeOfPrime P,hv,z,hzcoe,?_⟩
  change (rationalEval v hv).toRingHom z = u
  rw [← valuation_eval_eq v hv ev]
  exact hzev

end FourCorner.QuadraticPlaceExtension
#print axioms FourCorner.QuadraticPlaceExtension.exists_rational_place
