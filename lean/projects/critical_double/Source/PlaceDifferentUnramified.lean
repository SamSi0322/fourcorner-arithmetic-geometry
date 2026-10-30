import CriticalLiteralDouble
import Mathlib.RingTheory.Unramified.LocalRing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false
namespace FourCorner.PlaceDifferentUnramified
open AlgebraicCurve IsDedekindDomain
attribute [local instance] FractionRing.liftAlgebra
variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

/-- Unit different at an arbitrary actual place gives native formal
unramifiedness of its actual restriction map on valuation rings.
Every residue degree is retained; this is not restricted to rational places. -/
theorem restriction_formallyUnramified (w : Place K E)
    (hdiff : differentIdeal (w.restrict F).toValuationSubring
      (Place.integralClosureAt E (w.restrict F))=⊤) :
    (Place.restrictInclusion F w).FormallyUnramified := by
  let v := w.restrict F
  let A := v.toValuationSubring
  let B := Place.integralClosureAt E v
  let P := Place.fiberCenter E v rfl
  haveI : Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
    apply Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A F).symm.toRingEquiv
      (FractionRing.algEquiv B E).symm.toRingEquiv
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A F).symm
      (FractionRing.algEquiv B E).symm x
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) := Place.fiberCenter_liesOver rfl
  haveI : Algebra.IsUnramifiedAt A P.asIdeal := not_dvd_differentIdeal_iff.mp (by
    rw [hdiff]
    intro h
    exact P.isPrime.ne_top (top_unique (Ideal.le_of_dvd h)))
  let bToW : B →+* w.toValuationSubring :=
    (algebraMap B E).codRestrict w.toValuationSubring.toSubring
      (fun b => Place.forall_mem_of_restrict_eq (F':=E) (v:=v) (w:=w) rfl b)
  letI : Algebra B w.toValuationSubring := bToW.toAlgebra
  letI : Algebra A w.toValuationSubring := (Place.restrictInclusion F w).toAlgebra
  haveI : IsScalarTower A B w.toValuationSubring := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    apply Subtype.ext
    rfl
  let C := HeightOneSpectrum.valuationSubringAtPrime E P
  have hwval : w.toValuationSubring=HeightOneSpectrum.valuationSubringAtPrime E P :=
    Place.toValuationSubring_eq_of_restrict_eq rfl
  let eRing : C ≃+* w.toValuationSubring := {
    toFun := fun x => ⟨x.val,by rw [hwval]; exact x.property⟩
    invFun := fun x => ⟨x.val,by change x.val ∈ HeightOneSpectrum.valuationSubringAtPrime E P; rw [←hwval]; exact x.property⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    map_mul' := by intro a b; rfl
    map_add' := by intro a b; rfl }
  let e : C ≃ₐ[B] w.toValuationSubring := AlgEquiv.ofRingEquiv (f:=eRing) (by
    intro b
    apply Subtype.ext
    rfl)
  haveI : IsLocalization P.asIdeal.primeCompl w.toValuationSubring :=
    IsLocalization.isLocalization_of_algEquiv P.asIdeal.primeCompl e
  let eLoc : Localization.AtPrime P.asIdeal ≃ₐ[A] w.toValuationSubring :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)
      w.toValuationSubring).restrictScalars A
  haveI : Algebra.FormallyUnramified A w.toValuationSubring :=
    Algebra.FormallyUnramified.of_equiv (R:=A) (A:=Localization.AtPrime P.asIdeal) (B:=w.toValuationSubring) eLoc
  exact (RingHom.formallyUnramified_algebraMap).mpr inferInstance

#print axioms restriction_formallyUnramified
end FourCorner.PlaceDifferentUnramified
