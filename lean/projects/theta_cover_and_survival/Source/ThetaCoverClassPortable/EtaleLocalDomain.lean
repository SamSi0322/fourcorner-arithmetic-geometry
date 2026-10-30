import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Polynomial
namespace StandardEtaleLocalDomain
variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

theorem exists_prime_factor_at (f : R[X]) (q : Ideal R[X]) [q.IsPrime]
    (hf : f ∈ q) (hdf : derivative f ∉ q) :
    ∃ p h : R[X], Prime p ∧ p ∈ q ∧ f = p * h ∧ h ∉ q := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hdf (by simp)).elim
  | h₂ f hu => exact ((inferInstance : q.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem q hf hu)).elim
  | h₃ a p ha hp ih =>
    by_cases hpq : p ∈ q
    · refine ⟨p, a, hp, hpq, rfl, ?_⟩
      intro haq
      apply hdf
      rw [derivative_mul]
      exact q.add_mem (q.mul_mem_left _ haq) (q.mul_mem_right _ hpq)
    · have haq : a ∈ q := ((inferInstance : q.IsPrime).mem_or_mem hf).resolve_left hpq
      have hda : derivative a ∉ q := by
        intro hda
        apply hdf
        rw [derivative_mul]
        exact q.add_mem (q.mul_mem_left _ haq) (q.mul_mem_left _ hda)
      obtain ⟨r, h, hr, hrq, heq, hh⟩ := ih haq hda
      refine ⟨r, p * h, hr, hrq, ?_, ?_⟩
      · rw [heq]
        ac_rfl
      · exact fun hph => ((inferInstance : q.IsPrime).mem_or_mem hph).elim hpq hh

theorem isDomain_away_factor (P : StandardEtalePair R) (p h : R[X])
    (hp : Prime p) (heq : P.f = p * h) (hgh : ¬ p ∣ P.g * h) :
    IsDomain (Localization.Away (aeval P.X h)) := by
  letI : IsDomain (AdjoinRoot p) := AdjoinRoot.isDomain_of_prime hp
  let D := Localization.Away (AdjoinRoot.mk p (P.g * h))
  let B := Localization.Away (aeval P.X h)
  letI : IsDomain D := Localization.Away.isDomain (AdjoinRoot.mk_eq_zero.not.mpr hgh)
  let xD : D := algebraMap (AdjoinRoot p) D (AdjoinRoot.root p)
  let xB : B := algebraMap P.Ring B P.X
  have hdprod : IsUnit (aeval xD (P.g * h)) := by
    simpa only [xD, aeval_algebraMap_apply, AdjoinRoot.aeval_eq] using
      IsLocalization.Away.algebraMap_isUnit (AdjoinRoot.mk p (P.g * h))
  have hdprod' : IsUnit (aeval xD P.g * aeval xD h) := by
    simpa only [map_mul] using hdprod
  have hD : P.HasMap xD := by
    refine ⟨?_, isUnit_of_mul_isUnit_left hdprod'⟩
    simp [heq, xD, aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hB : P.HasMap xB := P.hasMap_X.map (Algebra.algHom R P.Ring B)
  have hBh : IsUnit (aeval xB h) := by
    simpa only [xB, aeval_algebraMap_apply] using
      IsLocalization.Away.algebraMap_isUnit (aeval P.X h)
  have hBp : aeval xB p = 0 := hBh.mul_left_eq_zero.mp (by simpa [heq] using hB.1)
  let a : AdjoinRoot p →ₐ[R] B := AdjoinRoot.liftAlgHom p (Algebra.ofId R B) xB hBp
  have ha : IsUnit (a (AdjoinRoot.mk p (P.g * h))) := by
    change IsUnit (aeval xB (P.g * h))
    rw [map_mul]
    exact hB.2.mul hBh
  let k : D →ₐ[R] B := IsLocalization.Away.liftAlgHom (AdjoinRoot.mk p (P.g * h)) ha
  let ell : P.Ring →ₐ[R] D := P.lift xD hD
  have hell : IsUnit (ell (aeval P.X h)) := by
    simpa only [← aeval_algHom_apply, ell, StandardEtalePair.lift_X] using
      isUnit_of_mul_isUnit_right hdprod'
  let j : B →ₐ[R] D := IsLocalization.Away.liftAlgHom (aeval P.X h) hell
  have hkj : k.comp j = AlgHom.id R B := by
    apply IsLocalization.algHom_ext (Submonoid.powers (aeval P.X h))
    apply P.hom_ext
    simp only [AlgHom.comp_apply, Algebra.algHom_apply, AlgHom.id_apply]
    change k (j (algebraMap P.Ring B P.X)) = algebraMap P.Ring B P.X
    simp only [j, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
      ell, StandardEtalePair.lift_X]
    change k ((P.lift xD hD) P.X) = xB
    rw [P.lift_X xD hD]
    change k (algebraMap (AdjoinRoot p) D (AdjoinRoot.root p)) = xB
    simp [k, a, AdjoinRoot.liftAlgHom_root]
  exact Function.Injective.isDomain j (fun x y he => by
    have hz := congrArg k he
    change (k.comp j) x = (k.comp j) y at hz
    simpa only [hkj, AlgHom.id_apply] using hz)

theorem pair_exists_away_isDomain (P : StandardEtalePair R) (q : Ideal P.Ring) [q.IsPrime] :
    ∃ s : P.Ring, s ∉ q ∧ IsDomain (Localization.Away s) := by
  let Q : Ideal R[X] := q.comap (aeval P.X).toRingHom
  letI : Q.IsPrime := Ideal.IsPrime.comap _
  have hf : P.f ∈ Q := by
    change aeval P.X P.f ∈ q
    rw [P.hasMap_X.1]
    exact q.zero_mem
  have hdf : derivative P.f ∉ Q := by
    exact q.notMem_of_isUnit (P.hasMap_X.isUnit_derivative_f)
  obtain ⟨p, h, hp, hpQ, heq, hhQ⟩ := exists_prime_factor_at P.f Q hf hdf
  refine ⟨aeval P.X h, hhQ, isDomain_away_factor P p h hp heq ?_⟩
  rintro ⟨k, hk⟩
  have hgh : P.g * h ∈ Q := hk ▸ Q.mul_mem_right k hpQ
  have hgQ : P.g ∉ Q := q.notMem_of_isUnit P.hasMap_X.2
  exact ((inferInstance : Q.IsPrime).mem_or_mem hgh).elim hgQ hhQ

variable {S : Type*} [CommRing S] [Algebra R S]
theorem exists_away_isDomain [Algebra.IsStandardEtale R S] (q : Ideal S) [q.IsPrime] :
    ∃ s : S, s ∉ q ∧ IsDomain (Localization.Away s) := by
  let P : StandardEtalePresentation R S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let e : S ≃ₐ[R] P.Ring := P.equivRing
  let Q : Ideal P.Ring := q.comap e.symm.toRingHom
  letI : Q.IsPrime := Ideal.IsPrime.comap _
  obtain ⟨s, hs, hD⟩ := pair_exists_away_isDomain P.P Q
  refine ⟨e.symm s, hs, ?_⟩
  letI := hD
  let ee : Localization.Away (e.symm s) ≃+* Localization.Away s :=
    IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers (e.symm s)) (T := Submonoid.powers s)
      (Localization.Away (e.symm s)) (Localization.Away s) e.toRingEquiv (by simp [Submonoid.map_powers])
  exact Function.Injective.isDomain ee ee.injective

end StandardEtaleLocalDomain
