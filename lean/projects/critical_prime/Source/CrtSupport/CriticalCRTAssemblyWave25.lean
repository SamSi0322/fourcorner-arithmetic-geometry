import CrtSupport.CriticalCRTPersistenceWave25
import CrtSupport.CriticalCongruenceWave24
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
namespace FourCorner.CriticalCRTWave25

/-- Positive integer representatives simultaneously realizing arbitrarily
high and unrelated local integer congruences. -/
theorem positive_integer_crt {ι : Type*} (t : Finset ι) (r : ι → ℤ) (n : ι → ℕ)
    (hn : ∀ i ∈ t, n i ≠ 0)
    (hpair : Set.Pairwise (↑t : Set ι) (Function.onFun Nat.Coprime n)) :
    ∃ X : ℕ, 0 < X ∧ ∀ i ∈ t, (n i : ℤ) ∣ (X : ℤ)-r i := by
  classical
  let a : ι → ℕ := fun i => (r i % (n i : ℤ)).toNat
  let c := Nat.chineseRemainderOfFinset a n t hn hpair
  let N := ∏ i ∈ t, n i
  have hN : 0 < N := Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr hn)
  refine ⟨c+N, by omega, ?_⟩
  intro i hi
  have hd : n i ∣ N := Finset.dvd_prod_of_mem n hi
  have hc : Nat.ModEq (n i) (c+N) (a i) := by
    apply Nat.ModEq.trans _ (c.property i hi)
    unfold Nat.ModEq
    simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
  have hz : (n i : ℤ) ≠ 0 := by exact_mod_cast hn i hi
  have ha : (a i : ℤ) = r i % (n i : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hz)
  have hci := (Int.natCast_modEq_iff.mpr hc)
  rw [ha] at hci
  simpa only [neg_sub] using (dvd_neg.mpr (Int.modEq_iff_dvd.mp (hci.trans (Int.mod_modEq _ _))))

/-- Local finite-depth integer data globalizes to infinitely many primitive
interior triples with actual simultaneous completed-field roots. -/
theorem simultaneous_from_local_data (P : Finset ℕ) (s : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, p ≠ 2)
    (hdata : ∀ p ∈ P, ∃ x y : ℤ, ∃ q : Fin 4 → ℤ,
      ¬(p : ℤ) ∣ x ∧
      (∀ j, criticalRadicands x y ((p : ℤ)^(2*s p)) j = (p : ℤ)^(2*s p)*q j) ∧
      (∀ j, ¬(p : ℤ) ∣ q j) ∧ (∀ j, IsSquare (q j : ZMod p))) :
    ∃ X Y a m : ℕ, 0 < X ∧ 0 < Y ∧ 0 < a ∧ 0 < m ∧
      (∀ k : ℕ, X < denominator a m k ∧ Y < denominator a m k ∧
        Nat.gcd (Nat.gcd X Y) (denominator a m k) = 1 ∧
        ∀ p (h : p ∈ P),
          let : Fact p.Prime := ⟨hp p h⟩
          padicValNat p (denominator a m k) = 2*s p ∧
          ∃ A : Fin 4 → ℚ_[p], ∀ j,
            A j ^ 2 = (criticalRadicands X Y (denominator a m k) j : ℚ_[p]) ∧
            (A j).valuation = (s p : ℤ)) ∧
      Function.Injective (fun k : ℕ => ((X : ℚ) / denominator a m k,
        (Y : ℚ) / denominator a m k)) := by
  classical
  have hex : ∀ p : ℕ, ∃ x y : ℤ, ∃ q : Fin 4 → ℤ,
      p ∈ P → ¬(p : ℤ) ∣ x ∧
      (∀ j, criticalRadicands x y ((p : ℤ)^(2*s p)) j = (p : ℤ)^(2*s p)*q j) ∧
      (∀ j, ¬(p : ℤ) ∣ q j) ∧ (∀ j, IsSquare (q j : ZMod p)) := by
    intro p
    by_cases h : p ∈ P
    · obtain ⟨x,y,q,hd⟩ := hdata p h
      exact ⟨x,y,q,fun _ => hd⟩
    · exact ⟨0,0,0,fun hc => (h hc).elim⟩
  choose x y q hloc using hex
  let n : ℕ → ℕ := fun p => p^(2*s p+1)
  have hn : ∀ p ∈ P, n p ≠ 0 := by
    intro p h
    exact pow_ne_zero _ (hp p h).ne_zero
  have hpair : Set.Pairwise (↑P : Set ℕ) (Function.onFun Nat.Coprime n) := by
    intro p hpP r hrP hpr
    exact ((Nat.coprime_primes (hp p hpP) (hp r hrP)).mpr hpr).pow _ _
  obtain ⟨X,hX,hxc⟩ := positive_integer_crt P x n hn hpair
  obtain ⟨Y,hY,hyc⟩ := positive_integer_crt P y n hn hpair
  have hXu (p : ℕ) (h : p ∈ P) : ¬p ∣ X := by
    intro hd
    have hd' : (p : ℤ) ∣ (X : ℤ) := by exact_mod_cast hd
    have hn' : (p : ℤ) ∣ (n p : ℤ) := by
      dsimp [n]
      exact dvd_pow_self _ (by omega)
    have hdiff := dvd_trans hn' (hxc p h)
    apply (hloc p h).1
    simpa only [sub_sub_cancel] using dvd_sub hd' hdiff
  have hcop : ∀ p ∈ P, Nat.Coprime (n p) (Nat.gcd X Y) := by
    intro p h
    exact ((hp p h).coprime_iff_not_dvd.mpr (hXu p h)).of_dvd_right
      (Nat.gcd_dvd_left X Y) |>.pow_left _
  obtain ⟨a,m,ha,hm,hfam,hinj⟩ := simultaneous_primitive_progression
    P (fun p => p^(2*s p)) n X Y hX hY hn hpair hcop
  refine ⟨X,Y,a,m,hX,hY,ha,hm,?_,?_⟩
  · intro k
    obtain ⟨h1,h2,h3,h4⟩ := hfam k
    refine ⟨h1,h2,h3,?_⟩
    intro p h
    let : Fact p.Prime := ⟨hp p h⟩
    refine ⟨exact_depth_of_modEq (by unfold denominator; omega) (h4 p h), ?_⟩
    have hl : (p : ℤ)^(2*s p+1) ∣
        (denominator a m k : ℤ) - (p : ℤ)^(2*s p) := by
      have hd := (h4 p h).symm.dvd
      simpa [n] using hd
    have hx : (p : ℤ)^(2*s p+1) ∣ (X : ℤ)-x p := by simpa [n] using hxc p h
    have hy : (p : ℤ)^(2*s p+1) ∣ (Y : ℤ)-y p := by simpa [n] using hyc p h
    exact critical_roots_persist_all_coordinates (hodd p h) (s p)
      (x p) (y p) ((p : ℤ)^(2*s p)) X Y (denominator a m k) (q p)
      hx hy hl (hloc p h).2.1 (hloc p h).2.2.1 (hloc p h).2.2.2
  · intro j k h
    exact hinj (congrArg Prod.fst h)

/-- The full simultaneous CRT construction takes only residue patterns
as its local arithmetic input; all coordinate witnesses, actual roots and
unbounded primitive rational families are constructed in the proof. -/
theorem simultaneous_from_residue_patterns (P : Finset ℕ) (s : ℕ → ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hodd : ∀ p ∈ P, p ≠ 2)
    (hspos : ∀ p ∈ P, 1 ≤ s p)
    (hpat : ∀ p ∈ P, ∃ i b c : ZMod p, i^2 = -1 ∧ b ≠ 0 ∧
      (c ≠ 0 ∧ c+b ≠ 0 ∧ c+i*b ≠ 0 ∧ c+(1+i)*b ≠ 0) ∧
      (IsSquare c ∧ IsSquare (c+b) ∧ IsSquare (c+i*b) ∧ IsSquare (c+(1+i)*b))) :
    ∃ X Y a m : ℕ, 0 < X ∧ 0 < Y ∧ 0 < a ∧ 0 < m ∧
      (∀ k : ℕ, X < denominator a m k ∧ Y < denominator a m k ∧
        Nat.gcd (Nat.gcd X Y) (denominator a m k) = 1 ∧
        ∀ p (h : p ∈ P),
          letI : Fact p.Prime := ⟨hp p h⟩
          padicValNat p (denominator a m k) = 2*s p ∧
          ∃ A : Fin 4 → ℚ_[p], ∀ j,
            A j ^ 2 = (criticalRadicands X Y (denominator a m k) j : ℚ_[p]) ∧
            (A j).valuation = (s p : ℤ)) ∧
      Function.Injective (fun k : ℕ => ((X : ℚ) / denominator a m k,
        (Y : ℚ) / denominator a m k)) := by
  apply simultaneous_from_local_data P s hp hodd
  intro p h
  let : Fact p.Prime := ⟨hp p h⟩
  obtain ⟨i,b,c,hi,hb,hu,hsq⟩ := hpat p h
  obtain ⟨X,Y,q,hXu,_hYu,hfac,hunit,hsquares⟩ :=
    critical_local_radicand_data (hodd p h) (s p) (hspos p h) i b c hi hb hu hsq
  exact ⟨X,Y,q,hXu,hfac,hunit,hsquares⟩

end FourCorner.CriticalCRTWave25
#print axioms FourCorner.CriticalCRTWave25.positive_integer_crt

#print axioms FourCorner.CriticalCRTWave25.simultaneous_from_local_data

#print axioms FourCorner.CriticalCRTWave25.simultaneous_from_residue_patterns
