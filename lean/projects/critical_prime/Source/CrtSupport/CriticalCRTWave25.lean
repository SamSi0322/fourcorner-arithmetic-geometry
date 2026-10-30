import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
namespace FourCorner.CriticalCRTWave25

/-- A denominator progression preserving any already fixed congruence class. -/
def denominator (a m k : ℕ) : ℕ := a + m * k

theorem denominator_unbounded (a m B : ℕ) (hm : 0 < m) :
    B < denominator a m (B + 1) := by
  unfold denominator
  nlinarith

theorem denominator_injective (a m : ℕ) (hm : 0 < m) :
    Function.Injective (denominator a m) := by
  intro j k h
  unfold denominator at h
  nlinarith

/-- Coprimality with the coordinate gcd survives an arbitrary progression
whose step is divisible by that gcd. -/
theorem denominator_primitive (X Y a m k : ℕ)
    (ha : Nat.Coprime (Nat.gcd X Y) a) (hm : Nat.gcd X Y ∣ m) :
    Nat.gcd (Nat.gcd X Y) (denominator a m k) = 1 := by
  obtain ⟨t, rfl⟩ := hm
  simpa [denominator, Nat.mul_assoc] using
    (Nat.coprime_add_mul_left_right (Nat.gcd X Y) a (t * k)).2 ha

/-- With positive X, distinct positive denominators give distinct actual
rational first coordinates. -/
theorem rational_coordinate_injective (X a m : ℕ) (hX : 0 < X)
    (ha : 0 < a) (hm : 0 < m) :
    Function.Injective (fun k : ℕ => (X : ℚ) / denominator a m k) := by
  intro j k h
  have hp (k : ℕ) : 0 < denominator a m k := by
    unfold denominator
    omega
  have hj : (denominator a m j : ℚ) ≠ 0 := by exact_mod_cast (hp j).ne'
  have hk : (denominator a m k : ℚ) ≠ 0 := by exact_mod_cast (hp k).ne'
  have hXq : (X : ℚ) ≠ 0 := by exact_mod_cast hX.ne'
  have he : (denominator a m j : ℚ) = denominator a m k := by
    apply (mul_left_cancel₀ hXq)
    exact (div_eq_div_iff hj hk).mp h |>.symm
  apply denominator_injective a m hm
  exact_mod_cast he

/-- Any primitive congruence progression contains an interior primitive
triple above every bound. The bound is unrestricted. -/
theorem primitive_interior_above (X Y a m B : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hm : 0 < m)
    (ha : Nat.Coprime (Nat.gcd X Y) a) (hdiv : Nat.gcd X Y ∣ m) :
    ∃ L : ℕ, B < L ∧ 0 < X ∧ 0 < Y ∧ X < L ∧ Y < L ∧
      Nat.gcd (Nat.gcd X Y) L = 1 ∧ ∃ k, L = denominator a m k := by
  let k := B + X + Y + 1
  refine ⟨denominator a m k, ?_, hX, hY, ?_, ?_,
    denominator_primitive X Y a m k ha hdiv, k, rfl⟩
  all_goals unfold denominator k; nlinarith

/-- A single additional residue digit enforces exact denominator depth. -/
theorem exact_depth_of_modEq {p L e : ℕ} [Fact p.Prime]
    (hL : L ≠ 0) (h : Nat.ModEq (p^(e+1)) L (p^e)) :
    padicValNat p L = e := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hd : p^e ∣ L := (h.dvd_iff (Nat.pow_dvd_pow p (by omega))).mpr (dvd_refl _)
  have hn : ¬p^(e+1) ∣ L := by
    intro hbad
    have hb := (h.dvd_iff (dvd_refl _)).mp hbad
    have := (Nat.pow_dvd_pow_iff_le_right hp).mp hb
    omega
  have hlo := (padicValNat_dvd_iff_le hL).mp hd
  have hhi : ¬ e+1 ≤ padicValNat p L := by
    intro hbad
    exact hn ((padicValNat_dvd_iff_le hL).mpr hbad)
  omega

/-- Finite CRT, with an additional coprimality constraint, gives an
unbounded progression of primitive interior triples and infinitely many
actual rational coordinates. There is no restriction on the moduli sizes. -/
theorem simultaneous_primitive_progression {ι : Type*} (t : Finset ι)
    (r n : ι → ℕ) (X Y : ℕ) (hX : 0 < X) (hY : 0 < Y)
    (hn : ∀ i ∈ t, n i ≠ 0)
    (hpair : Set.Pairwise (↑t : Set ι) (Function.onFun Nat.Coprime n))
    (hcop : ∀ i ∈ t, Nat.Coprime (n i) (Nat.gcd X Y)) :
    ∃ a m : ℕ, 0 < a ∧ 0 < m ∧
      (∀ k : ℕ, X < denominator a m k ∧ Y < denominator a m k ∧
        Nat.gcd (Nat.gcd X Y) (denominator a m k) = 1 ∧
        ∀ i ∈ t, Nat.ModEq (n i) (denominator a m k) (r i)) ∧
      Function.Injective (fun k : ℕ => (X : ℚ) / denominator a m k) := by
  classical
  let N := ∏ i ∈ t, n i
  have hN : N ≠ 0 := Finset.prod_ne_zero_iff.mpr hn
  have hD : 0 < Nat.gcd X Y := Nat.gcd_pos_of_pos_left Y hX
  have hc : Nat.Coprime N (Nat.gcd X Y) := Nat.coprime_prod_left_iff.mpr hcop
  let c := Nat.chineseRemainderOfFinset r n t hn hpair
  let d := Nat.chineseRemainder hc c 1
  let m := N * Nat.gcd X Y
  have hm : 0 < m := Nat.mul_pos (Nat.pos_of_ne_zero hN) hD
  have hmd : Nat.gcd X Y ∣ m := dvd_mul_left _ _
  have hda : Nat.Coprime (Nat.gcd X Y) d := by
    have he := d.property.2.gcd_eq
    exact Nat.coprime_comm.mpr (by simpa [Nat.Coprime] using he)
  have hlocal (k : ℕ) (i : ι) (hi : i ∈ t) :
      Nat.ModEq (n i) (denominator d m k) (r i) := by
    have hni : n i ∣ N := Finset.dvd_prod_of_mem n hi
    have hnmi : n i ∣ m := dvd_mul_of_dvd_left hni _
    have hstep : Nat.ModEq (n i) (denominator d m k) d := by
      unfold denominator Nat.ModEq
      simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hnmi]
    exact hstep.trans ((d.property.1.of_dvd hni).trans (c.property i hi))
  let a := denominator d m (X + Y + 1)
  have ha : 0 < a := by unfold a denominator; nlinarith
  refine ⟨a, m, ha, hm, ?_, rational_coordinate_injective X a m hX ha hm⟩
  intro k
  have he : denominator a m k = denominator d m (X + Y + 1 + k) := by
    unfold a denominator
    ring
  rw [he]
  refine ⟨?_, ?_, denominator_primitive X Y d m _ hda hmd, hlocal _⟩
  all_goals unfold denominator; nlinarith

/-- The exact finite-prime denominator clause of the critical CRT
construction, including primitive triples and distinct rational coordinates. -/
theorem finite_prime_exact_depth_progression (P : Finset ℕ) (s : ℕ → ℕ)
    (X Y : ℕ) (hX : 0 < X) (hY : 0 < Y)
    (hp : ∀ p ∈ P, p.Prime) (hu : ∀ p ∈ P, ¬p ∣ X) :
    ∃ a m : ℕ, 0 < a ∧ 0 < m ∧
      (∀ k : ℕ, X < denominator a m k ∧ Y < denominator a m k ∧
        Nat.gcd (Nat.gcd X Y) (denominator a m k) = 1 ∧
        ∀ p ∈ P, padicValNat p (denominator a m k) = 2*s p) ∧
      Function.Injective (fun k : ℕ => (X : ℚ) / denominator a m k) := by
  have hn : ∀ p ∈ P, p^(2*s p+1) ≠ 0 := by
    intro p hpm
    exact pow_ne_zero _ (hp p hpm).ne_zero
  have hpair : Set.Pairwise (↑P : Set ℕ)
      (Function.onFun Nat.Coprime (fun p => p^(2*s p+1))) := by
    intro p hpP q hqP hpq
    exact ((Nat.coprime_primes (hp p hpP) (hp q hqP)).mpr hpq).pow _ _
  have hcop : ∀ p ∈ P, Nat.Coprime (p^(2*s p+1)) (Nat.gcd X Y) := by
    intro p hpP
    exact ((hp p hpP).coprime_iff_not_dvd.mpr (hu p hpP)).of_dvd_right
      (Nat.gcd_dvd_left X Y) |>.pow_left _
  obtain ⟨a,m,ha,hm,hfam,hinj⟩ := simultaneous_primitive_progression
    P (fun p => p^(2*s p)) (fun p => p^(2*s p+1)) X Y hX hY hn hpair hcop
  refine ⟨a,m,ha,hm,?_,hinj⟩
  intro k
  obtain ⟨h1,h2,h3,h4⟩ := hfam k
  refine ⟨h1,h2,h3,?_⟩
  intro p hpP
  let : Fact p.Prime := ⟨hp p hpP⟩
  exact exact_depth_of_modEq (by unfold denominator; omega) (h4 p hpP)

/-- The natural-coordinate construction embeds into actual integer
triples; its integer triple range is infinite. -/
theorem integer_progression_triples_infinite (X Y a m : ℕ) (hm : 0 < m) :
    (Set.range (fun k : ℕ => ((X : ℤ), (Y : ℤ), (denominator a m k : ℤ)))).Infinite := by
  apply Set.infinite_range_of_injective
  intro j k h
  apply denominator_injective a m hm
  have he := congrArg (fun z : ℤ × ℤ × ℤ => z.2.2) h
  change (denominator a m j : ℤ) = (denominator a m k : ℤ) at he
  exact_mod_cast he

/-- Coprimality and the strict real interval transport to the actual integer
triple without changing any coordinate. -/
theorem integer_primitive_interior (X Y L : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hXL : X < L) (hYL : Y < L)
    (hg : Nat.gcd (Nat.gcd X Y) L = 1) :
    (0 : ℤ) < X ∧ (0 : ℤ) < Y ∧ (X : ℤ) < L ∧ (Y : ℤ) < L ∧
      Int.gcd (Int.gcd (X : ℤ) Y : ℤ) L = 1 := by
  refine ⟨by exact_mod_cast hX, by exact_mod_cast hY,
    by exact_mod_cast hXL, by exact_mod_cast hYL, ?_⟩
  simpa [Int.gcd_def] using hg

end FourCorner.CriticalCRTWave25
#print axioms FourCorner.CriticalCRTWave25.primitive_interior_above
#print axioms FourCorner.CriticalCRTWave25.rational_coordinate_injective

#print axioms FourCorner.CriticalCRTWave25.simultaneous_primitive_progression

#print axioms FourCorner.CriticalCRTWave25.exact_depth_of_modEq

#print axioms FourCorner.CriticalCRTWave25.finite_prime_exact_depth_progression

#print axioms FourCorner.CriticalCRTWave25.integer_progression_triples_infinite
#print axioms FourCorner.CriticalCRTWave25.integer_primitive_interior
