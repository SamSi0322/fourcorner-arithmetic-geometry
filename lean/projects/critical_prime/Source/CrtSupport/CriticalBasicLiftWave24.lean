import FourCorner.CommonRootTwoLift
import Mathlib.NumberTheory.Padics.PadicNumbers

set_option autoImplicit false
namespace FourCorner

/-- Hensel supplies integer roots of minus one modulo every prime power. -/
theorem critical_minus_one_mod_pow {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hi : IsSquare (-1 : ZMod p)) (n : ℕ) :
    ∃ r : ℤ, (p : ℤ)^n ∣ r^2+1 := by
  have hneg : ¬ (p : ℤ) ∣ (-1 : ℤ) := by
    intro hd
    have hd' : (p : ℤ) ∣ 1 := dvd_neg.mp hd
    have hp1 : p ∣ 1 := by exact_mod_cast hd'
    exact (Fact.out : p.Prime).not_dvd_one hp1
  have hres : PadicInt.toZMod (-1 : ℤ_[p]) ≠ 0 := by simp
  obtain ⟨z,hz⟩ := padicInt_isSquare_of_isSquare_residue_unit hp (-1 : ℤ_[p])
    hres (by simpa using hi)
  let v : ZMod (p^n) := PadicInt.toZModPow n z
  refine ⟨v.val, ?_⟩
  have hm := congrArg (PadicInt.toZModPow n) hz
  have hv : v*v = -1 := by
    simpa only [map_neg,map_one,map_mul] using hm.symm
  have hr : ((v.val : ℤ)^2+1 : ZMod (p^n)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination hv
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd ((v.val : ℤ)^2+1) (p^n)).mp (by simpa only [Int.cast_add, Int.cast_pow, Int.cast_one, Int.cast_natCast] using hr)
  simpa only [Nat.cast_pow] using hd

/-- The lifted root can retain either prescribed residue root. -/
theorem critical_minus_one_mod_pow_prescribed {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (i : ZMod p) (hi : i^2 = -1)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℤ, (p : ℤ)^n ∣ r^2+1 ∧ (r : ZMod p) = i := by
  obtain ⟨r,hr⟩ := critical_minus_one_mod_pow hp (by
    refine ⟨i, ?_⟩
    simpa [pow_two] using hi.symm) n
  have hpd : (p : ℤ) ∣ r^2+1 :=
    dvd_trans (dvd_pow_self _ (by omega : n ≠ 0)) hr
  have hrmod : (r : ZMod p)^2 = -1 := by
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (r^2+1) p).mpr hpd
    push_cast at hz
    linear_combination hz
  rcases eq_or_eq_neg_of_sq_eq_sq (r : ZMod p) i (hrmod.trans hi.symm) with he | he
  · exact ⟨r,hr,he⟩
  · refine ⟨-r, ?_, ?_⟩
    · simpa using hr
    · push_cast
      rw [he, neg_neg]

/-- Integral coordinates realizing the prescribed critical norm residue at
an unrestricted positive depth; this is an exact prime-power congruence. -/
theorem critical_local_coordinates {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (s : ℕ) (hs : 1 ≤ s)
    (i b c : ZMod p) (hi : i^2 = -1) (hb : b ≠ 0) :
    ∃ X Y q : ℤ, ¬ (p : ℤ) ∣ X ∧ ¬ (p : ℤ) ∣ Y ∧
      X^2+Y^2 = (p : ℤ)^(2*s)*q ∧ (q : ZMod p) = c ∧
      -2*(X : ZMod p) = b ∧ -2*(Y : ZMod p) = i*b := by
  have h2 : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using hp)
  have hi0 : i ≠ 0 := by intro he; simp [he] at hi
  let x : ZMod p := -b/2
  let X : ℤ := x.val
  have hX : (X : ZMod p) = x := by simp [X]
  have hx : x ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) h2
  let z0 : ZMod p := c/(2*i*x)
  let z : ℤ := z0.val
  have hz : (z : ZMod p) = z0 := by simp [z]
  obtain ⟨r,hr,hri⟩ := critical_minus_one_mod_pow_prescribed hp i hi (2*s+1) (by omega)
  obtain ⟨d,hd⟩ := hr
  let N : ℤ := (p : ℤ)^(2*s)
  have hN : (N : ZMod p) = 0 := by
    dsimp [N]
    push_cast
    rw [ZMod.natCast_self]
    exact zero_pow (by omega)
  let Y : ℤ := r*X+N*z
  let q : ℤ := (p : ℤ)*d*X^2+2*r*X*z+N*z^2
  have hY : (Y : ZMod p) = i*x := by
    simp only [Y,Int.cast_add,Int.cast_mul,hri,hX,hN,hz,zero_mul,add_zero]
  have hq : (q : ZMod p) = c := by
    simp only [q,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,
      Int.cast_natCast,ZMod.natCast_self,hri,hX,hN,hz,zero_mul,zero_add,add_zero]
    dsimp [z0]
    field_simp
  refine ⟨X,Y,q,?_,?_,?_,hq,?_,?_⟩
  · intro hd
    exact hx (hX ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd X p).mpr hd)
  · intro hd
    exact (mul_ne_zero hi0 hx) (hY ▸ (ZMod.intCast_zmod_eq_zero_iff_dvd Y p).mpr hd)
  · dsimp [Y,q,N]
    rw [pow_succ] at hd
    linear_combination X^2*hd
  · rw [hX]
    dsimp [x]
    field_simp
  · rw [hY]
    dsimp [x]
    field_simp

/-- Any prescribed nonzero square unit residue yields roots at every exact
scaled depth in the actual completed field. -/
theorem critical_scaled_square_root {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (s : ℕ) (q : ℤ)
    (hu : ¬ (p : ℤ) ∣ q) (hs : IsSquare (q : ZMod p)) :
    ∃ a : ℚ_[p], a ^ 2 = (p : ℚ_[p]) ^ (2*s) * q ∧
      a.valuation = (s : ℤ) := by
  obtain ⟨u, huq⟩ := padic_isSquare_of_isSquare_zmod_unit hp q hu hs
  have hq : (q : ℚ_[p]) ≠ 0 := by
    have hqi : q ≠ 0 := fun h => hu (h ▸ dvd_zero _)
    exact_mod_cast hqi
  have hune : u ≠ 0 := by
    intro he
    apply hq
    rw [huq, he, mul_zero]
  have huv : u.valuation = 0 := by
    have hv := congrArg (fun x : ℚ_[p] => x.valuation) huq
    rw [Padic.valuation_intCast, padicValInt.eq_zero_of_not_dvd hu,
      Padic.valuation_mul hune hune] at hv
    omega
  have hpn : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨(p : ℚ_[p]) ^ s * u, ?_, ?_⟩
  · rw [mul_pow, pow_two u, ← huq]
    congr 1
    rw [← pow_mul]
    congr 1
    omega
  · rw [Padic.valuation_mul (pow_ne_zero _ hpn) hune,
      Padic.valuation_pow, Padic.valuation_p, huv]
    simp

/-- The lift applies simultaneously to all four original integer radicands;
its quantifier on depth is unrestricted. -/
theorem critical_four_scaled_roots {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (s : ℕ) (Q q : Fin 4 → ℤ)
    (hfac : ∀ j, Q j = (p : ℤ) ^ (2*s) * q j)
    (hu : ∀ j, ¬ (p : ℤ) ∣ q j)
    (hs : ∀ j, IsSquare (q j : ZMod p)) :
    ∃ A : Fin 4 → ℚ_[p], ∀ j,
      A j ^ 2 = (Q j : ℚ_[p]) ∧ (A j).valuation = (s : ℤ) := by
  have hall : ∀ j : Fin 4, ∃ a : ℚ_[p],
      a ^ 2 = (Q j : ℚ_[p]) ∧ a.valuation = (s : ℤ) := by
    intro j
    obtain ⟨a, ha, hv⟩ := critical_scaled_square_root hp s (q j) (hu j) (hs j)
    refine ⟨a, ?_, hv⟩
    rw [hfac j]
    push_cast
    exact ha
  exact Classical.skolem.mp hall
/-- Actual four corner radicands, in the paper's ordered coordinates. -/
def criticalRadicands (X Y L : ℤ) : Fin 4 → ℤ :=
  ![X^2+Y^2, (X-L)^2+Y^2, X^2+(Y-L)^2, (X-L)^2+(Y-L)^2]

/-- A single exact norm congruence and the prescribed residue shifts suffice
for all four original radicands at the same integer point and arbitrary depth. -/
theorem critical_coordinate_lift {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (s : ℕ) (hspos : 1 ≤ s) (X Y M q : ℤ)
    (i b c : ZMod p)
    (hnorm : X^2 + Y^2 = (p : ℤ)^(2*s)*q)
    (hM : (M : ZMod p) = 1) (hq : (q : ZMod p) = c)
    (hX : -2*(X : ZMod p) = b) (hY : -2*(Y : ZMod p) = i*b)
    (hu : c ≠ 0 ∧ c+b ≠ 0 ∧ c+i*b ≠ 0 ∧ c+(1+i)*b ≠ 0)
    (hsq : IsSquare c ∧ IsSquare (c+b) ∧ IsSquare (c+i*b) ∧
      IsSquare (c+(1+i)*b)) :
    ∃ A : Fin 4 → ℚ_[p], ∀ j,
      A j ^ 2 = (criticalRadicands X Y ((p : ℤ)^(2*s)*M) j : ℚ_[p]) ∧
      (A j).valuation = (s : ℤ) := by
  let N : ℤ := (p : ℤ)^(2*s)
  let qs : Fin 4 → ℤ :=
    ![q, q-2*M*X+N*M^2, q-2*M*Y+N*M^2,
      q-2*M*X-2*M*Y+2*N*M^2]
  have hN : (N : ZMod p) = 0 := by
    dsimp [N]
    push_cast
    rw [ZMod.natCast_self]
    exact zero_pow (by omega)
  have hres : ∀ j : Fin 4, (qs j : ZMod p) =
      (![c,c+b,c+i*b,c+(1+i)*b] : Fin 4 → ZMod p) j := by
    intro j
    fin_cases j <;> simp [qs] <;> push_cast <;>
      simp only [hM,hq,hN,one_mul,zero_mul,add_zero] <;>
      first | linear_combination hX | linear_combination hY | linear_combination hX + hY
  apply critical_four_scaled_roots hp s _ qs
  · intro j
    fin_cases j <;> simp [criticalRadicands, qs] <;>
      dsimp [N] at * <;> linear_combination hnorm
  · intro j
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (qs j) p).mpr hd
    rw [hres j] at hz
    fin_cases j <;> simp at hz <;> tauto
  · intro j
    rw [hres j]
    fin_cases j <;> simp <;> tauto

end FourCorner
#print axioms FourCorner.critical_scaled_square_root
#print axioms FourCorner.critical_four_scaled_roots

#print axioms FourCorner.critical_coordinate_lift

#print axioms FourCorner.critical_minus_one_mod_pow

#print axioms FourCorner.critical_minus_one_mod_pow_prescribed

#print axioms FourCorner.critical_local_coordinates
