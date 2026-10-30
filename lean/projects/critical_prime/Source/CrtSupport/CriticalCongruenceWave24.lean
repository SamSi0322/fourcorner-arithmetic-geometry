import CrtSupport.CriticalBasicLiftWave24
import Mathlib.Data.Int.ModEq

set_option autoImplicit false
namespace FourCorner

/-- Polynomial congruence for all four actual ordered radicands, with all
three coordinates allowed to vary. -/
theorem critical_radicands_congr (D X Y L X' Y' L' : ℤ)
    (hX : D ∣ X'-X) (hY : D ∣ Y'-Y) (hL : D ∣ L'-L) :
    ∀ j : Fin 4, D ∣ criticalRadicands X' Y' L' j - criticalRadicands X Y L j := by
  have hx := Int.modEq_iff_dvd.mpr hX
  have hy := Int.modEq_iff_dvd.mpr hY
  have hl := Int.modEq_iff_dvd.mpr hL
  intro j
  apply Int.modEq_iff_dvd.mp
  fin_cases j <;> simp only [criticalRadicands, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
  · exact (hx.pow 2).add (hy.pow 2)
  · exact ((hx.sub hl).pow 2).add (hy.pow 2)
  · exact (hx.pow 2).add ((hy.sub hl).pow 2)
  · exact ((hx.sub hl).pow 2).add ((hy.sub hl).pow 2)

/-- Congruence through one power beyond twice the requested root depth
preserves the exact root depth for all four radicands. -/
theorem critical_roots_persist_all_coordinates {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (s : ℕ) (X Y L X' Y' L' : ℤ) (q : Fin 4 → ℤ)
    (hX : (p : ℤ)^(2*s+1) ∣ X'-X)
    (hY : (p : ℤ)^(2*s+1) ∣ Y'-Y)
    (hL : (p : ℤ)^(2*s+1) ∣ L'-L)
    (hfac : ∀ j, criticalRadicands X Y L j = (p : ℤ)^(2*s)*q j)
    (hu : ∀ j, ¬ (p : ℤ) ∣ q j)
    (hs : ∀ j, IsSquare (q j : ZMod p)) :
    ∃ A : Fin 4 → ℚ_[p], ∀ j,
      A j ^ 2 = (criticalRadicands X' Y' L' j : ℚ_[p]) ∧
      (A j).valuation = (s : ℤ) := by
  have hd := critical_radicands_congr ((p : ℤ)^(2*s+1)) X Y L X' Y' L' hX hY hL
  choose d hd using hd
  let q' : Fin 4 → ℤ := fun j => q j + p*d j
  have hfac' : ∀ j, criticalRadicands X' Y' L' j = (p : ℤ)^(2*s)*q' j := by
    intro j
    have hj := hd j
    rw [hfac j, pow_succ] at hj
    dsimp [q']
    linear_combination hj
  have hres : ∀ j, (q' j : ZMod p) = (q j : ZMod p) := by
    intro j
    simp [q',ZMod.natCast_self]
  apply critical_four_scaled_roots hp s _ q' hfac'
  · intro j hdiv
    apply hu j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (q j) p).mp
    rw [← hres j]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (q' j) p).mpr hdiv
  · intro j
    rw [hres j]
    exact hs j
/-- Finite residue patterns produce actual integer local data at every depth,
including all four normalized integer radicands needed for CRT transport. -/
theorem critical_local_radicand_data {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (s : ℕ) (hspos : 1 ≤ s) (i b c : ZMod p)
    (hi : i^2 = -1) (hb : b ≠ 0)
    (hu : c ≠ 0 ∧ c+b ≠ 0 ∧ c+i*b ≠ 0 ∧ c+(1+i)*b ≠ 0)
    (hsq : IsSquare c ∧ IsSquare (c+b) ∧ IsSquare (c+i*b) ∧
      IsSquare (c+(1+i)*b)) :
    ∃ X Y : ℤ, ∃ qs : Fin 4 → ℤ,
      ¬ (p : ℤ) ∣ X ∧ ¬ (p : ℤ) ∣ Y ∧
      (∀ j, criticalRadicands X Y ((p : ℤ)^(2*s)) j = (p : ℤ)^(2*s)*qs j) ∧
      (∀ j, ¬ (p : ℤ) ∣ qs j) ∧ (∀ j, IsSquare (qs j : ZMod p)) := by
  obtain ⟨X,Y,q,hXu,hYu,hnorm,hq,hX,hY⟩ := critical_local_coordinates hp s hspos i b c hi hb
  let N : ℤ := (p : ℤ)^(2*s)
  let qs : Fin 4 → ℤ := ![q,q-2*X+N,q-2*Y+N,q-2*X-2*Y+2*N]
  have hN : (N : ZMod p) = 0 := by
    dsimp [N]
    push_cast
    rw [ZMod.natCast_self]
    exact zero_pow (by omega)
  have hres : ∀ j : Fin 4, (qs j : ZMod p) =
      (![c,c+b,c+i*b,c+(1+i)*b] : Fin 4 → ZMod p) j := by
    intro j
    fin_cases j <;> simp [qs] <;> push_cast <;>
      simp only [hq,hN,mul_zero,add_zero] <;>
      first | linear_combination hX | linear_combination hY | linear_combination hX+hY
  refine ⟨X,Y,qs,hXu,hYu,?_,?_,?_⟩
  · intro j
    fin_cases j <;> simp [criticalRadicands,qs] <;>
      dsimp [N] at * <;> linear_combination hnorm
  · intro j hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (qs j) p).mpr hd
    rw [hres j] at hz
    fin_cases j <;> simp at hz <;> tauto
  · intro j
    rw [hres j]
    fin_cases j <;> simp <;> tauto

end FourCorner
#print axioms FourCorner.critical_radicands_congr
#print axioms FourCorner.critical_roots_persist_all_coordinates

#print axioms FourCorner.critical_local_radicand_data
