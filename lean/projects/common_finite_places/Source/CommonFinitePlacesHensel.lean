import FourCorner.CommonRootPadicResidue
import FourCorner.CommonRootSource
import Mathlib.Tactic
set_option autoImplicit false
namespace FourCorner.CommonFinitePlaces

theorem lift_unit_square {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (a : ℤ_[p]) (ha : PadicInt.toZMod a ≠ 0)
    (hs : IsSquare (PadicInt.toZMod a)) :
    ∃ x : ℚ_[p], x ≠ 0 ∧ x ^ 2 = (a : ℚ_[p]) := by
  obtain ⟨x, hx⟩ := (padicInt_isSquare_coe_iff_residue_unit hp a ha).mpr hs
  have he : x ^ 2 = (a : ℚ_[p]) := by simpa [pow_two] using hx.symm
  refine ⟨x, ?_, he⟩
  intro hz
  have ha0 : a = 0 := by
    apply PadicInt.ext
    simpa [hz] using he.symm
  exact ha (by simp [ha0])

/-- Literal five-radical affine Hensel lifting. The inverse denominators are
actual integral elements; all five nonzero residue conditions are retained. -/
theorem lift_five_radical_affine {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (t l k li ki : ℤ_[p])
    (hl : l * li = 1) (hk : k * ki = 1)
    (ht0 : (t : ℚ_[p]) ≠ 0) (ht1 : (t : ℚ_[p]) ≠ 1)
    (htm : (t : ℚ_[p]) ≠ -1)
    (hP : PadicInt.toZMod (l + (t+1)) ≠ 0)
    (hC : PadicInt.toZMod (l - (t-1)) ≠ 0)
    (hM : PadicInt.toZMod ((t-1) * ((t+1)-l) * li) ≠ 0)
    (hB : PadicInt.toZMod ((t+1) * (l+(t-1)) * li) ≠ 0)
    (hZ : PadicInt.toZMod (l * ki) ≠ 0)
    (sP : IsSquare (PadicInt.toZMod (l + (t+1))))
    (sC : IsSquare (PadicInt.toZMod (l - (t-1))))
    (sM : IsSquare (PadicInt.toZMod ((t-1) * ((t+1)-l) * li)))
    (sB : IsSquare (PadicInt.toZMod ((t+1) * (l+(t-1)) * li)))
    (sZ : IsSquare (PadicInt.toZMod (l * ki))) :
    ∃ (S : CommonRootSource ℚ_[p] (t : ℚ_[p])) (Z : ℚ_[p]),
      S.ell = (l : ℚ_[p]) ∧ Z ≠ 0 ∧ Z ^ 2 = S.ell / (k : ℚ_[p]) := by
  obtain ⟨P, hP0, eP⟩ := lift_unit_square hp _ hP sP
  obtain ⟨C, hC0, eC⟩ := lift_unit_square hp _ hC sC
  obtain ⟨M, hM0, eM⟩ := lift_unit_square hp _ hM sM
  obtain ⟨B, hB0, eB⟩ := lift_unit_square hp _ hB sB
  obtain ⟨Z, hZ0, eZ⟩ := lift_unit_square hp _ hZ sZ
  have hl' : (l : ℚ_[p]) * (li : ℚ_[p]) = 1 := by
    exact congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hl
  have hk' : (k : ℚ_[p]) * (ki : ℚ_[p]) = 1 := by
    exact congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hk
  have hl0 : (l : ℚ_[p]) ≠ 0 := left_ne_zero_of_mul_eq_one hl'
  have hk0 : (k : ℚ_[p]) ≠ 0 := left_ne_zero_of_mul_eq_one hk'
  have eli : (li : ℚ_[p]) = (l : ℚ_[p])⁻¹ := by
    apply (mul_left_cancel₀ hl0)
    simpa [hl0] using hl'
  have eki : (ki : ℚ_[p]) = (k : ℚ_[p])⁻¹ := by
    apply (mul_left_cancel₀ hk0)
    simpa [hk0] using hk'
  refine ⟨{
    ell := l, P := P, C := C, M := M, B := B,
    t_ne_zero := ht0, t_ne_one := ht1, t_ne_neg_one := htm,
    ell_ne_zero := hl0, P_ne_zero := hP0, C_ne_zero := hC0,
    M_ne_zero := hM0, B_ne_zero := hB0,
    sqP := ?_, sqC := ?_, sqM := ?_, sqB := ?_
  }, Z, rfl, hZ0, ?_⟩
  · simpa using eP
  · simpa using eC
  · simpa [eli, div_eq_mul_inv] using eM
  · simpa [eli, div_eq_mul_inv] using eB
  · simpa [eki, div_eq_mul_inv] using eZ

/-- All five finite branch sections are distinct, with every possible
parameter collision excluded. The sixth branch section lies at infinity. -/
theorem finite_branch_sections_distinct {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (t : K) (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (htm : t ≠ -1) :
    List.Pairwise (· ≠ ·) ([0, -(t+1), t-1, t+1, -(t-1)] : List K) := by
  have hs : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hT : t + 1 ≠ 0 := by
    intro hz
    exact htm (eq_neg_of_add_eq_zero_left hz)
  have h2t : 2*t ≠ 0 := mul_ne_zero h2 ht0
  have h2s : 2*(t-1) ≠ 0 := mul_ne_zero h2 hs
  have h2T : 2*(t+1) ≠ 0 := mul_ne_zero h2 hT
  simp only [List.pairwise_cons, List.mem_cons, 
    forall_eq_or_imp, List.not_mem_nil, 
    forall_false, implies_true, and_true]
  constructor
  · exact ⟨Ne.symm (neg_ne_zero.mpr hT), Ne.symm hs, Ne.symm hT,
      Ne.symm (neg_ne_zero.mpr hs)⟩
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro h; apply h2t; linear_combination -h
    · intro h; apply h2T; linear_combination -h
    · intro h; apply h2; linear_combination -h
  constructor
  · refine ⟨?_, ?_⟩
    · intro h; apply h2; linear_combination -h
    · intro h; apply h2s; linear_combination h
  · refine ⟨?_, trivial, List.Pairwise.nil⟩
    intro h; apply h2t; linear_combination h

/-- The numerical cutoff in the manuscript is already sufficient without
using a prime-gap table: the lower bound is positive for every integer >=1154. -/
theorem genus17_lower_bound_positive (p : ℕ) (hp : 1153 < p) :
    0 < (p : ℝ) + 1 - 34 * Real.sqrt p := by
  have hp' : (1154 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : (Real.sqrt (p : ℝ))^2 = p := Real.sq_sqrt (by positivity)
  have hprod : 0 ≤ (p : ℝ) * ((p : ℝ) - 1154) := by positivity
  by_contra hn
  have hh : (p : ℝ) + 1 ≤ 34 * Real.sqrt p := by linarith
  have hsq : ((p : ℝ) + 1)^2 ≤ (34 * Real.sqrt p)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hh
  nlinarith

/-- The actual residue branch sections remain distinct whenever the three
parameter residues are units. This is the explicit collision calculation
needed in a future integral normalization construction. -/
theorem residue_branch_sections_distinct {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (t : ℤ_[p])
    (ht0 : PadicInt.toZMod t ≠ 0)
    (ht1 : PadicInt.toZMod (t-1) ≠ 0)
    (htm : PadicInt.toZMod (t+1) ≠ 0) :
    List.Pairwise (· ≠ ·)
      ([0, -(PadicInt.toZMod t+1), PadicInt.toZMod t-1,
        PadicInt.toZMod t+1, -(PadicInt.toZMod t-1)] : List (ZMod p)) := by
  refine finite_branch_sections_distinct ?_ _ ht0 ?_ ?_
  · intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hh := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd
    rcases hh with h | h
    · exact (Fact.out : p.Prime).ne_one h
    · exact hp h
  · intro h
    apply ht1
    simp [map_sub, h]
  · intro h
    apply htm
    simp [h]
/-- Every allowed twisting product is an actual integral unit away from
2 and the support of d. Thus the twisting denominator is not omitted from
the good-prime conditions. -/
theorem twisting_product_residue_ne_zero {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (d : ℚ) (F : Finset ℕ)
    (hF : ∀ q ∈ F, q.Prime ∧ (q = 2 ∨ 0 < padicValRat q d))
    (hd : padicValRat p d = 0) :
    PadicInt.toZMod (∏ q ∈ F, (q : ℤ_[p])) ≠ 0 := by
  rw [map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  have hprime := (hF q hq).1
  have hqp : q ≠ p := by
    intro he
    rcases (hF q hq).2 with h | h
    · exact hp (he.symm.trans h)
    · rw [he, hd] at h
      exact lt_irrefl _ h
  simp only [map_natCast]
  intro hz
  have hpq : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp hz
  rcases (Nat.dvd_prime hprime).mp hpq with h | h
  · exact (Fact.out : p.Prime).ne_one h
  · exact hqp h.symm

/-- Explicit inverse denominator in the p-adic integer ring, obtained from
nonzero residue rather than assumed in the local existence proof. -/
theorem integral_inverse_of_residue_ne_zero {p : ℕ} [Fact p.Prime]
    (a : ℤ_[p]) (ha : PadicInt.toZMod a ≠ 0) :
    ∃ ai : ℤ_[p], a * ai = 1 := by
  have hu : IsUnit a := PadicInt.isUnit_iff.mpr
    ((padicInt_norm_eq_one_iff_residue_ne_zero a).mpr ha)
  exact ⟨↑(hu.unit⁻¹), by simpa only [IsUnit.unit_spec] using hu.unit.mul_inv⟩

/-- Every actual finite-field affine point of the five-radical cover
lifts to the actual p-adic affine cover. Unit denominators are constructed
from their residues; the residue source contains all four ordered roots. -/
theorem actual_affine_residue_point_lifts {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (t l k : ℤ_[p])
    (hl0 : PadicInt.toZMod l ≠ 0) (hk0 : PadicInt.toZMod k ≠ 0)
    (S₀ : CommonRootSource (ZMod p) (PadicInt.toZMod t))
    (hEll : S₀.ell = PadicInt.toZMod l)
    (Z₀ : ZMod p) (hZ₀ : Z₀^2 = S₀.ell / PadicInt.toZMod k) :
    ∃ (S : CommonRootSource ℚ_[p] (t : ℚ_[p])) (Z : ℚ_[p]),
      S.ell = (l : ℚ_[p]) ∧ Z ≠ 0 ∧ Z^2 = S.ell / (k : ℚ_[p]) := by
  obtain ⟨li, hli⟩ := integral_inverse_of_residue_ne_zero l hl0
  obtain ⟨ki, hki⟩ := integral_inverse_of_residue_ne_zero k hk0
  have hli' : PadicInt.toZMod li = (PadicInt.toZMod l)⁻¹ := by
    apply mul_left_cancel₀ hl0
    have h := congrArg PadicInt.toZMod hli
    simpa [hl0] using h
  have hki' : PadicInt.toZMod ki = (PadicInt.toZMod k)⁻¹ := by
    apply mul_left_cancel₀ hk0
    have h := congrArg PadicInt.toZMod hki
    simpa [hk0] using h
  have eP : PadicInt.toZMod (l+(t+1)) = S₀.P^2 := by
    simpa [hEll] using S₀.sqP.symm
  have eC : PadicInt.toZMod (l-(t-1)) = S₀.C^2 := by
    simpa [hEll] using S₀.sqC.symm
  have eM : PadicInt.toZMod ((t-1)*((t+1)-l)*li) = S₀.M^2 := by
    simpa [hEll, hli', div_eq_mul_inv] using S₀.sqM.symm
  have eB : PadicInt.toZMod ((t+1)*(l+(t-1))*li) = S₀.B^2 := by
    simpa [hEll, hli', div_eq_mul_inv] using S₀.sqB.symm
  have eZ : PadicInt.toZMod (l*ki) = Z₀^2 := by
    simpa [hEll, hki', div_eq_mul_inv] using hZ₀.symm
  have hZ0 : Z₀ ≠ 0 := by
    intro hz
    have he := hZ₀
    rw [hz, zero_pow (by decide)] at he
    have hh := (div_ne_zero S₀.ell_ne_zero hk0)
    exact hh he.symm
  have ht0 : (t : ℚ_[p]) ≠ 0 := by
    intro hz
    have he : t = 0 := PadicInt.ext hz
    exact S₀.t_ne_zero (by simp [he])
  have ht1 : (t : ℚ_[p]) ≠ 1 := by
    intro hz
    have he : t = 1 := PadicInt.ext hz
    exact S₀.t_ne_one (by simp [he])
  have htm : (t : ℚ_[p]) ≠ -1 := by
    intro hz
    have he : t = -1 := PadicInt.ext hz
    exact S₀.t_ne_neg_one (by simp [he])
  apply lift_five_radical_affine hp t l k li ki hli hki ht0 ht1 htm
  · rw [eP]; exact pow_ne_zero _ S₀.P_ne_zero
  · rw [eC]; exact pow_ne_zero _ S₀.C_ne_zero
  · rw [eM]; exact pow_ne_zero _ S₀.M_ne_zero
  · rw [eB]; exact pow_ne_zero _ S₀.B_ne_zero
  · rw [eZ]; exact pow_ne_zero _ hZ0
  · rw [eP]; exact IsSquare.sq _
  · rw [eC]; exact IsSquare.sq _
  · rw [eM]; exact IsSquare.sq _
  · rw [eB]; exact IsSquare.sq _
  · rw [eZ]; exact IsSquare.sq _

end FourCorner.CommonFinitePlaces
#print axioms FourCorner.CommonFinitePlaces.lift_unit_square
#print axioms FourCorner.CommonFinitePlaces.lift_five_radical_affine
#print axioms FourCorner.CommonFinitePlaces.finite_branch_sections_distinct

#print axioms FourCorner.CommonFinitePlaces.genus17_lower_bound_positive
#print axioms FourCorner.CommonFinitePlaces.residue_branch_sections_distinct

#print axioms FourCorner.CommonFinitePlaces.twisting_product_residue_ne_zero
#print axioms FourCorner.CommonFinitePlaces.integral_inverse_of_residue_ne_zero

#print axioms FourCorner.CommonFinitePlaces.actual_affine_residue_point_lifts
