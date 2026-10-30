import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-! Exact coordinate constituents of Proposition crit-elliptic.
No Scheme isomorphism or smoothness claim is inferred merely from these identities. -/
set_option autoImplicit false
namespace FourCorner.CriticalElliptic23
variable {k : Type*} [Field k]
def Shift (v : Fin 4 → k) : k := v 1 ^ 2 - v 0 ^ 2
def CriticalCoordinates (i : k) (v : Fin 4 → k) : Prop :=
  v 2 ^ 2 - v 0 ^ 2 = i * Shift v ∧
  v 3 ^ 2 - v 0 ^ 2 = (1+i) * Shift v

theorem boundary_squares (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hb : Shift v = 0) :
    ∀ j, v j ^ 2 = v 0 ^ 2 := by
  intro j
  fin_cases j
  · rfl
  · exact sub_eq_zero.mp hb
  · exact sub_eq_zero.mp (by simpa [hb] using hc.1)
  · exact sub_eq_zero.mp (by simpa [hb] using hc.2)

theorem boundary_zero_nonzero (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hb : Shift v = 0)
    (hn : ∃ j, v j ≠ 0) : v 0 ≠ 0 := by
  intro hz
  obtain ⟨j,hj⟩ := hn
  have h := boundary_squares i v hc hb j
  rw [hz, zero_pow (by decide)] at h
  exact hj ((pow_eq_zero_iff (by decide)).mp h)

theorem boundary_normalized (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hb : Shift v = 0)
    (hn : ∃ j, v j ≠ 0) :
    v 0 / v 0 = 1 ∧ ∀ j, v j / v 0 = 1 ∨ v j / v 0 = -1 := by
  have h0 := boundary_zero_nonzero i v hc hb hn
  refine ⟨div_self h0, ?_⟩
  intro j
  have hs : (v j / v 0)^2 = (1:k)^2 := by
    rw [div_pow, boundary_squares i v hc hb j, div_self (pow_ne_zero 2 h0), one_pow]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hs)

theorem signed_boundary (i : k) (e1 e2 e3 : k)
    (h1 : e1 = 1 ∨ e1 = -1) (h2 : e2 = 1 ∨ e2 = -1)
    (h3 : e3 = 1 ∨ e3 = -1) :
    CriticalCoordinates i ![1,e1,e2,e3] ∧ Shift ![1,e1,e2,e3] = 0 := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    rcases h3 with rfl | rfl <;> simp [CriticalCoordinates, Shift]

def sign (e : Bool) : k := if e then -1 else 1

theorem sign_choice (e : Bool) : sign (k:=k) e = 1 ∨ sign (k:=k) e = -1 := by
  cases e <;> simp [sign]

def signedVector (e : Fin 3 → Bool) : Fin 4 → k :=
  ![1,sign (e 0),sign (e 1),sign (e 2)]

theorem signedVector_nonzero (e : Fin 3 → Bool) : signedVector (k:=k) e ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [signedVector] using h0

def signedPoint (e : Fin 3 → Bool) : Projectivization k (Fin 4 → k) :=
  Projectivization.mk k (signedVector e) (signedVector_nonzero e)

theorem signedVector_on_boundary (i : k) (e : Fin 3 → Bool) :
    CriticalCoordinates i (signedVector e) ∧ Shift (signedVector (k:=k) e) = 0 :=
  signed_boundary i _ _ _ (sign_choice _) (sign_choice _) (sign_choice _)

theorem sign_injective (h2 : (2:k) ≠ 0) : Function.Injective (sign (k:=k)) := by
  intro a b hab
  cases a <;> cases b <;> try rfl
  · simp only [sign, Bool.false_eq_true, ↓reduceIte] at hab
    exact (h2 (by linear_combination hab)).elim
  · simp only [sign, Bool.false_eq_true, ↓reduceIte] at hab
    exact (h2 (by linear_combination -hab)).elim

/-- The eight listed sign vectors define eight distinct genuine projective points. -/
theorem signedPoint_injective (h2 : (2:k) ≠ 0) :
    Function.Injective (signedPoint (k:=k)) := by
  intro a b h
  obtain ⟨r,hr⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp h
  have hr1 : r = 1 := by
    have h0 := congrFun hr 0
    simpa [signedVector] using h0
  rw [hr1, one_smul] at hr
  funext j
  apply sign_injective h2
  fin_cases j
  · simpa [signedVector] using (congrFun hr 1).symm
  · simpa [signedVector] using (congrFun hr 2).symm
  · simpa [signedVector] using (congrFun hr 3).symm

/-- Exhaustiveness of the eight projective boundary points over arbitrary fields. -/
theorem projective_boundary_classification (i : k) (v : Fin 4 → k)
    (hv : v ≠ 0) (hc : CriticalCoordinates i v) (hb : Shift v = 0) :
    ∃ e : Fin 3 → Bool, Projectivization.mk k v hv = signedPoint e := by
  have hn : ∃ j, v j ≠ 0 := by
    by_contra hn
    apply hv
    funext j
    by_contra hj
    exact hn ⟨j,hj⟩
  have h0 := boundary_zero_nonzero i v hc hb hn
  have hs := (boundary_normalized i v hc hb hn).2
  have choices : ∀ j, ∃ e : Bool, v j / v 0 = sign e := by
    intro j
    rcases hs j with hj | hj
    · exact ⟨false,hj⟩
    · exact ⟨true,hj⟩
  obtain ⟨e1,h1⟩ := choices 1
  obtain ⟨e2,h2⟩ := choices 2
  obtain ⟨e3,h3⟩ := choices 3
  refine ⟨![e1,e2,e3], (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr ⟨v 0, ?_⟩⟩
  funext j
  fin_cases j
  · simp [signedVector]
  · change v 0 * sign e1 = v 1
    rw [← h1]
    field_simp
  · change v 0 * sign e2 = v 2
    rw [← h2]
    field_simp
  · change v 0 * sign e3 = v 3
    rw [← h3]
    field_simp

/-- The explicit boundary locus has cardinal eight, without a finite-field assumption. -/
theorem signedPoint_card (h2 : (2:k) ≠ 0) :
    Nat.card (Set.range (signedPoint (k:=k))) = 8 := by
  rw [← Nat.card_congr (Equiv.ofInjective (signedPoint (k:=k)) (signedPoint_injective h2))]
  simp [Nat.card_fun]

/-- The b=0 part of the actual homogeneous intersection in the projective point set. -/
def projectiveBoundary (i : k) : Set (Projectivization k (Fin 4 → k)) :=
  {P | ∃ (v : Fin 4 → k) (hv : v ≠ 0), Projectivization.mk k v hv = P ∧
    CriticalCoordinates i v ∧ Shift v = 0}

theorem projectiveBoundary_eq_range (i : k) :
    projectiveBoundary i = Set.range (signedPoint (k:=k)) := by
  ext P
  constructor
  · rintro ⟨v,hv,rfl,hc,hb⟩
    obtain ⟨e,he⟩ := projective_boundary_classification i v hv hc hb
    exact ⟨e,he.symm⟩
  · rintro ⟨e,rfl⟩
    exact ⟨signedVector e,signedVector_nonzero e,rfl,
      (signedVector_on_boundary i e).1,(signedVector_on_boundary i e).2⟩

theorem projectiveBoundary_card (i : k) (h2 : (2:k) ≠ 0) :
    Nat.card (projectiveBoundary i) = 8 := by
  rw [projectiveBoundary_eq_range]
  exact signedPoint_card h2

/-- The exact degree-four quotient equation on the b-nonzero chart. -/
theorem quotient_quartic (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hb : Shift v ≠ 0) :
    (v 0 * v 1 * v 2 * v 3 / Shift v ^ 2)^2 =
      (v 0 ^ 2 / Shift v) * (v 0 ^ 2 / Shift v + 1) *
      (v 0 ^ 2 / Shift v + i) * (v 0 ^ 2 / Shift v + 1+i) := by
  have h1 : v 1 ^ 2 = v 0 ^ 2 + Shift v := by unfold Shift; ring
  have h2 : v 2 ^ 2 = v 0 ^ 2 + i * Shift v := by linear_combination hc.1
  have h3 : v 3 ^ 2 = v 0 ^ 2 + (1+i) * Shift v := by linear_combination hc.2
  field_simp
  rw [h1,h2,h3]
  ring

/-- The quartic transformation is valid also in characteristic three. -/
theorem quartic_to_lemniscate (i T W : k) (hi : i^2 = -1)
    (hw : W^2 = T*(T+1)*(T+i)*(T+1+i)) :
    (2*W)^2 = 1 - ((1+i)*T+i)^4 := by
  linear_combination 4 * hw +
    (i^2*(T^4+4*T^3+6*T^2+4*T+1) +
      i*(4*T^4+12*T^3+12*T^2+4*T) + 5*T^4+8*T^3+4*T^2-1) * hi

theorem iota_nonzero (i : k) (hi : i^2 = -1) : i ≠ 0 := by
  intro hz
  have h : (1:k) = 0 := by simpa [hz] using hi
  exact one_ne_zero h

theorem iota_ne_one (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) : i ≠ 1 := by
  intro hz
  subst i
  exact h2 (by linear_combination hi)

theorem iota_add_one_nonzero (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0) : 1+i ≠ 0 := by
  intro hz
  exact h2 (by linear_combination hi + (1-i)*hz)

/-- Two particular coordinates cannot both vanish at a nonzero cone point. -/
theorem not_both_last_zero (i : k) (v : Fin 4 → k)
    (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0)
    (h2 : v 2 = 0) (h3 : v 3 = 0) : False := by
  have he := hc.1
  have hf := hc.2
  rw [h2] at he
  rw [h3] at hf
  have hb : Shift v = 0 := by linear_combination he-hf
  have h0 := boundary_zero_nonzero i v hc hb hn
  have hh := boundary_squares i v hc hb 2
  rw [h2] at hh
  exact pow_ne_zero 2 h0 (by simpa using hh.symm)

/-- Independence of the two literal quadric differentials, after cancelling 2.
The coefficient vector is exactly that in the paper's diagonal pencil. -/
theorem pencil_kernel_trivial (i : k) (hi : i^2 = -1) (h2 : (2:k) ≠ 0)
    (v : Fin 4 → k) (hc : CriticalCoordinates i v) (hn : ∃ j, v j ≠ 0)
    (l m : k)
    (g0 : ((i-1)*l+i*m)*v 0 = 0)
    (g1 : (-i*l-(1+i)*m)*v 1 = 0)
    (g2 : l*v 2 = 0) (g3 : m*v 3 = 0) : l = 0 ∧ m = 0 := by
  have hi0 := iota_nonzero i hi
  have hi1 := iota_ne_one i hi h2
  have hip := iota_add_one_nonzero i hi h2
  by_cases hl : l = 0
  · refine ⟨hl, ?_⟩
    by_contra hm
    have hv0 : v 0 = 0 := (mul_eq_zero.mp (by simpa [hl] using g0)).resolve_left (mul_ne_zero hi0 hm)
    have hv1 : v 1 = 0 := (mul_eq_zero.mp (by simpa [hl] using g1)).resolve_left (neg_ne_zero.mpr (mul_ne_zero hip hm))
    have hv3 : v 3 = 0 := (mul_eq_zero.mp g3).resolve_left hm
    have hv2 : v 2 = 0 := by
      have he := hc.1
      simp [Shift, hv0, hv1] at he
      exact he
    exact not_both_last_zero i v hc hn hv2 hv3
  · have hv2 : v 2 = 0 := (mul_eq_zero.mp g2).resolve_left hl
    by_cases hm : m = 0
    · have hv0 : v 0 = 0 := (mul_eq_zero.mp (by simpa [hm] using g0)).resolve_left (mul_ne_zero (sub_ne_zero.mpr hi1) hl)
      have hv1 : v 1 = 0 := (mul_eq_zero.mp (by simpa [hm] using g1)).resolve_left (mul_ne_zero (neg_ne_zero.mpr hi0) hl)
      have hv3 : v 3 = 0 := by
        have he := hc.2
        simp [Shift, hv0, hv1] at he
        exact he
      exact (not_both_last_zero i v hc hn hv2 hv3).elim
    · have hv3 : v 3 = 0 := (mul_eq_zero.mp g3).resolve_left hm
      exact (not_both_last_zero i v hc hn hv2 hv3).elim

/-- Rational map to the cubic, with its exact domain of definition. -/
theorem lemniscate_to_cubic (R S : k) (hR : R ≠ 0)
    (hs : S^2 = 1-R^4) :
    (4*(1+S)/R^3)^2 = (2*(1+S)/R^2)^3 + 4*(2*(1+S)/R^2) := by
  field_simp
  linear_combination -8*(1+S)*hs

/-- The inverse map, again only on its actual denominator-open domain. -/
theorem cubic_to_lemniscate (X Y : k) (hD : X^2+4 ≠ 0) (hY : Y ≠ 0)
    (hc : Y^2 = X^3+4*X) :
    ((X^2-4)/(X^2+4))^2 = 1-(2*X/Y)^4 := by
  field_simp
  linear_combination -16*X^2*(Y^2+X^3+4*X)*hc

/-- Scaling by 1+i turns the displayed +4 cubic into the exact -1 cubic. -/
theorem cubic_scaling (i X Y : k) (hi : i^2 = -1) (h : 1+i ≠ 0)
    (hc : Y^2 = X^3+4*X) :
    (Y/(1+i)^3)^2 = (X/(1+i)^2)^3-X/(1+i)^2 := by
  have hp : (1+i)^4 = (-4:k) := by
    linear_combination (i^2+4*i+5)*hi
  field_simp
  linear_combination hc + X * hp

#print axioms boundary_normalized
#print axioms signed_boundary
#print axioms signedPoint_injective
#print axioms projective_boundary_classification
#print axioms signedPoint_card
#print axioms projectiveBoundary_card
#print axioms quotient_quartic
#print axioms quartic_to_lemniscate
#print axioms pencil_kernel_trivial
#print axioms lemniscate_to_cubic
#print axioms cubic_to_lemniscate
#print axioms cubic_scaling
end FourCorner.CriticalElliptic23
