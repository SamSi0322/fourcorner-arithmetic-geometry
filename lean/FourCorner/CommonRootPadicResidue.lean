import FourCorner.CommonRootTwoLift
import FourCorner.PadicResidueSquareBasic

set_option autoImplicit false

namespace FourCorner

/-- The integral representative of an actual `p`-adic field element in the
closed unit ball. No choice or approximation is involved. -/
def padicIntegral {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) : ℤ_[p] :=
  ⟨x, hx⟩

@[simp] theorem padicIntegral_coe {p : ℕ} [Fact p.Prime]
    (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) : (padicIntegral x hx : ℚ_[p]) = x := rfl

/-- Reduction of an actual integral `p`-adic field element. -/
noncomputable def padicResidue {p : ℕ} [Fact p.Prime]
    (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) : ZMod p :=
  PadicInt.toZMod (padicIntegral x hx)

/-- The open unit ball is exactly the kernel of reduction. -/
theorem padicInt_norm_lt_one_iff_residue_zero {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal,
    ← PadicInt.ker_toZMod, RingHom.mem_ker]

/-- Nonzero residue is equivalent to unit norm. -/
theorem padicInt_norm_eq_one_iff_residue_ne_zero {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) : ‖x‖ = 1 ↔ PadicInt.toZMod x ≠ 0 := by
  constructor
  · intro hx hz
    have hsmall := (padicInt_norm_lt_one_iff_residue_zero x).mpr hz
    rw [hx] at hsmall
    exact lt_irrefl _ hsmall
  · intro hx
    apply le_antisymm (PadicInt.norm_le_one x)
    exact le_of_not_gt (fun h => hx ((padicInt_norm_lt_one_iff_residue_zero x).mp h))

/-- Field-norm form of the residue-unit criterion. -/
theorem padicInt_norm_coe_eq_one_of_residue_ne_zero {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) (hx : PadicInt.toZMod x ≠ 0) : ‖(x : ℚ_[p])‖ = 1 :=
  (padicInt_norm_eq_one_iff_residue_ne_zero x).mpr hx

/-- The exact odd-prime square criterion for a unit of the integral ring,
with its square root in the actual completed field. -/
theorem padicInt_isSquare_coe_iff_residue_unit {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (x : ℤ_[p]) (hx : PadicInt.toZMod x ≠ 0) :
    IsSquare (x : ℚ_[p]) ↔ IsSquare (PadicInt.toZMod x) := by
  constructor
  · exact padicInt_isSquare_toZMod_of_isSquare_coe x
  · intro hs
    exact (padicInt_isSquare_coe_iff x).mpr
      (padicInt_isSquare_of_isSquare_residue_unit hp x hx hs)

/-- A nonsquare residue obstructs squarehood in the actual p-adic field.
No unit assumption is needed for this direction. -/
theorem padicInt_not_isSquare_coe_of_residue {p : ℕ} [Fact p.Prime]
    (x : ℤ_[p]) (hx : ¬ IsSquare (PadicInt.toZMod x)) :
    ¬ IsSquare (x : ℚ_[p]) :=
  fun hs => hx (padicInt_isSquare_toZMod_of_isSquare_coe x hs)

/-- Reduction of an integral square is a square. -/
theorem padic_residue_isSquare_of_isSquare {p : ℕ} [Fact p.Prime]
    (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hs : IsSquare x) :
    IsSquare (padicResidue x hx) :=
  padicInt_isSquare_toZMod_of_isSquare_coe (padicIntegral x hx) hs

/-- Odd-prime Hensel lifting for an arbitrary actual field element of unit
norm, expressed through its integral representative and residue. -/
theorem padic_isSquare_iff_residue_of_norm_one {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (x : ℚ_[p]) (hx : ‖x‖ = 1) :
    IsSquare x ↔ IsSquare (padicResidue x hx.le) := by
  exact padicInt_isSquare_coe_iff_residue_unit hp (padicIntegral x hx.le)
    ((padicInt_norm_eq_one_iff_residue_ne_zero _).mp hx)

/-- A square residue lifts whenever the given integral element has unit norm. -/
theorem padic_isSquare_of_residue_unit {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (x : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hu : ‖x‖ = 1)
    (hs : IsSquare (padicResidue x hx)) : IsSquare x :=
  (padic_isSquare_iff_residue_of_norm_one hp x hu).mpr hs

end FourCorner

#print axioms FourCorner.padicInt_norm_eq_one_iff_residue_ne_zero
#print axioms FourCorner.padicInt_isSquare_coe_iff_residue_unit
#print axioms FourCorner.padicInt_not_isSquare_coe_of_residue
#print axioms FourCorner.padic_isSquare_iff_residue_of_norm_one
#print axioms FourCorner.padic_isSquare_of_residue_unit
