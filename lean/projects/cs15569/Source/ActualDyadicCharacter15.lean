import DyadicBridge
import DyadicCharacter
import CSFoundation.CommonSourceBeta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.CommonSource
open IsLocalRing
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq DyadicField := Classical.decEq _

/-- Canonical identification with the usual dyadic integers. -/
def dyadicIntegerEquiv15 : ℤ_[2] ≃+* DyadicIntegers :=
  by
    letI : Algebra ℤ DyadicIntegers := Ring.toIntAlgebra _
    exact @AlgEquiv.toRingEquiv _ _ _ _ _ _ _ _
      (@ContinuousAlgEquiv.toAlgEquiv _ _ _ _ _ _ _ _ _ _
      (PadicInt.adicCompletionIntegersEquiv ℤ ⟨2, Nat.prime_two⟩))

lemma dyadic_maximalIdeal15 : maximalIdeal DyadicIntegers = Ideal.span {(2 : DyadicIntegers)} := by
  have h := IsLocalRing.map_ringEquiv_maximalIdeal dyadicIntegerEquiv15
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span] at h
  norm_num only [Set.image_singleton, map_natCast, Nat.cast_ofNat] at h
  apply Eq.trans h.symm
  congr 1
  ext x
  simp only [Set.mem_singleton_iff]
  exact (congrArg (fun y => x = y) (map_ofNat dyadicIntegerEquiv15 2)).to_iff

/-- Canonical reduction of the actual completion integers modulo four. -/
def dyadicResidueFour15 : DyadicIntegers →+* ZMod 4 :=
  (show ℤ_[2] →+* ZMod 4 from PadicInt.toZModPow 2).comp dyadicIntegerEquiv15.symm.toRingHom

/-- Base change restricted to the actual rational formal neighborhood. -/
def rationalFiltrationMap15 (n : ℤ) (hn : n ≠ 0) (k : ℕ) :
    Hlevel n hn k →+ (letI := dyadicCurve_isElliptic hn;
      WeierstrassCurve.Affine.filtration (dyadic_model_eq n) k) := by
  letI := dyadicCurve_isElliptic hn
  exact { toFun := fun P => ⟨rationalToDyadic n P, P.property⟩
          map_zero' := Subtype.ext (map_zero _)
          map_add' := fun P Q => Subtype.ext (map_add _ _ _) }

/-- Actual rational mod-four formal-parameter character; no residue map is assumed. -/
def rationalDyadicCharacter15 (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    Hlevel n hn k →+ ZMod 4 := by
  letI := dyadicCurve_isElliptic hn
  exact (Dyadic.parameterCharacter (dyadic_model_eq n) dyadic_maximalIdeal15 hk
    dyadicResidueFour15).comp (rationalFiltrationMap15 n hn k)

/-- The chosen deeper level may contain the entire paper subgroup H. -/
def paperHToLevel15 (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (hdeep : H n hn ≤ Hlevel n hn k) : H n hn →+ Hlevel n hn k :=
  AddSubgroup.inclusion hdeep

/-- The paper's whole-H parameter character at any permitted common depth. -/
def paperDyadicCharacter15 (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) : H n hn →+ ZMod 4 :=
  (rationalDyadicCharacter15 n hn k hk).comp (paperHToLevel15 n hn k hdeep)

/-- Actual integral representative whose mod-four residue defines the rational character. -/
def rationalScaledParameter15 (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (P : Hlevel n hn k) : DyadicIntegers := by
  letI := dyadicCurve_isElliptic hn
  exact Dyadic.scaledParameter (dyadic_model_eq n) dyadic_maximalIdeal15
    (rationalFiltrationMap15 n hn k P)

theorem rationalDyadicCharacter_formula15 (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (hk : 1 ≤ k) (P : Hlevel n hn k) :
    rationalDyadicCharacter15 n hn k hk P =
      dyadicResidueFour15 (rationalScaledParameter15 n hn k P) := rfl

/-- Coordinate formula, valid for every rational point and every allowed depth. -/
theorem rationalScaledParameter_coordinate15 (n : ℤ) (hn : n ≠ 0) (k : ℕ)
    (P : Hlevel n hn k) (x y : ℚ)
    (h : (congruentCurve (n : ℚ)).toAffine.Nonsingular x y)
    (hP : (P : Point (n : ℚ)) = .some x y h) :
    (rationalScaledParameter15 n hn k P : DyadicField) =
      (-algebraMap ℚ DyadicField x / algebraMap ℚ DyadicField y) / 2^(k+1) := by
  letI := dyadicCurve_isElliptic hn
  apply Dyadic.scaledParameter_eq_neg_x_div_y (dyadic_model_eq n) dyadic_maximalIdeal15
  change rationalToDyadic n P.val = _
  rw [hP]
  rfl

/-- The original H=E₂ already has a canonical actual character (ν=2). -/
def basePaperDyadicCharacter15 (n : ℤ) (hn : n ≠ 0) : H n hn →+ ZMod 4 :=
  rationalDyadicCharacter15 n hn 1 (by decide)

/-- A finite row family on the actual entire rational H, retaining the canonical dyadic row. -/
def actualRows15 (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ}
    (odd : Fin s → H n hn →+ F4) : Fin (s+1) → H n hn →+ F4 :=
  Fin.cases (paperDyadicCharacter15 n hn k hk hdeep) odd

/-- All actual H compensators are retained by the row invariant. -/
theorem actual_compensation15 (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ}
    (odd : Fin s → H n hn →+ F4) (W Z : H n hn)
    (hW : eta (actualRows15 n hn k hk hdeep odd) W = 0) :
    b (actualRows15 n hn k hk hdeep odd) (W + 2 • Z) =
      b (actualRows15 n hn k hk hdeep odd) W +
        eta (actualRows15 n hn k hk hdeep odd) Z :=
  compensation _ hW Z

/-- Exact weighted dual certificate for the complete actual rational subgroup, all ranks. -/
theorem actual_dual_certificate15 (n : ℤ) (hn : n ≠ 0) (k : ℕ) (hk : 1 ≤ k)
    (hdeep : H n hn ≤ Hlevel n hn k) {s : ℕ}
    (odd : Fin s → H n hn →+ F4) (W : H n hn)
    (κ : (M (actualRows15 n hn k hk hdeep odd)).ker)
    (hW : classOf W = κ.val) :
    beta (actualRows15 n hn k hk hdeep odd) κ ≠ 0 ↔
      ∃ c : Fin (s+1) → F2,
        (∀ Z : H n hn, ∑ j, c j * eta (actualRows15 n hn k hk hdeep odd) Z j = 0) ∧
        half (weightedCharacter (actualRows15 n hn k hk hdeep odd) c W) = 1 :=
  beta_ne_zero_iff_weighted_certificate _ κ hW

#print axioms actual_compensation15
#print axioms actual_dual_certificate15

#print axioms paperDyadicCharacter15
#print axioms rationalScaledParameter_coordinate15

#print axioms dyadic_maximalIdeal15
#print axioms rationalDyadicCharacter15
end FourCorner.CommonSource
