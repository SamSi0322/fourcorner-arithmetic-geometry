import ThetaCoverClassPortable.ThetaLinesDualLines
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace FourCorner.ThetaLineGaloisAlgebra
open ThetaLinesAbsoluteGalois
abbrev K := ThetaBiquadratic
abbrev G := K ≃ₐ[ℚ] K
abbrev AbsoluteG := Qbar ≃ₐ[ℚ] Qbar

instance finiteSplittingField : FiniteDimensional ℚ K :=
  Module.Finite.trans (R := ℚ) ThetaSqrtTwo K

theorem splitting_degree : Module.finrank ℚ K = 4 := theta_biquadratic_degree_four

def signAut (er es : Bool) : G :=
  if er then (if es then thetaFlipTwo.trans thetaFlipFiftyone else thetaFlipTwo)
  else (if es then thetaFlipFiftyone else AlgEquiv.refl)

@[simp] theorem signAut_R (er es : Bool) :
    signAut er es thetaGaloisR = if er then -thetaGaloisR else thetaGaloisR := by
  cases er <;> cases es <;> simp [signAut]
@[simp] theorem signAut_S (er es : Bool) :
    signAut er es thetaGaloisS = if es then -thetaGaloisS else thetaGaloisS := by
  cases er <;> cases es <;> simp [signAut]

private theorem sign_injective (x : K) (hx : x ≠ 0) :
    Function.Injective (fun b : Bool => if b then -x else x) := by
  have hn : x ≠ -x := by
    intro h
    have htwo : (2 : K) * x = 0 := by calc
      2 * x = x + x := by ring
      _ = -x + x := congrArg (fun z => z + x) h
      _ = 0 := neg_add_cancel x
    exact hx ((mul_eq_zero.mp htwo).resolve_left (by norm_num))
  intro b c h
  cases b <;> cases c <;> simp_all

private theorem R_ne_zero : thetaGaloisR ≠ 0 := by
  intro h
  have hh := thetaGaloisR_sq
  rw [h, zero_pow (by decide)] at hh
  norm_num at hh
private theorem S_ne_zero : thetaGaloisS ≠ 0 := by
  intro h
  have hh := thetaGaloisS_sq
  rw [h, zero_pow (by decide)] at hh
  norm_num at hh

/-- A genuine equivalence with the four actual field automorphisms. -/
def signAutEquiv : (Bool × Bool) ≃ G := Equiv.ofBijective (fun e => signAut e.1 e.2) (by
  constructor
  · intro a b h
    apply Prod.ext
    · apply sign_injective thetaGaloisR R_ne_zero
      simpa only [signAut_R] using congrArg (fun f : G => f thetaGaloisR) h
    · apply sign_injective thetaGaloisS S_ne_zero
      simpa only [signAut_S] using congrArg (fun f : G => f thetaGaloisS) h
  · intro σ
    rcases theta_aut_four_cases σ with h | h | h | h
    · exact ⟨(false, false), h.symm⟩
    · exact ⟨(true, false), h.symm⟩
    · exact ⟨(false, true), h.symm⟩
    · exact ⟨(true, true), h.symm⟩)

theorem automorphism_card : Nat.card G = 4 := by
  rw [← Nat.card_congr signAutEquiv]
  norm_num

instance splittingGalois : IsGalois ℚ K :=
  IsGalois.of_card_aut_eq_finrank ℚ K (automorphism_card.trans splitting_degree.symm)

local instance : Algebra K Qbar := splittingEmbedding.toRingHom.toAlgebra
local instance : IsScalarTower ℚ K Qbar :=
  IsScalarTower.of_algebraMap_eq (fun q => (splittingEmbedding.commutes q).symm)
local instance : IsAlgClosure ℚ Qbar :=
  ⟨AlgebraicClosure.isAlgClosed ℚ, AlgebraicClosure.isAlgebraic ℚ⟩
local instance : Normal ℚ Qbar := IsAlgClosure.normal ℚ Qbar

/-- Actual restriction of the absolute Galois group to the embedded degree-four field. -/
def restrictAbsolute : AbsoluteG →* G := AlgEquiv.restrictNormalHom K

theorem restrictAbsolute_commutes (σ : AbsoluteG) (z : K) :
    splittingEmbedding (restrictAbsolute σ z) = σ (splittingEmbedding z) :=
  AlgEquiv.restrictNormal_commutes σ K z

theorem restrictAbsolute_surjective : Function.Surjective restrictAbsolute :=
  AlgEquiv.restrictNormalHom_surjective Qbar

@[simp] theorem restrictAbsolute_flipTwo : restrictAbsolute flipTwo = thetaFlipTwo :=
  AlgEquiv.restrict_liftNormal Qbar thetaFlipTwo
@[simp] theorem restrictAbsolute_flipFiftyone : restrictAbsolute flipFiftyone = thetaFlipFiftyone :=
  AlgEquiv.restrict_liftNormal Qbar thetaFlipFiftyone
end FourCorner.ThetaLineGaloisAlgebra
