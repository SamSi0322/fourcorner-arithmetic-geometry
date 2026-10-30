import ThetaLinesProjectiveLines
import ThetaBitangentGaloisWave36
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace FourCorner.ThetaLinesAbsoluteGalois
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev Qbar := AlgebraicClosure ℚ

local instance finiteBiquadratic : FiniteDimensional ℚ ThetaBiquadratic :=
  Module.Finite.trans (R:=ℚ) ThetaSqrtTwo ThetaBiquadratic
local instance algebraicBiquadratic : Algebra.IsAlgebraic ℚ ThetaBiquadratic :=
  Algebra.IsAlgebraic.of_finite ℚ ThetaBiquadratic

local instance closureQbar : IsAlgClosure ℚ Qbar :=
  ⟨AlgebraicClosure.isAlgClosed ℚ,AlgebraicClosure.isAlgebraic ℚ⟩
local instance normalQbar : Normal ℚ Qbar := IsAlgClosure.normal ℚ Qbar

def splittingEmbedding : ThetaBiquadratic →ₐ[ℚ] Qbar := IsAlgClosed.lift
local instance splittingAlgebra : Algebra ThetaBiquadratic Qbar := splittingEmbedding.toRingHom.toAlgebra
local instance splittingTower : IsScalarTower ℚ ThetaBiquadratic Qbar :=
  IsScalarTower.of_algebraMap_eq fun q => (splittingEmbedding.commutes q).symm

def r : Qbar := splittingEmbedding thetaGaloisR
def s : Qbar := splittingEmbedding thetaGaloisS
@[simp] theorem r_sq : r^2=2 := by rw [r,←map_pow,thetaGaloisR_sq,map_ofNat]
@[simp] theorem s_sq : s^2=51 := by rw [s,←map_pow,thetaGaloisS_sq,map_ofNat]

def flipTwo : Qbar ≃ₐ[ℚ] Qbar := thetaFlipTwo.liftNormal Qbar
def flipFiftyone : Qbar ≃ₐ[ℚ] Qbar := thetaFlipFiftyone.liftNormal Qbar

@[simp] theorem flipTwo_r : flipTwo r= -r := by
  change thetaFlipTwo.liftNormal Qbar (algebraMap ThetaBiquadratic Qbar thetaGaloisR)=_
  rw [AlgEquiv.liftNormal_commutes,thetaFlipTwo_R,map_neg]
  rfl
@[simp] theorem flipTwo_s : flipTwo s=s := by
  change thetaFlipTwo.liftNormal Qbar (algebraMap ThetaBiquadratic Qbar thetaGaloisS)=_
  rw [AlgEquiv.liftNormal_commutes,thetaFlipTwo_S]
  rfl
@[simp] theorem flipFiftyone_r : flipFiftyone r=r := by
  change thetaFlipFiftyone.liftNormal Qbar (algebraMap ThetaBiquadratic Qbar thetaGaloisR)=_
  rw [AlgEquiv.liftNormal_commutes,thetaFlipFiftyone_R]
  rfl
@[simp] theorem flipFiftyone_s : flipFiftyone s= -s := by
  change thetaFlipFiftyone.liftNormal Qbar (algebraMap ThetaBiquadratic Qbar thetaGaloisS)=_
  rw [AlgEquiv.liftNormal_commutes,thetaFlipFiftyone_S,map_neg]
  rfl

/-- Genuine automorphisms of the algebraic closure realize ALL independent
sign choices, rather than only formal automorphisms of a tuple of labels. -/
theorem absolute_independent_signs (er es : Bool) :
    ∃σ : Qbar ≃ₐ[ℚ] Qbar,σ r=(if er then -r else r) ∧ σ s=(if es then -s else s) := by
  cases er <;> cases es
  · exact ⟨AlgEquiv.refl, rfl,rfl⟩
  · exact ⟨flipFiftyone,flipFiftyone_r,flipFiftyone_s⟩
  · exact ⟨flipTwo,flipTwo_r,flipTwo_s⟩
  · refine ⟨flipTwo.trans flipFiftyone,?_,?_⟩ <;> simp

/-- Every absolute Galois automorphism acts on the actual radicals by signs. -/
theorem absolute_radical_signs (σ : Qbar ≃ₐ[ℚ] Qbar) :
    (σ r=r ∨ σ r= -r) ∧ (σ s=s ∨ σ s= -s) := by
  constructor
  · apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [←map_pow,r_sq,map_ofNat]
  · apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [←map_pow,s_sq,map_ofNat]

def coordinateMap (σ : Qbar ≃ₐ[ℚ] Qbar) :
    (Fin 3 → Qbar) →ₛₗ[σ.toRingHom] (Fin 3 → Qbar) where
  toFun v := fun i => σ (v i)
  map_add' v w := by ext i;simp
  map_smul' c v := by ext i;simp

theorem coordinateMap_injective (σ : Qbar ≃ₐ[ℚ] Qbar) : Function.Injective (coordinateMap σ) := by
  intro v w he
  funext i
  exact σ.injective (congrFun he i)

/-- The actual semilinear absolute Galois action on the native projective dual plane. -/
def projectiveAction (σ : Qbar ≃ₐ[ℚ] Qbar) :
    Projectivization Qbar (Fin 3 → Qbar) → Projectivization Qbar (Fin 3 → Qbar) :=
  Projectivization.map (coordinateMap σ) (coordinateMap_injective σ)

#print axioms splittingEmbedding
#print axioms absolute_independent_signs
#print axioms absolute_radical_signs
#print axioms projectiveAction
end
end FourCorner.ThetaLinesAbsoluteGalois
