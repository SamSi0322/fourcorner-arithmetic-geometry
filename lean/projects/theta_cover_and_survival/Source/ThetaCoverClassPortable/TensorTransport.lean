import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TensorProduct CategoryTheory
open scoped ChangeOfRings
noncomputable section
universe u

namespace Module.FaithfullyFlat
variable {R T : Type u} [CommRing R] [CommRing T]

def restrictedScalarEquiv {f g : R →+* T} (h : f = g) :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of T T) ≃ₗ[R]
      (ModuleCat.restrictScalars g).obj (ModuleCat.of T T) :=
  { AddEquiv.refl T with
    map_smul' := by
      intro r t
      change f r * (show T from t) = g r * (show T from t)
      rw [h] }

def tensorTransport {f g : R →+* T} (h : f = g) (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars f).obj M ⟶ (ModuleCat.extendScalars g).obj M := by
  let e := TensorProduct.congr (restrictedScalarEquiv h) (LinearEquiv.refl R M)
  apply ModuleCat.ofHom
  exact
  { e.toLinearMap with
    map_smul' := by
      intro t x
      change e (t • x) = t • e x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a m => rfl
      | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy }

@[simp] theorem tensorTransport_tmul {f g : R →+* T} (h : f = g)
    (M : ModuleCat.{u} R) (t : T) (m : M) :
    tensorTransport h M (t ⊗ₜ[R, f] m) = t ⊗ₜ[R, g] m := rfl

theorem tensorTransport_eq_eqToHom {f g : R →+* T} (h : f = g)
    (M : ModuleCat.{u} R) :
    tensorTransport h M =
      eqToHom (congrArg (fun k : R →+* T => (ModuleCat.extendScalars k).obj M) h) := by
  subst g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul t m => rfl
  | add x y hx hy =>
    change (tensorTransport rfl M).hom x = x at hx
    change (tensorTransport rfl M).hom y = y at hy
    change (tensorTransport rfl M).hom (x + y) = x + y
    rw [map_add, hx, hy]

end Module.FaithfullyFlat
