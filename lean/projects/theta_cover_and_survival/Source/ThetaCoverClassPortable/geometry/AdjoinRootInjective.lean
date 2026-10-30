import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-!
# Injective coordinate presentations by monic root adjunctions

Injective base change preserves a monic polynomial quotient: its canonical
representatives are remainders, and taking those remainders commutes with base
change. Evaluation into a field is then injective when the polynomial after base
change is irreducible.
-/

noncomputable section

namespace FourCorner.AdjoinRootInjective

open Polynomial

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Canonical base change sends a polynomial class to the mapped class. -/
theorem map_mk (i : R →+* S) (p f : R[X]) :
    AdjoinRoot.map i p (p.map i) dvd_rfl (AdjoinRoot.mk p f) =
      AdjoinRoot.mk (p.map i) (f.map i) := by
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map,
    ← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

/-- The canonical remainder representative commutes with monic base change. -/
theorem modByMonicHom_map (i : R →+* S) (p : R[X]) (hp : p.Monic)
    (x : AdjoinRoot p) :
    AdjoinRoot.modByMonicHom (hp.map i) (AdjoinRoot.map i p (p.map i) dvd_rfl x) =
      (AdjoinRoot.modByMonicHom hp x).map i := by
  induction x using AdjoinRoot.induction_on with
  | ih f =>
    rw [map_mk, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
      Polynomial.map_modByMonic i hp]

/-- Injective base change induces an injective map on a monic polynomial quotient.
Irreducibility is not required for this statement. -/
theorem map_injective (i : R →+* S) (hi : Function.Injective i)
    (p : R[X]) (hp : p.Monic) :
    Function.Injective (AdjoinRoot.map i p (p.map i) dvd_rfl) := by
  intro x y h
  apply (AdjoinRoot.mk_leftInverse hp).injective
  apply Polynomial.map_injective i hi
  have hm := congrArg (AdjoinRoot.modByMonicHom (hp.map i)) h
  exact (modByMonicHom_map i p hp x).symm.trans
    (hm.trans (modByMonicHom_map i p hp y))

end BaseChange

/-- A monic coordinate quotient evaluates injectively into a field if its
polynomial becomes irreducible over an injectively embedded intermediate field. -/
theorem lift_injective_of_monic_of_irreducible_map
    {R S E : Type*} [CommRing R] [Field S] [Field E]
    (i : R →+* S) (hi : Function.Injective i) (p : R[X]) (hp : p.Monic)
    (j : S →+* E) (r : E) (hirr : Irreducible (p.map i))
    (hroot : p.eval₂ (j.comp i) r = 0) :
    Function.Injective (AdjoinRoot.lift (j.comp i) r hroot) := by
  have : Fact (Irreducible (p.map i)) := ⟨hirr⟩
  have hroot' : (p.map i).eval₂ j r = 0 := by
    simpa only [Polynomial.eval₂_map] using hroot
  have heq : AdjoinRoot.lift (j.comp i) r hroot =
      (AdjoinRoot.lift j r hroot').comp (AdjoinRoot.map i p (p.map i) dvd_rfl) := by
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp
    · simp
  rw [heq]
  exact (AdjoinRoot.lift j r hroot').injective.comp (map_injective i hi p hp)

end FourCorner.AdjoinRootInjective

#print axioms FourCorner.AdjoinRootInjective.map_injective
#print axioms FourCorner.AdjoinRootInjective.lift_injective_of_monic_of_irreducible_map
