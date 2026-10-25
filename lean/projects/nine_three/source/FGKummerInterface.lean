import EllipticCurves.MordellWeil
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace FourCorner.FGKummer

variable {G : Type*} [AddCommGroup G] {M : Type*} [CommGroup M]

/-- The additive version of any faithfully transported Kummer map has the
actual doubling subgroup as its kernel. -/
theorem additive_kernel (δ : Multiplicative G →* M)
    (hker : δ.ker = (nsmulAddMonoidHom (α := G) 2).range.toSubgroup) :
    δ.toAdditiveRight.ker = (nsmulAddMonoidHom (α := G) 2).range := by
  ext P
  change δ (Multiplicative.ofAdd P) = 1 ↔ P ∈ _
  change Multiplicative.ofAdd P ∈ δ.ker ↔ P ∈ _
  rw [hker]
  rfl

/-- This equality uses the whole image, including points not represented by
rational two-torsion. -/
theorem quotient_card_eq_range (δ : Multiplicative G →* M)
    (hker : δ.ker = (nsmulAddMonoidHom (α := G) 2).range.toSubgroup) :
    Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) 2).range) =
      Nat.card δ.toAdditiveRight.range := by
  rw [← additive_kernel δ hker]
  exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange δ.toAdditiveRight).toEquiv

/-- A finite list covering every actual point image bounds the actual quotient. -/
theorem quotient_card_le_of_image_mem (δ : Multiplicative G →* M)
    (hker : δ.ker = (nsmulAddMonoidHom (α := G) 2).range.toSubgroup)
    (S : Finset M) (hS : ∀ P : G, δ (Multiplicative.ofAdd P) ∈ S) :
    Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) 2).range) ≤ S.card := by
  classical
  rw [quotient_card_eq_range δ hker]
  let f : δ.toAdditiveRight.range → {m : M // m ∈ S} :=
    fun y => ⟨Additive.toMul y.val, by
      obtain ⟨P, hP⟩ := y.property
      change δ.toAdditiveRight P = y.val at hP
      rw [← hP]
      exact hS P⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact Additive.toMul.injective (congrArg (fun z : {m : M // m ∈ S} => z.val) h)
  have hcard := Nat.card_le_card_of_injective f hf
  simpa using hcard

section Elliptic
open Polynomial WeierstrassCurve.Affine
variable {K : Type*} [Field K] [DecidableEq K]
    {W : WeierstrassCurve.Affine K} [W.IsCharNeTwoNF] [W.IsElliptic]

/-- Three distinct rational roots give four actual rational two-torsion points,
independently of any coincidences among their Kummer images. -/
theorem two_torsion_card_of_split (r : Fin 3 → K) (hr : Function.Injective r)
    (hf : W.f = ∏ i : Fin 3, (X - C (r i))) :
    Nat.card (nsmulAddMonoidHom (α := W.Point) 2).ker = 4 := by
  have hroot (x : K) : W.f.eval x = 0 ↔ ∃ i : Fin 3, x = r i := by
    rw [hf]
    classical
    simp [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]
  let f : Fin 3 → {x : K // W.f.eval x = 0} :=
    fun i => ⟨r i, (hroot (r i)).mpr ⟨i, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro i j h
    exact hr (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨i, hi⟩ := (hroot x.val).mp x.property
    exact ⟨i, Subtype.ext hi.symm⟩
  have hc : Nat.card {x : K // W.f.eval x = 0} = 3 := by
    rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
    simp
  rw [card_ker_nsmul_two, hc]

end Elliptic

end FourCorner.FGKummer

#print axioms FourCorner.FGKummer.additive_kernel
#print axioms FourCorner.FGKummer.quotient_card_eq_range
#print axioms FourCorner.FGKummer.quotient_card_le_of_image_mem

#print axioms FourCorner.FGKummer.two_torsion_card_of_split
