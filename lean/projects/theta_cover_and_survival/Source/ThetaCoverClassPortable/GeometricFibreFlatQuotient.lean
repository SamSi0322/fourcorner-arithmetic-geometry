import ThetaCoverClassPortable.FlatTransport
import ThetaCoverClassPortable.GeometricFibres
import ThetaCoverClassPortable.NoetherianIdealInduction
import ThetaCoverClassPortable.RegularQuotientFlat

/-!
Regularity on every algebraically closed fibre gives a regular element and a
flat hypersurface quotient over a Noetherian base. All ideal cancellation is
proved internally; neither fibre regularity over arbitrary quotients nor
flatness of the hypersurface is an input.
-/
noncomputable section
set_option autoImplicit false
open scoped TensorProduct nonZeroDivisors
universe u v

namespace FourCorner.GeometricFibreFlatQuotient

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Flat A B]

/-- A regular element of the actual residue-field tensor algebra cancels
modulo the actual extension of the corresponding prime ideal. -/
theorem prime_ideal_cancellation (g : B) (p : Ideal A) [p.IsPrime]
    (hg : g ⊗ₜ[A] (1 : p.ResidueField) ∈ nonZeroDivisors (B ⊗[A] p.ResidueField))
    (x : B) (hx : g * x ∈ p.map (algebraMap A B)) :
    x ∈ p.map (algebraMap A B) := by
  let i : B →ₐ[A] B ⊗[A] p.ResidueField := Algebra.TensorProduct.includeLeft
  have hker : RingHom.ker i.toRingHom = p.map (algebraMap A B) :=
    FlatTransport.ker_includeLeft_residueField p
  have hix : i (g * x) = 0 := by
    change g * x ∈ RingHom.ker i.toRingHom
    rwa [hker]
  have hz : i x = 0 := by
    apply (mem_nonZeroDivisors_iff.mp hg).1
    change i g * i x = 0
    rwa [← map_mul]
  rw [← hker]
  exact hz

/-- Noetherian induction, with the genuine flat colon and residue-field
kernel lemmas, proves cancellation modulo every extended ideal. -/
theorem all_ideal_cancellation [IsNoetherianRing A] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      g ⊗ₜ[A] (1 : K) ∈ nonZeroDivisors (B ⊗[A] K)) :
    ∀ (I : Ideal A) (x : B),
      g * x ∈ I.map (algebraMap A B) → x ∈ I.map (algebraMap A B) := by
  apply IdealInduction.all_ideal_cancellation g
  · intro p hp
    letI : p.IsPrime := hp
    exact prime_ideal_cancellation g p (GeometricFibres.residueField_regular g hg p)
  · exact FlatTransport.mem_map_colon_singleton_of_mul_mem

/-- The full algebraic statement: no Noetherian, finite-type, finite-module or
faithful-flatness assumption is imposed on B. -/
theorem regular_and_flat_quotient [IsNoetherianRing A] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      g ⊗ₜ[A] (1 : K) ∈ nonZeroDivisors (B ⊗[A] K)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) :=
  RegularQuotientFlat.regular_and_quotient_flat_of_allIdeal_regular g
    (all_ideal_cancellation g hg)

end FourCorner.GeometricFibreFlatQuotient

/-- Native caller spelling. For the geometric caller, Noetherian A is derived
from the affine open of its already locally Noetherian base scheme. -/
theorem Module.Flat.mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Flat A B] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      g ⊗ₜ[A] (1 : K) ∈ nonZeroDivisors (B ⊗[A] K)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) :=
  FourCorner.GeometricFibreFlatQuotient.regular_and_flat_quotient g hg

