import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Finiteness.Descent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
open TensorProduct
namespace FourCorner.QuasiFiniteFpqc

/-- Genuine descent of finite residue-field fibres. No finite type,
Noetherianity, freeness, or desired quasi-finiteness is assumed. -/
theorem quasiFinite_of_faithfullyFlat_baseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.FaithfullyFlat R S]
    [Algebra.QuasiFinite S (S ⊗[R] T)] : Algebra.QuasiFinite R T := by
  constructor
  intro P hP
  obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B:=S) P
  letI : Q.IsPrime := hQ
  letI : Q.LiesOver P := hQP
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  let e : Q.Fiber (S ⊗[R] T) ≃ₐ[Q.ResidueField]
      Q.ResidueField ⊗[P.ResidueField] (P.Fiber T) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  letI : Module.Finite Q.ResidueField (Q.Fiber (S ⊗[R] T)) := inferInstance
  letI : Module.Finite Q.ResidueField (Q.ResidueField ⊗[P.ResidueField] (P.Fiber T)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat Q.ResidueField

#print axioms quasiFinite_of_faithfullyFlat_baseChange
end FourCorner.QuasiFiniteFpqc

