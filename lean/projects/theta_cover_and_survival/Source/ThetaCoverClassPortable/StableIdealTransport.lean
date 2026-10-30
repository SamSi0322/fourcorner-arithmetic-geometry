import ThetaCoverClassPortable.FlatIdealTensorEquiv

namespace FourCorner.StableIdealTransport
noncomputable section
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

/-- Distinct actual scalar structures are retained in these tensor types,
even though their first underlying ring is B in both cases. -/
def tensorAlong (f : A →+* B) (I : Ideal A) : Type u :=
  letI := f.toAlgebra
  B ⊗[A] I

instance tensorAlongAddCommGroup (f : A →+* B) (I : Ideal A) : AddCommGroup (tensorAlong f I) := by
  letI := f.toAlgebra
  unfold tensorAlong
  infer_instance
instance tensorAlongModule (f : A →+* B) (I : Ideal A) : Module B (tensorAlong f I) := by
  letI := f.toAlgebra
  unfold tensorAlong
  infer_instance

 def extensionEquiv (f : A →+* B) (hf : letI := f.toAlgebra;Module.Flat A B) (I : Ideal A) :
    tensorAlong f I ≃ₗ[B] Ideal.map f I := by
  letI := f.toAlgebra
  letI := hf
  exact FourCorner.FlatIdealTensorEquiv.idealTensorEquiv I

/-- The REAL transport of an actual ideal layer from source pullback to
target pullback, derived from source/target flatness and the proved exact
ideal equality. Neither a descent datum nor its cocycle is assumed. -/
def transport (s t : A →+* B)
    (hs : letI := s.toAlgebra;Module.Flat A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (I : Ideal A) (hI : Ideal.map s I=Ideal.map t I) :
    tensorAlong s I ≃ₗ[B] tensorAlong t I :=
  (extensionEquiv s hs I).trans ((LinearEquiv.ofEq _ _ hI).trans (extensionEquiv t ht I).symm)

/-- Transport preserves the literal element in B represented by an ideal
tensor. This identity is what will prove source composition/cocycle by
injectivity, rather than assuming a module cocycle as a certificate. -/
theorem transport_value (s t : A →+* B)
    (hs : letI := s.toAlgebra;Module.Flat A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (I : Ideal A) (hI : Ideal.map s I=Ideal.map t I) (z : tensorAlong s I) :
    ((extensionEquiv t ht I) (transport s t hs ht I hI z) : B)=
      ((extensionEquiv s hs I) z : B) := by
  simp only [transport,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.coe_ofEq_apply]

 theorem transport_trans (s t v : A →+* B)
    (hs : letI := s.toAlgebra;Module.Flat A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (hv : letI := v.toAlgebra;Module.Flat A B)
    (I : Ideal A) (hst : Ideal.map s I=Ideal.map t I) (htv : Ideal.map t I=Ideal.map v I)
    (z : tensorAlong s I) :
    transport t v ht hv I htv (transport s t hs ht I hst z)=
      transport s v hs hv I (hst.trans htv) z := by
  apply (extensionEquiv v hv I).injective
  apply Subtype.ext
  rw [transport_value,transport_value,transport_value]

 theorem transport_self (s : A →+* B)
    (hs : letI := s.toAlgebra;Module.Flat A B) (I : Ideal A) (z : tensorAlong s I) :
    transport s s hs hs I rfl z=z := by
  apply (extensionEquiv s hs I).injective
  apply Subtype.ext
  exact transport_value s s hs hs I rfl z

#print axioms extensionEquiv
#print axioms transport
#print axioms transport_value
#print axioms transport_trans
#print axioms transport_self
end
end FourCorner.StableIdealTransport
