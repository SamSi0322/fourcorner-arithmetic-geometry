import ThetaCoverClassPortable.StableIdealTransport

namespace FourCorner.StableIdealTransport
noncomputable section
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]

/-- Actual tensor functor on the first ring factor, retaining each source
A-action. Defined even for NONFLAT B→T, by the true balanced tensor map. -/
def tensorMap (f : A →+* B) (g : B →+* T) (I : Ideal A) :
    tensorAlong f I →+ tensorAlong (g.comp f) I := by
  letI := f.toAlgebra
  letI := (g.comp f).toAlgebra
  let h : B →ₗ[A] T :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro a b
        change g (f a*b)=g (f a)*g b
        exact map_mul g _ _ }
  exact (TensorProduct.map h (LinearMap.id : I →ₗ[A] I)).toAddMonoidHom

 theorem tensorMap_tmul (f : A →+* B) (g : B →+* T) (I : Ideal A) (b : B) (j : I) :
    letI := f.toAlgebra
    letI := (g.comp f).toAlgebra
    tensorMap f g I (b ⊗ₜ[A] j)=g b ⊗ₜ[A] j := rfl

 theorem extensionEquiv_tmul (f : A →+* B)
    (hf : letI := f.toAlgebra;Module.Flat A B) (I : Ideal A) (b : B) (j : I) :
    letI := f.toAlgebra
    ((extensionEquiv f hf I) (b ⊗ₜ[A] j) : B)=f (j : A)*b := by
  letI := f.toAlgebra
  letI := hf
  exact FourCorner.FlatIdealTensorEquiv.idealTensorMap_tmul I b j

 theorem tensorMap_value (f : A →+* B) (g : B →+* T)
    (hf : letI := f.toAlgebra;Module.Flat A B)
    (hgf : letI := (g.comp f).toAlgebra;Module.Flat A T)
    (I : Ideal A) (z : tensorAlong f I) :
    ((extensionEquiv (g.comp f) hgf I) (tensorMap f g I z) : T)=g ((extensionEquiv f hf I) z : B) := by
  letI := f.toAlgebra
  letI := (g.comp f).toAlgebra
  let F : tensorAlong f I →+ T :=
    (((Ideal.map (g.comp f) I).subtype.toAddMonoidHom.comp
      (extensionEquiv (g.comp f) hgf I).toAddMonoidHom).comp (tensorMap f g I))
  let G : tensorAlong f I →+ T :=
    g.toAddMonoidHom.comp ((Ideal.map f I).subtype.toAddMonoidHom.comp
      (extensionEquiv f hf I).toAddMonoidHom)
  change F z=G z
  induction z using TensorProduct.induction_on with
  | zero => exact F.map_zero.trans G.map_zero.symm
  | tmul b j =>
      change ((extensionEquiv (g.comp f) hgf I) (tensorMap f g I (b ⊗ₜ[A] j)) : T)=
        g ((extensionEquiv f hf I) (b ⊗ₜ[A] j) : B)
      rw [tensorMap_tmul,extensionEquiv_tmul,extensionEquiv_tmul,map_mul]
      rfl
  | add x y hx hy =>
      exact (F.map_add x y).trans
        ((congrArg₂ (·+·) hx hy).trans (G.map_add x y).symm)

/-- True pullback naturality of the actual ideal transport. Requiring
flatness of the relevant A-actions here is precisely what justifies the
injectivity used in this proof; no flatness of B→T is presumed. -/
theorem transport_natural (s t : A →+* B) (g : B →+* T)
    (hs : letI := s.toAlgebra;Module.Flat A B)
    (ht : letI := t.toAlgebra;Module.Flat A B)
    (hgs : letI := (g.comp s).toAlgebra;Module.Flat A T)
    (hgt : letI := (g.comp t).toAlgebra;Module.Flat A T)
    (I : Ideal A) (hI : Ideal.map s I=Ideal.map t I) (z : tensorAlong s I) :
    tensorMap t g I (transport s t hs ht I hI z)=
      transport (g.comp s) (g.comp t) hgs hgt I
        (by simpa only [Ideal.map_map] using congrArg (Ideal.map g) hI)
        (tensorMap s g I z) := by
  apply (extensionEquiv (g.comp t) hgt I).injective
  apply Subtype.ext
  rw [tensorMap_value t g ht hgt I,transport_value,transport_value,tensorMap_value s g hs hgs I]

#print axioms tensorMap
#print axioms tensorMap_value
#print axioms transport_natural
end
end FourCorner.StableIdealTransport
