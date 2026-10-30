import ThetaCoverClassPortable.StableIdealTransportNaturality

namespace FourCorner.StableIdealTransport
noncomputable section
open scoped TensorProduct
universe u
variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]

 def mappedIdealHom (f : A →+* B) (g : B →+* T) (v : A →+* T)
    (hgv : g.comp f=v) (J : Ideal A) : Ideal.map f J →+ Ideal.map v J where
  toFun z := ⟨g (z : B),by
    rw [← hgv,← Ideal.map_map]
    exact Ideal.mem_map_of_mem g z.property⟩
  map_zero' := by apply Subtype.ext;exact map_zero g
  map_add' z w := by apply Subtype.ext;exact map_add g _ _

/-- The actual coefficient tensor pullback with its target A-action
identified by a PROVED ring-hom identity. Its pure formula is proved below. -/
def flatPull (f : A →+* B) (g : B →+* T) (v : A →+* T) (hgv : g.comp f=v)
    (hf : letI := f.toAlgebra;Module.Flat A B)
    (hv : letI := v.toAlgebra;Module.Flat A T) (J : Ideal A) :
    tensorAlong f J →+ tensorAlong v J :=
  (extensionEquiv v hv J).symm.toAddMonoidHom.comp
    ((mappedIdealHom f g v hgv J).comp (extensionEquiv f hf J).toAddMonoidHom)

 theorem flatPull_value (f : A →+* B) (g : B →+* T) (v : A →+* T) (hgv : g.comp f=v)
    (hf : letI := f.toAlgebra;Module.Flat A B)
    (hv : letI := v.toAlgebra;Module.Flat A T) (J : Ideal A) (z : tensorAlong f J) :
    ((extensionEquiv v hv J) (flatPull f g v hgv hf hv J z) : T)=g ((extensionEquiv f hf J) z : B) := by
  change ((extensionEquiv v hv J) ((extensionEquiv v hv J).symm _ ) : T)=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

 theorem flatPull_tmul (f : A →+* B) (g : B →+* T) (v : A →+* T) (hgv : g.comp f=v)
    (hf : letI := f.toAlgebra;Module.Flat A B)
    (hv : letI := v.toAlgebra;Module.Flat A T) (J : Ideal A) (b : B) (j : J) :
    letI := f.toAlgebra
    letI := v.toAlgebra
    flatPull f g v hgv hf hv J (b ⊗ₜ[A] j)=g b ⊗ₜ[A] j := by
  letI := f.toAlgebra
  letI := v.toAlgebra
  apply (extensionEquiv v hv J).injective
  apply Subtype.ext
  calc
    ((extensionEquiv v hv J) (flatPull f g v hgv hf hv J (b ⊗ₜ[A] j)) : T)=
        g ((extensionEquiv f hf J) (b ⊗ₜ[A] j) : B) := flatPull_value f g v hgv hf hv J _
    _ = g (f (j : A)*b) := congrArg g (extensionEquiv_tmul f hf J b j)
    _ = g (f (j : A))*g b := map_mul g _ _
    _ = v (j : A)*g b := congrArg (fun a=>a*g b) (RingHom.congr_fun hgv (j : A))
    _ = ((extensionEquiv v hv J) (g b ⊗ₜ[A] j) : T) := (extensionEquiv_tmul v hv J (g b) j).symm

 theorem extensionEquiv_smul_value (f : A →+* B)
    (hf : letI := f.toAlgebra;Module.Flat A B) (J : Ideal A) (b : B) (z : tensorAlong f J) :
    ((extensionEquiv f hf J) (b • z) : B)=b*((extensionEquiv f hf J) z : B) := by
  exact congrArg Subtype.val ((extensionEquiv f hf J).map_smul b z)

#print axioms flatPull
#print axioms flatPull_value
#print axioms flatPull_tmul
end
end FourCorner.StableIdealTransport
