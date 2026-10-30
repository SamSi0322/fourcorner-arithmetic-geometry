import ThetaCoverClassPortable.FlatIdealPull

namespace FourCorner.StableIdealTransport
noncomputable section
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

 def targetIdealHom (s t : A →+* B) (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) :
    J →+ Ideal.map s J where
  toFun j := ⟨t (j : A),hJ.symm ▸ Ideal.mem_map_of_mem t j.property⟩
  map_zero' := by apply Subtype.ext;exact map_zero t
  map_add' j k := by apply Subtype.ext;exact map_add t _ _

/-- The actual pre-coaction gamma, as the unique original source-flat
ideal tensor representing t(j) IN ORIGINAL B. No coaction identity input. -/
def preGamma (s t : A →+* B) (hs : letI := s.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) : J →+ tensorAlong s J :=
  (extensionEquiv s hs J).symm.toAddMonoidHom.comp (targetIdealHom s t J hJ)

 theorem preGamma_value (s t : A →+* B) (hs : letI := s.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) (j : J) :
    ((extensionEquiv s hs J) (preGamma s t hs J hJ j) : B)=t (j : A) := by
  change ((extensionEquiv s hs J) ((extensionEquiv s hs J).symm _) : B)=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

 theorem preGamma_target_smul (s t : A →+* B) (hs : letI := s.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) (a : A) (j : J) :
    preGamma s t hs J hJ (a • j)=t a • preGamma s t hs J hJ j := by
  apply (extensionEquiv s hs J).injective
  apply Subtype.ext
  rw [preGamma_value,extensionEquiv_smul_value,preGamma_value]
  exact map_mul t a (j : A)

/-- True A-linearity with the TARGET A-action on B_s tensor J retained
independently from the SOURCE A-action inside the tensor type. -/
def preGammaLinear (s t : A →+* B) (hs : letI := s.toAlgebra;Module.Flat A B)
    (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) :
    letI : Module A (tensorAlong s J) := Module.compHom (tensorAlong s J) t
    J →ₗ[A] tensorAlong s J := by
  letI : Module A (tensorAlong s J) := Module.compHom (tensorAlong s J) t
  exact {preGamma s t hs J hJ with map_smul':=preGamma_target_smul s t hs J hJ}

#print axioms preGamma
#print axioms preGamma_value
#print axioms preGamma_target_smul
#print axioms preGammaLinear
end
end FourCorner.StableIdealTransport
