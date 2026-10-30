import ThetaCoverClassPortable.RingMapTensorPushout

namespace FourCorner.TensorRingPoints
open CategoryTheory
noncomputable section
open scoped TensorProduct
universe u
variable {R S A T : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing T]
variable [Algebra R S] [Algebra R A]

abbrev scalarLeg : S →+* S ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
abbrev variableLeg : A →+* S ⊗[R] A := (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom

 theorem legs_compatible :
    (scalarLeg (R:=R) (S:=S) (A:=A)).comp (algebraMap R S)=
      (variableLeg (R:=R) (S:=S) (A:=A)).comp (algebraMap R A) :=
  congrArg CommRingCat.Hom.hom (CommRingCat.isPushout_tensorProduct R S A).w

 theorem hom_ext (f g : S ⊗[R] A →+* T)
    (hS : f.comp scalarLeg=g.comp scalarLeg) (hA : f.comp variableLeg=g.comp variableLeg) : f=g := by
  exact congrArg CommRingCat.Hom.hom ((CommRingCat.isPushout_tensorProduct R S A).hom_ext (k:=CommRingCat.ofHom f) (l:=CommRingCat.ofHom g)
    (CommRingCat.hom_ext hS) (CommRingCat.hom_ext hA))

 theorem hom_lift (f : S →+* T) (g : A →+* T)
    (hc : f.comp (algebraMap R S)=g.comp (algebraMap R A)) :
    ∃φ : S ⊗[R] A →+* T,φ.comp scalarLeg=f ∧ φ.comp variableLeg=g := by
  let h := CommRingCat.isPushout_tensorProduct R S A
  have hw : CommRingCat.ofHom (algebraMap R S) ≫ CommRingCat.ofHom f=
      CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom g := CommRingCat.hom_ext hc
  exact ⟨(h.desc (CommRingCat.ofHom f) (CommRingCat.ofHom g) hw).hom,
    congrArg CommRingCat.Hom.hom (h.inl_desc _ _ hw),
    congrArg CommRingCat.Hom.hom (h.inr_desc _ _ hw)⟩

#print axioms hom_lift
#print axioms hom_ext
end
end FourCorner.TensorRingPoints
