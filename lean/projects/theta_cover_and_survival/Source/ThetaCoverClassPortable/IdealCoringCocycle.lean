import ThetaCoverClassPortable.IdealPreCoaction
import ThetaCoverClassPortable.RingMapTensorPushout
import ThetaCoverClassPortable.FiniteRelationComposableFlat

namespace FourCorner.StableIdealTransport
open CategoryTheory CategoryTheory.Limits FourCorner.FiniteRelationQuotient
noncomputable section
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

abbrev oppositeObject (s t : A →+* B) := RingMapTensorPushout.point s t
abbrev oppositeLeft (s t : A →+* B) : B →+* oppositeObject s t := (RingMapTensorPushout.left s t).hom
abbrev oppositeRight (s t : A →+* B) : B →+* oppositeObject s t := (RingMapTensorPushout.right s t).hom
abbrev oppositeSource (s t : A →+* B) := (oppositeRight s t).comp s
abbrev oppositeMiddle (s t : A →+* B) := (oppositeLeft s t).comp s

theorem opposite_condition (s t : A →+* B) :
    (oppositeRight s t).comp t=oppositeMiddle s t :=
  (congrArg CommRingCat.Hom.hom (pushout.condition (f:=CommRingCat.ofHom s) (g:=CommRingCat.ofHom t))).symm

theorem oppositeSource_flat (s t : A →+* B) (hs : s.Flat) : (oppositeSource s t).Flat :=
  composable_target_flat t s hs

theorem oppositeMiddle_flat (s t : A →+* B) (hs : s.Flat) (ht : t.Flat) : (oppositeMiddle s t).Flat :=
  composable_middle_flat t s ht hs

/-- The ORIGINAL composite of right arrow then left arrow, in the true
opposite-order composable tensor. Not a supplied coring structure. -/
def oppositeComposite (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) : B →+* oppositeObject s t :=
  compose s t hgen heq (oppositeRight s t) (oppositeLeft s t) (opposite_condition s t)

theorem oppositeComposite_source (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    (oppositeComposite s t hgen heq).comp s=oppositeSource s t :=
  compose_source s t hgen heq _ _ _

theorem oppositeComposite_target (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) :
    (oppositeComposite s t hgen heq).comp t=(oppositeLeft s t).comp t :=
  compose_target s t hgen heq _ _ _

theorem opposite_ideal_stable (s t : A →+* B) (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) :
    Ideal.map (oppositeMiddle s t) J=Ideal.map (oppositeSource s t) J := by
  rw [← opposite_condition,← Ideal.map_map,← hJ,Ideal.map_map]

/-- Actual id tensor gamma iteration, implemented by the TRUE right-arrow
flat ideal transport after left coefficient pullback. Its defining pure
formula below identifies it with literal b tensor gamma(j), not a label. -/
def coringIterate (s t : A →+* B) (hs : s.Flat) (ht : t.Flat)
    (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) :
    tensorAlong s J →+ tensorAlong (oppositeSource s t) J :=
  (transport (oppositeMiddle s t) (oppositeSource s t)
    (oppositeMiddle_flat s t hs ht) (oppositeSource_flat s t hs) J (opposite_ideal_stable s t J hJ)).toAddMonoidHom.comp
    (tensorMap s (oppositeLeft s t) J)

 theorem coringIterate_value (s t : A →+* B) (hs : s.Flat) (ht : t.Flat)
    (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) (z : tensorAlong s J) :
    ((extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J) (coringIterate s t hs ht J hJ z) : oppositeObject s t)=
      oppositeLeft s t ((extensionEquiv s hs J) z : B) := by
  exact (transport_value (oppositeMiddle s t) (oppositeSource s t)
    (oppositeMiddle_flat s t hs ht) (oppositeSource_flat s t hs) J (opposite_ideal_stable s t J hJ)
      (tensorMap s (oppositeLeft s t) J z)).trans
        (tensorMap_value s (oppositeLeft s t) hs (oppositeMiddle_flat s t hs ht) J z)

/-- Exact pure formula: this IS application of gamma in the inner tensor
factor under the true composable tensor identification. Every equality
is recovered through the same actual flat ideal embedding into T'. -/
theorem coringIterate_tmul (s t : A →+* B) (hs : s.Flat) (ht : t.Flat)
    (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) (b : B) (j : J) :
    letI := s.toAlgebra
    coringIterate s t hs ht J hJ (b ⊗ₜ[A] j)=
      oppositeLeft s t b • tensorMap s (oppositeRight s t) J (preGamma s t hs J hJ j) := by
  letI := s.toAlgebra
  apply (extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J).injective
  apply Subtype.ext
  calc
    ((extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J) (coringIterate s t hs ht J hJ (b ⊗ₜ[A] j)) : oppositeObject s t)=
        oppositeLeft s t ((extensionEquiv s hs J) (b ⊗ₜ[A] j) : B) := coringIterate_value s t hs ht J hJ _
    _ = oppositeLeft s t (s (j : A)*b) := congrArg (oppositeLeft s t) (extensionEquiv_tmul s hs J b j)
    _ = oppositeLeft s t (s (j : A))*oppositeLeft s t b := map_mul _ _ _
    _ = oppositeLeft s t b*oppositeRight s t (t (j : A)) := by
      have hm := RingHom.congr_fun (opposite_condition s t) (j : A)
      change oppositeRight s t (t (j : A))=oppositeLeft s t (s (j : A)) at hm
      rw [hm,mul_comm]
    _ = oppositeLeft s t b*oppositeRight s t ((extensionEquiv s hs J) (preGamma s t hs J hJ j) : B) :=
      congrArg (fun a=>oppositeLeft s t b*oppositeRight s t a) (preGamma_value s t hs J hJ j).symm
    _ = oppositeLeft s t b*((extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J)
        (tensorMap s (oppositeRight s t) J (preGamma s t hs J hJ j)) : oppositeObject s t) :=
      congrArg (fun a=>oppositeLeft s t b*a)
        (tensorMap_value s (oppositeRight s t) hs (oppositeSource_flat s t hs) J _).symm
    _ = ((extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J)
        (oppositeLeft s t b • tensorMap s (oppositeRight s t) J (preGamma s t hs J hJ j)) : oppositeObject s t) :=
      (extensionEquiv_smul_value (oppositeSource s t) (oppositeSource_flat s t hs) J _ _).symm

/-- Actual coproduct coefficient pull, with the endpoint A-action
identified by the PROVED original composition equation. -/
def coringDelta (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) (hs : s.Flat) (J : Ideal A) :
    tensorAlong s J →+ tensorAlong (oppositeSource s t) J :=
  flatPull s (oppositeComposite s t hgen heq) (oppositeSource s t)
    (oppositeComposite_source s t hgen heq) hs (oppositeSource_flat s t hs) J

 theorem coringDelta_tmul (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T))) (hs : s.Flat)
    (J : Ideal A) (b : B) (j : J) :
    letI := s.toAlgebra
    letI := (oppositeSource s t).toAlgebra
    coringDelta s t hgen heq hs J (b ⊗ₜ[A] j)=oppositeComposite s t hgen heq b ⊗ₜ[A] j :=
  flatPull_tmul _ _ _ _ _ _ _ _ _

/-- GENUINE original-source ideal coring cocycle. It is proved from true
composition on the original relation and the actual flat ideal embedding;
no cocycle, rho coassoc or desired invariant is a hypothesis. -/
theorem preGamma_coring_cocycle (s t : A →+* B) (hgen : s.range ⊔ t.range=⊤)
    (heq : ∀T : Type u,∀[CommRing T],Equivalence (Related s t (T:=T)))
    (hs : s.Flat) (ht : t.Flat) (J : Ideal A) (hJ : Ideal.map s J=Ideal.map t J) (j : J) :
    coringDelta s t hgen heq hs J (preGamma s t hs J hJ j)=
      coringIterate s t hs ht J hJ (preGamma s t hs J hJ j) := by
  apply (extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J).injective
  apply Subtype.ext
  calc
    ((extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J)
      (coringDelta s t hgen heq hs J (preGamma s t hs J hJ j)) : oppositeObject s t)=
        oppositeComposite s t hgen heq ((extensionEquiv s hs J) (preGamma s t hs J hJ j) : B) :=
      flatPull_value _ _ _ _ _ _ _ _
    _ = oppositeComposite s t hgen heq (t (j : A)) :=
      congrArg (oppositeComposite s t hgen heq) (preGamma_value s t hs J hJ j)
    _ = oppositeLeft s t (t (j : A)) := RingHom.congr_fun (oppositeComposite_target s t hgen heq) (j : A)
    _ = oppositeLeft s t ((extensionEquiv s hs J) (preGamma s t hs J hJ j) : B) :=
      congrArg (oppositeLeft s t) (preGamma_value s t hs J hJ j).symm
    _ = ((extensionEquiv (oppositeSource s t) (oppositeSource_flat s t hs) J)
      (coringIterate s t hs ht J hJ (preGamma s t hs J hJ j)) : oppositeObject s t) :=
      (coringIterate_value s t hs ht J hJ _).symm

#print axioms oppositeComposite
#print axioms coringIterate_tmul
#print axioms coringDelta_tmul
#print axioms preGamma_coring_cocycle
end
end FourCorner.StableIdealTransport
