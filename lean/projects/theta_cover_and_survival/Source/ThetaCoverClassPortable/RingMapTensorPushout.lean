import ThetaCoverClassPortable.FiniteRelationTranslationAlgebra
import ThetaCoverClassPortable.ProjectiveAmbientCharpoly

namespace FourCorner.RingMapTensorPushout
open CategoryTheory CategoryTheory.Limits FourCorner.ProjectiveStabilizedDeterminant
open scoped TensorProduct
noncomputable section
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

abbrev point (f : R →+* S) (g : R →+* T) : CommRingCat.{u} :=
  pushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
abbrev left (f : R →+* S) (g : R →+* T) : CommRingCat.of S ⟶ point f g := pushout.inl _ _
abbrev right (f : R →+* S) (g : R →+* T) : CommRingCat.of T ⟶ point f g := pushout.inr _ _
abbrev pointAlgebra (f : R →+* S) (g : R →+* T) : Algebra S (point f g) := (left f g).hom.toAlgebra

/-- Native ring-category pushout equals the ACTUAL tensor base change,
with its original left scalar map. The two maps are kept independently,
even when S and T later have the same underlying type. -/
def tensorEquiv (f : R →+* S) (g : R →+* T) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := pointAlgebra f g
    S ⊗[R] T ≃ₐ[S] point f g := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  let h := CommRingCat.isPushout_tensorProduct R S T
  apply AlgEquiv.ofRingEquiv (f:=h.isoPushout.commRingCatIsoToRingEquiv)
  intro s
  exact congrArg (fun k : CommRingCat.of S ⟶ point f g=>k.hom s) h.inl_isoPushout_hom

 theorem tensorEquiv_left (f : R →+* S) (g : R →+* T) (s : S) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := pointAlgebra f g
    tensorEquiv f g (s ⊗ₜ[R] 1)=(left f g).hom s := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  exact (tensorEquiv f g).commutes s
 theorem tensorEquiv_right (f : R →+* S) (g : R →+* T) (t : T) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := pointAlgebra f g
    tensorEquiv f g (1 ⊗ₜ[R] t)=(right f g).hom t := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  let h := CommRingCat.isPushout_tensorProduct R S T
  exact congrArg (fun k : CommRingCat.of T ⟶ point f g=>k.hom t) h.inr_isoPushout_hom

 theorem tensorEquiv_tmul (f : R →+* S) (g : R →+* T) (s : S) (t : T) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := pointAlgebra f g
    tensorEquiv f g (s ⊗ₜ[R] t)=(left f g).hom s*(right f g).hom t := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  have he : (s ⊗ₜ[R] t : S ⊗[R] T)=(s ⊗ₜ[R] 1)*(1 ⊗ₜ[R] t) := by simp
  rw [he,map_mul,tensorEquiv_left,tensorEquiv_right]

 def pushoutFrame (f : R →+* S) (g : R →+* T)
    (p : letI := g.toAlgebra;Frame R T) :
    letI := pointAlgebra f g;Frame S (point f g) := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  exact transportFrame (baseChangeFrame S p) (tensorEquiv f g).toLinearEquiv

/-- The actual tensor-to-pushout comparison intertwines multiplication
by EVERY original right-ring element, not only its geometric value. -/
theorem multiplication_intertwines (f : R →+* S) (g : R →+* T) (t : T) :
    letI := f.toAlgebra
    letI := g.toAlgebra
    letI := pointAlgebra f g
    (tensorEquiv f g).toLinearMap.comp ((LinearMap.mulLeft R t).baseChange S)=
      (LinearMap.mulLeft S ((right f g).hom t)).comp (tensorEquiv f g).toLinearMap := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := pointAlgebra f g
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s x =>
      change tensorEquiv f g (s ⊗ₜ[R] (t*x))=(right f g).hom t*tensorEquiv f g (s ⊗ₜ[R] x)
      rw [tensorEquiv_tmul,tensorEquiv_tmul,map_mul]
      ac_rfl
  | add z w hz hw =>
      simpa only [map_add,LinearMap.comp_apply,LinearMap.mulLeft_apply,mul_add] using congrArg₂ (·+·) hz hw

#print axioms tensorEquiv
#print axioms pushoutFrame
#print axioms multiplication_intertwines
end
end FourCorner.RingMapTensorPushout
