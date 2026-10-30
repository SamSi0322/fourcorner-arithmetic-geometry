import CriticalAffineDomain
import geometry.PolynomialCoordinateBaseChange

noncomputable section
namespace FourCorner.CriticalAffineBaseChange
open Polynomial CriticalSquareclasses CriticalAffineTower
open Multiquadratic.CoordinateAlgebra Multiquadratic.BaseChange
open scoped TensorProduct

section Generic
variable {A S R T : Type*} [CommRing A] [CommRing S] [CommRing R] [CommRing T]
    [Algebra A S] [Algebra A R] [Algebra S T]
def stage₂EquivOfImages (e : S ⊗[A] R ≃ₐ[S] T) (a b : R) (a' b' : T)
    (ha : e (1 ⊗ₜ[A] a)=a') (hb : e (1 ⊗ₜ[A] b)=b') :
    S ⊗[A] Stage₂ R a b ≃ₐ[S] Stage₂ T a' b' := by
  subst a' b'
  exact stage₂Equiv e a b
end Generic

variable {k : Type*} [Field k] (i : k) (L : Type*) [Field L] [Algebra k L]

def towerEquiv : L ⊗[k] tower i ≃ₐ[L] tower (algebraMap k L i) :=
  stage₂EquivOfImages (polyEquivTensor' k L).symm (qB i) (qC i)
    (qB (algebraMap k L i)) (qC (algebraMap k L i))
    (by simp [qB,quadratic]) (by simp [qC,quadratic])

/-- The actual literal affine quotient, with its native ordered coordinate
presentation, commutes with EVERY extension of constants. -/
def affineEquiv : L ⊗[k] CriticalAffineGeometry.ring i ≃ₐ[L]
    CriticalAffineGeometry.ring (algebraMap k L i) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=L) (A₁:=L)) (CriticalAffineTower.equiv i)).trans
    ((towerEquiv i L).trans (CriticalAffineTower.equiv (algebraMap k L i)).symm)

theorem isDomain_tensor (hi : i^2= -1) (h2 : (2:k)≠0) :
    IsDomain (L ⊗[k] CriticalAffineGeometry.ring i) := by
  have hiL : (algebraMap k L i)^2= -(1:L) := by rw [←map_pow,hi,map_neg,map_one]
  have h2L : (2:L)≠0 := by simpa only [map_ofNat] using (_root_.map_ne_zero (algebraMap k L)).mpr h2
  letI := CriticalAffineDomain.ring_isDomain (algebraMap k L i) hiL h2L
  exact Function.Injective.isDomain (affineEquiv i L).toRingHom (affineEquiv i L).injective
end FourCorner.CriticalAffineBaseChange
#print axioms FourCorner.CriticalAffineBaseChange.affineEquiv
#print axioms FourCorner.CriticalAffineBaseChange.isDomain_tensor
