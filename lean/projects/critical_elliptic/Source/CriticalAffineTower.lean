import CriticalSquareclasses

noncomputable section
namespace FourCorner.CriticalAffineTower
open Polynomial CriticalSquareclasses CriticalAffineGeometry
open Biquadratic.CoordinateAlgebra
variable {k : Type*} [Field k]
abbrev tower (i : k) := CoordinateRing k[X] (qB i) (qC i)
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

def toAffine (i : k) : tower i →ₐ[k] ring i :=
  liftAlgHom k[X] (ring i) (Polynomial.aeval (coordinate i 0)) (qB i) (qC i)
    (coordinate i 1) (coordinate i 2) (by
      have h := (coordinate_equations i).1
      simp only [qB,quadratic,map_add,map_mul,map_pow,aeval_X,aeval_C,map_sub,map_one] at h ⊢
      linear_combination h) (by
      have h := (coordinate_equations i).2
      simp only [qC,quadratic,map_add,map_mul,map_pow,aeval_X,aeval_C,map_neg,map_add,map_one] at h ⊢
      linear_combination h)

def toTower (i : k) : ring i →ₐ[k] tower i :=
  ofCoordinates i (algebraMap k[X] (tower i) X)
    (coordinate₁ k[X] (qB i) (qC i)) (coordinate₂ k[X] (qB i) (qC i)) (by
      rw [coordinate₁_sq]
      change algebraMap k[X] (tower i) (C i*X^2+C (1-i))-1=_
      simp only [map_add,map_mul,map_pow]
      have hc (a : k) : algebraMap k[X] (tower i) (C a)=algebraMap k (tower i) a := rfl
      rw [hc,hc]
      simp only [map_sub,map_one]
      ring) (by
      rw [coordinate₂_sq]
      change algebraMap k[X] (tower i) (C (1+i)*X^2+C (-i))-1=_
      simp only [map_add,map_mul,map_pow]
      have hc (a : k) : algebraMap k[X] (tower i) (C a)=algebraMap k (tower i) a := rfl
      rw [hc,hc]
      simp only [map_neg,map_add,map_one,hc]
      ring)

lemma affine_hom_ext {S : Type*} [CommRing S] [Algebra k S] (i : k)
    (f g : ring i →ₐ[k] S) (h : ∀ j,f (coordinate i j)=g (coordinate i j)) : f=g := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact (f.commutes a).trans (g.commutes a).symm
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp => simpa only [map_mul,coordinate] using congrArg₂ (·*·) hp (h j)

lemma toAffine_coeff (i : k) (p : k[X]) :
    toAffine i (algebraMap k[X] (tower i) p)=Polynomial.aeval (coordinate i 0) p := by
  simp [toAffine,liftAlgHom_apply,lift_algebraMap]

lemma toAffine_root1 (i : k) : toAffine i (coordinate₁ k[X] (qB i) (qC i))=coordinate i 1 := by
  simp [toAffine,liftAlgHom_apply,lift_coordinate₁]
lemma toAffine_root2 (i : k) : toAffine i (coordinate₂ k[X] (qB i) (qC i))=coordinate i 2 := by
  simp [toAffine,liftAlgHom_apply,lift_coordinate₂]

lemma affine_inverse (i : k) : (toAffine i).comp (toTower i)=AlgHom.id k (ring i) := by
  apply affine_hom_ext
  intro j
  fin_cases j
  all_goals simp only [AlgHom.comp_apply,toTower,ofCoordinates_coordinate,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  · exact (toAffine_coeff i X).trans (Polynomial.aeval_X _)
  · exact toAffine_root1 i
  · exact toAffine_root2 i

lemma tower_inverse (i : k) : (toTower i).comp (toAffine i)=AlgHom.id k (tower i) := by
  suffices hh : ((toTower i).comp (toAffine i)).toRingHom=(AlgHom.id k (tower i)).toRingHom by
    exact AlgHom.ext (fun x=>RingHom.congr_fun hh x)
  apply ringHom_ext k[X] (tower i) (qB i) (qC i)
  · intro p
    change toTower i (toAffine i (algebraMap k[X] (tower i) p))=algebraMap k[X] (tower i) p
    rw [toAffine_coeff]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
    | monomial n a =>
      rw [←Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul,map_pow,aeval_C,aeval_X,AlgHom.commutes]
      have hx : toTower i (coordinate i 0)=algebraMap k[X] (tower i) X :=
        ofCoordinates_coordinate i _ _ _ _ _ 0
      rw [hx]
      rfl
  · change toTower i (toAffine i (coordinate₁ k[X] (qB i) (qC i)))=coordinate₁ k[X] (qB i) (qC i)
    rw [toAffine_root1]
    exact ofCoordinates_coordinate i _ _ _ _ _ 1
  · change toTower i (toAffine i (coordinate₂ k[X] (qB i) (qC i)))=coordinate₂ k[X] (qB i) (qC i)
    rw [toAffine_root2]
    exact ofCoordinates_coordinate i _ _ _ _ _ 2

def equiv (i : k) : ring i ≃ₐ[k] tower i :=
  AlgEquiv.ofAlgHom (toTower i) (toAffine i) (tower_inverse i) (affine_inverse i)
end FourCorner.CriticalAffineTower
#print axioms FourCorner.CriticalAffineTower.equiv
