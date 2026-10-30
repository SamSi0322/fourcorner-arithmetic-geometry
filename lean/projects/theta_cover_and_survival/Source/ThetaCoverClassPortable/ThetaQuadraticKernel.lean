import ThetaCoverClassPortable.FiniteJacobianSmooth
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Morphisms.Etale
noncomputable section
namespace FourCorner.ThetaQuadraticKernel
open Algebra AlgebraicGeometry MvPolynomial
universe u
variable {R : Type u} [CommRing R]
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def equation (b : R) (_ : Fin 1) : MvPolynomial (Fin 1) R := X 0^2-C b
def ideal (b : R) : Ideal (MvPolynomial (Fin 1) R) := Ideal.span (Set.range (equation b))
abbrev Q (b : R) := MvPolynomial (Fin 1) R ⧸ ideal b
instance (b : R) : Algebra R (Q b) := Ideal.Quotient.algebra R
def root (b : R) : Q b := Ideal.Quotient.mk _ (X 0)
lemma root_sq (b : R) : root b^2=algebraMap R (Q b) b := by
  have h : Ideal.Quotient.mk (ideal b) (equation b 0)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)
  change Ideal.Quotient.mk (ideal b) (X 0)^2=Ideal.Quotient.mk (ideal b) (C b)
  simpa only [equation,map_sub,map_pow,sub_eq_zero] using h

def polynomial (b : R) : Polynomial R := Polynomial.X^2-Polynomial.C b
lemma polynomial_monic (b : R) : (polynomial b).Monic := Polynomial.monic_X_pow_sub_C _ (by decide)
def polynomialEquiv : MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R := uniqueAlgEquiv R (Fin 1)
lemma ideal_map (b : R) : Ideal.span {polynomial b}=(ideal b).map (polynomialEquiv (R:=R)).toRingHom := by
  rw [ideal,Ideal.map_span]
  have he : (polynomialEquiv (R:=R)) '' Set.range (equation b)={polynomial b} := by
    ext p
    simp only [Set.mem_image,Set.mem_range,Set.mem_singleton_iff]
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      simp [polynomialEquiv,equation,polynomial,uniqueAlgEquiv]
    · intro hp
      subst p
      exact ⟨equation b 0,⟨0,rfl⟩,by simp [polynomialEquiv,equation,polynomial,uniqueAlgEquiv]⟩
  change Ideal.span {polynomial b}=Ideal.span ((polynomialEquiv (R:=R)) '' Set.range (equation b))
  rw [he]
def adjoinEquiv (b : R) : Q b ≃ₐ[R] AdjoinRoot (polynomial b) :=
  Ideal.quotientEquivAlg (ideal b) (Ideal.span {polynomial b}) polynomialEquiv (ideal_map b)
lemma finite (b : R) : Module.Finite R (Q b) := by
  haveI := (polynomial_monic b).finite_adjoinRoot
  exact Module.Finite.equiv (adjoinEquiv b).symm.toLinearEquiv
lemma free (b : R) : Module.Free R (Q b) := by
  haveI := (polynomial_monic b).free_adjoinRoot
  exact Module.Free.of_equiv (adjoinEquiv b).symm.toLinearEquiv
lemma root_unit (b : R) (hb : IsUnit b) : IsUnit (root b) := by
  let v : R := ↑hb.unit⁻¹
  have hv : b*v=1 := by
    have hh:=congrArg (fun z : Rˣ => (z:R)) (mul_inv_cancel hb.unit)
    simpa only [Units.val_mul,Units.val_one,v,hb.unit_spec] using hh
  apply IsUnit.of_mul_eq_one (root b*algebraMap R (Q b) v)
  rw [←mul_assoc,←pow_two,root_sq,←map_mul,hv,map_one]

def pres (b : R) : PreSubmersivePresentation R (Q b) (Fin 1) (Fin 1) :=
  .naive (v:=equation b) id Function.injective_id
lemma jacobian (b : R) : (pres b).jacobian=2*root b := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have he : (pres b).jacobiMatrix=fun r c=>pderiv r (equation b c) := by
    apply Matrix.ext
    intro r c
    exact PreSubmersivePresentation.jacobiMatrix_apply (pres b) r c
  rw [he,Matrix.det_fin_one]
  change Ideal.Quotient.mk (ideal b) (pderiv 0 (X 0^2-C b))=2*root b
  simp [root,pderiv_pow,map_ofNat]
lemma etale (b : R) (hb : IsUnit b) (h2 : IsUnit (2:R)) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap R (Q b)))) := by
  have hj : IsUnit (pres b).jacobian := by
    rw [jacobian]
    exact (h2.map (algebraMap R (Q b))).mul (root_unit b hb)
  have hs : Ideal.span (Set.range (fun _ : Fin 1=>(pres b).jacobian))=⊤ := by
    rw [Set.range_const,Ideal.span_singleton_eq_top]
    exact hj
  apply (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero _).mpr
  simpa using FiniteJacobianSmooth.spec_smooth_of_jacobian_span (fun _ : Fin 1=>pres b) hs

def ofRoot {S : Type u} [CommRing S] [Algebra R S] (b : R) (s : S)
    (hs : s^2=algebraMap R S b) : Q b →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval (fun _=>s)) (by
    have h : ideal b≤RingHom.ker (aeval (fun _ : Fin 1=>s)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      simpa [equation] using sub_eq_zero.mpr hs
    exact fun x hx=>h hx)
@[simp] lemma ofRoot_root {S : Type u} [CommRing S] [Algebra R S] (b : R) (s : S)
    (hs : s^2=algebraMap R S b) : ofRoot b s hs (root b)=s := aeval_X _ _
lemma hom_ext {b : R} {S : Type u} [CommRing S] [Algebra R S] {f g : Q b →ₐ[R] S}
    (h : f (root b)=g (root b)) : f=g := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction p using MvPolynomial.induction_on with
  | C a => exact (f.commutes a).trans (g.commutes a).symm
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p a hp =>
    have hx : f (Ideal.Quotient.mk _ (X a))=g (Ideal.Quotient.mk _ (X a)) := by
      have ha : a=0 := Subsingleton.elim _ _
      subst a
      exact h
    simpa only [map_mul] using congrArg₂ (·*·) hp hx

def basisTwo [Nontrivial R] (b : R) : Module.Basis (Fin 2) R (Q b) := by
  have hd : (polynomial b).natDegree=2 := by
    simp [polynomial,Polynomial.natDegree_X_pow_sub_C]
  let e : Fin (polynomial b).natDegree ≃ Fin 2 := finCongr hd
  exact (((AdjoinRoot.powerBasis' (polynomial_monic b)).basis).reindex e).map
    (adjoinEquiv b).symm.toLinearEquiv
end FourCorner.ThetaQuadraticKernel
#print axioms FourCorner.ThetaQuadraticKernel.finite
#print axioms FourCorner.ThetaQuadraticKernel.etale

#print axioms FourCorner.ThetaQuadraticKernel.basisTwo
