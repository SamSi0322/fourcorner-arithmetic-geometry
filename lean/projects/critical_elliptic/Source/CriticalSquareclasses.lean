import CriticalAffineGeometry
import geometry.SquarefreeRatFunc
import geometry.BiquadraticCoordinateAlgebra
import Mathlib.FieldTheory.Separable

noncomputable section
namespace FourCorner.CriticalSquareclasses
open Polynomial
variable {k : Type*} [Field k]
def quadratic (A B : k) : k[X] := C A*X^2+C B
def qB (i : k) := quadratic i (1-i)
def qC (i : k) := quadratic (1+i) (-i)

theorem quadratic_separable {A B : k} (hA : A≠0) (hB : B≠0) (h2 : (2:k)≠0) :
    (quadratic A B).Separable := by
  rw [separable_def]
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed k (AlgebraicClosure k)
    (quadratic A B) (derivative (quadratic A B))).mpr
  intro z
  by_contra! h
  have hz : z=0 := by
    simpa [quadratic,derivative_mul,derivative_pow,hA,h2] using h.2
  have hB' : algebraMap k (AlgebraicClosure k) B≠0 := (_root_.map_ne_zero _).mpr hB
  exact hB' (by simpa [quadratic,hz] using h.1)

theorem quadratic_nonunit {A B : k} (hA : A≠0) : ¬IsUnit (quadratic A B) := by
  intro h
  have hd : (quadratic A B).natDegree=2 := by
    rw [quadratic,natDegree_add_C,natDegree_C_mul hA,natDegree_X_pow]
  have hz := natDegree_eq_zero_of_isUnit h
  omega

theorem coprime (i : k) : IsCoprime (qB i) (qC i) := by
  refine ⟨C (1+i),-C i,?_⟩
  simp only [qB,qC,quadratic,map_add,map_sub,map_neg,map_one]
  ring

theorem independent (i : k) (hi : i^2= -1) (h2 : (2:k)≠0) :
    Biquadratic.IndependentSquareclasses (RatFunc k)
      (algebraMap k[X] (RatFunc k) (qB i)) (algebraMap k[X] (RatFunc k) (qC i)) := by
  have hi0 := CriticalElliptic23.iota_nonzero i hi
  have him := CriticalElliptic23.iota_ne_one i hi h2
  have hip := CriticalElliptic23.iota_add_one_nonzero i hi h2
  have hs : 1-i≠0 := sub_ne_zero.mpr (Ne.symm him)
  have hb : (qB i).Separable := quadratic_separable hi0 hs h2
  have hc : (qC i).Separable := quadratic_separable hip (neg_ne_zero.mpr hi0) h2
  have hbu : ¬IsUnit (qB i) := quadratic_nonunit hi0
  have hcu : ¬IsUnit (qC i) := quadratic_nonunit hip
  refine ⟨CoverFields.squarefree_not_isSquare_fraction _ hb.squarefree hbu,
    CoverFields.squarefree_not_isSquare_fraction _ hc.squarefree hcu,?_⟩
  rw [←map_mul]
  apply CoverFields.squarefree_not_isSquare_fraction _ ((hb.mul hc (coprime i)).squarefree)
  intro h
  exact hbu (isUnit_of_mul_isUnit_left h)
end FourCorner.CriticalSquareclasses
#print axioms FourCorner.CriticalSquareclasses.independent
