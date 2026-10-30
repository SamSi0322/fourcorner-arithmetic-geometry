import QuadraticUnitIntegralClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
namespace FourCorner.QuadraticUnitResidueAlgebra
open Polynomial Module QuadraticUnitIntegralClosure
variable {R F E : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field F] [Field E] [Algebra R F] [Algebra F E] [Algebra R E]
  [IsScalarTower R F E] [IsFractionRing R F] [FiniteDimensional F E]
set_option maxHeartbeats 1500000

theorem rootIntegral (u : R) (r : E) (hr : r^2=algebraMap R E u) : IsIntegral R r := by
  apply IsIntegral.of_pow (show 0<(2 : ℕ) by decide)
  rw [hr]
  exact isIntegral_algebraMap

theorem minpoly_base (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2) :
    minpoly R r=X^2-C u := by
  apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' F (rootIntegral u r hr),minpoly_eq u r hr hgen hdim]
  simp

/-- Genuine monogenic presentation of the actual integral closure. -/
def presentation (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    AdjoinRoot (X^2-C u) ≃ₐ[R] integralClosure R E := by
  letI : IsTorsionFree R E := Module.IsTorsionFree.trans_faithfulSMul R F E
  exact ((AdjoinRoot.algEquivOfEq R (X^2-C u) (minpoly R r) (minpoly_base u r hr hgen hdim).symm).trans
    (minpoly.equivAdjoin (rootIntegral u r hr))).trans
    (Subalgebra.equivOfEq _ _ (integralClosure_eq_adjoin u r hr hgen hdim hu h2).symm)

theorem presentation_root (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    ((presentation u r hr hgen hdim hu h2 (AdjoinRoot.root (X^2-C u)) : integralClosure R E) : E)=r := by
  simp [presentation,AdjoinRoot.algEquivOfEq_root,minpoly.equivAdjoin,AdjoinRoot.Minpoly.toAdjoin]

/-- The integral closure has actual power basis {1,r}. -/
def powerBasis (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) : PowerBasis R (integralClosure R E) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C u (by decide : (2 : ℕ) ≠ 0))).map
    (presentation u r hr hgen hdim hu h2)

theorem powerBasis_dim (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    (powerBasis u r hr hgen hdim hu h2).dim=2 := by
  simp [powerBasis,AdjoinRoot.powerBasis'_dim]

theorem powerBasis_gen (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    (((powerBasis u r hr hgen hdim hu h2).gen : integralClosure R E) : E)=r := by
  simpa only [powerBasis,PowerBasis.map_gen,AdjoinRoot.powerBasis'_gen] using
    presentation_root u r hr hgen hdim hu h2

/-- Genuine residue fibre algebra over any ideal, with closure generation
and its quadratic presentation proved above rather than assumed. -/
def residuePresentation (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) (I : Ideal R) :
    ((integralClosure R E) ⧸ I.map (algebraMap R (integralClosure R E))) ≃ₐ[R]
      AdjoinRoot (X^2-C (Ideal.Quotient.mk I u)) := by
  let f : R[X] := X^2-C u
  let e := presentation u r hr hgen hdim hu h2
  have heI : I.map (algebraMap R (integralClosure R E))=
      (I.map (AdjoinRoot.of f)).map e.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro a
    change algebraMap R (integralClosure R E) a=e (algebraMap R (AdjoinRoot (X^2-C u)) a)
    exact (e.commutes a).symm
  let q := Ideal.quotientEquivAlg (I.map (AdjoinRoot.of f))
    (I.map (algebraMap R (integralClosure R E))) e heI
  have hmap : f.map (Ideal.Quotient.mk I)=X^2-C (Ideal.Quotient.mk I u) := by simp [f]
  exact q.symm.trans ((AdjoinRoot.quotEquivQuotMap f I).trans
    ((AdjoinRoot.algEquivOfEq (R ⧸ I) _ _ hmap).restrictScalars R))

#print axioms minpoly_base
#print axioms presentation
#print axioms presentation_root
#print axioms powerBasis
#print axioms powerBasis_dim
#print axioms powerBasis_gen
#print axioms residuePresentation
end FourCorner.QuadraticUnitResidueAlgebra
