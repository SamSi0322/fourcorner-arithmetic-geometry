import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic

noncomputable section
namespace FourCorner.QuadraticUnitIntegralClosure
open Polynomial Module
variable {R F E : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field F] [Field E] [Algebra R F] [Algebra F E] [Algebra R E]
  [IsScalarTower R F E] [IsFractionRing R F] [FiniteDimensional F E]

set_option maxHeartbeats 1000000

/-- A genuine primitive quadratic square root has the displayed minimal polynomial. -/
theorem minpoly_eq (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2) :
    minpoly F r=X^2-C (algebraMap R F u) := by
  have hrF : r^2=algebraMap F E (algebraMap R F u) := by
    simpa only [← IsScalarTower.algebraMap_apply R F E] using hr
  have hi : IsIntegral F r := ⟨X^2-C (algebraMap R F u),monic_X_pow_sub_C _ (by decide),by simp [hrF]⟩
  have hdeg : (minpoly F r).natDegree=2 :=
    (PowerBasis.ofAdjoinEqTop hi hgen).finrank.symm.trans hdim
  symm
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) (monic_X_pow_sub_C _ (by decide))
  · exact minpoly.dvd F r (by simp [hrF])
  · simp [hdeg]

/-- Every actual element of the quadratic field has two field coordinates. -/
theorem coordinates (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2) (z : E) :
    ∃ m n : F,z=algebraMap F E m+algebraMap F E n*r := by
  have hm := minpoly_eq u r hr hgen hdim
  have hi : IsIntegral F r := IsIntegral.of_finite F r
  obtain ⟨f,hf,hz⟩ := (PowerBasis.ofAdjoinEqTop hi hgen).exists_eq_aeval z
  change f.natDegree<(minpoly F r).natDegree at hf
  rw [hm,natDegree_X_pow_sub_C] at hf
  have hdeg : f.natDegree≤1 := by omega
  refine ⟨f.coeff 0,f.coeff 1,?_⟩
  rw [eq_X_add_C_of_natDegree_le_one hdeg] at hz
  simpa [add_comm] using hz

theorem trace_root (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2) :
    Algebra.trace F E r=0 := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff,minpoly_eq u r hr hgen hdim]
  simp [Polynomial.nextCoeff]

theorem trace_coordinates (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2) (m n : F) :
    Algebra.trace F E (algebraMap F E m+algebraMap F E n*r)=2*m := by
  rw [map_add,← Algebra.smul_def,LinearMap.map_smul,trace_root u r hr hgen hdim,
    smul_zero,add_zero,Algebra.trace_algebraMap,hdim]
  simp [nsmul_eq_mul]

/-- Trace integrality recovers both actual field coordinates inside the
normal base ring, because 2 and the radicand are units. -/
theorem integral_coordinates (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) (z : E) (hz : IsIntegral R z) :
    ∃ m n : R,z=algebraMap R E m+algebraMap R E n*r := by
  have hrI : IsIntegral R r := by
    apply IsIntegral.of_pow (show 0<(2 : ℕ) by decide)
    rw [hr]
    exact isIntegral_algebraMap
  obtain ⟨m,n,hcoords⟩ := coordinates u r hr hgen hdim z
  have ht : Algebra.trace F E z=2*m := by rw [hcoords]; exact trace_coordinates u r hr hgen hdim m n
  have hrz : r*z=algebraMap F E (n*algebraMap R F u)+algebraMap F E m*r := by
    rw [hcoords,map_mul]
    have hrF : r^2=algebraMap F E (algebraMap R F u) := by
      simpa only [← IsScalarTower.algebraMap_apply R F E] using hr
    linear_combination (algebraMap F E n)*hrF
  have htrz : Algebra.trace F E (r*z)=2*algebraMap R F u*n := by
    rw [hrz,trace_coordinates u r hr hgen hdim]
    ring
  obtain ⟨a,ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R:=R) (K:=F) (Algebra.isIntegral_trace hz)
  obtain ⟨b,hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R:=R) (K:=F) (Algebra.isIntegral_trace (hrI.mul hz))
  obtain ⟨i2,hi2⟩ := h2.exists_right_inv
  obtain ⟨iu,hiu⟩ := hu.exists_right_inv
  have hi2F : (2 : F)*algebraMap R F i2=1 := by simpa only [map_mul,map_ofNat,map_one] using congrArg (algebraMap R F) hi2
  have hiuF : algebraMap R F u*algebraMap R F iu=1 := by simpa only [map_mul,map_one] using congrArg (algebraMap R F) hiu
  have hm : algebraMap R F (a*i2)=m := by
    rw [map_mul,ha,ht]
    linear_combination m*hi2F
  have hn : algebraMap R F (b*i2*iu)=n := by
    rw [map_mul,map_mul,hb,htrz]
    linear_combination (algebraMap R F u*n*algebraMap R F iu)*hi2F+n*hiuF
  refine ⟨a*i2,b*i2*iu,?_⟩
  rw [hcoords,IsScalarTower.algebraMap_apply R F E,hm,
    IsScalarTower.algebraMap_apply R F E,hn]

/-- The actual integral closure, with generation proved rather than assumed. -/
theorem integralClosure_eq_adjoin (u : R) (r : E) (hr : r^2=algebraMap R E u)
    (hgen : Algebra.adjoin F {r}=⊤) (hdim : Module.finrank F E=2)
    (hu : IsUnit u) (h2 : IsUnit (2 : R)) :
    integralClosure R E=Algebra.adjoin R {r} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨m,n,hcoords⟩ := integral_coordinates u r hr hgen hdim hu h2 z hz
    rw [hcoords]
    exact (Algebra.adjoin R {r}).add_mem ((Algebra.adjoin R {r}).algebraMap_mem m)
      ((Algebra.adjoin R {r}).mul_mem ((Algebra.adjoin R {r}).algebraMap_mem n)
        (Algebra.subset_adjoin (by simp)))
  · apply adjoin_le_integralClosure
    apply IsIntegral.of_pow (show 0<(2 : ℕ) by decide)
    rw [hr]
    exact isIntegral_algebraMap

#print axioms minpoly_eq
#print axioms coordinates
#print axioms trace_root
#print axioms trace_coordinates
#print axioms integral_coordinates
#print axioms integralClosure_eq_adjoin
end FourCorner.QuadraticUnitIntegralClosure
