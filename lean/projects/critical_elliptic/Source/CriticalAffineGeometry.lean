import CriticalProj23
import CriticalProjCoordinates23
import Mathlib.RingTheory.MvPolynomial.Ideal

noncomputable section
namespace FourCorner.CriticalAffineGeometry
open MvPolynomial
variable {k : Type*} [Field k]
abbrev ambient (k : Type*) [CommRing k] := MvPolynomial (Fin 3) k

def equation (i : k) : Fin 2 → ambient k
  | 0 => X 1^2-1-C i*(X 0^2-1)
  | 1 => X 2^2-1-C (1+i)*(X 0^2-1)
def ideal (i : k) : Ideal (ambient k) := Ideal.span (Set.range (equation i))
abbrev ring (i : k) := ambient k ⧸ ideal i
instance (i : k) : Algebra k (ring i) := Ideal.Quotient.algebra k
def coordinate (i : k) (j : Fin 3) : ring i := Ideal.Quotient.mk _ (X j)

theorem relation (i : k) (j : Fin 2) : Ideal.Quotient.mk (ideal i) (equation i j)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)

theorem coordinate_equations (i : k) :
    coordinate i 1^2-1=algebraMap k (ring i) i*(coordinate i 0^2-1) ∧
    coordinate i 2^2-1=algebraMap k (ring i) (1+i)*(coordinate i 0^2-1) := by
  have h0 := relation i 0
  have h1 := relation i 1
  simp only [equation,map_sub,map_pow,map_mul,map_one] at h0 h1
  exact ⟨sub_eq_zero.mp h0,sub_eq_zero.mp h1⟩

theorem coordinate_generates (i : k) : Algebra.adjoin k (Set.range (coordinate i))=⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C a => exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => simpa only [map_add] using Subalgebra.add_mem _ (hp trivial) (hq trivial)
  | mul_X p j hp =>
    simpa only [map_mul,coordinate] using Subalgebra.mul_mem _ (hp trivial) (Algebra.subset_adjoin (show coordinate i j∈Set.range (coordinate i) from ⟨j,rfl⟩))

def ofCoordinates {S : Type*} [CommRing S] [Algebra k S] (i : k) (a b c : S)
    (hb : b^2-1=algebraMap k S i*(a^2-1))
    (hc : c^2-1=algebraMap k S (1+i)*(a^2-1)) : ring i →ₐ[k] S :=
  Ideal.Quotient.liftₐ (ideal i) (MvPolynomial.aeval ![a,b,c]) (by
    have h : ideal i ≤ RingHom.ker (MvPolynomial.aeval ![a,b,c]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j,rfl⟩
      fin_cases j
      · simpa [equation] using sub_eq_zero.mpr hb
      · simpa [equation] using sub_eq_zero.mpr hc
    exact fun x hx => h hx)


@[simp] theorem ofCoordinates_coordinate {S : Type*} [CommRing S] [Algebra k S]
    (i : k) (a b c : S) (hb : b^2-1=algebraMap k S i*(a^2-1))
    (hc : c^2-1=algebraMap k S (1+i)*(a^2-1)) (j : Fin 3) :
    ofCoordinates i a b c hb hc (coordinate i j)=![a,b,c] j := by
  change MvPolynomial.aeval ![a,b,c] (X j)=_
  exact MvPolynomial.aeval_X _ _

end FourCorner.CriticalAffineGeometry
#print axioms FourCorner.CriticalAffineGeometry.coordinate_equations
#print axioms FourCorner.CriticalAffineGeometry.coordinate_generates
#print axioms FourCorner.CriticalAffineGeometry.ofCoordinates
