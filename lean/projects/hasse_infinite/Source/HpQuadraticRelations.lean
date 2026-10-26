import HpCanonicalBasis

namespace FourCorner.HpQuadraticRelations
open AlgebraicCurve HpLiteralField HpFieldGeometry HpRootProductBasis HpCanonicalBasis
noncomputable section
variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
attribute [local instance] Classical.propDecidable
local instance constantModule (p : K) : Module K (field K p) := Algebra.toModule

abbrev Pair := {ij : Fin 5 × Fin 5 // ij.1 < ij.2}
def pairSupport (ij : Pair) : Finset (Fin 4) := coordinateSupport ij.val.1 ∪ coordinateSupport ij.val.2
def mixedSupport : Option Pair → Finset (Fin 4)
  | none => ∅
  | some ij => pairSupport ij

theorem mixedSupport_injective : Function.Injective mixedSupport := by decide

theorem coordinate_mul (p : K) (ij : Pair) :
    coordinate K p ij.val.1*coordinate K p ij.val.2=monomial K p (pairSupport ij) := by
  unfold coordinate pairSupport monomial
  apply (Finset.prod_union _).symm
  have hd : ∀ij : Pair, Disjoint (coordinateSupport ij.val.1) (coordinateSupport ij.val.2) := by decide
  exact hd ij

theorem mixed_independent (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0) :
    LinearIndependent (RatFunc K) (fun j : Option Pair => monomial K p (mixedSupport j)) :=
  (monomials_linearIndependent K p hp ha hb).comp mixedSupport mixedSupport_injective

/-- No nontrivial off-diagonal quadratic combination can be a rational function of rho. -/
theorem mixed_relation (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (a : RatFunc K) (c : Pair → RatFunc K) :
    algebraMap (RatFunc K) (field K p) a +
      ∑ij,algebraMap (RatFunc K) (field K p) (c ij)*coordinate K p ij.val.1*coordinate K p ij.val.2=0
      ↔ a=0 ∧ ∀ij,c ij=0 := by
  constructor
  · intro h
    let g : Option Pair → RatFunc K := fun j => j.elim a c
    have hh : ∑j : Option Pair,g j • monomial K p (mixedSupport j)=0 := by
      rw [Fintype.sum_option]
      simp_rw [mul_assoc,coordinate_mul K p] at h
      simpa only [g,Option.elim_none,Option.elim_some,mixedSupport,Algebra.smul_def,
        monomial,Finset.prod_empty,mul_one] using h
    have hz := Fintype.linearIndependent_iff.mp (mixed_independent K p hp ha hb) g hh
    exact ⟨hz none,fun ij => hz (some ij)⟩
  · rintro ⟨rfl,hc⟩
    simp [hc]

/-- The exact linear coefficients of the literal five canonical-coordinate squares. -/
def slope (p : K) : Fin 5 → K := ![p,2*(p-1),2*(p+1),p-1,0]
def intercept (p : K) : Fin 5 → K := ![0,-2*(p-1),2*(p+1),p+1,1]

theorem coordinate_sq (p : K) (i : Fin 5) :
    coordinate K p i^2=algebraMap (RatFunc K) (field K p)
      (algebraMap K (RatFunc K) (slope K p i)*RatFunc.X+algebraMap K (RatFunc K) (intercept K p i)) := by
  fin_cases i <;> simp [coordinate,coordinateSupport,monomial,slope,intercept,root_sq,radicand,poly,
    map_mul,map_sub,map_add,map_ofNat,RatFunc.algebraMap_X,RatFunc.algebraMap_C,mul_sub,mul_add] <;> ring

def slopeSum (p : K) (d : Fin 5 → K) : K := ∑i,d i*slope K p i
def interceptSum (p : K) (d : Fin 5 → K) : K := ∑i,d i*intercept K p i

theorem diagonal_sum (p : K) (d : Fin 5 → K) :
    (∑i,algebraMap K (field K p) (d i)*coordinate K p i^2)=
    algebraMap (RatFunc K) (field K p)
      (algebraMap K (RatFunc K) (slopeSum K p d)*RatFunc.X+algebraMap K (RatFunc K) (interceptSum K p d)) := by
  simp only [slopeSum,interceptSum,map_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinate_sq]
  change algebraMap (RatFunc K) (field K p) (algebraMap K (RatFunc K) (d i)) * _ = _
  rw [← map_mul]
  congr 1
  simp only [map_mul]
  ring

theorem linear_rational_eq_zero (a b : K) :
    algebraMap K (RatFunc K) a*RatFunc.X+algebraMap K (RatFunc K) b=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro h
    have hh : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a*Polynomial.X+Polynomial.C b)=0 := by
      simpa only [map_add,map_mul,RatFunc.algebraMap_X,RatFunc.algebraMap_C,RatFunc.algebraMap_eq_C] using h
    have hj : Polynomial.C a*Polynomial.X+Polynomial.C b=0 :=
      (IsFractionRing.injective (Polynomial K) (RatFunc K)) (by simpa only [map_zero] using hh)
    have h1 := congrArg (fun f : (Polynomial K) => f.coeff 1) hj
    have h0 := congrArg (fun f : (Polynomial K) => f.coeff 0) hj
    exact ⟨by simpa using h1,by simpa using h0⟩
  · rintro ⟨rfl,rfl⟩
    simp

/-- The entire quadratic relation space has no cross terms, and its diagonal part is
exactly the kernel of the two literal coefficient functionals. -/
theorem quadratic_relation_iff (p : K) (hp : p ≠ 0) (ha : p-1 ≠ 0) (hb : p+1 ≠ 0)
    (d : Fin 5 → K) (c : Pair → K) :
    (∑i,algebraMap K (field K p) (d i)*coordinate K p i^2)+
      (∑ij,algebraMap K (field K p) (c ij)*coordinate K p ij.val.1*coordinate K p ij.val.2)=0
    ↔ (∀ij,c ij=0) ∧ slopeSum K p d=0 ∧ interceptSum K p d=0 := by
  rw [diagonal_sum]
  have he (ij : Pair) : algebraMap K (field K p) (c ij)=
      algebraMap (RatFunc K) (field K p) (algebraMap K (RatFunc K) (c ij)) :=
    (IsScalarTower.algebraMap_apply K (RatFunc K) (field K p) (c ij)).symm
  simp_rw [he]
  rw [mixed_relation K p hp ha hb,linear_rational_eq_zero]
  simp only [map_eq_zero]
  tauto

#print axioms mixed_relation
#print axioms coordinate_sq
#print axioms quadratic_relation_iff
end
end FourCorner.HpQuadraticRelations
