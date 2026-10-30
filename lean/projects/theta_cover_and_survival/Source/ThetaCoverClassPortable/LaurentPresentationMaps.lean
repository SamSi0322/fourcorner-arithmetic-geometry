import ThetaCoverClassPortable.LaurentFreeLocalizations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial LaurentPolynomial
universe u
namespace FourCorner.FiniteMapCohomology
variable {R : Type u} [CommRing R] {ι : Type*} [Fintype ι]
  (S : TwoChartCech.Sections (laurentCover R))

/-- A genuine presentation by the literal finite free standard twist. All
maps, both restriction squares and all three surjectivity assertions are
actual data; no cohomology finiteness is contained in this structure. -/
structure LaurentPresentation (d : ℤ) (ι : Type*) [Fintype ι] where
  negative : (ι → R[X]) →ₗ[R[X]] S.M0
  positive : (ι → R[X]) →ₗ[R[X]] S.M1
  overlap : (ι → LaurentPolynomial R) →ₗ[LaurentPolynomial R] S.M01
  comm_negative : ∀ p, S.r0 (negative p) = overlap ((freeTwistSections (R := R) (ι := ι) d).r0 p)
  comm_positive : ∀ p, S.r1 (positive p) = overlap ((freeTwistSections (R := R) (ι := ι) d).r1 p)
  surjective_negative : Function.Surjective negative
  surjective_positive : Function.Surjective positive
  surjective_overlap : Function.Surjective overlap

/-- The overlap map is the actual Laurent-linear combination of the
restrictions of the selected positive-chart sections. -/
def overlapCombination (x : ι → S.M1) : (ι → LaurentPolynomial R) →ₗ[LaurentPolynomial R] S.M01 :=
  Fintype.linearCombination (LaurentPolynomial R) (fun i => S.r1 (x i))

 theorem positive_combination_comm (x : ι → S.M1) (p : ι → R[X]) :
    S.r1 (Fintype.linearCombination R[X] x p) =
      overlapCombination S x (fun i => Polynomial.toLaurent (p i)) := by
  change S.r1 (∑ i, p i • x i) = ∑ i, Polynomial.toLaurent (p i) • S.r1 (x i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact S.r1_smul (p i) (x i)

 theorem negative_combination_comm (d : ℤ) (x : ι → S.M1) (y : ι → S.M0)
    (hxy : ∀ i, S.r1 (x i) = (T (-d) : LaurentPolynomial R) • S.r0 (y i)) (p : ι → R[X]) :
    S.r0 (Fintype.linearCombination R[X] y p) =
      overlapCombination S x ((freeTwistSections (R := R) (ι := ι) d).r0 p) := by
  change S.r0 (∑ i, p i • y i) =
    ∑ i, (T d * LaurentPolynomial.invert (Polynomial.toLaurent (p i))) • S.r1 (x i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [S.r0_smul,hxy i,smul_smul]
  change LaurentPolynomial.invert (Polynomial.toLaurent (p i)) • S.r0 (y i) = _
  congr 1
  rw [mul_right_comm,←T_add,add_neg_cancel,T_zero,one_mul]

 theorem overlapCombination_surjective (x : ι → S.M1)
    (hx : Submodule.span R[X] (Set.range x) = ⊤) (hlocal : PositiveLocalizes S) :
    Function.Surjective (overlapCombination S x) := by
  intro z
  obtain ⟨k,m,hm⟩ := positive_clearing S hlocal z
  have hm' : S.r1 m = (T (k:ℤ) : LaurentPolynomial R) • z := by
    simpa only [Units.smul_def,laurentVariableUnit_pow] using hm
  obtain ⟨p,hp⟩ := ((span_range_eq_top_iff_surjective_fintypeLinearCombination R[X] x).mp hx) m
  refine ⟨fun i => T (-(k:ℤ)) * Polynomial.toLaurent (p i),?_⟩
  change overlapCombination S x ((T (-(k:ℤ)) : LaurentPolynomial R) • (fun i => Polynomial.toLaurent (p i))) = z
  rw [map_smul,←positive_combination_comm,hp,hm',smul_smul,←T_add,neg_add_cancel,T_zero,one_smul]

 def presentationOfGenerators (d : ℤ) (x : ι → S.M1) (y : ι → S.M0)
    (hxy : ∀ i, S.r1 (x i) = (T (-d) : LaurentPolynomial R) • S.r0 (y i))
    (hx : Submodule.span R[X] (Set.range x) = ⊤)
    (hy : Submodule.span R[X] (Set.range y) = ⊤) (hlocal : PositiveLocalizes S) :
    LaurentPresentation S d ι where
  negative := Fintype.linearCombination R[X] y
  positive := Fintype.linearCombination R[X] x
  overlap := overlapCombination S x
  comm_negative := negative_combination_comm S d x y hxy
  comm_positive := positive_combination_comm S x
  surjective_negative := (span_range_eq_top_iff_surjective_fintypeLinearCombination R[X] y).mp hy
  surjective_positive := (span_range_eq_top_iff_surjective_fintypeLinearCombination R[X] x).mp hx
  surjective_overlap := overlapCombination_surjective S x hx hlocal

 theorem exists_laurent_presentation
    [Module.Finite R[X] S.M0] [Module.Finite R[X] S.M1]
    (h0 : NegativeLocalizes S) (h1 : PositiveLocalizes S) :
    ∃ (n a b : ℕ), Nonempty (LaurentPresentation S (-(n:ℤ)) (Fin a ⊕ Fin b)) := by
  obtain ⟨n,a,b,x,y,hxy,hx,hy⟩ := laurent_common_twist_generators S h0 h1
  refine ⟨n,a,b,⟨presentationOfGenerators S (-(n:ℤ)) x y ?_ hx hy h1⟩⟩
  intro i
  simpa only [neg_neg,Units.smul_def,laurentVariableUnit_pow] using hxy i

namespace LaurentPresentation
variable {S} {d : ℤ} (p : LaurentPresentation S d ι)
def cochain0 : ((ι → R[X]) × (ι → R[X])) →ₗ[R] (S.M0 × S.M1) :=
  (p.negative.restrictScalars R).prodMap (p.positive.restrictScalars R)
def cochain1 : (ι → LaurentPolynomial R) →ₗ[R] S.M01 := p.overlap.restrictScalars R

 theorem cochain0_surjective : Function.Surjective p.cochain0 := by
  rintro ⟨x,y⟩
  obtain ⟨a,ha⟩ := p.surjective_negative x
  obtain ⟨b,hb⟩ := p.surjective_positive y
  exact ⟨(a,b),Prod.ext ha hb⟩

 theorem cochain1_surjective : Function.Surjective p.cochain1 := p.surjective_overlap

 theorem cochain_comm : S.cechDiff.comp p.cochain0 =
    p.cochain1.comp (freeTwistSections (R := R) (ι := ι) d).cechDiff := by
  apply LinearMap.ext
  intro z
  change S.cechDiff (p.cochain0 z) = p.overlap ((freeTwistSections (R := R) (ι := ι) d).cechDiff z)
  rw [TwoChartCech.Sections.cechDiff_apply]
  change S.r1 (p.positive z.2) - S.r0 (p.negative z.1) =
    p.overlap ((freeTwistSections (R := R) (ι := ι) d).cechDiff z)
  rw [TwoChartCech.Sections.cechDiff_apply,map_sub,←p.comm_positive,←p.comm_negative]
end LaurentPresentation
end FourCorner.FiniteMapCohomology
