import ThetaCoverClassPortable.FiniteJacobianSmooth
import ThetaCoverClassPortable.OppositePostPChartScheme

noncomputable section
namespace FourCorner.OppositeProjective.PostPSmooth
open Algebra MvPolynomial PostPChart OppositeHomogeneousQuadrics OppositePolynomials
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1000000

abbrev ax (mu nu : K) (i : Fin 4) := Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (X i)
instance (mu nu : K) : Algebra K (PostPChart.affineRing mu nu) := Ideal.Quotient.algebra K

def columns : Fin 4 → Fin 3 → Fin 4
  | 0 => ![0,1,2]
  | 1 => ![3,1,2]
  | 2 => ![0,3,2]
  | 3 => ![0,1,3]
lemma columns_injective (i : Fin 4) : Function.Injective (columns i) := by
  fin_cases i <;> decide

def pres (mu nu : K) (i : Fin 4) :
    PreSubmersivePresentation K (PostPChart.affineRing mu nu) (Fin 4) (Fin 3) :=
  .naive (v := PostPChart.affineEquation mu nu) (columns i) (columns_injective i)

lemma pres_jacobi (mu nu : K) (i : Fin 4) :
    (pres mu nu i).jacobiMatrix = fun a b => pderiv (columns i a) (PostPChart.affineEquation mu nu b) := by
  apply Matrix.ext
  intro a b
  exact PreSubmersivePresentation.jacobiMatrix_apply (pres mu nu i) a b

lemma pres_map (mu nu : K) (i : Fin 4) (p : AffineAmbient K) :
    algebraMap (pres mu nu i).Ring (PostPChart.affineRing mu nu) p =
      Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) p := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma jacobian_formula (mu nu : K) (i : Fin 4) :
    (pres mu nu i).jacobian =
      ![16 * algebraMap K _ (A mu nu) * (algebraMap K _ nu)^2 * ax mu nu 0 * ax mu nu 1 * ax mu nu 2,
        8 * ax mu nu 3 * ax mu nu 1 * ax mu nu 2,
        8 * ax mu nu 2 * ((ax mu nu 3)^2 + (algebraMap K _ mu)^2*ax mu nu 3*ax mu nu 0 -
          2*algebraMap K _ (A mu nu)*(algebraMap K _ nu)^2*(ax mu nu 0)^2),
        8 * ax mu nu 1 * (2*algebraMap K _ (A mu nu)*(algebraMap K _ nu)^2*(ax mu nu 0)^2 +
          (algebraMap K _ mu)^2*ax mu nu 3*ax mu nu 0 - (ax mu nu 3)^2)] i := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, pres_map, pres_jacobi]
  have hc (a : K) : Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (C a) =
      algebraMap K (PostPChart.affineRing mu nu) a := rfl
  have hn (n : ℕ) : Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (n : AffineAmbient K) = n :=
    map_natCast _ n
  have h2 : Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (2 : AffineAmbient K) = 2 :=
    map_ofNat _ 2
  have hc2 : algebraMap K (PostPChart.affineRing mu nu) (2 : K) = 2 := map_ofNat _ 2
  rw [Matrix.det_fin_three]
  fin_cases i <;>
    simp [columns, PostPChart.affineEquation, Matrix.det_fin_three, map_add, map_sub, map_mul,
      map_pow, ax, hc, hn, h2, hc2, pderiv_pow] <;> ring




/-- Direct rank criterion on P=1. This includes every point at infinity T=0. -/
theorem scalar_nonzero {mu nu t q r z : K}
    (h0 : z^2 - A mu nu + 2*A mu nu*nu^2*t^2 = 0)
    (h1 : q^2 - 1 - mu^2*t^2 - 2*z*t = 0)
    (h2 : r^2 - 1 - mu^2*t^2 + 2*z*t = 0)
    (hm : mu ≠ 0) (hn : nu ≠ 0) (hA : A mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    16*A mu nu*nu^2*t*q*r ≠ 0 ∨ 8*z*q*r ≠ 0 ∨
      8*r*(z^2+mu^2*z*t-2*A mu nu*nu^2*t^2) ≠ 0 ∨
      8*q*(2*A mu nu*nu^2*t^2+mu^2*z*t-z^2) ≠ 0 := by
  have he0 : z^2 - A mu nu*(1:K)^2 + 2*A mu nu*nu^2*t^2 = 0 := by simpa using h0
  have he1 : q^2 - (1:K)^2 - mu^2*t^2 - 2*z*t = 0 := by simpa using h1
  have he2 : r^2 - (1:K)^2 - mu^2*t^2 + 2*z*t = 0 := by simpa using h2
  have hvec : ¬((1:K)=0 ∧ q=0 ∧ r=0 ∧ z=0 ∧ t=0) := by
    rintro ⟨h,_,_,_,_⟩; exact one_ne_zero h
  by_cases hq : q=0
  · have hr : r ≠ 0 := fun hr => Scalar.not_both_QR_zero he0 he1 he2 hvec hA hS ⟨hq,hr⟩
    have hz := Scalar.Qzero_shift_ne_zero he0 he1 he2 hvec hA hm hq
    refine Or.inr (Or.inr (Or.inl ?_))
    intro hd
    have hold : 8*r*(z+A mu nu*t) = 0 := by
      rw [hq] at h1
      linear_combination -8*r*t*h0 -8*r*z*h1 - t*hd
    exact mul_ne_zero (mul_ne_zero (by norm_num) hr) hz hold
  by_cases hr : r=0
  · have hz := Scalar.Rzero_shift_ne_zero he0 he1 he2 hvec hA hm hr
    refine Or.inr (Or.inr (Or.inr ?_))
    intro hd
    have hold : 8*q*(z-A mu nu*t) = 0 := by
      rw [hr] at h2
      linear_combination 8*q*t*h0 -8*q*z*h2 -t*hd
    exact mul_ne_zero (mul_ne_zero (by norm_num) hq) hz hold
  by_cases hz : z=0
  · have ht : t ≠ 0 := by
      intro ht
      have hh := h0
      simp [hz,ht] at hh
      exact hA hh
    exact Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hA) (pow_ne_zero _ hn)) ht) hq) hr)
  exact Or.inr (Or.inl (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hz) hq) hr))

theorem field_point_jacobian {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hS : S mu nu ≠ 0)
    (F : Type u) [Field F] [Algebra K F] (f : PostPChart.affineRing mu nu →ₐ[K] F) :
    ∃ i : Fin 4, f (pres mu nu i).jacobian ≠ 0 := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let m := algebraMap K F mu
  let n := algebraMap K F nu
  let t := f (ax mu nu 0)
  let q := f (ax mu nu 1)
  let r := f (ax mu nu 2)
  let z := f (ax mu nu 3)
  have hrel (i : Fin 3) : f (Ideal.Quotient.mk (PostPChart.affineIdeal mu nu)
      (PostPChart.affineEquation mu nu i)) = 0 := by
    have hi : Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (PostPChart.affineEquation mu nu i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    exact (congrArg f hi).trans (map_zero f)
  have hc (a : K) : f (Ideal.Quotient.mk (PostPChart.affineIdeal mu nu) (C a)) = algebraMap K F a := f.commutes a
  have h0 : z^2-A m n+2*A m n*n^2*t^2=0 := by
    have h := hrel 0
    simp [PostPChart.affineEquation,hc,map_ofNat,A] at h
    dsimp [z,t,m,n,ax,A]
    linear_combination h
  have h1 : q^2-1-m^2*t^2-2*z*t=0 := by
    have h := hrel 1
    simp [PostPChart.affineEquation,hc,map_ofNat] at h
    dsimp [z,t,q,m,ax]
    linear_combination h
  have h2 : r^2-1-m^2*t^2+2*z*t=0 := by
    have h := hrel 2
    simp [PostPChart.affineEquation,hc,map_ofNat] at h
    dsimp [z,t,r,m,ax]
    linear_combination h
  have hmf : m ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hm
  have hnf : n ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hn
  have haf : A m n ≠ 0 := by simpa [m,n,← A_map] using (map_ne_zero (algebraMap K F)).mpr hA
  have hsf : S m n ≠ 0 := by simpa [m,n,← S_map] using (map_ne_zero (algebraMap K F)).mpr hS
  rcases scalar_nonzero h0 h1 h2 hmf hnf haf hsf with h|h|h|h
  · exact ⟨0, by simpa [jacobian_formula,m,n,t,q,r,z,map_ofNat,← A_map] using h⟩
  · exact ⟨1, by simpa [jacobian_formula,m,n,t,q,r,z,map_ofNat,← A_map] using h⟩
  · exact ⟨2, by simpa [jacobian_formula,m,n,t,q,r,z,map_ofNat,← A_map] using h⟩
  · exact ⟨3, by simpa [jacobian_formula,m,n,t,q,r,z,map_ofNat,← A_map] using h⟩

/-- Full smoothness of the literal P=1 quotient, including all infinity points. -/
theorem affine_smooth {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap K (PostPChart.affineRing mu nu)))) := by
  have hspan := FiniteJacobianSmooth.jacobian_span_of_field_points (pres mu nu)
    (field_point_jacobian hm hn hA hS)
  simpa using FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres mu nu) hspan

end FourCorner.OppositeProjective.PostPSmooth
#print axioms FourCorner.OppositeProjective.PostPSmooth.jacobian_formula

#print axioms FourCorner.OppositeProjective.PostPSmooth.scalar_nonzero
#print axioms FourCorner.OppositeProjective.PostPSmooth.affine_smooth
