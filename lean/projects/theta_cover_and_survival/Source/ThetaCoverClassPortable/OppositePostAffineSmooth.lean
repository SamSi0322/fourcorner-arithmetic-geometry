import ThetaCoverClassPortable.FiniteJacobianSmooth
import ThetaCoverClassPortable.Slot02HighChartIntegral

noncomputable section
namespace FourCorner.OppositeProjective.PostSmooth
open Algebra MvPolynomial HighAffine OppositeHomogeneousQuadrics OppositePolynomials
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1000000

def columns : Fin 4 → Fin 3 → Fin 4
  | 0 => ![0,1,2]
  | 1 => ![3,1,2]
  | 2 => ![0,3,2]
  | 3 => ![0,1,3]
lemma columns_injective (i : Fin 4) : Function.Injective (columns i) := by
  fin_cases i <;> decide

def pres (mu nu : K) (i : Fin 4) :
    PreSubmersivePresentation K (OppositeProjective.affineRing mu nu) (Fin 4) (Fin 3) :=
  .naive (v := affineEquation mu nu) (columns i) (columns_injective i)

lemma pres_jacobi (mu nu : K) (i : Fin 4) :
    (pres mu nu i).jacobiMatrix = fun a b => pderiv (columns i a) (affineEquation mu nu b) := by
  apply Matrix.ext
  intro a b
  exact PreSubmersivePresentation.jacobiMatrix_apply (pres mu nu i) a b

lemma pres_map (mu nu : K) (i : Fin 4) (p : AffineAmbient K) :
    algebraMap (pres mu nu i).Ring (OppositeProjective.affineRing mu nu) p =
      Ideal.Quotient.mk (OppositeProjective.affineIdeal mu nu) p := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma jacobian_formula (mu nu : K) (i : Fin 4) :
    (pres mu nu i).jacobian =
      ![-8 * algebraMap K _ (A mu nu) * ax mu nu 0 * ax mu nu 1 * ax mu nu 2,
        8 * ax mu nu 3 * ax mu nu 1 * ax mu nu 2,
        8 * ax mu nu 0 * ax mu nu 2 * (ax mu nu 3 + algebraMap K _ (A mu nu)),
        8 * ax mu nu 0 * ax mu nu 1 * (ax mu nu 3 - algebraMap K _ (A mu nu))] i := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, pres_map, pres_jacobi]
  have hc (a : K) : Ideal.Quotient.mk (OppositeProjective.affineIdeal mu nu) (C a) =
      algebraMap K (OppositeProjective.affineRing mu nu) a := rfl
  have hn (n : ℕ) : Ideal.Quotient.mk (OppositeProjective.affineIdeal mu nu) (n : AffineAmbient K) = n :=
    map_natCast _ n
  have h2 : Ideal.Quotient.mk (OppositeProjective.affineIdeal mu nu) (2 : AffineAmbient K) = 2 :=
    map_ofNat _ 2
  have hc2 : algebraMap K (OppositeProjective.affineRing mu nu) (2 : K) = 2 := map_ofNat _ 2
  rw [Matrix.det_fin_three]
  fin_cases i <;>
    simp [columns, affineEquation, Matrix.det_fin_three, map_add, map_sub, map_mul,
      map_pow, ax, hc, hn, h2, hc2, pderiv_pow] <;> ring


/-- The previously proved scalar minors certify actual presentation Jacobians at every field-valued point. -/
theorem field_point_jacobian {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0)
    (F : Type u) [Field F] [Algebra K F] (f : OppositeProjective.affineRing mu nu →ₐ[K] F) :
    ∃ i : Fin 4, f (pres mu nu i).jacobian ≠ 0 := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let m := algebraMap K F mu
  let n := algebraMap K F nu
  let p := f (ax mu nu 0)
  let q := f (ax mu nu 1)
  let r := f (ax mu nu 2)
  let z := f (ax mu nu 3)
  have hr := affineRelations mu nu
  have h0 := congrArg f hr.1
  have h1 := congrArg f hr.2.1
  have h2 := congrArg f hr.2.2
  simp only [map_pow, map_mul, map_sub, map_add, map_ofNat, AlgHom.commutes, A_map] at h0 h1 h2
  have he0 : z^2 - A m n*p^2 + 2*A m n*n^2*(1:F)^2 = 0 := by
    dsimp [m,n,p,z]
    rw [A_map]
    linear_combination h0
  have he1 : q^2 - p^2 - m^2*(1:F)^2 - 2*z*1 = 0 := by
    dsimp [m,p,q,z]; linear_combination h1
  have he2 : r^2 - p^2 - m^2*(1:F)^2 + 2*z*1 = 0 := by
    dsimp [m,p,r,z]; linear_combination h2
  have hmf : m ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hm
  have hnf : n ≠ 0 := (map_ne_zero (algebraMap K F)).mpr hn
  have haf : A m n ≠ 0 := by simpa [m,n,← A_map] using (map_ne_zero (algebraMap K F)).mpr hA
  have hbf : B m n ≠ 0 := by simpa [m,n,← B_map] using (map_ne_zero (algebraMap K F)).mpr hB
  have hsf : S m n ≠ 0 := by simpa [m,n,← S_map] using (map_ne_zero (algebraMap K F)).mpr hS
  have hne : ¬(p=0 ∧ q=0 ∧ r=0 ∧ z=0 ∧ (1:F)=0) := by
    rintro ⟨_,_,_,_,h⟩; exact one_ne_zero h
  rcases Scalar.nonzero_minor_alternative he0 he1 he2 hne hmf hnf haf hbf hsf with h|h|h|h
  · exact ⟨0, by simpa [jacobian_formula, m,n,p,q,r,z,map_ofNat,← A_map] using h⟩
  · exact ⟨1, by simpa [jacobian_formula, m,n,p,q,r,z,map_ofNat,← A_map] using h⟩
  · exact ⟨2, by simpa [jacobian_formula, m,n,p,q,r,z,map_ofNat,← A_map] using h⟩
  · exact ⟨3, by simpa [jacobian_formula, m,n,p,q,r,z,map_ofNat,← A_map] using h⟩

/-- The genuine four-variable quotient is smooth of relative dimension one over K. -/
theorem affine_smooth {mu nu : K} (hm : mu ≠ 0) (hn : nu ≠ 0)
    (hA : A mu nu ≠ 0) (hB : B mu nu ≠ 0) (hS : S mu nu ≠ 0) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap K (OppositeProjective.affineRing mu nu)))) := by
  have hspan := FiniteJacobianSmooth.jacobian_span_of_field_points (pres mu nu)
    (field_point_jacobian hm hn hA hB hS)
  simpa using FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres mu nu) hspan

end FourCorner.OppositeProjective.PostSmooth
#print axioms FourCorner.OppositeProjective.PostSmooth.jacobian_formula

#print axioms FourCorner.OppositeProjective.PostSmooth.field_point_jacobian
#print axioms FourCorner.OppositeProjective.PostSmooth.affine_smooth
