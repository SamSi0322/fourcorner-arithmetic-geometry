import FiniteJacobianSmooth
import AdjacentPostScalarSmooth

noncomputable section
namespace FourCorner.AdjacentPostSmooth
open Algebra MvPolynomial Slot03HighAdjacentProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def columns : Fin 4 → Fin 3 → Fin 4
  | 0 => ![0,2,3]
  | 1 => ![1,2,3]
  | 2 => ![0,1,3]
  | 3 => ![0,1,2]
lemma columns_injective (i : Fin 4) : Function.Injective (columns i) := by
  fin_cases i <;> decide

def pres (c : K) (i : Fin 4) : PreSubmersivePresentation K (affineRing c) (Fin 4) (Fin 3) :=
  .naive (v := affineEquation c) (columns i) (columns_injective i)

lemma pres_jacobi (c : K) (i : Fin 4) :
    (pres c i).jacobiMatrix = fun a b => pderiv (columns i a) (affineEquation c b) := by
  apply Matrix.ext
  intro a b
  exact PreSubmersivePresentation.jacobiMatrix_apply (pres c i) a b

lemma pres_map (c : K) (i : Fin 4) (p : AffineAmbient K) :
    algebraMap (pres c i).Ring (affineRing c) p = Ideal.Quotient.mk (affineIdeal c) p := rfl

lemma jacobian_formula (c : K) (i : Fin 4) :
    (pres c i).jacobian =
      ![8*algebraMap K _ (c^2-1)*aX c 0*aX c 2*aX c 3,
        8*algebraMap K _ (c^2)*aX c 1*aX c 2*aX c 3,
        8*aX c 3*(aX c 0*aX c 1+2*algebraMap K _ (c^2-1)*aX c 0+algebraMap K _ (c^2)*aX c 1),
        -8*aX c 2*(aX c 0*aX c 1+2*algebraMap K _ (c^2-1)*aX c 0-algebraMap K _ (c^2)*aX c 1)] i := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, pres_map, pres_jacobi]
  have hc (a : K) : Ideal.Quotient.mk (affineIdeal c) (C a) = algebraMap K (affineRing c) a := rfl
  have hn (n : ℕ) : Ideal.Quotient.mk (affineIdeal c) (n : AffineAmbient K) = n := map_natCast _ n
  have h2 : Ideal.Quotient.mk (affineIdeal c) (2 : AffineAmbient K) = 2 := map_ofNat _ 2
  have hc2 : algebraMap K (affineRing c) (2 : K) = 2 := map_ofNat _ 2
  have hcf (a : K) : aC c a = algebraMap K (affineRing c) a := rfl
  have hd2 (j : Fin 4) : pderiv j (2 : AffineAmbient K) = 0 := by
    have he : (2 : AffineAmbient K) = C (2 : K) := by simp [map_ofNat]
    rw [he, pderiv_C]
  rw [Matrix.det_fin_three]
  fin_cases i <;>
    simp [columns, affineEquation, Matrix.det_fin_three, map_add, map_sub, map_mul,
      map_pow, aX, hc, hn, h2, hc2, hcf, hd2, pderiv_pow] <;> ring

/-- The computed minors are nonzero at every actual field-valued point of the affine source. -/
theorem field_point_jacobian (c : K) (h : AdjacentPolynomials.Admissible c)
    (F : Type u) [Field F] [Algebra K F] (f : affineRing c →ₐ[K] F) :
    ∃ i : Fin 4, f (pres c i).jacobian ≠ 0 := by
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let k := algebraMap K F c
  let u := f (aX c 0)
  let v := f (aX c 1)
  let p := f (aX c 2)
  let r := f (aX c 3)
  have h0 := congrArg f (affine_relation0 c)
  have hp := congrArg f (affine_relation1 c)
  have hr := congrArg f (affine_relation2 c)
  have hcf (a : K) : f (aC c a) = algebraMap K F a := f.commutes a
  simp only [map_add,map_sub,map_mul,map_pow,map_one,map_zero,map_ofNat,hcf,AlgHom.commutes] at h0 hp hr
  have he0 : (k^2-1)*u^2+k^2*v^2-k^2*(k^2-1)=0 := by
    dsimp [k,u,v]
    simpa only [map_sub,map_pow,map_mul,map_one] using h0
  have heP : p^2=(u+1)^2+(v-2)^2 := hp
  have heR : r^2=(u-1)^2+(v-2)^2 := hr
  have had : AdjacentPolynomials.Admissible k := h.map (algebraMap K F)
  rcases AdjacentPostScalar.nonzero_minor_alternative k u v p r had he0 heP heR with hh|hh|hh|hh
  · exact ⟨0, by simpa [jacobian_formula,k,u,v,p,r,map_ofNat] using hh⟩
  · exact ⟨1, by simpa [jacobian_formula,k,u,v,p,r,map_ofNat] using hh⟩
  · exact ⟨2, by simpa [jacobian_formula,k,u,v,p,r,map_ofNat] using hh⟩
  · refine ⟨3, ?_⟩
    have hneg : -(8*p*(u*v+2*(k^2-1)*u-k^2*v)) ≠ 0 := neg_ne_zero.mpr hh
    convert hneg using 1 <;> simp [jacobian_formula,k,u,v,p,r,map_ofNat] <;> ring

/-- Actual smoothness of relative dimension one of the literal affine three-equation quotient. -/
theorem affine_smooth (c : K) (h : AdjacentPolynomials.Admissible c) :
    AlgebraicGeometry.SmoothOfRelativeDimension 1
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K (affineRing c)))) := by
  have hspan := FiniteJacobianSmooth.jacobian_span_of_field_points (pres c) (field_point_jacobian c h)
  simpa using FiniteJacobianSmooth.spec_smooth_of_jacobian_span (pres c) hspan

#print axioms jacobian_formula
#print axioms field_point_jacobian
#print axioms affine_smooth
end FourCorner.AdjacentPostSmooth
