import OrderedSourceCoordinates
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace FourCorner.OriginalCoverCompletion.OrderedSource
open RationalAlgebra

namespace RationalAlgebra
variable {F : Type*} [Field F] [CharZero F]

theorem pureReturn_recover (U V W T : F) (hT : T≠0) :
    let r := pureReturn U V W T
    (r 2+r 5)/(r 2-r 5)=U ∧
    2*(r 4-r 3)/(r 2-r 5)=V ∧
    2*(r 3+r 4)/(r 2-r 5)=W ∧
    2/(r 2-r 5)=T := by
  dsimp only
  have hd : pureReturn U V W T 2-pureReturn U V W T 5=2/T := by simp [pureReturn]; ring
  rw [hd]
  simp [pureReturn]
  refine ⟨?_,?_,?_⟩ <;> field_simp <;> ring

theorem pureReturn_t (p beta U V W T : F) (hT : T≠0)
    (hU : U^2=p*beta) (hV : V^2=2*(p-1)*(beta-1))
    (hW : W^2=2*(p+1)*(beta+1)) :
    tPlus (pureReturn U V W T) = ((p+1)*beta+p-1)/T^2 := by
  simp [tPlus,pureReturn]
  field_simp
  linear_combination 4*hU+hW-hV

theorem pair_t {n a c : F} (hn : n≠0) (ha : a≠0) (hcm : c-n≠0) (hac : a+c≠0) :
    ((pairP n a+1)*pairBeta n c+pairP n a-1)/
      ((pairP n a-1)*pairBeta n c+pairP n a+1) = (c-a)/(a+c) := by
  have hd : (pairP n a-1)*pairBeta n c+pairP n a+1 = -2*n*(a+c)/(a*(c-n)) := by
    unfold pairP pairBeta; field_simp; ring
  have ht : (pairP n a+1)*pairBeta n c+pairP n a-1 = -2*n*(c-a)/(a*(c-n)) := by
    unfold pairP pairBeta; field_simp; ring
  rw [hd,ht]
  field_simp

theorem metric_q_square {n a c u : F} (hn : n≠0) (hac : a+c≠0)
    (hu : u^2=-(a*c)/n) :
    (2*u/(a+c))^2=(((c-a)/(a+c))^2-1)/n := by
  field_simp
  have hh := (eq_div_iff hn).mp hu
  linear_combination 4*hh

theorem pair_recover_a {n a : F} (hn : n≠0) (ha : a≠0) : -n/pairP n a=a := by
  unfold pairP; field_simp

theorem pair_recover_c {n c : F} (hn : n≠0) (hcm : c-n≠0) :
    n*(pairBeta n c+1)/(pairBeta n c-1)=c := by
  unfold pairBeta; field_simp; ring_nf; field_simp

theorem pair_recover_b {a b v : F} (ha : a≠0) (hv : v≠0) :
    -a*v*pairV a b v/2=b := by
  unfold pairV; field_simp

theorem pair_recover_v {n a u v : F} (ha : a≠0) (ham : a-n≠0) (hu : u≠0) (hv : v≠0) :
    2*(a-n)*u/(a*pairW n a u v)=v := by
  unfold pairW; field_simp

theorem pair_recover_ell {n a b c ell u v : F}
    (hn : n≠0) (hb : b≠0) (hu : u≠0) (hv : v≠0) (hcm : c-n≠0)
    (hv2 : v^2=-((a-n)*(c-n))/n) :
    pairU n a b ell u v*u*(c-n)=ell := by
  rw [pairU_simplified hn hb hu hv hcm hv2]
  field_simp

theorem pair_recover_h {n a b ell u v h : F} (hU : pairU n a b ell u v≠0) :
    pairT n a b ell u v h/(2*pairU n a b ell u v)=h := by
  unfold pairT; field_simp
end RationalAlgebra

def sourceQ (n : ℚ) : sourceField n := 2*uCoord n/(aCoord n+cCoord n)

theorem originalImage_t (n : ℚ) (hn : n≠0) :
    tPlus (originalImage n)=(cCoord n-aCoord n)/(aCoord n+cCoord n) := by
  rw [originalImage, pureReturn_t _ _ _ _ _ _ (pureT_ne n hn) (pureU_square n hn)
    (pureV_square n hn) (pureW_square n hn),pureT_square n hn]
  exact pair_t (n_ne n hn) (a_ne n) (c_minus_ne n hn) (a_c_ne n)

/-- The exact quadratic relation holds in the independently constructed five-root source. -/
theorem sourceQ_literal_square (n : ℚ) (hn : n≠0) : sourceQ n^2=
    ((originalImage n 2*originalImage n 5+originalImage n 3*originalImage n 4)^2-1)/
      algebraMap ℚ (sourceField n) n := by
  change sourceQ n^2=(tPlus (originalImage n)^2-1)/_
  rw [originalImage_t n hn,←nCoord_eq]
  exact metric_q_square (n_ne n hn) (a_c_ne n) (coordinate_squares n 2)

/-- Every pure coordinate is recovered with its sign from the same ordered radii. -/
theorem originalImage_recover (n : ℚ) (hn : n≠0) :
    let r := originalImage n
    (r 2+r 5)/(r 2-r 5)=pureU n ∧
    2*(r 4-r 3)/(r 2-r 5)=pureV n ∧
    2*(r 3+r 4)/(r 2-r 5)=pureW n ∧
    2/(r 2-r 5)=pureT n :=
  pureReturn_recover _ _ _ _ (pureT_ne n hn)

theorem pureP_ne (n : ℚ) (hn : n≠0) : pureP n≠0 :=
  div_ne_zero (neg_ne_zero.mpr (n_ne n hn)) (a_ne n)

theorem originalImage_parameters (n : ℚ) (hn : n≠0) :
    let r := originalImage n
    (2-(r 4-r 3)^2)/(r 2-r 5)^2=pureP n ∧
    (r 2+r 5)^2/(2-(r 4-r 3)^2)=pureBeta n :=
  pureReturn_parameters _ _ _ _ _ _ (pureT_ne n hn) (pureP_ne n hn)
    (pureU_square n hn) (pureV_square n hn) (pureT_square n hn)

theorem source_recover_a (n : ℚ) (hn : n≠0) : -nCoord n/pureP n=aCoord n :=
  pair_recover_a (n_ne n hn) (a_ne n)
theorem source_recover_c (n : ℚ) (hn : n≠0) :
    nCoord n*(pureBeta n+1)/(pureBeta n-1)=cCoord n :=
  pair_recover_c (n_ne n hn) (c_minus_ne n hn)
theorem source_recover_u (n : ℚ) : sourceQ n*(aCoord n+cCoord n)/2=uCoord n := by
  unfold sourceQ; field_simp [a_c_ne n]
theorem source_recover_v (n : ℚ) (hn : n≠0) :
    2*(aCoord n-nCoord n)*uCoord n/(aCoord n*pureW n)=vCoord n :=
  pair_recover_v (a_ne n) (a_minus_ne n) (u_ne n hn) (v_ne n hn)
theorem source_recover_b (n : ℚ) (hn : n≠0) :
    -aCoord n*vCoord n*pureV n/2=bCoord n :=
  pair_recover_b (a_ne n) (v_ne n hn)
theorem source_recover_ell (n : ℚ) (hn : n≠0) :
    pureU n*uCoord n*(cCoord n-nCoord n)=ellCoord n :=
  pair_recover_ell (n_ne n hn) (b_ne n) (u_ne n hn) (v_ne n hn)
    (c_minus_ne n hn) (coordinate_squares n 3)
theorem source_recover_h (n : ℚ) (hn : n≠0) : pureT n/(2*pureU n)=hCoord n :=
  pair_recover_h (pureU_ne n hn)

#print axioms sourceQ_literal_square
#print axioms originalImage_recover
#print axioms originalImage_parameters
#print axioms source_recover_ell
end FourCorner.OriginalCoverCompletion.OrderedSource
