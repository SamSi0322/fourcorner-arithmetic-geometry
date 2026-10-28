import ThetaContactOddness
import QuarticSingletonZero

namespace FourCorner.ThetaLiteralBinaryRestrictions
open AlgebraicGeometry AlgebraicCurve MvPolynomial
open ThetaDGeometricModel ThetaLinesPolynomialContacts ThetaContactTangencyCertificates
open BinaryQuarticDoubleRoots
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The ACTUAL literal line restriction as a coefficient-level homogeneous
binary polynomial, not a function-only surrogate. -/
def restriction (L : ThetaLine K) : Binary K :=
  match L with
  | .affine α β => thetaF (X 0) (X 1) (C α*X 0+C β*X 1)
  | .vertical t => thetaF (C t*X 0) (X 0) (X 1)
  | .yzero => thetaF (X 0) 0 (X 1)

 theorem thetaF_homogeneous (f g h : Binary K)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 1) (hh : h.IsHomogeneous 1) :
    (thetaF f g h).IsHomogeneous 4 := by
  have he : thetaF f g h=
      C (9801:K)*(f^4+g^4)+C (19598:K)*(f^2*g^2)-
        C (39592:K)*((f^2+g^2)*h^2)+C (39984:K)*h^4 := by
    simp only [thetaF,map_ofNat]
    ring
  rw [he]
  have hf2 := hf.pow 2
  have hg2 := hg.pow 2
  have hh2 := hh.pow 2
  exact (((((hf.pow 4).add (hg.pow 4)).C_mul 9801).add
    ((hf2.mul hg2).C_mul 19598)).sub (((hf2.add hg2).mul hh2).C_mul 39592)).add
      ((hh.pow 4).C_mul 39984)

 theorem homogeneous (L : ThetaLine K) : (restriction L).IsHomogeneous 4 := by
  have h0 := MvPolynomial.isHomogeneous_X (R:=K) (0:Fin 2)
  have h1 := MvPolynomial.isHomogeneous_X (R:=K) (1:Fin 2)
  cases L with
  | affine α β => exact thetaF_homogeneous _ _ _ h0 h1 ((h0.C_mul α).add (h1.C_mul β))
  | vertical t => exact thetaF_homogeneous _ _ _ (h0.C_mul t) h0 h1
  | yzero => exact thetaF_homogeneous _ _ _ h0 (MvPolynomial.isHomogeneous_zero (Fin 2) K 1) h1

 theorem eval_restriction (L : ThetaLine K) (v : Fin 2 → K) :
    MvPolynomial.aeval v (restriction L)=L.restrict (v 0) (v 1) := by
  cases L <;> simp [restriction,ThetaLine.restrict,thetaF]

 theorem dehom_affine (α β : K) : dehom (restriction (.affine α β))=affineRestriction α β := by
  simp [dehom,restriction,affineRestriction,thetaF]

 theorem dehom_vertical (t : K) : dehom (restriction (.vertical t))=verticalRestriction t := by
  simp [dehom,restriction,verticalRestriction,thetaF]

 theorem affine_not_zero (α β : K) : restriction (.affine α β)≠0 := by
  intro hz
  have hp : affineRestriction α β=0 := by
    have he := congrArg dehom hz
    rw [dehom_affine] at he
    have hz0 : dehom (0:Binary K)=0 := by simp [dehom]
    rw [hz0] at he
    exact he
  have h0 : thetaF 0 1 β=0 := by
    have he := congrArg (Polynomial.eval (0:K)) hp
    simpa [affineRestriction,thetaF] using he
  have hb : β≠0 := by intro he;rw [he] at h0;norm_num [thetaF] at h0
  have ha : α≠0 := by
    intro he
    rw [he] at hp
    have heq : affineRestriction (0:K) β=
        Polynomial.C 9801*Polynomial.X^4+
          Polynomial.C (19598-39592*β^2)*Polynomial.X^2+
            Polynomial.C (9801-39592*β^2+39984*β^4) := by
      simp only [affineRestriction,thetaF,map_sub,map_add,map_mul,map_pow,map_ofNat,map_zero]
      ring
    have he4 := congrArg (fun p : Polynomial K=>p.coeff 4) (hp.symm.trans heq)
    norm_num only [Polynomial.coeff_zero,Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C] at he4
    norm_num at he4
  have hd : YFu (0:K) β+α*YFv 0 β=0 := by
    have he : (affineRestriction α β).derivative.eval 0=0 := by rw [hp];simp
    rw [affine_derivative] at he
    simpa only [mul_zero,zero_add] using he
  have hm : (2:K)*α*β*(79968*β^2-39592)=0 := by
    unfold YFu YFv at hd
    linear_combination hd
  have hc : 79968*β^2-39592=0 :=
    (mul_eq_zero.mp hm).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb)
  have hbad : (4*39984*9801-39592^2:K)=0 := by
    unfold thetaF at h0
    linear_combination (4*39984)*h0-(79968*β^2-39592)*hc
  norm_num at hbad

 theorem nonzero (L : ThetaLine K) : restriction L≠0 := by
  cases L with
  | affine α β => exact affine_not_zero α β
  | vertical t =>
    intro h
    have he := congrArg (MvPolynomial.aeval (![0,1]:Fin 2→K)) h
    norm_num [restriction,thetaF] at he
  | yzero =>
    intro h
    have he := congrArg (MvPolynomial.aeval (![0,1]:Fin 2→K)) h
    norm_num [restriction,thetaF] at he

 theorem square_of_polynomial_square (L : ThetaLine K) (c a b d : K) (hc : c≠0)
    (he : restriction L=C c*(quadratic a b d)^2) : IsThetaSquareContact L := by
  refine ⟨c,a,b,d,hc,?_⟩
  intro x y
  have hh := congrArg (MvPolynomial.aeval (![x,y]:Fin 2→K)) he
  rw [eval_restriction] at hh
  simpa [quadratic] using hh

#print axioms homogeneous
#print axioms nonzero
#print axioms square_of_polynomial_square
end
end FourCorner.ThetaLiteralBinaryRestrictions
