import ThetaCoverClassPortable.ThetaLiteralBinaryRestrictions

namespace FourCorner.ThetaLiteralRootJets
open AlgebraicGeometry AlgebraicCurve MvPolynomial
open ThetaDGeometricModel ThetaLiteralBinaryRestrictions ThetaContactTangencyCertificates BinaryQuarticDoubleRoots
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

 theorem partial_ofNat (i : Fin 2) (n : ℕ) [n.AtLeastTwo] :
    MvPolynomial.pderiv i (OfNat.ofNat n : Binary K)=0 := (MvPolynomial.pderiv i).map_natCast n

 theorem thetaF_C (x y z : Binary K) : thetaF x y z=
    C (9801:K)*(x^4+y^4)+C (19598:K)*x^2*y^2-
      C (39592:K)*(x^2+y^2)*z^2+C (39984:K)*z^4 := by
  simp only [thetaF,map_ofNat]

 theorem affine_finite (α β t : K) (hz : thetaF t 1 (α*t+β)=0)
    (hd : YFu t (α*t+β)+α*YFv t (α*t+β)=0) :
    ZeroJet (restriction (.affine α β)) ![t,1] := by
  refine ⟨?_,?_⟩
  · rw [eval_restriction];simpa [ThetaLine.restrict] using hz
  · intro i;fin_cases i
    all_goals
      rw [restriction,thetaF_C]
      simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
        MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,smul_eq_mul]
      simp
      unfold thetaF at hz
      unfold YFu YFv at hd
    · linear_combination hd
    · linear_combination 4*hz-t*hd

 theorem vertical_finite (s t : K) (hz : thetaF (s*t) t 1=0)
    (hd : ZFy (s*t) t+s*ZFx (s*t) t=0) :
    ZeroJet (restriction (.vertical s)) ![t,1] := by
  refine ⟨?_,?_⟩
  · rw [eval_restriction];simpa [ThetaLine.restrict] using hz
  · intro i;fin_cases i
    all_goals
      rw [restriction,thetaF_C]
      simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
        MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,smul_eq_mul]
      simp
      unfold thetaF at hz
      unfold ZFx ZFy at hd
    · linear_combination hd
    · linear_combination 4*hz-t*hd

 theorem yzero_finite (t : K) (hz : thetaF t 0 1=0) (hd : ZFx t 0=0) :
    ZeroJet (restriction .yzero) ![t,1] := by
  refine ⟨?_,?_⟩
  · rw [eval_restriction];exact hz
  · intro i;fin_cases i
    all_goals
      rw [restriction,thetaF_C]
      simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
        MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,smul_eq_mul]
      simp
      unfold thetaF at hz
      unfold ZFx at hd
    · linear_combination hd
    · linear_combination 4*hz-t*hd

 theorem affine_infinity (α β : K) (hz : thetaF 1 0 α=0)
    (hd : -β*YFv 0 α-YFu 0 α=0) :
    ZeroJet (restriction (.affine α β)) ![1,0] := by
  refine ⟨?_,?_⟩
  · rw [eval_restriction];simpa [ThetaLine.restrict] using hz
  · intro i;fin_cases i
    all_goals
      rw [restriction,thetaF_C]
      simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
        MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,smul_eq_mul]
      simp
      unfold thetaF at hz
      unfold YFu YFv at hd
    · linear_combination 4*hz
    · linear_combination -hd

 theorem vertical_infinity (s : K) (hz : thetaF s 1 0=0) :
    ZeroJet (restriction (.vertical s)) ![1,0] := by
  refine ⟨?_,?_⟩
  · rw [eval_restriction];simpa [ThetaLine.restrict] using hz
  · intro i;fin_cases i
    all_goals
      rw [restriction,thetaF_C]
      simp only [map_add,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
        MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,smul_eq_mul]
      simp
    unfold thetaF at hz
    linear_combination 4*hz

#print axioms affine_finite
#print axioms vertical_finite
#print axioms yzero_finite
#print axioms affine_infinity
#print axioms vertical_infinity
end
end FourCorner.ThetaLiteralRootJets
