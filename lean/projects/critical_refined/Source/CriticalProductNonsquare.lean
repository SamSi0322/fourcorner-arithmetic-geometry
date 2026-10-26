import TwoRootProductObstruction

noncomputable section
namespace FourCorner.CriticalProductNonsquare
open Polynomial
variable {k : Type*} [Field k] [IsAlgClosed k]

/-- The literal product radicand on the original two-root function field is
nonsquare over every algebraically closed constant field of characteristic not two. -/
theorem literal_product_nonsquare (i:k) (hi:i^2 = -1) (h2:(2:k)≠0) :
    ¬ IsSquare (2*(CriticalRadicalField.c k i +
      CriticalRadicalField.a k i*CriticalRadicalField.b k i)) := by
  let F := RatFunc k
  let B : F := CriticalRadicalField.radicandB k i
  let C : F := CriticalRadicalField.radicandC k i
  let r := Multiquadratic.radical F B
  let s := Multiquadratic.radical F C
  have hind := CriticalSquareclasses.independent i hi h2
  obtain ⟨j,hj⟩ := IsAlgClosed.exists_pow_nat_eq i (n:=2) (by norm_num)
  let d : F := algebraMap k F j*(RatFunc.X^2-1)
  have hjF : (algebraMap k F j)^2=algebraMap k F i := by
    simpa only [map_pow] using congrArg (algebraMap k F) hj
  have hd : d^2=RatFunc.X^2*B-C := by
    dsimp [d,B,C,CriticalRadicalField.radicandB,CriticalRadicalField.radicandC,
      CriticalSquareclasses.qB,CriticalSquareclasses.qC,CriticalSquareclasses.quadratic]
    simp only [map_add,map_sub,map_mul,map_pow,map_neg,
      RatFunc.algebraMap_X,RatFunc.algebraMap_C,←RatFunc.algebraMap_eq_C]
    linear_combination (RatFunc.X^2-1)^2 * hjF
  have hiF : (algebraMap k F i)^2 = -1 := by
    simpa only [map_pow,map_neg,map_one] using congrArg (algebraMap k F) hi
  have hnC : ¬IsSquare (-C) := by
    rintro ⟨z,hz⟩
    apply hind.second
    refine ⟨algebraMap k F i*z,?_⟩
    have hz2:z^2 = -C := by simpa only [sq] using hz.symm
    have he : (algebraMap k F i*z)^2=C := by rw [mul_pow,hiF,hz2];ring
    simpa only [sq] using he.symm
  have h2F : (2:F)≠0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap k F)).mpr h2
  rintro ⟨w,hw⟩
  have bad := TwoRootProductObstruction.no_square RatFunc.X B C d r s
    (Multiquadratic.radical_sq F B) (Multiquadratic.radical_sq F C)
    hind.first hind.second hind.product h2F hd hnC w
  apply bad
  have he := congrArg (fun x : CriticalRadicalField.field k i =>
    (x : AlgebraicClosure F)) hw
  change 2*(s+algebraMap F (AlgebraicClosure F) RatFunc.X*r) = (w:AlgebraicClosure F)*(w:AlgebraicClosure F) at he
  simpa only [sq] using he.symm

#print axioms literal_product_nonsquare
end FourCorner.CriticalProductNonsquare
