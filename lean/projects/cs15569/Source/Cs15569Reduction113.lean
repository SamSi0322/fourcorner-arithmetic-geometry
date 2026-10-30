import Cs15569RationalReduction
import Cs15569SourceParity
import Cs15569Group

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

private def fieldCoordinates {K : Type*} [Field K] {W : WeierstrassCurve.Affine K} :
    W.Point → Option (K × K)
  | .zero => none
  | .some x y _ => some (x,y)

private theorem fieldCoordinates_injective {K : Type*} [Field K]
    {W : WeierstrassCurve.Affine K} : Function.Injective (fieldCoordinates (W:=W)) := by
  intro Q R hh
  cases Q <;> cases R <;> simp_all [fieldCoordinates]

private def curveEqualityEquiv {K : Type*} [Field K] [DecidableEq K]
    {W W' : WeierstrassCurve.Affine K} (h : W=W') : W.Point ≃+ W'.Point := by
  subst W'
  exact AddEquiv.refl _

private theorem curveEqualityEquiv_coordinates {K : Type*} [Field K] [DecidableEq K]
    {W W' : WeierstrassCurve.Affine K} (h : W=W') (Q : W.Point) :
    fieldCoordinates (curveEqualityEquiv h Q)=fieldCoordinates Q := by
  subst W'
  rfl

private theorem residue113_model : residueCurve 15569 113=Cs15569Group.curve := by
  ext <;> decide

def model113 : ResiduePoint 15569 113 ≃+ Cs15569Group.Pt := curveEqualityEquiv residue113_model

def red113 : E →+ Cs15569Group.Pt :=
  model113.toAddMonoidHom.comp (reduce 15569 (by decide) (by decide))

private theorem red113_coordinates (Q : E) :
    fieldCoordinates (red113 Q)=
      residueCoordinates (reduce 15569 (by decide) (by decide) Q) := by
  change fieldCoordinates (curveEqualityEquiv residue113_model _)=_
  rw [curveEqualityEquiv_coordinates]
  cases (reduce (q:=113) 15569 (by decide) (by decide) Q) <;> rfl

def w113 : Cs15569Group.Pt := .some 36 58 (by
  rw [WeierstrassCurve.Affine.nonsingular_iff,WeierstrassCurve.Affine.equation_iff]
  decide)

theorem red113_P : red113 P=w113 := by
  apply fieldCoordinates_injective
  rw [red113_coordinates,P_reduction_coordinates (by decide) (by decide) (by decide)]
  change some ((15569*7809^2/7760^2 : ZMod 113),
    (-(15569*7809*108983*11009)/7760^3 : ZMod 113))=some (36,58)
  exact congrArg some (Prod.ext Cs15569Finite.p_reduced_coordinates.1 Cs15569Finite.p_reduced_coordinates.2)

theorem red113_G : red113 G=Cs15569Group.A2 := by
  apply fieldCoordinates_injective
  rw [red113_coordinates,G_reduction_coordinates (by decide) (by decide) (by decide)]
  change some ((15569*13522049^2/13382920^2 : ZMod 113),
    (-(15569*13522049*1934751*2373852137)/13382920^3 : ZMod 113))=some (81,112)
  exact congrArg some (Prod.ext Cs15569Finite.g_reduced_coordinates.1 Cs15569Finite.g_reduced_coordinates.2)

/-- Canonical reduction to the entire actual finite group, then its already
proved exponent16. No local113 halving/descent premise is necessary. -/
theorem red113_sixteen (Q : E) : red113 (16 • Q)=0 := by
  rw [map_nsmul]
  exact Cs15569Group.whole_group_exponent _

private theorem eight_g113 : 8 • Cs15569Group.A2=0 := by
  have hh := Cs15569Group.a_double
  have ha : 16 • Cs15569Group.A=0 := Cs15569Group.whole_group_exponent _
  rw [show 16=8*2 by norm_num,mul_nsmul',two_nsmul,hh] at ha
  exact ha

private theorem w113_relation : w113=2 • Cs15569Group.A2+Cs15569Group.Tplus := by
  symm
  rw [two_nsmul,Cs15569Group.a2_double]
  apply fieldCoordinates_injective
  rw [Cs15569Group.A4,Cs15569Group.Tplus,
    WeierstrassCurve.Affine.Point.add_of_X_ne (by decide)]
  change some (_,_)=some (36,58)
  simp only [Option.some.injEq,Prod.mk.injEq]
  norm_num [WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope,Cs15569Group.curve,WeierstrassCurve.toAffine]
  simp only [show (77 : ZMod 113) ≠ 88 by decide,if_false]
  rw [show (79/(-11) : ZMod 113)=75 by
    apply (div_eq_iff (by decide)).mpr
    decide]
  decide

private theorem eight_w113 : 8 • w113=0 := by
  rw [w113_relation,nsmul_add,←mul_nsmul]
  have ht : 2 • Cs15569Group.Tplus=0 := by
    rw [two_nsmul,Cs15569Group.Tplus]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    decide
  rw [show 8*2=16 by norm_num,Cs15569Group.whole_group_exponent]
  rw [show 8=4*2 by norm_num,mul_nsmul',ht,nsmul_zero,add_zero]

/-- Complete whole-H mod2 generation is essential here: it proves that EVERY
H remainder is annihilated by8 after reduction. All H compensators remain. -/
theorem red113_eight_H (Q : ActualH) : red113 (8 • (Q:E))=0 := by
  obtain ⟨k,m,hk,hm,Z,hQ⟩ := actual_H_mod_two Q
  have hpoint := congrArg (fun Q : ActualH => (Q:E)) hQ
  change (Q:E)=k • G+m • P+2 • (Z:E) at hpoint
  rw [hpoint,nsmul_add,nsmul_add,map_add,map_add,map_nsmul,map_nsmul,map_nsmul,
    map_nsmul,map_nsmul,map_nsmul,red113_G,red113_P]
  rw [nsmul_left_comm Cs15569Group.A2 k 8,nsmul_left_comm w113 m 8,eight_g113,eight_w113,
    nsmul_zero,nsmul_zero,zero_add,zero_add,←mul_nsmul]
  exact Cs15569Group.whole_group_exponent _

/-- The original same coefficients reduce every actual H point. -/
theorem red113_coefficients {Q Z : ActualH} {k m : ℕ}
    (he : Q=k • HG+m • HP+8 • Z) :
    red113 (Q:E)=k • Cs15569Group.A2+m • w113 := by
  have hpoint := congrArg (fun Q : ActualH => (Q:E)) he
  change (Q:E)=k • G+m • P+8 • (Z:E) at hpoint
  rw [hpoint,map_add,map_add,map_nsmul,map_nsmul,red113_G,red113_P,red113_eight_H,add_zero]

/-- Public coordinate compatibility for further same-source reduction bridges. -/
theorem red113_coordinates_bridge (Q : E) :
    fieldCoordinates (red113 Q)=residueCoordinates (reduce (q:=113) 15569 (by decide) (by decide) Q) :=
  red113_coordinates Q

theorem w113_eq_two_g_plus_root : w113=2 • Cs15569Group.A2+Cs15569Group.Tplus := w113_relation

theorem g113_eight_zero : 8 • Cs15569Group.A2=0 := eight_g113

theorem w113_eight_zero : 8 • w113=0 := eight_w113

theorem red113_Tplus : red113 (Tplus 15569 (by norm_num))=Cs15569Group.Tplus := by
  apply fieldCoordinates_injective
  rw [red113_coordinates]
  let he : CongruentEquation 15569 15569 0 := by norm_num [CongruentEquation]
  have ht := reduction_fraction_coordinates (q:=113) (by decide) (by decide) he
    15569 1 0 1 (by decide) (by decide) (by norm_num) (by norm_num)
  change residueCoordinates (reduce (q:=113) 15569 (by decide) (by decide)
    (finitePoint (by norm_num) he))=some (88,0)
  rw [ht]
  norm_num only [Int.cast_one,Int.cast_zero,div_one]
  decide

theorem red113_Tminus : red113 (Tminus 15569 (by norm_num))=Cs15569Group.T0+Cs15569Group.Tplus := by
  have hh : Tminus (15569 : ℚ) (by norm_num)=T0 15569 (by norm_num)+Tplus 15569 (by norm_num) :=
    (T0_add_Tplus 15569 (by norm_num)).symm
  rw [hh,map_add,red113_Tplus]
  congr 1
  apply fieldCoordinates_injective
  rw [red113_coordinates]
  let he : CongruentEquation 15569 0 0 := by norm_num [CongruentEquation]
  have ht := reduction_fraction_coordinates (q:=113) (by decide) (by decide) he
    0 1 0 1 (by decide) (by decide) (by norm_num) (by norm_num)
  change residueCoordinates (reduce (q:=113) 15569 (by decide) (by decide)
    (finitePoint (by norm_num) he))=some (0,0)
  rw [ht]
  norm_num

#print axioms red113
#print axioms red113_P
#print axioms red113_G
#print axioms red113_eight_H
#print axioms red113_coefficients
end
end FourCorner.Cs15569Completion
