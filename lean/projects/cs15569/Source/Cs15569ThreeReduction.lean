import Cs15569RationalReduction
import Cs15569SourceParity
import ActualBranch15569
import ThreeRootDisks15569
import OddEvenMismatch

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def redThree : E →+ ResiduePoint 15569 3 := reduce 15569 (by decide) (by decide)
def threeT0 : ResiduePoint 15569 3 := residueT0 15569 (by decide)
def threeTplus : ResiduePoint 15569 3 := residueTplus 15569 (by decide) (by decide)

theorem whole_three_double_zero (Q : ResiduePoint 15569 3) : 2 • Q=0 := by
  cases Q with
  | zero => change 2 • (0 : ResiduePoint 15569 3)=0; simp
  | some x y he =>
    have hf : ∀ x y : ZMod 3,
        y^2=x^3+2*x → y=0 := by decide
    have hy : y=0 := by
      apply hf x y
      have hh := he.1
      rw [WeierstrassCurve.Affine.equation_iff] at hh
      convert hh using 1 <;>
        norm_num [residueCurve,integralCurve,WeierstrassCurve.map,WeierstrassCurve.toAffine]
      rw [←neg_mul,show (-242393761 : ZMod 3)=2 by decide]
    rw [two_nsmul]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [WeierstrassCurve.Affine.negY,residueCurve,integralCurve,WeierstrassCurve.map,
      WeierstrassCurve.toAffine,hy]

theorem redThree_P : redThree P=threeT0 := by
  apply residueCoordinates_injective
  have hh := P_reduction_coordinates (q:=3) (by decide) (by decide) (by decide)
  have hf : ((15569*7809^2/7760^2 : ZMod 3),
      (-(15569*7809*108983*11009)/7760^3 : ZMod 3))=(0,0) := by
    apply Prod.ext
    · apply (div_eq_iff (by decide)).mpr
      decide
    · apply (div_eq_iff (by decide)).mpr
      decide
  change residueCoordinates (reduce 15569 (by decide) (by decide) P)=_
  rw [hh,hf]
  rfl

theorem redThree_G : redThree G=threeTplus := by
  apply residueCoordinates_injective
  have hh := G_reduction_coordinates (q:=3) (by decide) (by decide) (by decide)
  have hf : ((15569*13522049^2/13382920^2 : ZMod 3),
      (-(15569*13522049*1934751*2373852137)/13382920^3 : ZMod 3))=(2,0) := by
    apply Prod.ext
    · apply (div_eq_iff (by decide)).mpr
      decide
    · apply (div_eq_iff (by decide)).mpr
      decide
  change residueCoordinates (reduce 15569 (by decide) (by decide) G)=_
  rw [hh,hf]
  rw [threeTplus,residueCoordinates_Tplus]
  decide

theorem redThree_coefficients {Q Z : ActualH} {k m : ℕ}
    (he : Q=k • HG+m • HP+8 • Z) :
    redThree (Q:E)=(k%2) • threeTplus+(m%2) • threeT0 := by
  have he' := congrArg (fun Q : ActualH => (Q:E)) he
  change (Q:E)=k • G+m • P+8 • (Z:E) at he'
  rw [he',map_add,map_add,map_nsmul,map_nsmul,map_nsmul,redThree_G,redThree_P]
  rw [nsmul_eq_mod_nsmul 8 (whole_three_double_zero (redThree (Z:E)))]
  norm_num
  rw [nsmul_eq_mod_nsmul k (whole_three_double_zero threeTplus),
    nsmul_eq_mod_nsmul m (whole_three_double_zero threeT0)]

private theorem threeT0_ne_zero : threeT0 ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

private theorem three_even_mismatch (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders)
    (hmismatch : (1<‖(r.x : ℚ_[3])‖ ∧ ‖(r.w : ℚ_[3])‖<1) ∨
      (‖(r.x : ℚ_[3])‖<1 ∧ 1<‖(r.w : ℚ_[3])‖)) :
    ¬ IsSquare (commonSourceReturn (15569 : ℚ_[3]) S.a S.c) := by
  have ho := actual_pair_unique_branch S r
  have ha : (S.a : ℚ_[3])=commonSourceTranslateMinus (15569 : ℚ_[3]) r.x := by
    dsimp [commonSourceTranslateMinus] at ho ⊢
    exact_mod_cast ho.1
  have hc : (S.c : ℚ_[3])=commonSourceTranslatePlus (15569 : ℚ_[3]) r.w := by
    dsimp [commonSourceTranslatePlus] at ho ⊢
    exact_mod_cast ho.2
  have hn : ‖(15569 : ℚ_[3])‖=1 := parameter_norm_eq_one 15569 (by decide)
  rcases hmismatch with ⟨hx,hw⟩ | ⟨hx,hw⟩
  · apply three_minus_minus (e:=(S.e : ℚ_[3]))
    · rw [ha]
      exact (csOdd_torsion_disks_from_infinity (by decide : 3 ≠ 2) hn hx).2.2
    · rw [hc]
      exact (csOdd_torsion_disks_from_zero (by decide : 3 ≠ 2) hn hw).1
    · exact_mod_cast S.e_ne
    · have hh : S.e^2=S.c*(S.c-15569)*(S.c+15569) := S.hR
      exact_mod_cast hh
  · apply three_plus_plus
    · rw [ha]
      exact (csOdd_torsion_disks_from_zero (by decide : 3 ≠ 2) hn hx).2
    · rw [hc]
      exact (csOdd_torsion_disks_from_infinity (by decide : 3 ≠ 2) hn hw).2.1

/-- The actual all-depth Q3 square condition forces the SAME global
coefficients k,k' to be odd. No local Kummer row table is assumed. -/
theorem three_forces_odd_coefficients (S : ActualPair 15569 n15569_ne_zero)
    (r : S.Remainders) {Z Z' : ActualH} {k m k' m' : ℕ}
    (hU : S.U=k • HG+m • HP+8 • Z) (hV : S.V=k' • HG+m' • HP+8 • Z')
    (hs : IsSquare (commonSourceReturn (15569 : ℚ_[3]) S.a S.c)) :
    k%2=1 ∧ k'%2=1 := by
  obtain ⟨hkpar,hmpar⟩ := actual_source_coefficient_parities S hU hV
  have hkodd : k%2=1 := by
    by_contra hh
    have hk : k%2=0 := by omega
    have hk' : k'%2=0 := by omega
    have hu := redThree_coefficients hU
    have hv := redThree_coefficients hV
    rw [hk,zero_nsmul,zero_add] at hu
    rw [hk',zero_nsmul,zero_add] at hv
    have hredU : redThree (finitePoint (by norm_num) r.hU)=(m%2) • threeT0 := by rw [←r.eqU]; exact hu
    have hredV : redThree (finitePoint (by norm_num) r.hV)=(m'%2) • threeT0 := by rw [←r.eqV]; exact hv
    have hlabelsU : redThree (finitePoint (by norm_num) r.hU)=0 ∨
        redThree (finitePoint (by norm_num) r.hU)=threeT0 := by
      rcases (show m%2=0 ∨ m%2=1 by omega) with h | h <;> rw [hredU,h] <;> simp
    have hlabelsV : redThree (finitePoint (by norm_num) r.hV)=0 ∨
        redThree (finitePoint (by norm_num) r.hV)=threeT0 := by
      rcases (show m'%2=0 ∨ m'%2=1 by omega) with h | h <;> rw [hredV,h] <;> simp
    have hne : redThree (finitePoint (by norm_num) r.hU) ≠
        redThree (finitePoint (by norm_num) r.hV) := by
      rw [hredU,hredV]
      rcases (show m%2=0 ∨ m%2=1 by omega) with h | h
      · have hm' : m'%2=1 := by omega
        rw [h,hm',zero_nsmul,one_nsmul]
        exact threeT0_ne_zero.symm
      · have hm' : m'%2=0 := by omega
        rw [h,hm',zero_nsmul,one_nsmul]
        exact threeT0_ne_zero
    have hdisks := actual_even_reduction_mismatch (q:=3) (n:=15569) (by decide) (by decide)
      r.hU r.hV hlabelsU hlabelsV hne
    exact three_even_mismatch S r hdisks hs
  exact ⟨hkodd,by omega⟩

#print axioms whole_three_double_zero
#print axioms redThree_P
#print axioms redThree_G
#print axioms redThree_coefficients
#print axioms three_forces_odd_coefficients
end
end FourCorner.Cs15569Completion
