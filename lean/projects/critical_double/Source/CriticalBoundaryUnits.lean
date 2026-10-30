import CriticalBoundaryResidues
import CriticalBoundaryRootCounts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace FourCorner.CriticalBoundaryUnits
open AlgebraicCurve CriticalRadicalField ResiduePlaceEvaluation CriticalBoundaryResidues
open CriticalElliptic23 CriticalBoundaryRootCounts
variable {k:Type*} [Field k]

lemma negative_sign (e:Fin 3→Bool) (ho:¬ordinary e) :
    sign (k:=k) (e 2)= -(sign (e 0)*sign (e 1)) := by
  cases h0:e 0 <;> cases h1:e 1 <;> cases h2:e 2 <;> simp_all [ordinary,sign]

/-- At every actual rational boundary place, the original field extension
has a genuine primitive unit equation with EXACT residue ±4 or±i as labelled
by that place's same three original coordinate residues. -/
theorem normalized_unit (i:k) (hi:i^2 = -1) (h2:(2:k)≠0)
    (v:Place k (field k i)) (hv:v.IsRational) (hp:0<v.ord (shift i))
    (e:Fin 3→Bool)
    (ha:evaluate v hv (A i hi h2 v hp)=sign (e 0))
    (hb:evaluate v hv (B i hi h2 v hp)=sign (e 1))
    (hc:evaluate v hv (C i hi h2 v hp)=sign (e 2)) :
    ∃ u:v.toValuationSubring, IsUnit u ∧ ∃ r:CriticalLiteralDouble.field k i,
      r^2=algebraMap (field k i) (CriticalLiteralDouble.field k i) (u:field k i) ∧
      Algebra.adjoin (field k i) {r}=⊤ ∧ evaluate v hv u=residue i e := by
  classical
  let aa:=A i hi h2 v hp
  let bb:=B i hi h2 v hp
  let cc:=C i hi h2 v hp
  have hprod0:sign (k:=k) (e 0)*sign (e 1)≠0 :=
    mul_ne_zero (sign_nonzero _) (sign_nonzero _)
  by_cases ho:ordinary e
  · let u:v.toValuationSubring:=2*(cc+aa*bb)
    have hu:evaluate v hv u=residue i e := by
      dsimp [u]
      rw [map_mul,map_ofNat,map_add,map_mul,ha,hb,hc,(ordinary_iff e h2).mp ho,residue,if_pos ho]
      ring
    have hunit:IsUnit u := (ResidueValuationFacts.evaluate_nonzero_iff_unit v hv u).mp
      (by rw [hu];exact residue_nonzero i hi h2 e)
    refine ⟨u,hunit,CriticalLiteralDouble.root k i,?_,CriticalLiteralDouble.root_generates k i,hu⟩
    exact CriticalLiteralDouble.root_square k i
  · let fp:v.toValuationSubring:=cc-aa*bb
    have hfp:evaluate v hv fp= -2*(sign (e 0)*sign (e 1)) := by
      dsimp [fp]
      rw [map_sub,map_mul,ha,hb,hc,negative_sign e ho]
      ring
    have hfp0:evaluate v hv fp≠0 := by
      rw [hfp]
      exact mul_ne_zero (neg_ne_zero.mpr h2) hprod0
    let invfp:v.toValuationSubring:=⟨(fp:field k i)⁻¹,inverse_mem v hv fp hfp0⟩
    have hinv:evaluate v hv invfp=(evaluate v hv fp)⁻¹ := by
      have hmul:invfp*fp=1 := by
        apply Subtype.ext
        exact inv_mul_cancel₀ (CriticalProductValuation.nonzero i hi h2).2
      apply mul_right_cancel₀ hfp0
      rw [inv_mul_cancel₀ hfp0]
      simpa only [map_mul,map_one] using congrArg (evaluate v hv) hmul
    let u:v.toValuationSubring:= -2*algebraMap k v.toValuationSubring i*invfp
    have hu:evaluate v hv u=residue i e := by
      have hp2:(sign (k:=k) (e 0)*sign (e 1))^2=1 := by
        rw [mul_pow,CriticalSignPoints.sign_sq,CriticalSignPoints.sign_sq,one_mul]
      have he:(-2*i)/(-2*(sign (e 0)*sign (e 1)))=i*(sign (e 0)*sign (e 1)) := by
        apply (div_eq_iff (mul_ne_zero (neg_ne_zero.mpr h2) hprod0)).mpr
        linear_combination (2*i)*hp2
      dsimp [u]
      rw [map_mul,map_mul,map_neg,map_ofNat,evaluate_constant,hinv,hfp]
      simpa only [residue,if_neg ho,div_eq_mul_inv] using he
    have hunit:IsUnit u := (ResidueValuationFacts.evaluate_nonzero_iff_unit v hv u).mp
      (by rw [hu];exact residue_nonzero i hi h2 e)
    refine ⟨u,hunit,CriticalLiteralDouble.root k i /
      algebraMap (field k i) (CriticalLiteralDouble.field k i) (shift i),?_,
      normalized_root_generates i hi h2,hu⟩
    have he:(u:field k i)= -2*algebraMap k (field k i) i/CriticalProductValuation.f' i := by
      change -2*algebraMap k (field k i) i*(c k i-a k i*b k i)⁻¹ = _
      rw [div_eq_mul_inv]
      rfl
    rw [he]
    exact normalized_root_square i hi h2

end FourCorner.CriticalBoundaryUnits
#print axioms FourCorner.CriticalBoundaryUnits.normalized_unit
