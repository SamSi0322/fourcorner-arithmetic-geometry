import Cs15569FiniteSource113
import Cs15569DyadicOddDepth

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

theorem normalized_reduction_coefficients {Q Z : ActualH} {k m : ℕ}
    (he : Q=k • HG+m • HP+8 • Z) :
    red113 (Q:E)=g113 ((k+2*m : ℕ) : ZMod 8)+t113 (m : ZMod 2) := by
  rw [red113_coefficients he,g113_nat,t113_nat,w113_eq_two_g_plus_root,nsmul_add,add_nsmul]
  rw [show (2*m : ℕ)=m*2 by omega,mul_nsmul']
  abel

private theorem source_red_first (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders)
    {Z : ActualH} {k m : ℕ} (he : S.U=k • HG+m • HP+8 • Z) :
    red113 (finitePoint (by norm_num) S.hQ)=
      g113 (((k+2*m : ℕ) : ZMod 8)+4)+t113 ((m : ZMod 2)+1) := by
  have ht := (actual_source_torsion_labels S r).1
  have hh : finitePoint (by norm_num) S.hQ=(S.U:E)+Tminus 15569 (by norm_num) := by
    rw [S.hQU,ht]
  rw [hh,map_add,red113_Tminus,normalized_reduction_coefficients he,map_add,map_add,
    g113_four_eq_T0]
  have ht1 : t113 1=Cs15569Group.Tplus := by simpa only [Nat.cast_one,one_nsmul] using t113_nat 1
  rw [ht1]
  abel

private theorem source_red_second (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders)
    {Z : ActualH} {k m : ℕ} (he : S.V=k • HG+m • HP+8 • Z) :
    red113 (finitePoint (by norm_num) S.hR)=
      g113 ((k+2*m : ℕ) : ZMod 8)+t113 ((m : ZMod 2)+1) := by
  have ht := (actual_source_torsion_labels S r).2
  have hh : finitePoint (by norm_num) S.hR=(S.V:E)+Tplus 15569 (by norm_num) := by
    rw [S.hRV,ht]
  rw [hh,map_add,red113_Tplus,normalized_reduction_coefficients he,map_add]
  have ht1 : t113 1=Cs15569Group.Tplus := by simpa only [Nat.cast_one,one_nsmul] using t113_nat 1
  rw [ht1]
  abel

private theorem parity_torsion_match {m m' : ℕ} (h : (m+m')%2=1) :
    (m' : ZMod 2)+1=(m : ZMod 2) := by
  have hh : (m : ZMod 2)+(m' : ZMod 2)=1 := by
    rw [←Nat.cast_add,←ZMod.natCast_mod (m+m') 2,h]
    norm_num
  have hf : ∀ a b : ZMod 2, a+b=1 → b+1=a := by decide
  exact hf _ _ hh

private theorem sign_to_normalized {k m k' m' : ℕ}
    (h : (7*k+6*m : ZMod 8)=(7*k'+6*m' : ZMod 8) ∨
      (7*k+6*m : ZMod 8)= -(7*k'+6*m' : ZMod 8)) :
    ((k'+2*m' : ℕ) : ZMod 8)=((k+2*m : ℕ) : ZMod 8) ∨
      ((k'+2*m' : ℕ) : ZMod 8)= -((k+2*m : ℕ) : ZMod 8) := by
  have hf (k m : ℕ) : (7*k+6*m : ZMod 8)= -((k+2*m : ℕ) : ZMod 8) := by
    push_cast
    rw [show (7 : ZMod 8)= -1 by decide,show (6 : ZMod 8)= -2 by decide]
    ring
  rw [hf,hf] at h
  rcases h with h | h
  · left
    exact (neg_injective h).symm
  · right
    simpa only [neg_neg] using h.symm

/-- The SAME arbitrary original rational Q,R reduce to exactly the four
nonzero abscissa pairs of the paper. All mod8 compensators were retained,
and both local square hypotheses concern the literal original return. -/
theorem actual_source_four_abscissae (S : ActualPair 15569 n15569_ne_zero) (r : S.Remainders)
    (hs2 : IsSquare (commonSourceReturn (15569 : ℚ_[2]) S.a S.c))
    (hs3 : IsSquare (commonSourceReturn (15569 : ℚ_[3]) S.a S.c)) :
    (abscissa113 (red113 (finitePoint (by norm_num) S.hQ)),
      abscissa113 (red113 (finitePoint (by norm_num) S.hR)))=(some 11,some 81) ∨
    (abscissa113 (red113 (finitePoint (by norm_num) S.hQ)),
      abscissa113 (red113 (finitePoint (by norm_num) S.hR)))=(some 16,some 87) ∨
    (abscissa113 (red113 (finitePoint (by norm_num) S.hQ)),
      abscissa113 (red113 (finitePoint (by norm_num) S.hR)))=(some 81,some 11) ∨
    (abscissa113 (red113 (finitePoint (by norm_num) S.hQ)),
      abscissa113 (red113 (finitePoint (by norm_num) S.hR)))=(some 87,some 16) := by
  obtain ⟨k,m,hk,hm,Z,hU⟩ := actual_H_mod_eight S.U
  obtain ⟨k',m',hk',hm',Z',hV⟩ := actual_H_mod_eight S.V
  obtain ⟨hko,hk'o,hsign⟩ := actual_source_mod_eight_sign S r hU hV hk hm hk' hm' hs2 hs3
  have hpar := (actual_source_coefficient_parities S hU hV).2
  have hlabels := parity_torsion_match hpar
  have hnormsign := sign_to_normalized hsign
  have hodd : (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)) (((k+2*m : ℕ) : ZMod 8))=1 := by
    rw [map_natCast,←ZMod.natCast_mod (k+2*m) 2,show (k+2*m)%2=1 by omega]
    norm_num
  have htable := full_odd_abscissa_table (((k+2*m : ℕ) : ZMod 8)) (m : ZMod 2) hodd
  have hR : abscissa113 (red113 (finitePoint (by norm_num) S.hR))=
      abscissa113 (g113 (((k+2*m : ℕ) : ZMod 8))+t113 (m : ZMod 2)) := by
    rw [source_red_second S r hV,hlabels]
    rcases hnormsign with hsame | hneg
    · rw [hsame]
    · rw [hneg,map_neg]
      have ht : t113 (m : ZMod 2)= -t113 (m : ZMod 2) := by
        rw [←map_neg]
        congr 1
        exact (by decide : ∀ a : ZMod 2, a= -a) _
      have hp : -g113 (((k+2*m : ℕ) : ZMod 8))+t113 (m : ZMod 2)=
          -(g113 (((k+2*m : ℕ) : ZMod 8))+t113 (m : ZMod 2)) := by
        calc
          _ = -g113 (((k+2*m : ℕ) : ZMod 8)) + -t113 (m : ZMod 2) :=
            congrArg (fun P : P113 => -g113 (((k+2*m : ℕ) : ZMod 8))+P) ht
          _ = _ := (neg_add _ _).symm
      rw [hp,abscissa113_neg]
  rw [source_red_first S r hU,hR]
  exact htable

#print axioms normalized_reduction_coefficients
#print axioms actual_source_four_abscissae
end
end FourCorner.Cs15569Completion
