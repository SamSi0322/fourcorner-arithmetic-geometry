import Cs15569DyadicGeneration

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

theorem δ_nsmul (Q : E) (k : ℕ) : δ (k • Q)=(δ Q)^k := by
  unfold δ
  rw [ofAdd_nsmul,map_pow]

theorem δ_eight (Q : E) : δ (8 • Q)=1 := by
  apply (kummerDelta_eq_one_iff_double 15569 (by norm_num) _).mpr
  exact ⟨4 • Q,by simp only [smul_smul]; norm_num⟩

private theorem N_order : orderOf N=2 :=
  orderOf_eq_prime (by simpa only [pow_two] using N_mul_N) N_ne_one

private theorem N_pow_one (k : ℕ) : N^k=1 ↔ k%2=0 := by
  rw [←orderOf_dvd_iff_pow_eq_one,N_order,Nat.dvd_iff_mod_eq_zero]

/-- Ordered Kummer rows for arbitrary SAME whole-H mod8 coefficients. -/
theorem coefficient_kummer {Q Z : ActualH} {k m : ℕ}
    (he : Q=k • HG+m • HP+8 • Z) :
    δ (Q:E) 0=N^(k+m) ∧ δ (Q:E) 1=N^k := by
  have he' := congrArg (fun Q : ActualH => (Q:E)) he
  change (Q:E)=k • G+m • P+8 • (Z:E) at he'
  rw [he',δ_add,δ_add,δ_nsmul,δ_nsmul,δ_eight]
  simp only [Pi.mul_apply,Pi.pow_apply,Pi.one_apply]
  rw [G_kummer.1,P_kummer.1,G_kummer.2,P_kummer.2,one_pow,mul_one,mul_one,mul_one,pow_add]
  exact ⟨rfl,rfl⟩

/-- The complete P+2H source coset forces the exact manuscript parities.
Both mod8 coefficient representations refer to the same actual U,V. -/
theorem actual_source_coefficient_parities (S : ActualPair 15569 n15569_ne_zero)
    {Z Z' : ActualH} {k m k' m' : ℕ}
    (hU : S.U=k • HG+m • HP+8 • Z)
    (hV : S.V=k' • HG+m' • HP+8 • Z') :
    (k+k')%2=0 ∧ (m+m')%2=1 := by
  obtain ⟨C,hC⟩ := actual_pair_complete_coset S
  have hC' := congrArg (fun Q : ActualH => (Q:E)) hC
  change (S.U:E)+(S.V:E)=P+2 • (C:E) at hC'
  have hδ : δ (S.U:E)*δ (S.V:E)=δ P := by
    rw [←δ_add,hC',entire_compensated_P_class]
  have hk := congrFun hδ 1
  have hm := congrFun hδ 0
  simp only [Pi.mul_apply] at hk hm
  rw [(coefficient_kummer hU).2,(coefficient_kummer hV).2,P_kummer.2,←pow_add] at hk
  rw [(coefficient_kummer hU).1,(coefficient_kummer hV).1,P_kummer.1,←pow_add] at hm
  have hkpar := (N_pow_one (k+k')).mp hk
  have htot : ((k+m)+(k'+m'))%2=1 := by
    by_contra hn
    have hh : ((k+m)+(k'+m'))%2=0 := by omega
    have hp := (N_pow_one _).mpr hh
    exact N_ne_one (hm.symm.trans hp)
  exact ⟨hkpar,by omega⟩

theorem actual_source_mod_eight (S : ActualPair 15569 n15569_ne_zero) :
    ∃ k m k' m' : ℕ, k<8 ∧ m<8 ∧ k'<8 ∧ m'<8 ∧
      ∃ Z Z' : ActualH, S.U=k • HG+m • HP+8 • Z ∧
        S.V=k' • HG+m' • HP+8 • Z' ∧ (k+k')%2=0 ∧ (m+m')%2=1 := by
  obtain ⟨k,m,hk,hm,Z,hU⟩ := actual_H_mod_eight S.U
  obtain ⟨k',m',hk',hm',Z',hV⟩ := actual_H_mod_eight S.V
  exact ⟨k,m,k',m',hk,hm,hk',hm',Z,Z',hU,hV,actual_source_coefficient_parities S hU hV⟩

#print axioms coefficient_kummer
#print axioms actual_source_coefficient_parities
#print axioms actual_source_mod_eight
end
end FourCorner.Cs15569Completion
