import Cs15569DyadicSplitting
import ActualPairData

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace FourCorner.Cs15569Completion
open CommonSource
noncomputable section

theorem n15569_ne_zero : (15569 : ℤ) ≠ 0 := by norm_num

abbrev ActualH := H 15569 (by norm_num)
def HP : ActualH := ⟨P,P_mem_H⟩
def HG : ActualH := ⟨G,G_mem_H⟩

private theorem lift_ambient_coset {Q R : E} (hh : ∃ z : E, Q=R+2 • z) :
    ∃ z : ActualH, Q=R+2 • (z : E) := by
  obtain ⟨z,hz⟩ := hh
  obtain ⟨Z,hZ,hdouble⟩ := actual_H_halving (Q:=2 • z) ⟨z,rfl⟩
  exact ⟨⟨Z,hZ⟩,by rw [hdouble]; exact hz⟩

/-- Actual complete H/2H generation by the stated points P,G. The halving
compensator is in H because the dyadic direct sum was proved above. -/
theorem actual_H_mod_two : ∀ Q : ActualH, ∃ k m : ℕ, k<2 ∧ m<2 ∧
    ∃ Z : ActualH, Q=k • HG+m • HP+2 • Z := by
  intro Q
  rcases entire_H_ambient_mod_two Q Q.property with h0 | hP | hG | hGP
  · obtain ⟨Z,hZ⟩ := lift_ambient_coset (Q:=(Q:E)) (R:=0) (by simpa using h0)
    refine ⟨0,0,by decide,by decide,Z,?_⟩
    apply Subtype.ext
    simpa only [zero_nsmul,zero_add,AddSubgroup.coe_add,AddSubgroup.coe_nsmul] using hZ
  · obtain ⟨Z,hZ⟩ := lift_ambient_coset hP
    refine ⟨0,1,by decide,by decide,Z,?_⟩
    apply Subtype.ext
    simpa only [zero_nsmul,one_nsmul,zero_add,AddSubgroup.coe_add,AddSubgroup.coe_nsmul,HP] using hZ
  · obtain ⟨Z,hZ⟩ := lift_ambient_coset hG
    refine ⟨1,0,by decide,by decide,Z,?_⟩
    apply Subtype.ext
    simpa only [zero_nsmul,one_nsmul,add_zero,AddSubgroup.coe_add,AddSubgroup.coe_nsmul,HG] using hZ
  · obtain ⟨Z,hZ⟩ := lift_ambient_coset hGP
    refine ⟨1,1,by decide,by decide,Z,?_⟩
    apply Subtype.ext
    simpa only [one_nsmul,AddSubgroup.coe_add,AddSubgroup.coe_nsmul,HG,HP] using hZ

/-- The exact unbounded H/8H generation used in the manuscript; three actual
halving substitutions retain the entire H, not a finite-index subgroup. -/
theorem actual_H_mod_eight : ∀ Q : ActualH, ∃ k m : ℕ, k<8 ∧ m<8 ∧
    ∃ Z : ActualH, Q=k • HG+m • HP+8 • Z :=
  Cs15569Finite.mod_eight_generation HG HP actual_H_mod_two

/-- Exact restricted kernel, with no splitting/kernel premise remaining. -/
theorem actual_H_kummer_kernel (Q : ActualH) :
    δ (Q:E)=1 ↔ ∃ Z : ActualH, 2 • Z=Q := by
  rw [δ,kummerDelta_eq_one_iff_double]
  constructor
  · intro hh
    obtain ⟨Z,hZ,hdouble⟩ := actual_H_halving hh
    exact ⟨⟨Z,hZ⟩,Subtype.ext hdouble⟩
  · rintro ⟨Z,hZ⟩
    exact ⟨(Z:E),congrArg (fun Q : ActualH => (Q:E)) hZ⟩

/-- A raw finite rational source with the two ordered source-square slots
constructs the actual same-source pair. No direct-sum premise is assumed. -/
theorem raw_source_actual_pair {a b c e u v : ℚ}
    (ha : -(15569 : ℚ)<a) (ha0 : a<0) (hc : 15569<c)
    (hQ : CongruentEquation 15569 a b) (hR : CongruentEquation 15569 c e)
    (hu : u^2= -(a*c)/15569) (hv : v^2= -((a-15569)*(c-15569))/15569)
    (hf : IsSquare (commonSourceReturn (15569 : ℚ_[2]) a c)) :
    ∃ S : ActualPair 15569 n15569_ne_zero, S.a=a ∧ S.b=b ∧ S.c=c ∧ S.e=e := by
  obtain ⟨U,hU,tQ,htQ,hQU⟩ := actual_dyadic_splitting (finitePoint (by norm_num) hQ)
  obtain ⟨V,hV,tR,htR,hRV⟩ := actual_dyadic_splitting (finitePoint (by norm_num) hR)
  let S : ActualPair 15569 n15569_ne_zero := {
    a := a
    b := b
    c := c
    e := e
    u := u
    v := v
    hnpos := by norm_num
    han := ha
    ha := ha0
    hc := hc
    hQ := hQ
    hR := hR
    hu := hu
    hv := hv
    U := ⟨U,hU⟩
    V := ⟨V,hV⟩
    tauQ := tQ
    tauR := tR
    htQ := htQ
    htR := htR
    hQU := hQU
    hRV := hRV
    hf := commonRoot_even_val_of_isSquare hf }
  exact ⟨S,rfl,rfl,rfl,rfl⟩

/-- Full actual complete source coset, with the actual distinguished P and
an unrestricted actual H compensator. No representative restriction occurs. -/
theorem actual_pair_complete_coset (S : ActualPair 15569 n15569_ne_zero) :
    ∃ Z : ActualH, S.U+S.V=HP+2 • Z := by
  apply S.complete_coset (Or.inl (by norm_num)) actual_dyadic_direct_sum HP
  constructor
  · intro _
    exact P_kummer
  · intro hbad
    norm_num at hbad

/-- Every actual H compensator has the same ordered global source row.
The equality quantifies over all Z in H, at all heights and depths. -/
theorem entire_compensated_P_class (Z : ActualH) : δ (P+2 • (Z:E))=δ P := by
  have hk : δ (2 • (Z:E))=1 := by
    exact (kummerDelta_eq_one_iff_double 15569 (by norm_num) _).mpr ⟨(Z:E),rfl⟩
  rw [δ_add,hk,mul_one]

#print axioms actual_H_mod_two
#print axioms actual_H_mod_eight
#print axioms actual_H_kummer_kernel
#print axioms raw_source_actual_pair
#print axioms actual_pair_complete_coset
#print axioms entire_compensated_P_class
end
end FourCorner.Cs15569Completion
