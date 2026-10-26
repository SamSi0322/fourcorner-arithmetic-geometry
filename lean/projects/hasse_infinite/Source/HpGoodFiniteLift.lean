import HpBranchAlgebra
import HpHenselInfinity

namespace FourCorner.HpGoodFiniteLift
open HpResidueCharts HpLiteralField HpBranchPlaces HpBranchAlgebra HpHenselOrdinary
noncomputable section
variable {q : ℕ} [Fact q.Prime]

 theorem norm_eq_one_of_residue (x : ℤ_[q]) (hx : PadicInt.toZMod x ≠ 0) : ‖(x : ℚ_[q])‖=1 := by
  apply le_antisymm x.property
  by_contra hn
  have hh : ‖x‖<1 := lt_of_not_ge hn
  exact hx ((padicInt_norm_lt_one_iff_residue_zero x).mp hh)

/-- The exact rational branch centers have integral representatives whenever
the three original parameter coefficients have good reduction. -/
theorem centers (p : ℚ) (P : ℤ_[q]) (hP : (P : ℚ_[q])=(p : ℚ_[q]))
    (ha : PadicInt.toZMod P-1 ≠ 0) :
    ∃ A : Fin 4 → ℤ_[q],∀i,(A i : ℚ_[q])=((branch ℚ p i : ℚ) : ℚ_[q]) := by
  have hnorm : ‖((P-1 : ℤ_[q]) : ℚ_[q])‖=1 :=
    norm_eq_one_of_residue (P-1) (by simpa only [map_sub,map_one] using ha)
  let AI : ℤ_[q] := ⟨((P-1 : ℤ_[q]) : ℚ_[q])⁻¹,by rw [norm_inv,hnorm];norm_num⟩
  let A : Fin 4 → ℤ_[q] := ![0,1,-1,-(P+1)*AI]
  refine ⟨A,?_⟩
  intro i
  have hi : (AI : ℚ_[q])=((p : ℚ_[q])-1)⁻¹ := by
    change (((P-1 : ℤ_[q]) : ℚ_[q]))⁻¹=((p : ℚ_[q])-1)⁻¹
    rw [PadicInt.coe_sub,PadicInt.coe_one,hP]
  fin_cases i
  · simp [A,branch]
  · simp [A,branch]
  · simp [A,branch]
  · change ((-(P+1)*AI : ℤ_[q]) : ℚ_[q])=((-(p+1)/(p-1) : ℚ) : ℚ_[q])
    rw [PadicInt.coe_mul,PadicInt.coe_neg,PadicInt.coe_add,PadicInt.coe_one,hP,hi]
    push_cast
    rfl

/-- All finite residue points lift on the actual four-root source. The
zero-root case uses its exact rational branch center and free root; no
nonzero-residue or ordinary-chart hypothesis is inserted. -/
theorem finite (hq : q ≠ 2) (p : ℚ) (hp : 1<p) (P : ℤ_[q])
    (hP : (P : ℚ_[q])=(p : ℚ_[q]))
    (hP0 : PadicInt.toZMod P ≠ 0) (hPa : PadicInt.toZMod P-1 ≠ 0)
    (hPb : PadicInt.toZMod P+1 ≠ 0)
    (a : ZMod q) (r0 : Fin 4 → ZMod q) (hr0 : ∀i,r0 i^2=values (PadicInt.toZMod P) a i) :
    ∃S : HasseNorms.LocalPoint ℚ_[q] (p : ℚ_[q]),Transcendental ℚ S.rho := by
  classical
  letI : NeZero (2 : ZMod q) := ⟨by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff 2 q).mp he
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (Fact.out : q.Prime).ne_one h
    · exact hq h⟩
  by_cases hn : ∀i,r0 i ≠ 0
  · obtain ⟨A,hA⟩ := ZMod.ringHom_surjective PadicInt.toZMod a
    exact HpHenselOrdinary.ordinary hq p P A hP r0 (by simpa only [hA]) hn
  · push_neg at hn
    obtain ⟨pivot,hzero⟩ := hn
    have hother := roots_at_most_one_zero (PadicInt.toZMod P) a hP0 hPa hPb r0 hr0 pivot hzero
    obtain ⟨A,hA⟩ := centers p P hP hPa
    have hp0 : p ≠ 0 := by linarith
    have hpa : p-1 ≠ 0 := by linarith
    have hpb : p+1 ≠ 0 := by linarith
    have hqpa : (p : ℚ_[q])-1 ≠ 0 := by exact_mod_cast hpa
    have hAzero : values P (A pivot) pivot=0 := by
      apply Subtype.ext
      change ((values P (A pivot) pivot : ℤ_[q]) : ℚ_[q])=0
      have hm := map_values (PadicInt.Coe.ringHom (p:=q)) P (A pivot) pivot
      change ((values P (A pivot) pivot : ℤ_[q]) : ℚ_[q])=
        values (P : ℚ_[q]) (A pivot : ℚ_[q]) pivot at hm
      rw [hm,hP,hA,values_factor _ _ hqpa]
      have hbmap : ((branch ℚ p pivot : ℚ) : ℚ_[q])=branch ℚ_[q] (p : ℚ_[q]) pivot := by
        simpa using map_branch (Rat.castHom ℚ_[q]) p pivot
      rw [hbmap,sub_self,mul_zero]
    have hcenter : PadicInt.toZMod (A pivot)=a := by
      have hz : values (PadicInt.toZMod P) (PadicInt.toZMod (A pivot)) pivot=0 := by
        rw [← map_values,hAzero,map_zero]
      have hz' : values (PadicInt.toZMod P) a pivot=0 := by rw [← hr0,hzero];norm_num
      exact ((values_zero_iff _ _ hP0 hPa hPb pivot).mp hz).trans
        ((values_zero_iff _ _ hP0 hPa hPb pivot).mp hz').symm
    obtain ⟨e,r,he,hrne,hrs⟩ := HpHenselBranch.branch hq p (branch ℚ p pivot)
      (coefficient ℚ p pivot)⁻¹ (inv_ne_zero (coefficient_ne_zero ℚ p hp0 hpa hpb pivot))
      P (A pivot) hP (hA pivot) pivot (pivot_parameter p hp0 hpa hpb pivot)
      r0 (by simpa only [hcenter]) hother
    exact ⟨toLocalPoint p e he r hrne hrs,he⟩

#print axioms centers
#print axioms finite
end
end FourCorner.HpGoodFiniteLift
