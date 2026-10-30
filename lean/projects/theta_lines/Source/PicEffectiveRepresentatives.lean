import DivisorPicPrincipal

noncomputable section
set_option autoImplicit false
open AlgebraicCurve
namespace FourCorner.DivisorPicClassification
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_base_constant (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.ord (algebraMap K F c)=0 := by
  have hn : algebraMap K F c≠0 := (map_ne_zero (algebraMap K F)).mpr hc
  have hpos : 0≤v.ord (algebraMap K F c) :=
    (v.adicValuation_le_one_iff.mp (v.adicValuation_algebraMap_le_one c)).resolve_left hn
  have hneg : 0≤v.ord ((algebraMap K F c)⁻¹) := by
    have hh := (v.adicValuation_le_one_iff.mp
      (v.adicValuation_algebraMap_le_one c⁻¹)).resolve_left ((map_ne_zero (algebraMap K F)).mpr (inv_ne_zero hc))
    simpa only [map_inv₀] using hh
  rw [v.ord_inv] at hneg
  omega

 theorem one_mem_of_effective {D : Divisor K F} (hD : 0≤D) : (1:F)∈LSpace D := by
  apply mem_lSpace_iff_ord.mpr
  right
  intro v
  have hh := hD v
  simpa using neg_nonpos.mpr hh

/-- A positive TRUE LSpace yields a genuine effective divisor of the SAME
Picard class and degree, using the actual divisor of a nonzero section. -/
theorem effective_representative_of_ell_pos [HasPrincipalDivisors K F]
    (D : Divisor K F) (h : 0<ell D) :
    ∃ E : Divisor K F, 0≤E ∧ divisorClass E=divisorClass D ∧
      Divisor.degree E=Divisor.degree D ∧ ell E=ell D := by
  letI : Module.Finite K (LSpace D) := Module.finite_of_finrank_pos h
  letI : Nontrivial (LSpace D) := Module.finrank_pos_iff.mp h
  obtain ⟨x,hx⟩ := exists_ne (0:LSpace D)
  have hx0 : (x:F)≠0 := fun hh=>hx (Subtype.ext hh)
  have hb := (mem_lSpace_iff_ord.mp x.2).resolve_left hx0
  let E : Divisor K F := D+principalDivisor (x:F) hx0
  have hcl : divisorClass E=divisorClass D := by
    apply (class_eq_iff_principal_sub E D).mpr
    refine ⟨x,hx0,fun v=>?_⟩
    simp only [E,Finsupp.sub_apply,Finsupp.add_apply,principalDivisor_apply]
    ring
  refine ⟨E,?_,hcl,?_,ell_eq_of_class_eq hcl⟩
  · intro v
    change 0≤D v+principalDivisor (x:F) hx0 v
    rw [principalDivisor_apply]
    linarith [hb v]
  · simp only [E,map_add,degree_principalDivisor,add_zero]

 theorem effective_representative_of_picEll_pos [HasPrincipalDivisors K F]
    (c : Pic K F) (hc : 0<picEll c) :
    ∃ E : Divisor K F, 0≤E ∧ divisorClass E=c ∧
      Divisor.degree E=picDegree c ∧ ell E=picEll c := by
  obtain ⟨E,hE,hcl,hdeg,hell⟩ := effective_representative_of_ell_pos c.out hc
  have hout : divisorClass c.out=c := Quotient.out_eq c
  refine ⟨E,hE,hcl.trans hout,?_,hell⟩
  rw [hdeg,←picDegree_class,hout]

/-- Uniqueness is proved from dimension ONE of the genuine LSpace, not
assumed as part of an odd-theta or contact-line designation. -/
theorem effective_representative_unique {D E : Divisor K F}
    (hD : 0≤D) (hE : 0≤E) (hell : ell D=1)
    (hcl : divisorClass E=divisorClass D) : E=D := by
  obtain ⟨f,hf,hfdiv⟩ := (class_eq_iff_principal_sub E D).mp hcl
  have hfmem : f∈LSpace D := mem_lSpace_iff_ord.mpr (Or.inr fun v=>by
    have hh:=hfdiv v
    simp only [Finsupp.sub_apply] at hh
    have hev : (0:ℤ)≤E v := hE v
    linarith [hev])
  let oneD : LSpace D := ⟨1,one_mem_of_effective hD⟩
  have h1 : oneD≠0 := fun hh=>one_ne_zero (congrArg Subtype.val hh)
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one hell h1 (⟨f,hfmem⟩:LSpace D)
  have hcf : algebraMap K F c=f := by
    have hh:=congrArg Subtype.val hc
    simpa only [oneD,Submodule.coe_smul_of_tower,Algebra.smul_def,mul_one] using hh
  have hc0 : c≠0 := fun hh=>hf (by rw [←hcf,hh,map_zero])
  ext v
  have hh:=hfdiv v
  rw [←hcf,ord_base_constant v hc0] at hh
  simp only [Finsupp.sub_apply] at hh
  linarith

#print axioms effective_representative_of_picEll_pos
#print axioms effective_representative_unique
end FourCorner.DivisorPicClassification
