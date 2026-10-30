import ThetaCoverClassPortable.HalfCanonicalDifferential
import ThetaCoverClassPortable.SmallSquareSpaceBound

noncomputable section
set_option autoImplicit false
open AlgebraicCurve KaehlerDifferential
namespace FourCorner.DivisorPicClassification
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

 theorem lSpace_mul_mem {D E : Divisor K F} {f g : F}
    (hf : f∈LSpace D) (hg : g∈LSpace E) : f*g∈LSpace (D+E) := by
  by_cases hf0 : f=0
  · simpa [hf0] using (LSpace (D+E)).zero_mem
  by_cases hg0 : g=0
  · simpa [hg0] using (LSpace (D+E)).zero_mem
  have hb := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
  have hc := (mem_lSpace_iff_ord.mp hg).resolve_left hg0
  refine mem_lSpace_iff_ord.mpr (Or.inr fun v=>?_)
  rw [v.ord_mul hf0 hg0,Finsupp.add_apply]
  linarith [hb v,hc v]

/-- The special genus-three bound is obtained from the proved algebraic
multiplication-space lemma, with the actual LSpaces and scalar actions. -/
 theorem effective_ell_le_two_of_double_ell_three [IsAlgClosed K]
    (B : Divisor K F) (hB : 0≤B) (h : ell ((2:ℕ) • B)=3) : ell B≤2 :=
  small_square_space_bound (LSpace B) (LSpace ((2:ℕ) • B))
    (one_mem_of_effective hB)
    (fun f hf g hg=>by simpa only [two_nsmul] using lSpace_mul_mem hf hg) h

variable [IsCurveOver K F] [HasCanonicalDivisor (K:=K) (F:=F)]
variable [∀v : Place K F,v.DCoordGenerates]

 theorem same_canonical_divisor_scalar (hconst : ConstantsAreBase K F)
    {ω η : Ω[F⁄K]} (hω : ω≠0) (hη : η≠0)
    (hdiv : canonicalDivisorOf hω=canonicalDivisorOf hη) :
    ∃ c : K,c≠0 ∧ c • ω=η := by
  obtain ⟨f,hf⟩ := exists_smul_eq_of_finrank_eq_one IsCurveOver.finrank_kaehler hω η
  have hf0 : f≠0 := by
    intro hh
    rw [hh,zero_smul] at hf
    exact hη hf.symm
  have hord : ∀v : Place K F,v.ord f=0 := by
    intro v
    have h1:=congrArg (fun D:Divisor K F=>D v) hdiv
    simp only [canonicalDivisorOf_apply] at h1
    have h2 : v.ordDifferential η=v.ord f+v.ordDifferential ω := by
      rw [←hf]
      exact v.ordDifferential_smul hf0 (coeff_ne_zero hω v)
    linarith
  have hmem : f∈LSpace (0:Divisor K F) :=
    mem_lSpace_iff_ord.mpr (Or.inr fun v=>by simpa [hord v])
  rw [hconst] at hmem
  obtain ⟨c,hc⟩ := hmem
  have hcf : algebraMap K F c=f := hc
  refine ⟨c,fun hc0=>hf0 (by rw [←hcf,hc0,map_zero]),?_⟩
  rw [←hcf] at hf
  simpa only [algebraMap_smul] using hf

/-- Intrinsic odd theta classes have ONE genuine effective representative.
The two canonical facts are standard geometric inputs; the actual original
curve application below discharges them by its proved genus-three RR. -/
 theorem oddTheta_effective_unique [IsAlgClosed K]
    (hdegree : picDegree (canonicalClass K F)=4)
    (hellK : ∀{ω : Ω[F⁄K]} (hω : ω≠0),ell (canonicalDivisorOf hω)=3)
    (c : Pic K F) (hc : IsOddThetaClass c) :
    ∃ B : Divisor K F,0≤B ∧ divisorClass B=c ∧ Divisor.degree B=2 ∧ ell B=1 ∧
      (∀E : Divisor K F,0≤E → divisorClass E=c → E=B) ∧
      ∃(ω : Ω[F⁄K])(hω : ω≠0),ω∈regularDifferentials K F ∧
        canonicalDivisorOf hω=(2:ℕ) • B := by
  have hpos : 0<picEll c := hc.2.pos
  obtain ⟨B,hB,hcl,hdeg,hell⟩ := effective_representative_of_picEll_pos c hpos
  have hdegc : picDegree c=2 := by
    have hh:=congrArg (fun z:Pic K F=>picDegree z) hc.1
    rw [map_nsmul,hdegree] at hh
    norm_num only [nsmul_eq_mul] at hh
    omega
  have hhalf : (2:ℕ) • divisorClass B=canonicalClass K F := by rw [hcl];exact hc.1
  obtain ⟨ω,hω,hreg,hcan⟩ := half_canonical_effective_differential B hB hhalf
  have hb2 : ell ((2:ℕ) • B)=3 := by rw [←hcan];exact hellK hω
  have hle := effective_ell_le_two_of_double_ell_three B hB hb2
  have hell1 : ell B=1 := by
    obtain ⟨n,hn⟩ := hc.2
    omega
  refine ⟨B,hB,hcl,hdeg.trans hdegc,hell1,?_,ω,hω,hreg,hcan⟩
  intro E hE hEc
  exact effective_representative_unique hB hE hell1 (hEc.trans hcl.symm)

#print axioms effective_ell_le_two_of_double_ell_three
#print axioms same_canonical_divisor_scalar
#print axioms oddTheta_effective_unique
end FourCorner.DivisorPicClassification
