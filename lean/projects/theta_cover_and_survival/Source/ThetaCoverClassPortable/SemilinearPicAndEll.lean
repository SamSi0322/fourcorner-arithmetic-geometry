import ThetaCoverClassPortable.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import ThetaCoverClassPortable.DivisorPicPrincipal

noncomputable section
set_option autoImplicit false
open AlgebraicCurve
namespace FourCorner.SemilinearPicAndEll
open DivisorPicClassification
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Extend the genuine principal-divisor action to the FULL divisor Pic,
not only Pic0, using the actual quotient additive homomorphism. -/
instance : SMul (SemilinearAut K F) (Pic K F) where
  smul g := QuotientAddGroup.map (Divisor.principal (K:=K) (F:=F))
    (Divisor.principal (K:=K) (F:=F)) (DistribSMul.toAddMonoidHom (Divisor K F) g)
    (by intro D h;change g • D∈Divisor.principal;exact SemilinearAut.smul_mem_principal g h)

 theorem pic_smul_class (g : SemilinearAut K F) (D : Divisor K F) :
    g • divisorClass D=divisorClass (g • D) := rfl

instance : DistribMulAction (SemilinearAut K F) (Pic K F) where
  one_smul c := by
    obtain ⟨D,rfl⟩ := QuotientAddGroup.mk_surjective c
    change divisorClass ((1:SemilinearAut K F) • D)=divisorClass D
    rw [one_smul]
  mul_smul g h c := by
    obtain ⟨D,rfl⟩ := QuotientAddGroup.mk_surjective c
    change divisorClass ((g*h) • D)=divisorClass (g • h • D)
    rw [mul_smul]
  smul_zero g := by
    change divisorClass (g • (0:Divisor K F))=divisorClass 0
    rw [smul_zero]
  smul_add g c d := by
    obtain ⟨D,rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨E,rfl⟩ := QuotientAddGroup.mk_surjective d
    change divisorClass (g • (D+E))=divisorClass (g • D+g • E)
    rw [smul_add]

 theorem smul_effective (g : SemilinearAut K F) {D : Divisor K F} (hD : 0≤D) : 0≤g • D := by
  intro v
  change 0≤(g • D) v
  rw [SemilinearAut.divisor_smul_apply]
  exact hD (g⁻¹ • v)

 theorem smul_mem_lSpace (g : SemilinearAut K F) (D : Divisor K F) {f : F}
    (hf : f∈LSpace D) : g • f∈LSpace (g • D) := by
  by_cases hf0 : f=0
  · simpa [hf0] using (LSpace (g • D)).zero_mem
  have hb := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
  apply mem_lSpace_iff_ord.mpr
  right
  intro w
  have hh:=SemilinearAut.ord_smul g (g⁻¹ • w) f
  rw [smul_inv_smul] at hh
  rw [hh,SemilinearAut.divisor_smul_apply]
  exact hb _

/-- The genuine additive isomorphism of actual LSpaces, with explicit
semilinearity over the actual base automorphism proved next. -/
def lSpaceAddEquiv (g : SemilinearAut K F) (D : Divisor K F) : LSpace D ≃+ LSpace (g • D) where
  toFun f := ⟨g • (f:F),smul_mem_lSpace g D f.2⟩
  invFun f := ⟨g⁻¹ • (f:F),by
    have hh:=smul_mem_lSpace g⁻¹ (g • D) f.2
    simpa only [inv_smul_smul] using hh⟩
  left_inv f := by ext;exact inv_smul_smul g (f:F)
  right_inv f := by ext;exact smul_inv_smul g (f:F)
  map_add' f h := by ext;exact smul_add g (f:F) (h:F)

@[simp] theorem lSpaceAddEquiv_apply (g : SemilinearAut K F) (D : Divisor K F) (f : LSpace D) :
    (lSpaceAddEquiv g D f:F)=g • (f:F) := rfl

 theorem lSpaceAddEquiv_smul (g : SemilinearAut K F) (D : Divisor K F)
    (a : K) (f : LSpace D) :
    lSpaceAddEquiv g D (a • f)=SemilinearAut.baseAut g a • lSpaceAddEquiv g D f := by
  apply Subtype.ext
  simp only [lSpaceAddEquiv_apply,Submodule.coe_smul_of_tower,Algebra.smul_def]
  rw [smul_mul',SemilinearAut.smul_algebraMap]

 theorem ell_smul (g : SemilinearAut K F) (D : Divisor K F) : ell (g • D)=ell D := by
  have hh := rank_eq_of_equiv_equiv (SemilinearAut.baseAut g) (lSpaceAddEquiv g D)
    (SemilinearAut.baseAut g).bijective (lSpaceAddEquiv_smul g D)
  exact (congrArg Cardinal.toNat hh).symm

 theorem picEll_smul (g : SemilinearAut K F) (c : Pic K F) : picEll (g • c)=picEll c := by
  obtain ⟨D,rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [pic_smul_class,picEll_class,picEll_class,ell_smul]

 theorem picDegree_smul [HasPrincipalDivisors K F] (g : SemilinearAut K F) (c : Pic K F) :
    picDegree (g • c)=picDegree c := by
  obtain ⟨D,rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [pic_smul_class,picDegree_class,picDegree_class,SemilinearAut.degree_smul]

#print axioms lSpaceAddEquiv_smul
#print axioms ell_smul
#print axioms picEll_smul
end FourCorner.SemilinearPicAndEll
