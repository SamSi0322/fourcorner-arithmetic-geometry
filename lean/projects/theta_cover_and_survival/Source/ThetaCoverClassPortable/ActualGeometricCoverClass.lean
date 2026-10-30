import ThetaCoverClassPortable.ActualNativeModelPlaces
import ThetaCoverClassPortable.ActualDictionaryClassCompatibility
import ThetaCoverClassPortable.ThetaCoverPointModuleComparison
import ThetaCoverClassPortable.ThetaCoverPic0

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory NeronModelInfra
namespace FourCorner.ActualGeometricCoverDeltaComparison
open ThetaDGeometricModel SmoothProperRationalPointPlaces SmoothProperClosedPointPlaces
local instance : IsIntegral geometricD := geometric_integral
local instance : Algebra K field := fieldAlgebra
local instance : IsCurveOver K field := field_isCurveOver
local instance : Algebra.EssFiniteType K field := field_essFiniteType
local instance : IsProper toBase := geometric_proper
local instance : SmoothOfRelativeDimension 1 toBase := geometric_smooth

abbrev modelPoint (M : CurveModel K field) (i : geometricD ≅ M.C) (hi : i.hom ≫ M.toBase=toBase)
    (P : RationalPoint toBase) : RationalPoint M.toBase :=
  ⟨P.val ≫ i.hom,by rw [Category.assoc,hi];exact P.property⟩

def pairDivisor (p : PointPairTensorFamily.Pair toBase) : Divisor K field :=
  Finsupp.single (pointEquivRationalPlace toBase ⟨p.1.val,p.1.property⟩).val 1 -
  Finsupp.single (pointEquivRationalPlace toBase ⟨p.2.val,p.2.property⟩).val 1

lemma actual_pair_divisor_sum : (ThetaActualPointPairs.actualPairs.map pairDivisor).sum =
    ThetaCoverBoundaryPoints.boundarySum-ThetaDCanonicalInfinityDivisor.infinitySum := by
  unfold ThetaActualPointPairs.actualPairs
  rw [List.map_ofFn,List.sum_ofFn]
  change (∑j : Fin 4,(Finsupp.single (ThetaCoverBoundaryPoints.place (ThetaActualPointPairs.boundaryEnumeration j)) 1 -
    Finsupp.single (ThetaDFourInfinityPlaces.place (ThetaActualPointPairs.infinityEnumeration j)) 1))=_
  rw [Finset.sum_sub_distrib,
    ThetaActualPointPairs.boundaryEnumeration.sum_comp (fun p=>Finsupp.single (ThetaCoverBoundaryPoints.place p) (1:ℤ)),
    ThetaActualPointPairs.infinityEnumeration.sum_comp (fun p=>Finsupp.single (ThetaDFourInfinityPlaces.place p) (1:ℤ)),
    ThetaActualPointPairs.infinitySum_eq]
  rfl

theorem actual_geometric_cover_class
    (M : CurveModel K field) (i : geometricD ≅ M.C) (hi : i.hom ≫ M.toBase=toBase)
    (hgeneric : geometricD.fromSpecStalk (genericPoint geometricD) ≫ i.hom=
      Spec.map (CommRingCat.ofHom M.ffEquiv.symm.toRingHom) ≫ M.C.fromSpecStalk (genericPoint M.C))
    (cl : M.C.Modules → Pic K field)
    (hcl_iso : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L=cl L')
    (hcl_tensor : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
      cl (L⊗L')=cl L+cl L')
    (hcl_one : cl (𝟙_ M.C.Modules)=0)
    (hcl_pt : ∀ (P : RationalPoint M.toBase) (n : ℕ),
      cl (((P.val.ker)^n).invModule)=QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace P) (1:ℤ)) ∧
      cl (((P.val.ker)^n).module)=QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace P) (1:ℤ)))) :
    cl ((Scheme.Modules.pullback i.inv).obj ThetaGeometricKummerLine.L)=
      QuotientAddGroup.mk (ThetaCoverPic0.zeroDegreeDivisor : Divisor K field) := by
  have hinv : ∀ P : PointPairTensorFamily.Point toBase, P.val.ker.IsInvertible := fun P=>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p:=toBase) P.val P.property
  have hminv : ∀ P : RationalPoint M.toBase,P.val.ker.IsInvertible := fun P=>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p:=M.toBase) P.val P.property
  have pairInv : ∀ p : PointPairTensorFamily.Pair toBase,
      Scheme.Modules.IsInvertible (PointPairTensorFamily.pairModule toBase p) := fun p=>
    (hinv p.1).isInvertible_invModule.tensor (hinv p.2).isInvertible_module
  have listInv : ∀ ps : List (PointPairTensorFamily.Pair toBase),
      Scheme.Modules.IsInvertible (PointPairTensorFamily.tensorModule toBase ps) := by
    intro ps
    induction ps with
    | nil => exact Scheme.Modules.isInvertible_unit _
    | cons p ps ih => exact (pairInv p).tensor ih
  have hp : ∀ P : PointPairTensorFamily.Point toBase,
      Nonempty ((Scheme.Modules.pullback i.inv).obj P.val.ker.invModule ≅
        (modelPoint M i hi ⟨P.val,P.property⟩).val.ker.invModule) ∧
      Nonempty ((Scheme.Modules.pullback i.inv).obj P.val.ker.module ≅
        (modelPoint M i hi ⟨P.val,P.property⟩).val.ker.module) := by
    intro P
    have he : (modelPoint M i hi ⟨P.val,P.property⟩).val ≫ i.inv=P.val := by
      simp only [modelPoint,Category.assoc,Iso.hom_inv_id,Category.comp_id]
    haveI : IsClosedImmersion P.val := isClosedImmersion_of_comp_eq_id toBase P.val P.property
    simpa only [pow_one] using Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso i.inv P.val
      (modelPoint M i hi ⟨P.val,P.property⟩).val he (hinv P) (hminv _) 1
  have hpair : ∀ p : PointPairTensorFamily.Pair toBase,
      cl ((Scheme.Modules.pullback i.inv).obj (PointPairTensorFamily.pairModule toBase p))=
        QuotientAddGroup.mk (pairDivisor p) := by
    intro p
    obtain ⟨eP⟩ := (hp p.1).1
    obtain ⟨eQ⟩ := (hp p.2).2
    have hP := (hcl_pt (modelPoint M i hi ⟨p.1.val,p.1.property⟩) 1).1
    have hQ := (hcl_pt (modelPoint M i hi ⟨p.2.val,p.2.property⟩) 1).2
    simp only [pow_one,one_smul] at hP hQ
    simp only [actual_model_point_place toBase M i hi hgeneric] at hP hQ
    rw [hcl_iso _ _ ((pairInv p).pullback i.inv) ⟨
      Scheme.Modules.pullbackTensorObjIso i.inv _ _ ≪≫ tensorIso eP eQ⟩,
      hcl_tensor _ _ (hminv _).isInvertible_invModule (hminv _).isInvertible_module,hP,hQ,
      ←QuotientAddGroup.mk_add]
    simp only [pairDivisor,sub_eq_add_neg]
  have hlist : ∀ ps : List (PointPairTensorFamily.Pair toBase),
      cl ((Scheme.Modules.pullback i.inv).obj (PointPairTensorFamily.tensorModule toBase ps))=
        QuotientAddGroup.mk ((ps.map pairDivisor).sum) := by
    intro ps
    induction ps with
    | nil =>
      change cl ((Scheme.Modules.pullback i.inv).obj (𝟙_ geometricD.Modules))=QuotientAddGroup.mk (0:Divisor K field)
      calc
        _ = cl (𝟙_ M.C.Modules) := hcl_iso _ _ ((show Scheme.Modules.IsInvertible (𝟙_ geometricD.Modules)
          from Scheme.Modules.isInvertible_unit _).pullback i.inv) ⟨Scheme.Modules.pullbackTensorUnitObjIso i.inv⟩
        _ = _ := hcl_one.trans (QuotientAddGroup.mk_zero _).symm
    | cons p ps ih =>
      rw [PointPairTensorFamily.tensorModule,hcl_iso _ _ (((pairInv p).tensor (listInv ps)).pullback i.inv)
        ⟨Scheme.Modules.pullbackTensorObjIso i.inv _ _⟩,
        hcl_tensor _ _ ((pairInv p).pullback i.inv) ((listInv ps).pullback i.inv),hpair,ih,
        ←QuotientAddGroup.mk_add]
      rfl
  obtain ⟨eL⟩ := ThetaCoverPointModuleComparison.actual_module_iso
  have hLinv : Scheme.Modules.IsInvertible ThetaGeometricKummerLine.L := ThetaQQKummerLine.L_invertible.pullback _
  rw [hcl_iso _ _ (hLinv.pullback i.inv) ⟨(Scheme.Modules.pullback i.inv).mapIso eL⟩,
    hlist,actual_pair_divisor_sum]
  rfl

end FourCorner.ActualGeometricCoverDeltaComparison
