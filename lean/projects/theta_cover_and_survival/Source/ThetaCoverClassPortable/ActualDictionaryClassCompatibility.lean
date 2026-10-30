import ThetaCoverClassPortable.ActualPic0DictionaryFMD

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry AlgebraicCurve CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.RelPicard
open P2MW.ActualPic0DictionaryFMD.AlgebraicGeometry.RelPicard.PtsCoreGlue
universe u v
namespace FourCorner.ActualGeometricCoverDeltaComparison

/-- The native dictionary is fixed by the actual Poincare sheaf class, for
any genuine divisor-class map with its kernel-point normalization. -/
theorem exists_dictionary_with_class
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c)
    (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    {F : Type v} [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]
    (M : CurveModel k F) (e : M.C ≅ C) (he : e.hom ≫ c = M.toBase)
    (ε' : {p : Spec (.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (hε' : ε'.1 ≫ e.hom = ε.1)
    (cl : M.C.Modules → Pic k F)
    (hcl_iso : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L = cl L')
    (hcl_tensor : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
      cl (L ⊗ L') = cl L + cl L')
    (hcl_one : cl (𝟙_ M.C.Modules) = 0)
    (hcl_pt : ∀ (P : {p : Spec (.of k) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) (n : ℕ),
      cl (((P.1.ker)^n).invModule) = QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace P) (1:ℤ)) ∧
      cl (((P.1.ker)^n).module) = QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace P) (1:ℤ)))) :
    letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
    ∃ pts : Pic0 k F ≃ (Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk J.toBase),
      (∀ a b, pts (a+b)=pts a*pts b) ∧
      ∀ Dv : Divisor.degZero (K:=k) (F:=F),
        cl ((Scheme.Modules.pullback (e.hom ≫ toProdSpec c)).obj
          (h.poincare.pullbackAlong ⟨(pts (Pic0.mk Dv)).left,Over.w (pts (Pic0.mk Dv))⟩).L) =
        QuotientAddGroup.mk (Dv : Divisor k F) := by
  classical
  letI := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition J from h).grpObj
  obtain ⟨pts,hmul,hlist,-⟩ := P2MW.ActualPic0DictionaryFMD.solution k c ε 𝔉 J h M e he ε' hε'
  have hker : ∀ (P : {p : Spec (.of k) ⟶ M.C // p ≫ M.toBase=𝟙 _}) (n:ℕ),
      ((P.1.ker)^n).IsInvertible := fun P n =>
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p:=M.toBase) P.1 P.2).pow n
  have hfold : ∀ l : List {p : Spec (.of k) ⟶ M.C // p ≫ M.toBase=𝟙 _},
      Scheme.Modules.IsInvertible
        (l.foldr (fun P A => ((((P.1.ker)^1).invModule ⊗ (((ε'.1).ker)^1).module) ⊗ A)) (𝟙_ M.C.Modules)) ∧
      cl (l.foldr (fun P A => ((((P.1.ker)^1).invModule ⊗ (((ε'.1).ker)^1).module) ⊗ A)) (𝟙_ M.C.Modules)) =
        QuotientAddGroup.mk ((l.map fun P=>Finsupp.single (M.pointEquivPlace P) (1:ℤ)).sum -
          (l.length:ℤ) • Finsupp.single (M.pointEquivPlace ε') 1) := by
    intro l
    induction l with
    | nil =>
      refine ⟨Scheme.Modules.isInvertible_unit _, ?_⟩
      simpa only [List.foldr_nil,List.map_nil,List.sum_nil,List.length_nil,Nat.cast_zero,zero_smul,
        sub_zero,QuotientAddGroup.mk_zero] using hcl_one
    | cons P l ih =>
      have hp := (hker P 1).isInvertible_invModule.tensor (hker ε' 1).isInvertible_module
      refine ⟨hp.tensor ih.1,?_⟩
      rw [List.foldr_cons,hcl_tensor _ _ hp ih.1,hcl_tensor _ _ (hker P 1).isInvertible_invModule
        (hker ε' 1).isInvertible_module,(hcl_pt P 1).1,(hcl_pt ε' 1).2,ih.2]
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_succ,one_smul,add_smul]
      rw [←QuotientAddGroup.mk_add,←QuotientAddGroup.mk_add]
      congr 1
      abel
  refine ⟨pts,hmul,fun Dv=>?_⟩
  obtain ⟨l,hl⟩ := AlgebraicCurve.exists_list_isPrincipal_sub_sum_single_sub_smul_single
    (M.pointEquivPlace ε') (Dv:Divisor k F) (Divisor.mem_degZero.mp Dv.2)
  let Ps := l.map M.pointEquivPlace.symm
  let D' : Divisor k F := (l.map fun w=>Finsupp.single w (1:ℤ)).sum -
    (l.length:ℤ) • Finsupp.single (M.pointEquivPlace ε') 1
  have hD' : D' ∈ Divisor.degZero (K:=k) (F:=F) := by
    rw [Divisor.mem_degZero]
    simp [D',map_sub,map_list_sum,Function.comp_def,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]
  let Dv' : Divisor.degZero (K:=k) (F:=F) := ⟨D',hD'⟩
  have hclass : Pic0.mk Dv = Pic0.mk Dv' := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    exact hl
  have hmap : (Ps.map fun P=>Finsupp.single (M.pointEquivPlace P) (1:ℤ)).sum -
      (Ps.length:ℤ) • Finsupp.single (M.pointEquivPlace ε') 1 = D' := by
    simp only [Ps,List.map_map,List.length_map,Function.comp_def,Equiv.apply_symm_apply]
    rfl
  obtain ⟨i⟩ := hlist Ps Dv' hmap.symm
  obtain ⟨iF⟩ := nonempty_pullback_pointsSubBasepointModule_iso_foldr c M.toBase e.hom he ε ε' hε' Ps
  rw [hclass]
  rw [hcl_iso _ _ ((h.poincare.pullbackAlong _).isInvertible.pullback _) ⟨
    (Scheme.Modules.pullback (e.hom ≫ toProdSpec c)).mapIso i ≪≫ iF⟩,(hfold Ps).2,hmap]
  exact (QuotientAddGroup.eq_iff_sub_mem.mpr hl).symm

/-- Equality is detected by the native class of the actual Poincare fibre;
this rules out replacing the canonical dictionary by an arbitrary equivalence. -/
theorem dictionary_point_eq_iff_class
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (.of k))
    (ε : SchemeHomOver (𝟙 (Spec (.of k))) c) (J : RelativePic0Designation k c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    {F : Type v} [Field F] [Algebra k F]
    (M : CurveModel k F) (e : M.C ≅ C) (cl : M.C.Modules → Pic k F)
    (pts : Pic0 k F ≃ (Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk J.toBase))
    (hclass : ∀ Dv : Divisor.degZero (K:=k) (F:=F),
      cl ((Scheme.Modules.pullback (e.hom ≫ toProdSpec c)).obj
        (h.poincare.pullbackAlong ⟨(pts (Pic0.mk Dv)).left,Over.w (pts (Pic0.mk Dv))⟩).L)=
      QuotientAddGroup.mk (Dv:Divisor k F))
    (p : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk J.toBase) (Dv : Divisor.degZero (K:=k) (F:=F)) :
    pts (Pic0.mk Dv)=p ↔
      cl ((Scheme.Modules.pullback (e.hom ≫ toProdSpec c)).obj
        (h.poincare.pullbackAlong ⟨p.left,Over.w p⟩).L)=QuotientAddGroup.mk (Dv:Divisor k F) := by
  constructor
  · intro heq
    rw [←heq]
    exact hclass Dv
  · intro hp
    obtain ⟨ξ,rfl⟩ := pts.surjective p
    obtain ⟨E,rfl⟩ := Pic0.mk_surjective ξ
    rw [hclass] at hp
    have he : Pic0.mk Dv=Pic0.mk E := by
      rw [pic0_mk_eq_iff]
      exact hp.symm
    exact congrArg pts he

end FourCorner.ActualGeometricCoverDeltaComparison
