import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry

/-- The actual graph commutes with arbitrary change of its test scheme. -/
theorem graphOver_mapOnProdOver {C S : Scheme.{u}} (f : C ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (a : T' ⟶ C) (ha : a ≫ f = g') (q : T ⟶ T') (hq : q ≫ g' = g) :
    graphOver f (q ≫ a) (by rw [Category.assoc, ha, hq]) ≫ mapOnProdOver f q hq =
      q ≫ graphOver f a ha := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- This is a genuine scheme pullback square, without flatness or reducedness. -/
theorem isPullback_graphOver_mapOnProdOver {C S : Scheme.{u}} (f : C ⟶ S)
    {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (a : T' ⟶ C) (ha : a ≫ f = g') (q : T ⟶ T') (hq : q ≫ g' = g) :
    IsPullback (graphOver f (q ≫ a) (by rw [Category.assoc, ha, hq])) q
      (mapOnProdOver f q hq) (graphOver f a ha) := by
  have hsnd {Z : Scheme.{u}} (l : Z ⟶ pullback f g) (r : Z ⟶ T')
      (h : l ≫ mapOnProdOver f q hq = r ≫ graphOver f a ha) :
      (l ≫ pullback.snd f g) ≫ q = r := by
    have h' := congrArg (fun k => k ≫ pullback.snd f g') h
    simpa only [Category.assoc, mapOnProdOver_snd, graphOver_snd, Category.comp_id] using h'
  have hfst {Z : Scheme.{u}} (l : Z ⟶ pullback f g) (r : Z ⟶ T')
      (h : l ≫ mapOnProdOver f q hq = r ≫ graphOver f a ha) :
      l ≫ pullback.fst f g = r ≫ a := by
    have h' := congrArg (fun k => k ≫ pullback.fst f g') h
    simpa only [Category.assoc, mapOnProdOver_fst, graphOver_fst] using h'
  apply IsPullback.of_isLimit' ⟨graphOver_mapOnProdOver f a ha q hq⟩
  refine PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ pullback.snd f g) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · simp only [Category.assoc, graphOver_fst]
      rw [← Category.assoc, ← Category.assoc, hsnd s.fst s.snd s.condition]
      exact (hfst s.fst s.snd s.condition).symm
    · simp only [Category.assoc, graphOver_snd, Category.comp_id]
  · intro s
    exact hsnd s.fst s.snd s.condition
  · intro s m hm _
    have h := congrArg (fun k => k ≫ pullback.snd f g) hm
    simpa only [Category.assoc, graphOver_snd, Category.comp_id] using h

/-- The closed graph's ACTUAL ideal sheaf pulls back exactly. Arbitrary base
change is allowed, including all nonreduced test schemes. -/
theorem ker_graphOver_comap_mapOnProdOver {C S : Scheme.{u}} (f : C ⟶ S)
    [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (a : T' ⟶ C) (ha : a ≫ f = g') (q : T ⟶ T') (hq : q ≫ g' = g) :
    (graphOver f a ha).ker.comap (mapOnProdOver f q hq) =
      (graphOver f (q ≫ a) (by rw [Category.assoc, ha, hq])).ker := by
  let H := isPullback_graphOver_mapOnProdOver f a ha q hq
  calc
    (graphOver f a ha).ker.comap (mapOnProdOver f q hq) =
        (pullback.fst (mapOnProdOver f q hq) (graphOver f a ha)).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _).symm
    _ = (H.isoPullback.hom ≫ pullback.fst _ _).ker :=
      (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (graphOver f (q ≫ a) (by rw [Category.assoc, ha, hq])).ker := by
      rw [H.isoPullback_hom_fst]

/-- Products of genuine graph ideals commute with arbitrary test-scheme base
change. No field, point-set, reducedness or flatness premise is introduced. -/
theorem prodKerGraph_comap_mapOnProdOver {C S : Scheme.{u}} {f : C ⟶ S}
    [IsSeparated f] {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (a : Fin r → (T' ⟶ C)) (ha : ∀ i, a i ≫ f = g')
    (q : T ⟶ T') (hq : q ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f q hq) =
      prodKerGraph f (fun i => q ≫ a i) (fun i => by rw [Category.assoc, ha, hq]) := by
  classical
  have H (s : Finset (Fin r)) :
      (s.prod (fun i => (graphOver f (a i) (ha i)).ker)).comap (mapOnProdOver f q hq) =
        s.prod (fun i => (graphOver f (q ≫ a i) (by rw [Category.assoc, ha, hq])).ker) := by
    induction s using Finset.induction_on with
    | empty => simpa using Scheme.IdealSheafData.comap_top (mapOnProdOver f q hq)
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Scheme.IdealSheafData.comap_mul, Finset.prod_insert hi,
        ih, ker_graphOver_comap_mapOnProdOver f (a i) (ha i) q hq]
  exact H Finset.univ

end AlgebraicGeometry
