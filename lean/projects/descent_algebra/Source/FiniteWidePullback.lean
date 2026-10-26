import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.Data.Fintype.EquivFin

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits
universe v u
namespace FourCorner.FiniteWidePullback
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  (P : MorphismProperty C) [P.IsMultiplicative] [P.IsStableUnderBaseChange]

theorem exists_good_limit (n : ℕ) (B : C) (objs : Fin n → C)
    (arrows : ∀ j, objs j ⟶ B) (hP : ∀ j, P (arrows j)) :
    ∃ s : WidePullbackCone arrows, Nonempty (IsLimit s) ∧ P s.base := by
  induction n with
  | zero =>
      let s : WidePullbackCone arrows := WidePullbackCone.mk (𝟙 B)
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      refine ⟨s, ⟨WidePullbackCone.IsLimit.mk s (fun t => t.base) ?_ ?_ ?_⟩, P.id_mem B⟩
      · intro t
        change t.base ≫ 𝟙 B=t.base
        exact Category.comp_id _
      · intro t j
        exact Fin.elim0 j
      · intro t m hm _
        change m ≫ 𝟙 B=t.base at hm
        exact (Category.comp_id m).symm.trans hm
  | succ n ih =>
      obtain ⟨s, ⟨hs⟩, hbase⟩ := ih (fun j => objs j.succ)
        (fun j => arrows j.succ) (fun j => hP j.succ)
      let b : pullback (arrows 0) s.base ⟶ B :=
        pullback.snd (arrows 0) s.base ≫ s.base
      let legs : ∀ j : Fin (n+1), pullback (arrows 0) s.base ⟶ objs j :=
        Fin.cases (pullback.fst (arrows 0) s.base)
          (fun j => pullback.snd (arrows 0) s.base ≫ s.π j)
      have hw : ∀ j, legs j ≫ arrows j = b := by
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact pullback.condition
        · simp [legs, b, Category.assoc]
      let q : WidePullbackCone arrows := WidePullbackCone.mk b legs hw
      let tailLift (t : WidePullbackCone arrows) : t.pt ⟶ s.pt :=
        WidePullbackCone.IsLimit.lift hs t.base (fun j => t.π j.succ)
          (fun j => t.condition j.succ)
      have tail_base (t : WidePullbackCone arrows) : tailLift t ≫ s.base = t.base := by
        simp [tailLift]
      have tail_leg (t : WidePullbackCone arrows) (j : Fin n) :
          tailLift t ≫ s.π j = t.π j.succ := by
        simp [tailLift]
      let lift (t : WidePullbackCone arrows) : t.pt ⟶ q.pt :=
        pullback.lift (t.π 0) (tailLift t) (by rw [t.condition, tail_base])
      have hlim : IsLimit q := WidePullbackCone.IsLimit.mk q lift (by
          intro t
          simp [lift, q, b, Category.assoc, tail_base]) (by
          intro t j
          refine Fin.cases ?_ (fun j => ?_) j
          · simp [lift, q, legs]
          · simp [lift, q, legs, Category.assoc, tail_leg]) (by
          intro t m hm hlegs
          apply pullback.hom_ext
          · simpa [lift, q, legs] using hlegs 0
          · apply WidePullbackCone.IsLimit.hom_ext hs
            · simpa [lift, q, b, Category.assoc, tail_base] using hm
            · intro j
              simpa [lift, q, legs, Category.assoc, tail_leg] using hlegs j.succ)
      refine ⟨q, ⟨hlim⟩, ?_⟩
      exact P.comp_mem _ _ (P.pullback_snd (arrows 0) s.base (hP 0)) hbase

theorem fin_base (n : ℕ) {B : C} (objs : Fin n → C)
    (arrows : ∀ j, objs j ⟶ B) (hP : ∀ j, P (arrows j)) :
    P (WidePullback.base arrows) := by
  obtain ⟨s, ⟨hs⟩, hb⟩ := exists_good_limit P n B objs arrows hP
  let e := hs.conePointUniqueUpToIso (limit.isLimit (WidePullbackShape.wideCospan B objs arrows))
  have he : e.hom ≫ WidePullback.base arrows = s.base :=
    hs.conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
  have hcomp : P (e.hom ≫ WidePullback.base arrows) := by rw [he]; exact hb
  exact (P.cancel_left_of_respectsIso _ _).mp hcomp

end FourCorner.FiniteWidePullback

namespace CategoryTheory.MorphismProperty
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]

/-- The actual base map of every finite wide pullback preserves any
multiplicative property stable under arbitrary base change. -/
theorem widePullback_base {ι : Type} [Finite ι] {B : C} (objs : ι → C)
    (arrows : ∀ j, objs j ⟶ B) (hP : ∀ j, P (arrows j)) :
    P (WidePullback.base arrows) := by
  classical
  letI := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let s : WidePullbackCone arrows := limit.cone (WidePullbackShape.wideCospan B objs arrows)
  let hs : IsLimit (s.reindex e) :=
    (WidePullbackCone.reindexIsLimitEquiv s e).symm (limit.isLimit _)
  let q := limit.cone (WidePullbackShape.wideCospan B (fun j => objs (e j)) (fun j => arrows (e j)))
  let hq := limit.isLimit (WidePullbackShape.wideCospan B (fun j => objs (e j)) (fun j => arrows (e j)))
  let i := hs.conePointUniqueUpToIso hq
  have hi : i.hom ≫ WidePullback.base (fun j => arrows (e j)) = WidePullback.base arrows :=
    hs.conePointUniqueUpToIso_hom_comp hq none
  rw [← hi]
  exact P.comp_mem _ _ (P.of_isIso _) (FourCorner.FiniteWidePullback.fin_base P _ _ _ (fun j => hP (e j)))

end CategoryTheory.MorphismProperty
#print axioms FourCorner.FiniteWidePullback.exists_good_limit
#print axioms CategoryTheory.MorphismProperty.widePullback_base
