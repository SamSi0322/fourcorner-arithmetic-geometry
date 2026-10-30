import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_sameDivisorScheme
import ThetaCoverClassPortable.Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FourCorner.AffineRelationRank

/-- The literal ideal-sheaf classification yields equivalence on ALL scheme tests,
without restricting the test maps to fields, reduced rings, or a chosen base fibre. -/
theorem sameDivisor_equivalence {U S R : Scheme.{u}} (f : U ⟶ S) (r : ℕ)
    (s t : R ⟶ fibrePowOver f r)
    (hst : s ≫ fibrePowOver.toBase f r = t ≫ fibrePowOver.toBase f r)
    (hformula : ∀ ⦃T : Scheme.{u}⦄ (u v : T ⟶ fibrePowOver f r)
      (huv : u ≫ fibrePowOver.toBase f r = v ≫ fibrePowOver.toBase f r),
      (∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
        SameDivisor f (fun i => u ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp])
          (fun i => v ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp, huv])) :
    ∀ T : Scheme.{u}, Equivalence fun u v : T ⟶ fibrePowOver f r =>
      ∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v := by
  intro T
  let b := fibrePowOver.toBase f r
  have hbase : ∀ {u v : T ⟶ fibrePowOver f r},
      (∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) → u ≫ b = v ≫ b := by
    rintro u v ⟨w, rfl, rfl⟩
    simpa only [Category.assoc] using congrArg (w ≫ ·) hst
  have classify : ∀ (g : T ⟶ S) (u v : T ⟶ fibrePowOver f r)
      (hu : u ≫ b = g) (hv : v ≫ b = g),
      (∃ w : T ⟶ R, w ≫ s = u ∧ w ≫ t = v) ↔
        SameDivisor (g := g) f (fun i => u ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp]; exact hu)
          (fun i => v ≫ fibrePowOver.proj f r i)
          (fun i => by rw [Category.assoc, fibrePowOver.proj_comp]; exact hv) := by
    intro g u v hu hv
    subst g
    exact hformula u v hv.symm
  refine ⟨?_, ?_, ?_⟩
  · intro u
    exact (classify (u ≫ b) u u rfl rfl).mpr (by rfl)
  · intro u v huv
    have h := hbase huv
    exact (classify (u ≫ b) v u h.symm rfl).mpr
      ((classify (u ≫ b) u v rfl h.symm).mp huv).symm
  · intro u v w huv hvw
    have h1 := hbase huv
    have h2 := hbase hvw
    exact (classify (u ≫ b) u w rfl (h1.trans h2).symm).mpr
      (((classify (u ≫ b) u v rfl h1.symm).mp huv).trans
        ((classify (u ≫ b) v w h1.symm (h1.trans h2).symm).mp hvw))

/-- A genuine closed relation map gives the original all-test joint monomorphism. -/
theorem relation_joint_mono {S X R : Scheme.{u}} (g : X ⟶ S) (s t : R ⟶ X)
    (hst : s ≫ g = t ≫ g) [IsClosedImmersion (pullback.lift s t hst)] :
    ∀ {T : Scheme.{u}} (a b : T ⟶ R),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b := by
  intro T a b hs ht
  apply (cancel_mono (pullback.lift s t hst)).mp
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst] using hs
  · simpa only [Category.assoc, pullback.lift_snd] using ht

end FourCorner.AffineRelationRank
