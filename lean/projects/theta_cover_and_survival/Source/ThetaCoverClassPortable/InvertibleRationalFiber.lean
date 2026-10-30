import ThetaCoverClassPortable.KummerSquareLine

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
namespace FourCorner.InvertibleRationalFiber

/-- Actual invertible module on the one-point scheme of a field is free of
rank one. The isomorphism is obtained from a genuine local trivialization. -/
theorem exists_iso_unit {k : Type} [Field k] (M : (Spec (.of k)).Modules)
    (hM : Scheme.Modules.IsInvertible M) : Nonempty (M ≅ 𝟙_ (Spec (.of k)).Modules) := by
  obtain ⟨V,hV,⟨e⟩⟩ := hM.exists_trivialization (IsLocalRing.closedPoint k)
  have htop : V=⊤ := by
    apply top_unique
    intro x _
    simpa only [Subsingleton.elim x (IsLocalRing.closedPoint k)] using hV
  subst V
  let ji := (Spec (.of k)).topIso
  exact ⟨((Scheme.Modules.pullbackId _).app M).symm ≪≫
    ((Scheme.Modules.pullbackCongr ji.inv_hom_id).app M).symm ≪≫
    ((Scheme.Modules.pullbackComp ji.inv ji.hom).app M).symm ≪≫
    (Scheme.Modules.pullback ji.inv).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso ji.inv⟩

def basis {k : Type} [Field k] {X : Scheme} (p : Spec (.of k) ⟶ X)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    (Scheme.Modules.pullback p).obj M ≅ 𝟙_ (Spec (.of k)).Modules :=
  (exists_iso_unit _ (hM.pullback p)).some

#print axioms basis
end FourCorner.InvertibleRationalFiber
