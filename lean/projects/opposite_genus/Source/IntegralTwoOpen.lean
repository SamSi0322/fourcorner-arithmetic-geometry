import OppositePostIntegral

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FourCorner
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Integral open subschemes with nonempty overlap glue to an integral scheme. -/
theorem integral_two_open {X : Scheme.{u}} (U V : X.Opens)
    [IsIntegral U.toScheme] [IsIntegral V.toScheme]
    (hcov : U ⊔ V = ⊤) (hne : ((U : Set X) ∩ V).Nonempty) : IsIntegral X := by
  let W : Bool → X.Opens := fun b => if b then U else V
  have hW : iSup W = ⊤ := by simpa [W,iSup_bool_eq] using hcov
  let C := X.openCoverOfIsOpenCover W hW
  haveI : ∀ i, IsReduced (C.X i) := by
    intro i
    change IsReduced (W i).toScheme
    cases i
    · simpa [W] using (inferInstance : IsReduced V.toScheme)
    · simpa [W] using (inferInstance : IsReduced U.toScheme)
  haveI : IsReduced X := IsReduced.of_openCover X C
  have hU : IsIrreducible (U : Set X) := isIrreducible_iff_irreducibleSpace.mpr (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hV : IsIrreducible (V : Set X) := isIrreducible_iff_irreducibleSpace.mpr (inferInstanceAs (IrreducibleSpace V.toScheme))
  have hVU : (V : Set X) ⊆ closure (U : Set X) :=
    (subset_closure_inter_of_isPreirreducible_of_isOpen hV.isPreirreducible U.isOpen (by simpa only [Set.inter_comm] using hne)).trans
      (closure_mono Set.inter_subset_right)
  have hdense : closure (U : Set X) = Set.univ :=
    Set.eq_univ_of_univ_subset fun x _ => by
      have hx : x ∈ U ∨ x ∈ V := by
        change x ∈ U ⊔ V
        rw [hcov]; trivial
      exact hx.elim (fun hu => subset_closure hu) (fun hv => hVU hv)
  haveI : IrreducibleSpace X := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← hdense]
    exact hU.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end FourCorner
#print axioms FourCorner.integral_two_open
