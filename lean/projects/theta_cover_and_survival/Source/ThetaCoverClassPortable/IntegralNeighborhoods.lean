import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false
open Set

/-- A connected space locally admitting irreducible open neighborhoods is
irreducible. No finiteness assumption on the space is needed. -/
theorem irreducibleSpace_of_connected_of_preirreducible_open_neighborhoods
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X]
    (hloc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U) :
    IrreducibleSpace X := by
  refine { isPreirreducible_univ := ?_, toNonempty := inferInstance }
  intro u v hu hv huN hvN
  let D : Set X := {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreirreducible U ∧ (U ∩ u).Nonempty}
  have hDo : IsOpen D := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro x ⟨U, hU, hxU, hUi, hUu⟩
    exact ⟨U, fun y hyU => ⟨U, hU, hyU, hUi, hUu⟩, hU, hxU⟩
  have hDco : IsOpen Dᶜ := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hxD
    obtain ⟨O, hO, hxO, hOi⟩ := hloc x
    refine ⟨O, ?_, hO, hxO⟩
    intro y hyO hyD
    obtain ⟨W, hW, hyW, hWi, hWu⟩ := hyD
    obtain ⟨z, hzW, hzO, hzu⟩ := hWi O u hO hu ⟨y, hyW, hyO⟩ hWu
    exact hxD ⟨O, hO, hxO, hOi, ⟨z, hzO, hzu⟩⟩
  have hDN : D.Nonempty := by
    obtain ⟨x, _, hxu⟩ := huN
    obtain ⟨U, hU, hxU, hUi⟩ := hloc x
    exact ⟨x, U, hU, hxU, hUi, x, hxU, hxu⟩
  have hDall : D = univ := IsClopen.eq_univ ⟨isOpen_compl_iff.mp hDco, hDo⟩ hDN
  obtain ⟨y, _, hyv⟩ := hvN
  have hyD : y ∈ D := by rw [hDall]; trivial
  obtain ⟨W, hW, hyW, hWi, hWu⟩ := hyD
  obtain ⟨z, _, hzu, hzv⟩ := hWi u v hu hv hWu ⟨y, hyW, hyv⟩
  exact ⟨z, mem_univ _, hzu, hzv⟩

open CategoryTheory
namespace AlgebraicGeometry

/-- Actual integral open charts prove reducedness and irreducibility globally
on a connected scheme. -/
theorem isIntegral_of_connected_of_integral_open_charts (X : Scheme)
    [ConnectedSpace X]
    (hloc : ∀ x : X, ∃ (Y : Scheme) (g : Y ⟶ X) (y : Y),
      IsOpenImmersion g ∧ IsIntegral Y ∧ g y = x) : IsIntegral X := by
  haveI : IrreducibleSpace X :=
    irreducibleSpace_of_connected_of_preirreducible_open_neighborhoods X (fun x => by
      obtain ⟨Y, g, y, hg, hY, hxy⟩ := hloc x
      letI := hg
      letI := hY
      refine ⟨range g, g.isOpenEmbedding.isOpen_range, ⟨y, hxy⟩, ?_⟩
      simpa only [image_univ] using
        ((IrreducibleSpace.isIrreducible_univ Y).image g g.continuous.continuousOn).isPreirreducible)
  haveI (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨Y, g, y, hg, hY, hxy⟩ := hloc x
    letI := hg
    letI := hY
    rw [← hxy]
    exact isReduced_of_injective _ (asIso (g.stalkMap y)).commRingCatIsoToRingEquiv.injective
  haveI : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end AlgebraicGeometry
