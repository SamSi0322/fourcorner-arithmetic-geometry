import ThetaCoverClassPortable.ReplayImports
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ThetaCoverClassPortable.Definitions.Def_SheafOfModules_Monoidal
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ThetaCoverClassPortable.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow
import ThetaCoverClassPortable.ActualAwayFBSFlatBase
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_tensorPow_mul_iso
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensorPow
import ThetaCoverClassPortable.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_forall_mem_finset_away
import ThetaCoverClassPortable.P2M.Util
namespace P2MW.ActualFBSFlatBase

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory"


namespace W2FINSketch

noncomputable def tensorPowIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    (b : ℕ) → (L.tensorPow b ≅ L'.tensorPow b)
  | 0 => Iso.refl _
  | b + 1 => tensorPowIso e b ⊗ᵢ e

end W2FINSketch

open W2FINSketch in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hflat : ∀ (K : Type u) [Field K] [Algebra R K], Module.Flat R K)
    (hfib : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K], ∃ n : ℕ,
      Scheme.Modules.FiniteBySections
        ((Scheme.Modules.pullback (Limits.pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj (L.tensorPow n))
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    :
    ∃ n : ℕ, Scheme.Modules.FiniteBySections (L.tensorPow n) f := by
  classical

  have loc := fun 𝔭 : PrimeSpectrum R =>
    P2MW.ActualAwayFBSFlatBase.solution R f L hL hflat hfib 𝔭
  choose g hg n hn hFBS using loc

  have hcover : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ 𝔭 : PrimeSpectrum R, ((PrimeSpectrum.basicOpen (g 𝔭) : TopologicalSpace.Opens (PrimeSpectrum R)) :
        Set (PrimeSpectrum R)) :=
    fun 𝔭 _ => Set.mem_iUnion.2 ⟨𝔭, hg 𝔭⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun 𝔭 : PrimeSpectrum R => ((PrimeSpectrum.basicOpen (g 𝔭) : TopologicalSpace.Opens (PrimeSpectrum R)) :
      Set (PrimeSpectrum R)))
    (fun 𝔭 => (PrimeSpectrum.basicOpen (g 𝔭)).isOpen) hcover

  set s : Finset R := t.image g with hs_def
  have hs : Ideal.span (s : Set R) = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, PrimeSpectrum.zeroLocus_span,
      Set.eq_empty_iff_forall_notMem]
    intro 𝔮 h𝔮
    obtain ⟨𝔭, h𝔭t, hmem⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ 𝔮))
    have hgs : g 𝔭 ∈ (s : Set R) := by
      rw [hs_def, Finset.coe_image]
      exact ⟨𝔭, h𝔭t, rfl⟩
    exact hmem (h𝔮 hgs)

  have hNpos : 0 < ∏ 𝔭 ∈ t, n 𝔭 := Finset.prod_pos fun 𝔭 _ => hn 𝔭
  refine ⟨∏ 𝔭 ∈ t, n 𝔭, Scheme.Modules.FiniteBySections.of_forall_mem_finset_away f (L.tensorPow _)
    (hL.tensorPow _) s hs ?_⟩

  intro r hr
  obtain ⟨𝔭, h𝔭t, rfl⟩ := Finset.mem_image.1 hr
  obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem n h𝔭t
  rw [hb] at hNpos ⊢
  have hbpos : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hNpos)
  set ι := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (g 𝔭))))
  set p := Limits.pullback.fst f ι
  set f' := Limits.pullback.snd f ι
  have hV := Scheme.Modules.FiniteBySections.tensorPow (f := f') (hFBS 𝔭) hbpos
  refine Scheme.Modules.FiniteBySections.of_iso ?_ hV
  exact tensorPowIso (Scheme.Modules.nonempty_pullback_tensorPow_iso p L (n 𝔭)).some b ≪≫
    (Scheme.Modules.nonempty_tensorPow_mul_iso ((Scheme.Modules.pullback p).obj L) (n 𝔭) b).some.symm ≪≫
    (Scheme.Modules.nonempty_pullback_tensorPow_iso p L (n 𝔭 * b)).some.symm
