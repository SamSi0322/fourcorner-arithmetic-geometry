import ThetaCoverClassPortable.IntegralNeighborhoods
import ThetaCoverClassPortable.EtaleLocalDomain
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Polynomial.UniqueFactorization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
noncomputable section
universe u
namespace AlgebraicGeometry

theorem localizationAway_point_lift (R : CommRingCat.{u}) (f : R) (x : Spec R)
    (hx : f ∉ x.asIdeal) :
    ∃ y : Spec (CommRingCat.of (Localization.Away f)),
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) y = x := by
  change x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))
  rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
  exact hx

theorem smooth_spec_integral_open_chart (k : Type u) [Field k]
    (R : CommRingCat.{u}) (t : Spec R ⟶ Spec (CommRingCat.of k))
    (hsm : Smooth t) (x : Spec R) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec R) (y : Y),
      IsOpenImmersion g ∧ IsIntegral Y ∧ g y = x := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective t
  have hRing : φ.hom.Smooth := HasRingHomProperty.Spec_iff.mp hsm
  algebraize [φ.hom]
  letI : Algebra.Smooth k R := RingHom.smooth_algebraMap.mp hRing
  obtain ⟨f, hfx, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := x.asIdeal)
  letI := hAlg
  letI := hTower
  letI := hEtale
  obtain ⟨y, hy⟩ := localizationAway_point_lift R f x hfx
  obtain ⟨s, hsy, hDomain⟩ := StandardEtaleLocalDomain.exists_away_isDomain
    (R := MvPolynomial (Fin n) k) (S := Localization.Away f) y.asIdeal
  letI := hDomain
  obtain ⟨z, hz⟩ := localizationAway_point_lift (CommRingCat.of (Localization.Away f)) s y hsy
  let g := Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f) (Localization.Away s))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
  refine ⟨Spec (CommRingCat.of (Localization.Away s)), g, z, inferInstance, inferInstance, ?_⟩
  change Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
    (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f) (Localization.Away s))) z) = x
  rw [hz, hy]

theorem scheme_iso_inv_hom_point {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    e.inv (e.hom x) = x := by
  have h := congrArg (fun q : X ⟶ X => q x) e.hom_inv_id
  exact h

theorem smooth_integral_open_charts (k : Type u) [Field k] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of k)) (hsm : Smooth t) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (y : Y),
      IsOpenImmersion g ∧ IsIntegral Y ∧ g y = x := by
  letI := hsm
  obtain ⟨i, y, hxy⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let e := U.isoSpec
  let t' := e.inv ≫ X.affineCover.f i ≫ t
  have ht' : Smooth t' := inferInstance
  obtain ⟨V, g, z, hg, hV, hgz⟩ :=
    smooth_spec_integral_open_chart k _ t' ht' (e.hom y)
  letI := hg
  let g' := g ≫ e.inv ≫ X.affineCover.f i
  refine ⟨V, g', z, inferInstance, hV, ?_⟩
  change (X.affineCover.f i) (e.inv (g z)) = x
  have he := (congrArg e.inv hgz).trans (scheme_iso_inv_hom_point e y)
  exact (congrArg (X.affineCover.f i) he).trans hxy

/-- A smooth geometrically connected scheme over a field is integral. The
section arguments retain the exact public caller interface. -/
theorem isIntegral_of_smooth_of_geometricallyConnected
    (k : Type u) [Field k] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of k)) (hsm : Smooth t) (hgc : GeometricallyConnected t)
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ t = 𝟙 _) : IsIntegral X := by
  letI := hgc
  haveI : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton t
  exact isIntegral_of_connected_of_integral_open_charts X (smooth_integral_open_charts k t hsm)

end AlgebraicGeometry
