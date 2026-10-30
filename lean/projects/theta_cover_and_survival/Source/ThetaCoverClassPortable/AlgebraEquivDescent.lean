import ThetaCoverClassPortable.ModuleColimitTensor
import ThetaCoverClassPortable.HomFactor
import ThetaCoverClassPortable.ScalarExtensionMaps

noncomputable section
set_option autoImplicit false
open scoped TensorProduct
universe u v w z p q n
namespace FourCorner.FPDescent

variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
  [Nonempty ι] [IsDirectedOrder ι]
  (S : ι → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  (f : ∀ i j, i ≤ j → S i →ₐ[R] S j)
  [hsys : DirectedSystem S (fun i j h => f i j h)]
  (B : Type z) [CommRing B] [Algebra R B]
  (φ : ∀ i, S i →ₐ[R] B)
  (hφ : ∀ (i j : ι) (h : i ≤ j), (φ j).comp (f i j h) = φ i)

include hφ in
theorem tensor_cocone_comp (N : Type n) [AddCommGroup N] [Module R N]
    (i j : ι) (h : i ≤ j) :
    ((φ j).toLinearMap.rTensor N).comp ((f i j h).toLinearMap.rTensor N) =
      (φ i).toLinearMap.rTensor N := by
  rw [← LinearMap.rTensor_comp, ← AlgHom.comp_toLinearMap, hφ]

omit [Nonempty ι] [IsDirectedOrder ι] in
theorem tensor_transition_comp (N : Type n) [AddCommGroup N] [Module R N]
    (i j k : ι) (hij : i ≤ j) (hjk : j ≤ k) :
    ((f j k hjk).toLinearMap.rTensor N).comp ((f i j hij).toLinearMap.rTensor N) =
      (f i k (hij.trans hjk)).toLinearMap.rTensor N := by
  rw [← LinearMap.rTensor_comp]
  congr 1
  ext x
  exact DirectedSystem.map_map' (fun i j h => f i j h) hij hjk x

include hφ hsys in
/-- Finitely presented modules and their inverse maps descend together along
an actual directed algebra colimit. Both inverse identities hold at the
selected stage, not merely after mapping to the colimit. -/
theorem exists_linearEquiv_of_finitePresentation
    (hsurj : ∀ b : B, ∃ (i : ι) (x : S i), φ i x = b)
    (hzero : ∀ (i : ι) (x : S i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    (P : Type p) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (Q : Type q) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
    (e : B ⊗[R] P ≃ₗ[B] B ⊗[R] Q) :
    ∃ (i : ι) (ei : S i ⊗[R] P ≃ₗ[S i] S i ⊗[R] Q),
      ((φ i).toLinearMap.rTensor Q).comp (ei.toLinearMap.restrictScalars R) =
        (e.toLinearMap.restrictScalars R).comp ((φ i).toLinearMap.rTensor P) := by
  classical
  letI : DirectedSystem S (fun i j h => (f i j h).toLinearMap) :=
    { map_self := fun {i} x => DirectedSystem.map_self' f x
      map_map := fun {k j i} hij hjk x => DirectedSystem.map_map' f hij hjk x }
  let W : ModuleColimitWitness R ι S (fun i j h => (f i j h).toLinearMap) B :=
    { incl := fun i => (φ i).toLinearMap
      comm := fun i j h => by ext x; exact AlgHom.congr_fun (hφ i j h) x
      surj := hsurj
      vanish := hzero }
  let WP := tensorColimitWitness P W
  let WQ := tensorColimitWitness Q W
  let eu : P →ₗ[R] B ⊗[R] Q :=
    (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R B P 1)
  let gu : Q →ₗ[R] B ⊗[R] P :=
    (e.symm.toLinearMap.restrictScalars R).comp (TensorProduct.mk R B Q 1)
  obtain ⟨i,vi,hvi⟩ := exists_factor_of_finitePresentation WQ eu
  obtain ⟨j,vj,hvj⟩ := exists_factor_of_finitePresentation WP gu
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  let v : P →ₗ[R] S k ⊗[R] Q := ((f i k hik).toLinearMap.rTensor Q).comp vi
  let w : Q →ₗ[R] S k ⊗[R] P := ((f j k hjk).toLinearMap.rTensor P).comp vj
  have hv : ((φ k).toLinearMap.rTensor Q).comp v = eu := by
    change ((φ k).toLinearMap.rTensor Q).comp
      (((f i k hik).toLinearMap.rTensor Q).comp vi) = eu
    rw [← LinearMap.comp_assoc, tensor_cocone_comp S f B φ hφ]
    exact hvi
  have hw : ((φ k).toLinearMap.rTensor P).comp w = gu := by
    change ((φ k).toLinearMap.rTensor P).comp
      (((f j k hjk).toLinearMap.rTensor P).comp vj) = gu
    rw [← LinearMap.comp_assoc, tensor_cocone_comp S f B φ hφ]
    exact hvj
  let fk := v.liftBaseChange (S k)
  let gk := w.liftBaseChange (S k)
  have hfk (x : S k ⊗[R] P) :
      (φ k).toLinearMap.rTensor Q (fk x) = e ((φ k).toLinearMap.rTensor P x) := by
    exact LinearMap.congr_fun
      (liftBaseChange_compatible (φ k) v e.toLinearMap
        (fun p => LinearMap.congr_fun hv p)) x
  have hgk (x : S k ⊗[R] Q) :
      (φ k).toLinearMap.rTensor P (gk x) = e.symm ((φ k).toLinearMap.rTensor Q x) := by
    exact LinearMap.congr_fun
      (liftBaseChange_compatible (φ k) w e.symm.toLinearMap
        (fun q => LinearMap.congr_fun hw q)) x
  let uP : P →ₗ[R] S k ⊗[R] P := TensorProduct.mk R (S k) P 1
  let uQ : Q →ₗ[R] S k ⊗[R] Q := TensorProduct.mk R (S k) Q 1
  let vP := ((gk.comp fk).restrictScalars R).comp uP
  let vQ := ((fk.comp gk).restrictScalars R).comp uQ
  have hP : (WP.incl k).comp vP = (WP.incl k).comp uP := by
    ext p
    change (φ k).toLinearMap.rTensor P (gk (fk (1 ⊗ₜ[R] p))) =
      (φ k).toLinearMap.rTensor P (1 ⊗ₜ[R] p)
    rw [hgk, hfk, e.symm_apply_apply]
  have hQ : (WQ.incl k).comp vQ = (WQ.incl k).comp uQ := by
    ext q
    change (φ k).toLinearMap.rTensor Q (fk (gk (1 ⊗ₜ[R] q))) =
      (φ k).toLinearMap.rTensor Q (1 ⊗ₜ[R] q)
    rw [hfk, hgk, e.apply_symm_apply]
  obtain ⟨lP,hklP,hlP⟩ := exists_eventual_eq_of_finite WP k vP uP hP
  obtain ⟨lQ,hklQ,hlQ⟩ := exists_eventual_eq_of_finite WQ k vQ uQ hQ
  obtain ⟨m,hlPm,hlQm⟩ := exists_ge_ge lP lQ
  let hkm : k ≤ m := hklP.trans hlPm
  have hPm : ((f k m hkm).toLinearMap.rTensor P).comp vP =
      ((f k m hkm).toLinearMap.rTensor P).comp uP := by
    have hh := congrArg (fun a => ((f lP m hlPm).toLinearMap.rTensor P).comp a) hlP
    change ((f lP m hlPm).toLinearMap.rTensor P).comp
        (((f k lP hklP).toLinearMap.rTensor P).comp vP) =
      ((f lP m hlPm).toLinearMap.rTensor P).comp
        (((f k lP hklP).toLinearMap.rTensor P).comp uP) at hh
    simpa only [← LinearMap.comp_assoc, tensor_transition_comp S f] using hh
  have hQm : ((f k m hkm).toLinearMap.rTensor Q).comp vQ =
      ((f k m hkm).toLinearMap.rTensor Q).comp uQ := by
    have hh := congrArg (fun a => ((f lQ m hlQm).toLinearMap.rTensor Q).comp a) hlQ
    change ((f lQ m hlQm).toLinearMap.rTensor Q).comp
        (((f k lQ hklQ).toLinearMap.rTensor Q).comp vQ) =
      ((f lQ m hlQm).toLinearMap.rTensor Q).comp
        (((f k lQ hklQ).toLinearMap.rTensor Q).comp uQ) at hh
    simpa only [← LinearMap.comp_assoc, tensor_transition_comp S f] using hh
  let fm := scalarPush (f k m hkm) fk
  let gm := scalarPush (f k m hkm) gk
  have hgf : gm.comp fm = LinearMap.id := by
    change (scalarPush (f k m hkm) gk).comp (scalarPush (f k m hkm) fk) = _
    rw [← scalarPush_comp]
    have hh : scalarPush (f k m hkm) (gk.comp fk) =
        scalarPush (f k m hkm) (LinearMap.id : S k ⊗[R] P →ₗ[S k] S k ⊗[R] P) :=
      scalarPush_eq_of_unit _ _ _ (fun p => LinearMap.congr_fun hPm p)
    rw [hh, scalarPush_id]
  have hfg : fm.comp gm = LinearMap.id := by
    change (scalarPush (f k m hkm) fk).comp (scalarPush (f k m hkm) gk) = _
    rw [← scalarPush_comp]
    have hh : scalarPush (f k m hkm) (fk.comp gk) =
        scalarPush (f k m hkm) (LinearMap.id : S k ⊗[R] Q →ₗ[S k] S k ⊗[R] Q) :=
      scalarPush_eq_of_unit _ _ _ (fun q => LinearMap.congr_fun hQm q)
    rw [hh, scalarPush_id]
  refine ⟨m, LinearEquiv.ofLinearMap fm gm hfg hgf, ?_⟩
  change ((φ m).toLinearMap.rTensor Q).comp (fm.restrictScalars R) = _
  apply liftBaseChange_compatible
  intro p
  change (φ m).toLinearMap.rTensor Q
      ((f k m hkm).toLinearMap.rTensor Q (fk (1 ⊗ₜ[R] p))) = e (1 ⊗ₜ[R] p)
  rw [← LinearMap.comp_apply, tensor_cocone_comp S f B φ hφ, hfk]
  simp

end FourCorner.FPDescent

theorem Module.IsDirectLimit.exists_linearEquiv_of_finitePresentation
    {R : Type u} [CommRing R] {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type w) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[R] S j) [DirectedSystem S (fun i j h => f i j h)]
    (B : Type z) [CommRing B] [Algebra R B] (φ : ∀ i, S i →ₐ[R] B)
    (hφ : ∀ (i j : ι) (h : i ≤ j), (φ j).comp (f i j h) = φ i)
    (hsurj : ∀ b : B, ∃ (i : ι) (x : S i), φ i x = b)
    (hzero : ∀ (i : ι) (x : S i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    (P : Type p) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (Q : Type q) [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
    (e : B ⊗[R] P ≃ₗ[B] B ⊗[R] Q) :
    ∃ (i : ι) (ei : S i ⊗[R] P ≃ₗ[S i] S i ⊗[R] Q),
      ((φ i).toLinearMap.rTensor Q).comp (ei.toLinearMap.restrictScalars R) =
        (e.toLinearMap.restrictScalars R).comp ((φ i).toLinearMap.rTensor P) :=
  FourCorner.FPDescent.exists_linearEquiv_of_finitePresentation S f B φ hφ hsurj hzero P Q e
