import ThetaCoverClassPortable.ModuleColimitWitness
import Mathlib.Algebra.Module.FinitePresentation

/-! Finite generators and relations in a genuine directed module colimit.
No flatness, Noetherianity or projectivity is assumed. -/
noncomputable section
set_option autoImplicit false

universe u v w z p
namespace FourCorner.FPDescent

variable {R : Type u} [CommRing R]
  {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
  [DirectedSystem G (f · · ·)]
  {M : Type z} [AddCommGroup M] [Module R M]

/-- A finite set of stages has an upper bound also above a designated stage.
The empty set is allowed. -/
theorem finite_stage_upper_bound (s : Finset ι) (i : ι) :
    ∃ j, i ≤ j ∧ ∀ k ∈ s, k ≤ j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨i, le_rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨j, hij, hj⟩ := ih
    obtain ⟨k, hjk, hak⟩ := exists_ge_ge j a
    refine ⟨k, hij.trans hjk, ?_⟩
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hak
    · exact (hj t ht).trans hjk

/-- Finite families of representatives may be moved to one stage. -/
theorem family_stage_upper_bound {κ : Type*} [Fintype κ] (a : κ → ι) (i : ι) :
    ∃ j, i ≤ j ∧ ∀ k, a k ≤ j := by
  classical
  obtain ⟨j, hij, hj⟩ := finite_stage_upper_bound (Finset.univ.image a) i
  exact ⟨j, hij, fun k => hj (a k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)⟩

variable (W : ModuleColimitWitness R ι G f M)

/-- Two maps from a finitely generated module which agree in the colimit
agree at one later stage. Vanishing is used only on finitely many generators. -/
theorem exists_eventual_eq_of_finite
    {P : Type p} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (i : ι) (v w : P →ₗ[R] G i)
    (heq : (W.incl i).comp v = (W.incl i).comp w) :
    ∃ (j : ι) (hij : i ≤ j), (f i j hij).comp v = (f i j hij).comp w := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := P)
  have hv (k : Fin n) : W.incl i (v (s k) - w (s k)) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun heq (s k))
  choose a hai hzero using fun k : Fin n => W.vanish i (v (s k) - w (s k)) (hv k)
  obtain ⟨j, hij, hj⟩ := family_stage_upper_bound a i
  refine ⟨j, hij, LinearMap.ext_on_range hs ?_⟩
  intro k
  change f i j hij (v (s k)) = f i j hij (w (s k))
  apply sub_eq_zero.mp
  rw [← map_sub]
  have hh := congrArg (f (a k) j (hj k)) (hzero k)
  rw [map_zero] at hh
  exact (DirectedSystem.map_map' f (hai k) (hj k) _).symm.trans hh

/-- A map from a finite free module lifts to one stage by lifting the finitely
many basis images and moving their representatives to a common stage. -/
theorem exists_factor_fin_free (n : ℕ) (u : (Fin n → R) →ₗ[R] M) :
    ∃ (i : ι) (v : (Fin n → R) →ₗ[R] G i), (W.incl i).comp v = u := by
  classical
  let b := Pi.basisFun R (Fin n)
  choose a y hy using fun k : Fin n => W.surj (u (b k))
  obtain ⟨i, _, hi⟩ := family_stage_upper_bound a (Classical.arbitrary ι)
  let z : Fin n → G i := fun k => f (a k) i (hi k) (y k)
  refine ⟨i, b.constr R z, ?_⟩
  apply b.ext
  intro k
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis]
  change W.incl i (f (a k) i (hi k) (y k)) = u (b k)
  have hc := LinearMap.congr_fun (W.comm (a k) i (hi k)) (y k)
  exact hc.trans (hy k)

/-- Every map from a finitely presented module into a genuine directed colimit
factors at a stage. The presentation kernel is finitely generated; its finitely
many relations vanish together at a later stage before taking the quotient. -/
theorem exists_factor_of_finitePresentation
    {P : Type p} [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
    (u : P →ₗ[R] M) :
    ∃ (i : ι) (v : P →ₗ[R] G i), (W.incl i).comp v = u := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R P
  let q : (Fin n → R) →ₗ[R] P := e.symm.toLinearMap.comp K.mkQ
  obtain ⟨i, a, ha⟩ := exists_factor_fin_free W n (u.comp q)
  letI : Module.Finite R K := Module.Finite.of_fg hK
  have hrel : (W.incl i).comp (a.comp K.subtype) = (W.incl i).comp (0 : K →ₗ[R] G i) := by
    ext k
    have hh := LinearMap.congr_fun ha (k : Fin n → R)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero]
    change W.incl i (a (k : Fin n → R)) = 0
    have hq : K.mkQ (k : Fin n → R) = 0 := (Submodule.Quotient.mk_eq_zero K).mpr k.property
    simpa only [q, LinearMap.comp_apply, LinearEquiv.coe_coe, hq, map_zero] using hh
  obtain ⟨j, hij, hj⟩ := exists_eventual_eq_of_finite W i (a.comp K.subtype) 0 hrel
  let a' : (Fin n → R) →ₗ[R] G j := (f i j hij).comp a
  have hk : K ≤ LinearMap.ker a' := by
    intro x hx
    have hh := LinearMap.congr_fun hj (⟨x, hx⟩ : K)
    simpa [a'] using hh
  let v : P →ₗ[R] G j := (K.liftQ a' hk).comp e.toLinearMap
  refine ⟨j, v, ?_⟩
  ext x
  obtain ⟨y, hy⟩ := K.mkQ_surjective (e x)
  have hxy : q y = x := by
    change e.symm (K.mkQ y) = x
    rw [hy, e.symm_apply_apply]
  rw [← hxy]
  change W.incl j ((K.liftQ a' hk) (e (e.symm (K.mkQ y)))) = u (q y)
  rw [e.apply_symm_apply]
  change W.incl j (a' y) = u (q y)
  have hc := LinearMap.congr_fun (W.comm i j hij) (a y)
  exact hc.trans (LinearMap.congr_fun ha y)

end FourCorner.FPDescent
