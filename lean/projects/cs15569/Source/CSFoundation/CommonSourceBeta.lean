import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The common-source character obstruction

This file proves the algebraic part of the common-source criterion for an arbitrary
abelian group.  The quotient is the complete quotient `H / 2H`; no generators,
rank bound, or finite-index replacement for `H` is used.
-/

namespace FourCorner.CommonSource

abbrev F2 := ZMod 2
abbrev F4 := ZMod 4

/-- Reduction modulo two. -/
def parity : F4 →+ F2 :=
  (ZMod.castHom (by norm_num : 2 ∣ 4) F2).toAddMonoidHom

/-- Halving an even residue modulo four, with an irrelevant extension to odd residues. -/
def half (x : F4) : F2 := (x.val / 2 : ℕ)

lemma parity_zero : parity 0 = 0 := map_zero parity
lemma parity_two_mul (x : F4) : parity (2 * x) = 0 := by
  revert x
  decide
lemma half_add {x y : F4} (hx : parity x = 0) (hy : parity y = 0) :
    half (x + y) = half x + half y := by
  revert x y
  decide
lemma half_two_mul (x : F4) : half (2 * x) = parity x := by
  revert x
  decide
lemma half_eq_zero {x : F4} (hx : parity x = 0) : half x = 0 ↔ x = 0 := by
  revert x
  decide
lemma even_double_eq_zero {x : F4} (hx : x = 0 ∨ x = 2) : x + x = 0 := by
  rcases hx with rfl | rfl <;> decide

variable {H : Type*} [AddCommGroup H] {ι : Type*}

/-- The image of doubling on the entire source group. -/
def doubles (H : Type*) [AddCommGroup H] : AddSubgroup H :=
  (nsmulAddMonoidHom 2 : H →+ H).range

abbrev ModTwo (H : Type*) [AddCommGroup H] := H ⧸ doubles H

instance modTwoModule : Module F2 (ModTwo H) :=
  QuotientAddGroup.zmodModule (n := 2) fun x ↦ ⟨x, rfl⟩

/-- Projection to the complete source quotient. -/
def classOf : H →+ ModTwo H := QuotientAddGroup.mk' (doubles H)

lemma classOf_surjective : Function.Surjective (classOf (H := H)) :=
  QuotientAddGroup.mk'_surjective _

lemma classOf_eq_iff (W W' : H) : classOf W' = classOf W ↔ ∃ Z, W' = W + 2 • Z := by
  change (QuotientAddGroup.mk W' : ModTwo H) = QuotientAddGroup.mk W ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · rintro ⟨Z, hZ⟩
    refine ⟨Z, ?_⟩
    change 2 • Z = W' - W at hZ
    calc
      W' = W + (W' - W) := by abel
      _ = W + 2 • Z := by rw [← hZ]
  · rintro ⟨Z, rfl⟩
    exact ⟨Z, by simp⟩

variable (φ : ι → H →+ F4)

/-- The simultaneous parity characters on the original group. -/
def eta : H →+ (ι → F2) where
  toFun x j := parity (φ j x)
  map_zero' := by ext j; simp [parity_zero]
  map_add' := by intros; ext j; simp

lemma eta_doubles (x : H) : eta φ (2 • x) = 0 := by
  ext j
  change parity (φ j (2 • x)) = 0
  rw [map_nsmul, nsmul_eq_mul]
  exact parity_two_mul _

/-- The matrix-free linear map of parity characters on `H / 2H`. -/
def M : ModTwo H →ₗ[F2] (ι → F2) :=
  (QuotientAddGroup.lift (doubles H) (eta φ) (by
    rintro _ ⟨x, rfl⟩
    exact eta_doubles φ x)).toZModLinearMap 2

@[simp] lemma M_classOf (x : H) : M φ (classOf x) = eta φ x := rfl

/-- All even rows are halved simultaneously. -/
def b (W : H) : ι → F2 := fun j ↦ half (φ j W)

lemma b_add {W W' : H} (hW : eta φ W = 0) (hW' : eta φ W' = 0) :
    b φ (W + W') = b φ W + b φ W' := by
  ext j
  change half (φ j (W + W')) = half (φ j W) + half (φ j W')
  rw [map_add]
  exact half_add (congrFun hW j) (congrFun hW' j)

/-- Every element of `H`, including all undetermined compensation points, is allowed. -/
theorem compensation {W : H} (hW : eta φ W = 0) (Z : H) :
    b φ (W + 2 • Z) = b φ W + eta φ Z := by
  ext j
  change half (φ j (W + 2 • Z)) = half (φ j W) + parity (φ j Z)
  rw [map_add, map_nsmul]
  rw [two_nsmul, ← two_mul]
  rw [half_add (congrFun hW j) (parity_two_mul _), half_two_mul]

/-- The cokernel of all parity rows, with no dimension assumption on the source. -/
abbrev Cokernel := (ι → F2) ⧸ (M φ).range

/-- A representative in `H` of an element of the kernel of `M`. -/
noncomputable def representative (κ : (M φ).ker) : H :=
  (classOf_surjective κ.val).choose

lemma representative_class (κ : (M φ).ker) :
    classOf (representative φ κ) = κ.val :=
  (classOf_surjective κ.val).choose_spec

lemma representative_even (κ : (M φ).ker) : eta φ (representative φ κ) = 0 := by
  rw [← M_classOf, representative_class]
  exact κ.property

/-- The secondary obstruction associated to a kernel class. -/
noncomputable def betaValue (κ : (M φ).ker) : Cokernel φ :=
  Submodule.Quotient.mk (b φ (representative φ κ))

lemma betaValue_eq {W : H} (κ : (M φ).ker) (hW : classOf W = κ.val) :
    betaValue φ κ = Submodule.Quotient.mk (b φ W) := by
  obtain ⟨Z, hZ⟩ := (classOf_eq_iff W (representative φ κ)).mp
    ((representative_class φ κ).trans hW.symm)
  have he : eta φ W = 0 := by rw [← M_classOf, hW]; exact κ.property
  unfold betaValue
  rw [hZ, compensation φ he, Submodule.Quotient.mk_add]
  have hz : (Submodule.Quotient.mk (eta φ Z) : Cokernel φ) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨classOf Z, rfl⟩
  rw [hz, add_zero]

/-- The secondary invariant is an F₂-linear map from `ker M` to `coker M`. -/
noncomputable def beta : (M φ).ker →ₗ[F2] Cokernel φ :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := betaValue φ
    map_zero' := by
      rw [betaValue_eq φ 0 (map_zero classOf)]
      have hb : b φ 0 = 0 := by ext j; simp [b, half]
      rw [hb]
      rfl
    map_add' := by
      intro κ κ'
      rw [betaValue_eq φ (κ + κ') (show classOf
        (representative φ κ + representative φ κ') = (κ + κ').val by
          rw [map_add, representative_class, representative_class]; rfl)]
      rw [b_add φ (representative_even φ κ) (representative_even φ κ')]
      exact Submodule.Quotient.mk_add _ }

@[simp] lemma beta_eq {W : H} (κ : (M φ).ker) (hW : classOf W = κ.val) :
    beta φ κ = Submodule.Quotient.mk (b φ W) := betaValue_eq φ κ hW

/-- Vanishing means that a single point compensates all rows simultaneously. -/
theorem beta_eq_zero_iff {W : H} (κ : (M φ).ker) (hW : classOf W = κ.val) :
    beta φ κ = 0 ↔ ∃ Z : H, b φ W = eta φ Z := by
  rw [beta_eq φ κ hW, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨Z, rfl⟩ := classOf_surjective z
    exact ⟨Z, hz.symm⟩
  · rintro ⟨Z, hZ⟩
    exact ⟨classOf Z, hZ.symm⟩

/-- The same pair and the same complete source coset yield one simultaneous kernel point. -/
theorem pair_common_kernel (d : ι) {U V W Z : H}
    (hsource : U + V = W + 2 • Z)
    (hsign : φ d V = φ d U ∨ φ d V = -φ d U)
    (hodd : ∀ j, j ≠ d → φ j U = φ j V ∧ (φ j U = 0 ∨ φ j U = 2)) :
    ∃ K Z' : H, K = W + 2 • Z' ∧ ∀ j, φ j K = 0 := by
  rcases hsign with hsame | hopposite
  · refine ⟨U - V, Z - V, ?_, ?_⟩
    · calc
        U - V = (U + V) - 2 • V := by abel
        _ = W + 2 • (Z - V) := by rw [hsource]; abel
    · intro j
      rw [map_sub]
      by_cases hj : j = d
      · subst j; rw [hsame, sub_self]
      · rw [(hodd j hj).1, sub_self]
  · refine ⟨U + V, Z, hsource, ?_⟩
    intro j
    rw [map_add]
    by_cases hj : j = d
    · subst j; rw [hopposite, add_neg_cancel]
    · rw [← (hodd j hj).1]
      exact even_double_eq_zero (hodd j hj).2

/-- A point in the simultaneous character kernel forces the secondary invariant to vanish. -/
theorem beta_eq_zero_of_common_kernel {W K Z : H} (κ : (M φ).ker)
    (hW : classOf W = κ.val) (hK : K = W + 2 • Z)
    (hzero : ∀ j, φ j K = 0) : beta φ κ = 0 := by
  have hclass : classOf K = κ.val :=
    ((classOf_eq_iff W K).mpr ⟨Z, hK⟩).trans hW
  rw [beta_eq φ κ hclass]
  have hb : b φ K = 0 := by ext j; simp [b, hzero, half]
  rw [hb]
  rfl

/-- Algebraic conclusion of the common-source criterion, retaining all compensation points. -/
theorem beta_eq_zero_of_pair (d : ι) {U V W Z : H} (κ : (M φ).ker)
    (hW : classOf W = κ.val) (hsource : U + V = W + 2 • Z)
    (hsign : φ d V = φ d U ∨ φ d V = -φ d U)
    (hodd : ∀ j, j ≠ d → φ j U = φ j V ∧ (φ j U = 0 ∨ φ j U = 2)) :
    beta φ κ = 0 := by
  obtain ⟨K, Z', hK, hzero⟩ := pair_common_kernel φ d hsource hsign hodd
  exact beta_eq_zero_of_common_kernel φ κ hW hK hzero

/-- Intrinsic form of the common correction: vanishing is equivalent to a zero-character
representative anywhere in the complete coset. -/
theorem beta_eq_zero_iff_kernel_representative {W : H} (κ : (M φ).ker)
    (hW : classOf W = κ.val) :
    beta φ κ = 0 ↔ ∃ Z : H, ∀ j, φ j (W + 2 • Z) = 0 := by
  constructor
  · intro hβ
    obtain ⟨Z, hZ⟩ := (beta_eq_zero_iff φ κ hW).mp hβ
    refine ⟨Z, ?_⟩
    have he : eta φ W = 0 := by rw [← M_classOf, hW]; exact κ.property
    have he' : eta φ (W + 2 • Z) = 0 := by
      rw [map_add, eta_doubles, he, add_zero]
    have hb : b φ (W + 2 • Z) = 0 := by
      rw [compensation φ he, hZ]
      ext j
      exact CharTwo.add_self_eq_zero _
    intro j
    exact (half_eq_zero (congrFun he' j)).mp (congrFun hb j)
  · rintro ⟨Z, hZ⟩
    exact beta_eq_zero_of_common_kernel φ κ hW rfl hZ

/-- A source representative with vanishing parity defines a kernel class. -/
def kernelClass (W : H) (hW : eta φ W = 0) : (M φ).ker :=
  ⟨classOf W, hW⟩

@[simp] lemma kernelClass_coe (W : H) (hW : eta φ W = 0) :
    (kernelClass φ W hW).val = classOf W := rfl

/-- A nonzero secondary invariant excludes the whole simultaneous pair. -/
theorem no_pair_of_beta_ne_zero (d : ι) {W : H} (κ : (M φ).ker)
    (hW : classOf W = κ.val) (hβ : beta φ κ ≠ 0) :
    ¬ ∃ U V Z : H, U + V = W + 2 • Z ∧
      (φ d V = φ d U ∨ φ d V = -φ d U) ∧
      (∀ j, j ≠ d → φ j U = φ j V ∧ (φ j U = 0 ∨ φ j U = 2)) := by
  rintro ⟨U, V, Z, hsource, hsign, hodd⟩
  exact hβ (beta_eq_zero_of_pair φ d κ hW hsource hsign hodd)

open scoped BigOperators

lemma linearForm_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2) (v : ι → ZMod 2) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  classical
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : Pi.single i (v i) = v i • (Pi.single i (1 : ZMod 2)) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]
  rw [h, map_smul]
  simp [mul_comm]

lemma notMem_iff_finite_certificate {ι : Type*} [Fintype ι]
    (S : Submodule (ZMod 2) (ι → ZMod 2)) (b : ι → ZMod 2) :
    b ∉ S ↔ ∃ c : ι → ZMod 2,
      (∀ v ∈ S, ∑ i, c i * v i = 0) ∧ ∑ i, c i * b i = 1 := by
  classical
  constructor
  · intro hb
    have hbq : S.mkQ b ≠ 0 := by
      simpa using hb
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hbq
    let g : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 := f.comp S.mkQ
    refine ⟨fun i => g (Pi.single i 1), ?_, ?_⟩
    · intro v hv
      rw [← linearForm_eq_sum g v]
      have hvq : S.mkQ v = 0 := by simpa using hv
      change f (S.mkQ v) = 0
      rw [hvq, map_zero]
    · rw [← linearForm_eq_sum g b]
      exact hf
  · rintro ⟨c, hc, hb⟩ hm
    have h := hc b hm
    rw [hb] at h
    exact one_ne_zero h


/-- Finite dual certificates are equivalent to nonvanishing of the intrinsic obstruction. -/
theorem beta_ne_zero_iff_certificate [Fintype ι] {W : H} (κ : (M φ).ker)
    (hW : classOf W = κ.val) :
    beta φ κ ≠ 0 ↔ ∃ c : ι → F2,
      (∀ Z : H, ∑ j, c j * eta φ Z j = 0) ∧ ∑ j, c j * b φ W j = 1 := by
  rw [beta_eq φ κ hW, ne_eq, Submodule.Quotient.mk_eq_zero,
    notMem_iff_finite_certificate]
  constructor
  · rintro ⟨c, hc, hb⟩
    exact ⟨c, fun Z ↦ hc (eta φ Z) ⟨classOf Z, rfl⟩, hb⟩
  · rintro ⟨c, hc, hb⟩
    refine ⟨c, ?_, hb⟩
    rintro v ⟨x, rfl⟩
    obtain ⟨Z, rfl⟩ := classOf_surjective x
    exact hc Z

/-- A finite certificate excludes every pair in the complete source coset. -/
theorem no_pair_of_certificate [Fintype ι] (d : ι) {W : H} (κ : (M φ).ker)
    (hW : classOf W = κ.val) (c : ι → F2)
    (hc : ∀ Z : H, ∑ j, c j * eta φ Z j = 0)
    (hb : ∑ j, c j * b φ W j = 1) :
    ¬ ∃ U V Z : H, U + V = W + 2 • Z ∧
      (φ d V = φ d U ∨ φ d V = -φ d U) ∧
      (∀ j, j ≠ d → φ j U = φ j V ∧ (φ j U = 0 ∨ φ j U = 2)) := by
  apply no_pair_of_beta_ne_zero φ d κ hW
  exact (beta_ne_zero_iff_certificate φ κ hW).mpr ⟨c, hc, hb⟩

lemma parity_weight (c : F2) (x : F4) : parity (c.val • x) = c * parity x := by
  revert c x
  decide

lemma half_weight {x : F4} (c : F2) (hx : parity x = 0) :
    half (c.val • x) = c * half x := by
  revert c x
  decide

lemma half_sum (S : Finset ι) (f : ι → F4) (hf : ∀ j ∈ S, parity (f j) = 0) :
    half (∑ j ∈ S, f j) = ∑ j ∈ S, half (f j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [half]
  | @insert a S ha ih =>
    have hfa : parity (f a) = 0 := hf a (Finset.mem_insert_self a S)
    have hfS : ∀ j ∈ S, parity (f j) = 0 :=
      fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    have he : parity (∑ j ∈ S, f j) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero hfS
    rw [Finset.sum_insert ha, Finset.sum_insert ha, half_add hfa he, ih hfS]

/-- Coefficients in F₂ are represented by zero or one when weighting the mod-four rows. -/
def weightedCharacter [Fintype ι] (c : ι → F2) : H →+ F4 :=
  ∑ j, (c j).val • φ j

lemma parity_weightedCharacter [Fintype ι] (c : ι → F2) (Z : H) :
    parity (weightedCharacter φ c Z) = ∑ j, c j * eta φ Z j := by
  simp only [weightedCharacter, AddMonoidHom.finsetSum_apply, AddMonoidHom.nsmul_apply,
    map_sum, parity_weight]
  rfl

/-- The dot-product obstruction is exactly the paper's half of the weighted character. -/
lemma half_weightedCharacter [Fintype ι] (c : ι → F2) {W : H}
    (hW : eta φ W = 0) :
    half (weightedCharacter φ c W) = ∑ j, c j * b φ W j := by
  simp only [weightedCharacter, AddMonoidHom.finsetSum_apply, AddMonoidHom.nsmul_apply]
  rw [half_sum]
  · apply Finset.sum_congr rfl
    intro j _
    exact half_weight (c j) (congrFun hW j)
  · intro j _
    rw [parity_weight]
    change c j * eta φ W j = 0
    rw [hW]
    simp

/-- The parity relation makes the half-weighted character additive on all of H. -/
def weightedHalf [Fintype ι] (c : ι → F2)
    (hc : ∀ Z : H, ∑ j, c j * eta φ Z j = 0) : H →+ F2 where
  toFun Z := half (weightedCharacter φ c Z)
  map_zero' := by simp [half]
  map_add' := by
    intro X Y
    rw [map_add]
    exact half_add ((parity_weightedCharacter φ c X).trans (hc X))
      ((parity_weightedCharacter φ c Y).trans (hc Y))

/-- The secondary character defined by a certificate is independent of every representative. -/
def certificateCharacter [Fintype ι] (c : ι → F2)
    (hc : ∀ Z : H, ∑ j, c j * eta φ Z j = 0) : ModTwo H →ₗ[F2] F2 :=
  (QuotientAddGroup.lift (doubles H) (weightedHalf φ c hc) (by
    rintro _ ⟨Z, rfl⟩
    change weightedHalf φ c hc (2 • Z) = 0
    rw [map_nsmul, two_nsmul]
    exact CharTwo.add_self_eq_zero _)).toZModLinearMap 2

@[simp] lemma certificateCharacter_classOf [Fintype ι] (c : ι → F2)
    (hc : ∀ Z : H, ∑ j, c j * eta φ Z j = 0) (W : H) :
    certificateCharacter φ c hc (classOf W) = half (weightedCharacter φ c W) := rfl

/-- The explicit half-weighted certificate criterion. -/
theorem beta_ne_zero_iff_weighted_certificate [Fintype ι] {W : H} (κ : (M φ).ker)
    (hW : classOf W = κ.val) :
    beta φ κ ≠ 0 ↔ ∃ c : ι → F2,
      (∀ Z : H, ∑ j, c j * eta φ Z j = 0) ∧
      half (weightedCharacter φ c W) = 1 := by
  have he : eta φ W = 0 := by rw [← M_classOf, hW]; exact κ.property
  simp_rw [half_weightedCharacter φ _ he]
  exact beta_ne_zero_iff_certificate φ κ hW

end FourCorner.CommonSource
