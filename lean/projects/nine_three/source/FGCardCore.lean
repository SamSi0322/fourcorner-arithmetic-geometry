import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace FGCardCore

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

abbrev DoubleKer (G : Type*) [AddCommGroup G] := (nsmulAddMonoidHom (α := G) 2).ker
abbrev DoubleQuot (G : Type*) [AddCommGroup G] := G ⧸ (nsmulAddMonoidHom (α := G) 2).range

noncomputable def doubleKerEquiv (e : G ≃+ H) : DoubleKer G ≃ DoubleKer H where
  toFun x := ⟨e x, by
    have h : 2 • x.val = 0 := x.property
    change 2 • e x.val = 0
    rw [← map_nsmul, h, map_zero]⟩
  invFun x := ⟨e.symm x, by
    have h : 2 • x.val = 0 := x.property
    change 2 • e.symm x.val = 0
    rw [← map_nsmul, h, map_zero]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

noncomputable def doubleKerFreeProdEquiv (n : ℕ) (T : Type*) [AddCommGroup T] :
    DoubleKer ((Fin n →₀ ℤ) × T) ≃ DoubleKer T where
  toFun x := ⟨x.val.2, by simpa using congrArg Prod.snd x.property⟩
  invFun x := ⟨(0, x.val), by
    change (2 • (0, x.val) : (Fin n →₀ ℤ) × T) = 0
    ext
    · simp
    · exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      have h := congrArg Prod.fst x.property
      change (2 : ℕ) • x.val.1 = 0 at h
      have : x.val.1 = 0 := by
        ext i
        have hi := congrArg (fun f : Fin n →₀ ℤ => f i) h
        simp only [Finsupp.smul_apply, Finsupp.zero_apply, nsmul_eq_mul] at hi
        simp only [Finsupp.zero_apply]
        omega
      exact this.symm
    · rfl
  right_inv x := rfl

instance doubleQuotFinite [AddGroup.FG G] : Finite (DoubleQuot G) :=
  AddCommGroup.finite_of_fg_isAddTorsion _
    (AddCommGroup.isAddTorsion_quotient_range_nsmulAddMonoidHom G (by decide))

noncomputable def doubleQuotEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) : DoubleQuot G ≃+ DoubleQuot H :=
  QuotientAddGroup.congr _ _ e (e.map_range_nsmulAddMonoidHom 2)

theorem doubleRangeProd (G H : Type*) [AddCommGroup G] [AddCommGroup H] :
    (nsmulAddMonoidHom (α := G × H) 2).range =
      ((nsmulAddMonoidHom (α := G) 2).range).prod
        ((nsmulAddMonoidHom (α := H) 2).range) := by
  change ((nsmulAddMonoidHom (α := G) 2).prodMap
      (nsmulAddMonoidHom (α := H) 2)).range = _
  exact AddMonoidHom.range_prodMap _ _

theorem doubleQuotProdCard (G H : Type*) [AddCommGroup G] [AddCommGroup H] :
    Nat.card (DoubleQuot (G × H)) = Nat.card (DoubleQuot G) * Nat.card (DoubleQuot H) := by
  change (nsmulAddMonoidHom (α := G × H) 2).range.index = _
  rw [doubleRangeProd, AddSubgroup.index_prod]
  rfl

theorem doubleQuotFreeCard (n : ℕ) :
    Nat.card (DoubleQuot (Fin n →₀ ℤ)) = 2 ^ n := by
  change (nsmulAddMonoidHom (α := Fin n →₀ ℤ) 2).range.index = _
  rw [AddSubgroup.index_range_nsmul]
  simp

theorem doubleQuotFiniteCard (T : Type*) [AddCommGroup T] [Finite T] :
    Nat.card (DoubleQuot T) = Nat.card (DoubleKer T) := by
  exact AddSubgroup.index_range

theorem doubleQuotFreeProdCard (n : ℕ) (T : Type*) [AddCommGroup T] [Finite T] :
    Nat.card (DoubleQuot ((Fin n →₀ ℤ) × T)) = 2 ^ n * Nat.card (DoubleKer T) := by
  rw [doubleQuotProdCard, doubleQuotFreeCard, doubleQuotFiniteCard]

/-- A finitely generated abelian group whose doubling kernel has four elements and
whose quotient by doubling has at most four elements is finite. -/
theorem finite_of_double_card [AddGroup.FG G]
    (hker : Nat.card (DoubleKer G) = 4)
    (hquot : Nat.card (DoubleQuot G) ≤ 4) : Finite G := by
  obtain ⟨n, ι, fι, p, hp, k, ⟨e⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let : Fintype ι := fι
  let (i : ι) : NeZero (p i ^ k i) := ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := DirectSum ι (fun i => ZMod (p i ^ k i))
  have : Finite T := Finite.of_equiv (∀ i : ι, ZMod (p i ^ k i))
    DFinsupp.equivFunOnFintype.symm
  have hT : Nat.card (DoubleKer T) = 4 := by
    rw [← Nat.card_congr (doubleKerFreeProdEquiv n T),
      ← Nat.card_congr (doubleKerEquiv e)]
    exact hker
  have hn : Nat.card (DoubleQuot ((Fin n →₀ ℤ) × T)) ≤ 4 := by
    rw [← Nat.card_congr (doubleQuotEquiv e).toEquiv]
    exact hquot
  rw [doubleQuotFreeProdCard, hT] at hn
  have hn0 : n = 0 := by
    by_contra h
    have : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
           _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.one_le_iff_ne_zero.mpr h)
    omega
  subst n
  exact Finite.of_equiv ((Fin 0 →₀ ℤ) × T) e.symm.toEquiv

/-- Under the same cardinality conditions, every element has finite additive order. -/
theorem isAddTorsion_of_double_card [AddGroup.FG G]
    (hker : Nat.card (DoubleKer G) = 4)
    (hquot : Nat.card (DoubleQuot G) ≤ 4) : IsAddTorsion G := by
  have : Finite G := finite_of_double_card hker hquot
  exact isAddTorsion_of_finite

#print axioms finite_of_double_card
#print axioms isAddTorsion_of_double_card

end FGCardCore

