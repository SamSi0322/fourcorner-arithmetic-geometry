import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

noncomputable section
namespace FourCorner.CommonLiteralField
variable (K : Type*) [Field K]

/-- The four literal radicands, in paper order P,C,M,B. -/
def radicand (t : K) : Fin 4 → RatFunc K
  | 0 => RatFunc.X + algebraMap K (RatFunc K) (t+1)
  | 1 => RatFunc.X - algebraMap K (RatFunc K) (t-1)
  | 2 => algebraMap K (RatFunc K) (t-1) *
      (algebraMap K (RatFunc K) (t+1) - RatFunc.X) / RatFunc.X
  | 3 => algebraMap K (RatFunc K) (t+1) *
      (RatFunc.X + algebraMap K (RatFunc K) (t-1)) / RatFunc.X

def radical (t : K) (i : Fin 4) : AlgebraicClosure (RatFunc K) :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) (radicand K t i))
    (show 0 < (2 : ℕ) by decide))

theorem radical_sq (t : K) (i : Fin 4) :
    radical K t i ^ 2 =
      algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) (radicand K t i) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (RatFunc K) (AlgebraicClosure (RatFunc K)) (radicand K t i))
    (show 0 < (2 : ℕ) by decide))

/-- The actual common four-root function field, inside an algebraic closure
of K(ell). No degree or genus is assigned by this definition. -/
def field (t : K) : IntermediateField (RatFunc K) (AlgebraicClosure (RatFunc K)) :=
  IntermediateField.adjoin (RatFunc K) (Set.range (radical K t))

def root (t : K) (i : Fin 4) : field K t :=
  ⟨radical K t i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩

theorem root_sq (t : K) (i : Fin 4) :
    root K t i ^ 2 = algebraMap (RatFunc K) (field K t) (radicand K t i) := by
  apply Subtype.ext
  exact radical_sq K t i

/-- These four chosen roots generate exactly the declared field. -/
theorem root_adjoin_eq_top (t : K) :
    IntermediateField.adjoin (RatFunc K) (Set.range (root K t)) = ⊤ := by
  apply IntermediateField.lift_injective (field K t)
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨root K t i, ⟨i, rfl⟩, rfl⟩

#print axioms root_sq
#print axioms root_adjoin_eq_top
end FourCorner.CommonLiteralField
