import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Module.Rat
noncomputable section
namespace FourCorner.OriginalCoverCompletion

/-- A field generated over Q by f(F) and q is generated over F by q,
where the F-algebra structure is the actual embedding f. -/
theorem adjoin_top_of_rational_generators {F E ι : Type*} [Field F] [Field E]
    [Algebra ℚ F] [Algebra ℚ E] [Algebra F E] [IsScalarTower ℚ F E]
    (z : ι → E) (q : E)
    (hgen : IntermediateField.adjoin ℚ (Set.range z∪{q})=⊤)
    (hcoords : ∀i,∃x,algebraMap F E x=z i) :
    IntermediateField.adjoin F {q}=(⊤ : IntermediateField F E) := by
  let L := IntermediateField.adjoin F {q}
  apply top_unique
  intro w hw
  clear hw
  have hw : w∈IntermediateField.adjoin ℚ (Set.range z∪{q}) := by rw [hgen]; trivial
  induction hw using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨i,rfl⟩|hx
    · obtain ⟨u,hu⟩ := hcoords i
      rw [←hu]
      exact L.algebraMap_mem u
    · have he : x=q := Set.mem_singleton_iff.mp hx
      rw [he]
      exact IntermediateField.mem_adjoin_simple_self F q
  | algebraMap r =>
    rw [IsScalarTower.algebraMap_apply ℚ F E]
    exact L.algebraMap_mem (algebraMap ℚ F r)
  | add x y hx hy ihx ihy => exact L.add_mem ihx ihy
  | inv x hx ih => exact L.inv_mem ih
  | mul x y hx hy ihx ihy => exact L.mul_mem ihx ihy

#print axioms adjoin_top_of_rational_generators
end FourCorner.OriginalCoverCompletion
