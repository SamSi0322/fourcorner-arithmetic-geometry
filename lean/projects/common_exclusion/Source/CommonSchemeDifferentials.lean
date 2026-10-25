import CommonSchemeModel
import geometry.SchemeModelTwoAffineCover
import ModelGenusBridge.KaehlerSheafGenus

noncomputable section
namespace FourCorner.CommonSchemeModel
open AlgebraicGeometry AlgebraicCurve
universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The actual geometric smooth proper model has nine independent GLOBAL
regular Kähler differentials, with finiteness proved by the sheaf bridge. -/
theorem model_globalDifferentials_finrank_nine (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm : t ≠ -1) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (model t ht0 ht1 htm).toBase (model t ht0 ht1 htm).toBase.kaehler ⊤
    Module.Finite K Γ((model t ht0 ht1 htm).toBase.kaehler, ⊤) ∧
      Module.finrank K Γ((model t ht0 ht1 htm).toBase.kaehler, ⊤) = 9 := by
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
    (model t ht0 ht1 htm).toBase (model t ht0 ht1 htm).toBase.kaehler ⊤
  letI : FiniteDimensional (RatFunc K) (CommonLiteralField.field K t) :=
    FiniteDimensional.of_finrank_pos (by
      rw [CommonLiteralField.finrank_field_eq_sixteen K ht0 ht1 htm]; norm_num)
  obtain ⟨hfin,hrank⟩ := @KaehlerSheafBridge.finite_and_finrank_globalDifferentials_eq_genusFF
    K _ _ (model t ht0 ht1 htm).C
    (SchemeModelFiniteExtension.twoAffineOpenCover K (CommonLiteralField.field K t))
    (model t ht0 ht1 htm).toBase (model_integral t ht0 ht1 htm)
    (model_proper t ht0 ht1 htm) (model_smooth t ht0 ht1 htm)
  exact ⟨hfin,hrank.trans (geometric_model_genus_nine t ht0 ht1 htm)⟩

#print axioms model_globalDifferentials_finrank_nine
end FourCorner.CommonSchemeModel
