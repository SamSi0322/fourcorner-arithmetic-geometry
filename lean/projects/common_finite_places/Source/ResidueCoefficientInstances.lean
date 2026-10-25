import ResidueRadicalField

noncomputable section
namespace FourCorner.ResidueCoefficientInstances
variable {K : Type*} [Field K]

/-- Freeze the actual coefficient embedding before specializing K to a
concrete finite field; this contains no Scheme or genus data. -/
abbrev constantAlgebra (t κ : K) : Algebra K (CommonGenus17Field.field K t κ) := inferInstance

end FourCorner.ResidueCoefficientInstances
