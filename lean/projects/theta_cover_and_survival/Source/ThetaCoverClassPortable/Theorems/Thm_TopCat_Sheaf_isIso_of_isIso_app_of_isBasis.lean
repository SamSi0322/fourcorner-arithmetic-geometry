import Mathlib.Topology.Sheaves.SheafCondition.Sites
open CategoryTheory Opposite TopologicalSpace
universe u v w
namespace TopCat.Sheaf
variable {C:Type u} [Category.{v} C] {X:TopCat.{w}} {ι:Type*}
 {B:ι→Opens X} {F G:TopCat.Sheaf C X}
theorem isIso_of_isIso_app_of_isBasis (h:Opens.IsBasis (Set.range B))
 {φ:F⟶G} (hi:∀i,IsIso (φ.hom.app (op (B i)))):IsIso φ :=
 isIso_iff_isIso_basis h hi
end TopCat.Sheaf
