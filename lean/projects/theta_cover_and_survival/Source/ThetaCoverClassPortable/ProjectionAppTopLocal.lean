import ThetaCoverClassPortable.FieldH0BaseChange
import Mathlib.Topology.Sheaves.SheafCondition.Sites
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace FourCorner.ProjectionAppTopLocal
variable {X Y:Scheme.{u}}
def structureMap (q:X⟶Y):Y.sheaf⟶(TopCat.Sheaf.pushforward CommRingCat q.base).obj X.sheaf:=
 ⟨q.toLRSHom'.toHom.c⟩
theorem bijective_appTop_of_affine_local (q:X⟶Y)
 (h:∀(U:Y.Opens),IsAffineOpen U→Function.Bijective (q.app U)):
 Function.Bijective q.appTop := by
  let a:=structureMap q
  have hb:Opens.IsBasis (Set.range (fun U:{U:Y.Opens//IsAffineOpen U}=>U.val)) := by
    have hs:Set.range (fun U:{U:Y.Opens//IsAffineOpen U}=>U.val)=Y.affineOpens := by
      ext U
      constructor
      · rintro ⟨U,rfl⟩;exact U.property
      · intro hU;exact ⟨⟨U,hU⟩,rfl⟩
    rw [hs]
    exact Y.isBasis_affineOpens
  haveI:IsIso a:=TopCat.Sheaf.isIso_iff_isIso_basis hb (fun U=>
    (ConcreteCategory.isIso_iff_bijective _).mpr (h U.val U.property))
  haveI:IsIso ((TopCat.Sheaf.forget CommRingCat Y).map a):=inferInstance
  haveI:IsIso (a.hom.app (op ⊤)):=inferInstance
  exact (ConcreteCategory.isIso_iff_bijective _).mp (inferInstance:IsIso (a.hom.app (op ⊤)))
#print axioms bijective_appTop_of_affine_local
end FourCorner.ProjectionAppTopLocal
