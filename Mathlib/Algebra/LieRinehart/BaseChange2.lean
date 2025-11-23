import Mathlib.Algebra.LieRinehart.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Prod

section relative_derivations
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']


--Todo: After Derivation.compAlgebraMap there should be a lemma showing that the association is
-- linear, like bere but with values in `M`
def derivation_pullback : Derivation R A' A' →ₗ[A'] Derivation R A A' :=
{
  toFun :=  Derivation.compAlgebraMap (R := R) (A := A) (B := A') (M := A')
  map_add' := by exact fun x y ↦ rfl
  map_smul' := by exact fun m x ↦ rfl
}

def σ := Algebra.ofId A A'




end relative_derivations
