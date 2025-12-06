import Mathlib.Algebra.LieRinehart.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Prod

section relative_derivations
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
variable {L : Type*} [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
[LieRingModule L A] [LieModule R L A] [LieRinehartAlgebra R A L]



def σ := Algebra.ofId A A'


open TensorProduct


variable (R A A' L) in
@[simps!]
def anchor_and_mult : A'→ₗ[A] L →ₗ[A] (Derivation R A A') :=
{
  toFun := fun a ↦a • (σ.toLinearMap.compDer ∘ₗ (LieRinehartAlgebra.ρ R A L).toLinearMap)
  map_add' := by exact fun x y↦
    Module.add_smul x y (σ.toLinearMap.compDer ∘ₗ (LieRinehartAlgebra.ρ R A L).toLinearMap)
  map_smul' := by exact fun m x ↦
    IsScalarTower.smul_assoc m x (σ.toLinearMap.compDer ∘ₗ (LieRinehartAlgebra.ρ R A L).toLinearMap)
}

variable (R A A' L) in
@[simps!]
def induced_rel_derivation :  (A'⊗[A] L) →ₗ[A'] (Derivation R A A') :=
{
  toFun := TensorProduct.lift (anchor_and_mult R A A' L)
  map_add' := by simp only [map_add, implies_true]
  map_smul' := by
    intros a x;
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero, RingHom.id_apply]
    | tmul x y =>
      ext b;
      simp only [smul_tmul', smul_eq_mul, lift.tmul, RingHom.id_apply, Derivation.coe_smul,
        Pi.smul_apply]
      unfold anchor_and_mult
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, LinearMap.coe_comp,
        Function.comp_apply, Derivation.coe_smul, Derivation.coe_comp,
        LinearMap.coe_restrictScalars, AlgHom.coe_toLinearMap, Derivation.coeFn_coe, Pi.smul_apply,
        smul_eq_mul]
      unfold LieRinehartAlgebra.ρ
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, LinearMap.coe_mk, AddHom.coe_mk]
      exact mul_assoc a x (σ ⁅y, b⁆)
    | add x y h1 h2 =>
      simp only [smul_add, map_add]
      rw [h1,h2]
}


variable (R A A' L) in
abbrev LRPullback := LinearMap.ker
(LinearMap.coprod (induced_rel_derivation R A A' L) (Derivation.compAlgebraMapL R A A' A'))

end relative_derivations

section tensorsurjection
open TensorProduct

variable {R A M N} [CommRing R] [CommRing A] [Algebra R A]
[AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
[AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]



variable (R A M N) in
def canprodmap :  M →ₗ[R] N →ₗ[R] M ⊗[A] N
:={
  toFun:= (LinearMap.restrictScalars R) ∘ ((TensorProduct.mk A M N).restrictScalars R)
  map_add' := by simp only [LinearMap.coe_restrictScalars, Function.comp_apply, map_add,
    LinearMap.restrictScalars_add, implies_true]
  map_smul' := by simp only [LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearMap.map_smul_of_tower, LinearMap.restrictScalars_smul, RingHom.id_apply, implies_true]
}

variable (R A M N) in
abbrev pushtensor : M⊗[R] N →ₗ[R]  M ⊗[A] N := TensorProduct.lift (canprodmap R A M N)

open Function

variable (R A M N) in
theorem pushtensorsurj : Surjective (pushtensor R A M N) := by
  intro y
  let ⟨t,ht⟩:= TensorProduct.exists_finset y
  use  t.sum fun i ↦ i.1 ⊗ₜ[R] i.2
  simp only [map_sum, lift.tmul]
  exact id (Eq.symm ht)





end tensorsurjection
