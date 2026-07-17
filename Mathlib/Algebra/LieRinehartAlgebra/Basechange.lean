/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.Quotient
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.SemiDirect
public import Mathlib.Algebra.Lie.Derivation.BaseChange
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
/-!
....
-/

public section

namespace LieRinehartAlgebra


variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']

variable {L : Type*} [LieRing L] [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [LieAlgebra R L] [LieRinehartAlgebra R A L]

open TensorProduct LieAlgebra.SemiDirectSum


-- Defining the space Basechange, the goal is to show it is a Lie-Rinehart algebra
private def relative_anchor : A'⊗[A] L →ₗ[A'] Derivation R A A' :=
  LinearMap.liftBaseChange (A := A') (((Algebra.ofId A A').toLinearMap.compDer)
  ∘ₗ (LieRinehartAlgebra.anchor R A L).toLinearMap')

private lemma relative_anchor_apply (a : A') (l : L) (z : A) : relative_anchor (R := R) (a⊗ₜl) (z) =
    ⁅l, z⁆ • a := by
  simp [Algebra.smul_def, mul_comm]
  rfl

variable (R A A' L) in
def Basechange : Submodule A'  ((A' ⊗[A] L) × (Derivation R A' A')) where
  carrier := {x | relative_anchor x.1 = Derivation.compAlgebraMapL R A A' A' x.2}
  zero_mem' := by simp
  add_mem' {_ _} _ _ := by simp_all
  smul_mem' _ _ _ := by simp_all


-- To get the Bracket on Basechange we need a series of intermediate spaces
-- #1 LR
local notation "LR" => ((A' ⊗[R] L) ⋊⁅(Lie.Derivation.ofDerivation L)⁆ (Derivation R A' A'))

local instance : Module A' LR := Equiv.module A' (toProdl (Lie.Derivation.ofDerivation L)).toEquiv

private lemma LR_smul (a : A') (x : LR) : a • x = ⟨a • x.left, a • x.right⟩ := rfl

local instance : LieRingModule LR A' where
  bracket x a:= x.right a
  add_lie := by simp
  lie_add := by simp
  leibniz_lie x y a:= by simp [Derivation.commutator_apply]

private lemma LR_bracket_apply (x : LR) (a : A') : ⁅x, a⁆ = x.right a  := rfl

-- this is general and might be related to one of the derivation lemmas from the old version
private lemma rtensor_derivation {R A' M : Type*}
    [CommSemiring R] [CommSemiring A'] [Algebra R A'] [AddCommMonoid M] [Module R M]
    {d : Derivation R A' A'} {a : A'} {x : A' ⊗[R] M} :
    (d.rTensor M)  (a • x) = a • (d.rTensor M x) + (d a) • x  := by
  refine x.induction_on (by simp) (by simp [smul_tmul', add_tmul, mul_comm]) ?_
  intros _ _ h1 h2
  simp_rw [smul_add, map_add, smul_add, h1, h2]
  abel

-- this is general
theorem rTensor_smul' {R A M N P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [AddCommMonoid P] [Module R M] [Module R N] [Module R P]
    [CommSemiring A] [Algebra R A] [Module A N] [Module A P] [IsScalarTower R A N]
    [IsScalarTower R A P] (a : A) (f : N →ₗ[R] P) :
    (a • f).rTensor M = a • f.rTensor M := by  ext; simp; rfl


local instance : LieRinehartRing A' LR where
  lie_smul_eq_mul' _ _ _:= by simp [LR_bracket_apply, LR_smul];
  leibniz_mul_right' _ _ _ := by simp [LR_bracket_apply, mul_comm]
  leibniz_smul_right' x y a:= by
    simp [LR_smul, LR_bracket_apply, smul_sub, smul_add, rtensor_derivation, rTensor_smul']
    abel

local instance : LieRinehartAlgebra R A' LR where
  smul_assoc _ _ _ := by simp [LR_smul]
  smul_lie _ _ _ := by simp [LR_bracket_apply]
  lie_smul _ _ _ := by simp [LR_bracket_apply]

variable (R A A' L) in
abbrev tens_proj : LR →ₗ[A'] (A' ⊗[A] L) × (Derivation R A' A') where
  toFun :=
    ((TensorProduct.mapOfCompatibleSMul A R A' A' L).prodMap LinearMap.id) ∘
    (toProdl (Lie.Derivation.ofDerivation L))
  map_add' := by simp
  map_smul' a x:= by simp [LR_smul]

variable (R A A' L) in
private def LR' : LieRinehartSubalgebra A' LR :=
{
  __ := (Basechange R A A' L).comap (tens_proj R A A' L)
  lie_mem' {x y} hx hy := by sorry -- in the other file
}


-- # 3

private def K : StrictLieRinehartIdeal A' (LR' R A A' L) :=
{
  __ := ((tens_proj R A A' L)∘ₗ (LieRinehartSubalgebra.incl (LR' R A A' L) R).toLinearMap').ker
  ideal' {l l'} hl := by simp_all; sorry
  isotropic l a hl := by simp_all; sorry
}


end LieRinehartAlgebra
