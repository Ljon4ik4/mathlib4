/-
Copyright (c) 2025 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/


import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Module.LinearMap.Basic


/-!
# Lie Rinehart algebras
This file defines Lie-Rinehart algebras and their morphisms.
Lie Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
singular foliations. They typical Cartan calculus of differential geometry can be restated fully in
terms of the Chevalley-Eilenberg algebra of a Lie-Rinehart algebra.

## References

*

## Tags

Lie-Rinehart algebra
-/


/-- A Lie-Rinehart algebra over a commutative Ring `R` is a commutative `R`-algebra `A` together
with an `A`-module `L` equipped with a Lie bracket and a Lie algebra and module homomorphism
`ρ:L→ Der_R(A,A)` to the derivations of `A`, such that the Leibniz rule `⁅x,a•y⁆=a•⁅x,y⁆+ρ(x)(a)•y`
is satisfied.
-/
class LieRinehartAlgebra {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A]
[LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
(ρ : L →ₗ[A] Derivation R A A) where
islie : ∀ (x y : L), ρ ⁅x,y⁆ = ⁅ ρ x, ρ y ⁆
leibniz : ∀ (x y : L) (a : A), ⁅x,a • y⁆ = a• ⁅ x, y ⁆ + ((ρ (x)) (a))•y


namespace LieRinehart


/-- A homomorphism of Lie-Rinehart algebras `(A,L)`, `(A',L')` consists of an algebra map `σ:A→ A'`
and an `A`-linear map `F: L→L'` which is also a Lie algebra homomorphism.
-/
structure Hom {R A A' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing A']
[Algebra R A'] (σ : A →+* A') {L L' : Type*} [LieRing L] [Module A L]
[LieAlgebra R L] [IsScalarTower R A L] [LieRing L'] [Module A' L']
[LieAlgebra R L'] [IsScalarTower R A' L']
(ρ : L →ₗ[A] Derivation R A A) (ρ' : L' →ₗ[A'] Derivation R A' A')
[LieRinehartAlgebra ρ] [LieRinehartAlgebra ρ'] extends LinearMap σ L L' where
isLie : ∀ (x y : L), toFun ⁅x,y⁆ = ⁅ toFun x, toFun y ⁆
anchorcomp: ∀ (a : A) (l : L), σ ((ρ l) a)  =  ((ρ' (toFun l)) (σ a))


variable {R : Type} [CommRing R]
variable {A : Type} [CommRing A] [Algebra R A]
variable {L : Type} [LieRing L] [Module A L] [LieAlgebra R L]
[IsScalarTower R A L]
variable {A' : Type} [CommRing A'] [Algebra R A']
variable {L' : Type} [LieRing L'] [Module A' L'] [LieAlgebra R L']
[IsScalarTower R A' L']
variable {A'' : Type} [CommRing A''] [Algebra R A'']
variable {L'' : Type} [LieRing L''] [Module A'' L''] [LieAlgebra R L'']
variable (σ : A →ₐ[R] A')
variable (ρ : L →ₗ[A] Derivation R A A) [LieRinehartAlgebra ρ]
variable (ρ' : L' →ₗ[A'] Derivation R A' A') [LieRinehartAlgebra ρ']


/-- `Der_R(A,A)` itself is a Lie-Rinehart algebra with `ρ=id`
-/
instance : LieRinehartAlgebra (LinearMap.id :(Derivation R A A)→ₗ[A] (Derivation R A A)) where
islie:= by simp
leibniz:= by
  intros x y a
  ext b
  simp only [Derivation.commutator_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    Derivation.leibniz, LinearMap.id_coe, id_eq, Derivation.coe_add, Pi.add_apply];
  ring

/-- The identity morphism of a Lie Rinehart algebra L
-/
def id : LieRinehart.Hom (RingHom.id A) ρ ρ :=
{
  (LinearMap.id : L→ₗ[A] L) with
  isLie:= by simp
  anchorcomp := by simp
}

end LieRinehart
