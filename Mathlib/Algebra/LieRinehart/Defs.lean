/-
Copyright (c) 2025 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/

import Mathlib.RingTheory.Derivation.Lie

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
[Algebra R A'] (σ : A →ₐ[R] A') {L L' : Type*} [LieRing L] [Module A L]
[LieAlgebra R L] [IsScalarTower R A L] [LieRing L'] [Module A' L']
[LieAlgebra R L'] [IsScalarTower R A' L']
(ρ : L →ₗ[A] Derivation R A A) (ρ' : L' →ₗ[A'] Derivation R A' A')
[LieRinehartAlgebra ρ] [LieRinehartAlgebra ρ'] extends L →ₛₗ[σ.toRingHom] L' where
isLie : ∀ (x y : L), toLinearMap ⁅x,y⁆ = ⁅ toLinearMap x, toLinearMap y ⁆
anchorcomp: ∀ (a : A) (l : L), σ ((ρ l) a)  =  ((ρ' (toLinearMap l)) (σ a))

@[inherit_doc]
notation:25 ρ " →ₗ⁅" σ:25 "⁆ " ρ':0 => LieRinehart.Hom σ ρ ρ'






variable {R : Type} [CommRing R]

variable {A : Type} [CommRing A] [Algebra R A]
variable {L : Type} [LieRing L] [Module A L] [LieAlgebra R L]
[IsScalarTower R A L]
variable (ρ : L →ₗ[A] Derivation R A A) [LieRinehartAlgebra ρ]


variable {A' : Type} [CommRing A'] [Algebra R A']
variable {L' : Type} [LieRing L'] [Module A' L'] [LieAlgebra R L']
[IsScalarTower R A' L']
variable (ρ' : L' →ₗ[A'] Derivation R A' A') [LieRinehartAlgebra ρ']

variable {A'' : Type} [CommRing A''] [Algebra R A'']
variable {L'' : Type} [LieRing L''] [Module A'' L''] [LieAlgebra R L'']
[IsScalarTower R A'' L'']
variable (ρ'' : L'' →ₗ[A''] Derivation R A'' A'') [LieRinehartAlgebra ρ'']

variable (σ : A →ₐ[R] A')
variable (σ' : A' →ₐ[R] A'')









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

--TODO: Make this callable and add doc
def toLieHom (f : ρ →ₗ⁅σ⁆ ρ') : L →ₗ⁅R⁆ L' := {
  f.toLinearMap.toAddMonoidHom with
  map_smul' := by
    intros r x
    simp
    simp only [(IsScalarTower.algebraMap_smul (R:=R) (A:=A) (M:=L) r x).symm]
    calc f.toLinearMap ((algebraMap R A) r • x)
      = σ.toRingHom ((algebraMap R A) r) • f.toLinearMap (x) :=
       by rw [f.map_smulₛₗ (R:= A) (c := (algebraMap R A) r) (M:=L) (x:=x)]
      _ = r • f.toLinearMap (x) := by simp
  map_lie' := by
    apply f.isLie
  }

/-- The identity morphism of a Lie Rinehart algebra
-/
def id : LieRinehart.Hom (AlgHom.id R A) ρ ρ :=
{
  (LinearMap.id : L→ₗ[A] L) with
  isLie:= by simp
  anchorcomp := by simp
}

variable (f : ρ →ₗ⁅σ⁆ ρ')
variable (g : ρ' →ₗ⁅σ'⁆ ρ'')

--todo: add doc
def comp (f : ρ →ₗ⁅σ⁆ ρ') (g : ρ' →ₗ⁅σ'⁆ ρ'') : ρ →ₗ⁅AlgHom.comp σ' σ⁆ ρ'' :=
  { g.toLinearMap.toAddMonoidHom.comp f.toLinearMap with
  -- The map_smul and the .toMonoidHom are needed because RingHomCompTriple instance is not
  -- recognized
    map_smul' := by simp
    isLie := by
      intros x y
      simp
      calc  g.toLinearMap (f.toLinearMap ⁅x, y⁆)
        = g.toLinearMap ( ⁅f.toLinearMap x, f.toLinearMap  y⁆ ) := by rw [f.isLie]
        _ = ⁅ g.toLinearMap (f.toLinearMap x), g.toLinearMap (f.toLinearMap  y) ⁆ :=by rw [g.isLie]
    anchorcomp := by
      simp
      intros a l
      calc  σ' (σ ((ρ l) a))
        = σ' ((ρ' (f.toLinearMap l)) (σ a)) := by rw [f.anchorcomp]
        _ = (ρ'' (g.toLinearMap (f.toLinearMap l))) (σ' (σ a)) := by rw [g.anchorcomp]
  }


end LieRinehart
