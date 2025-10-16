import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Module.LinearMap.Basic

class LieRinehartAlgebra (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A]
(L : Type) [AddCommMonoid L] [Module A L] [LieRing L] [LieAlgebra R L] where
ρ : L →ₗ[A] Derivation R A A
islie : ∀ (x y : L), ρ ⁅x,y⁆ = ⁅ ρ x, ρ y ⁆
leibniz : ∀ (x y : L) (a : A), ⁅x,a • y⁆ = a• ⁅ x, y ⁆ + ((ρ (x)) (a))•y


variable {R : Type} [CommRing R]
variable {A : Type} [CommRing A] [Algebra R A]

instance : LieRinehartAlgebra R A (Derivation R A A) where
ρ := LinearMap.id
islie:= by simp
leibniz:= by
  intros x y a
  ext b
  simp only [Derivation.commutator_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    Derivation.leibniz, LinearMap.id_coe, id_eq, Derivation.coe_add, Pi.add_apply];
  ring

structure LRMap (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A]
(L : Type) [AddCommMonoid L] [Module A L] [LieRing L] [LieAlgebra R L]
(LR : LieRinehartAlgebra R A L) [CommRing R] (A' : Type) [CommRing A'] [Algebra R A']
(L' : Type) [AddCommMonoid L'] [Module A' L'] [LieRing L'] [LieAlgebra R L']
(LR' : LieRinehartAlgebra R A' L') (σ : A →+* A') extends LinearMap σ L L' where
isLie : ∀ (x y : L), toFun ⁅x,y⁆ = ⁅ toFun x, toFun y ⁆
anchorcomp: ∀ (a : A) (l : L), σ ((LR.ρ l) a)  =  ((LR'.ρ (toFun l)) (σ a))
