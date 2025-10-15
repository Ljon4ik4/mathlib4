import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Algebra.Module.LinearMap.Basic

variable {R : Type} [CommRing R]
variable {A : Type} [CommRing A] [Algebra R A]
variable {L : Type} [AddCommMonoid L] [Module A L] [LieRing L] [LieAlgebra R L]

class LieRinehartAlgebra (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A]
(L : Type) [AddCommMonoid L] [Module A L] [LieRing L] [LieAlgebra R L] where
ρ : L →ₗ[A] Derivation R A A
protected islie : ∀ (x y : L), ρ ⁅x,y⁆ = ⁅ ρ x, ρ y ⁆
protected leibniz : ∀ (x y : L) (a : A), ⁅x,a • y⁆ = a• ⁅ x, y ⁆ + ((ρ (x)) (a))•y

instance : LieRinehartAlgebra R A (Derivation R A A) where
ρ := LinearMap.id
islie:= by simp
leibniz:= by
  intros x y a
  ext b
  simp only [Derivation.commutator_apply, Derivation.coe_smul, Pi.smul_apply, smul_eq_mul,
    Derivation.leibniz, LinearMap.id_coe, id_eq, Derivation.coe_add, Pi.add_apply];
  ring
