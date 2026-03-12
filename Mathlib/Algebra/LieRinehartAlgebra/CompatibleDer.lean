import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.RingTheory.Derivation.Lie

-- this is not needed for basechange and can be a separate PR
-- to add to semidirectsum
namespace LieAlgebra
namespace SemiDirectSum
section DirectSum

variable {R : Type*} [CommRing R]
variable {K : Type*} [LieRing K] [LieAlgebra R K]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (R K L) in
abbrev DirectLieSum := K ⋊⁅(0 : L→ₗ⁅R⁆ (LieDerivation R K K))⁆ L

notation:35 K " ⊕⁅" R "⁆" L:35 => DirectLieSum R K L

def projl' : (K ⊕⁅R⁆ L →ₗ⁅R⁆ K) where
  __ := projl 0
  map_lie' := by simp

end DirectSum
end SemiDirectSum
end LieAlgebra

--to add to Derivation.Lie
section CompatibleDerivations
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']

variable (R A A') in
def CompatibleDerivations : LieSubalgebra R  ( (Derivation R A' A') ⊕⁅R⁆ (Derivation R A A)) where
  carrier := { x | (x.left).compAlgebraMapL R A A' A'
    = (Algebra.ofId A A').toLinearMap.compDer (x.right) }
  add_mem' {x y} hx hy  := by simp at hx hy; simp [hx,hy]
  zero_mem' := by simp
  smul_mem'  c x h := by simp at h; simp [h]
  lie_mem' {x y} hx hy := by
    have hxx (a : A) := congrArg (fun f => f a) hx
    have hyy (a : A) := congrArg (fun f => f a) hy
    simp at hxx hyy
    ext z
    simp [Derivation.commutator_apply, hxx, hyy]
end CompatibleDerivations
