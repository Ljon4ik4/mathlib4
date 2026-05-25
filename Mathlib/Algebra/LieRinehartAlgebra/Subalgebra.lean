import Mathlib.Algebra.LieRinehartAlgebra.Defs


section

variable (A L : Type*) [CommRing A] [LieRing L] [Module A L] [LieRingModule L A]

structure LieRinehartSubring extends Submodule A L where
  lie_mem' {a b} : a ∈ carrier → b ∈ carrier → ⁅a,  b⁆ ∈ carrier

namespace LieRinehartSubring


end LieRinehartSubring


end
