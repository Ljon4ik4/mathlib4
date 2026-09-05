import Mathlib.Algebra.LieRinehartAlgebra.Defs
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Data.Finmap

variable (R A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [CommRing R] [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]
    (i : ℕ)

def differential : (Module.Dual A (⋀[A]^i L))
    →ₗ[R] (Module.Dual A (⋀[A]^(i+1) L)) := {
  toFun α := sorry
  map_add' := sorry
  map_smul' := sorry
}

-- #check exteriorPower.alternatingMapLinearEquiv

-- #check AlternatingMap R L A (Fin i)

-- #check AlternatingMap.mk


variable (α : L [⋀^Fin i]→ₗ[A] A)

#check AlternatingMap.coe_multilinearMap_mk ( R:= A)
  (
    fun (x : (Fin i) → L) => (∑ j : Fin i, ⁅(x j) , α (x.erase i) ⁆)
  )

#check Finset.sum_erase_attach

#check Finmap.erase
