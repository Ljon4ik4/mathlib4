import Mathlib.Algebra.LieRinehart.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic

variable {R : Type} [CommRing R]

variable {A : Type} [CommRing A] [Algebra R A]
variable {A' : Type} [CommRing A'] [Algebra R A']
variable (σ : A →ₐ[R] A')
variable {L : Type} [LieRing L] [LieAlgebra R L] [Module A L] [IsScalarTower R A L]

#check Derivation R A (σ.inducedMod)




--instance pullback (σ L ρ) [CommRing R][CommRing A] [Algebra R A][LieRing L] [Module A L]
--[LieAlgebra R L] [IsScalarTower R A L] [CommRing A'] [Algebra R A'] :
--LieRinehartAlgebra R A' (TensorProduct R A L) := {}
-- Module.compHom A' σ.toRingHom
