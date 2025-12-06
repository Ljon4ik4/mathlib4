import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower



section restrictScalars_sl
variable {R : Type*} [CommRing R]
variable {A : Type*} [Ring A] [Algebra R A]
variable {A' : Type*} [Ring A'] [Algebra R A']
variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] [Module A' M₂] [IsScalarTower R A' M₂]
variable {σ : A →ₐ[R] A'}

def LinearMap.restrictScalars_semilin (f : M →ₛₗ[σ.toRingHom] M₂) : (M →ₗ[R] M₂) := {
  f with
  map_smul':= by
    intros r m
    simp only [AlgHom.toRingHom_eq_coe, AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
    rw [←(IsScalarTower.algebraMap_smul A r m)]
    rw [f.map_smulₛₗ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, algebraMap_smul]
}

@[simp]
lemma restrictScalars_semilin.lem_RestrictedScalarhom (f : M →ₛₗ[σ.toRingHom] M₂) (x : M) :
f  x= (f.restrictScalars_semilin) x
:= by rfl

--variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃] [Module A M₃] [IsScalarTower R A M₃]
--lemma restrict_scalars_semi_is_restrict_scalars ( f : M →ₗ[A] M₃ ):
--f.restrictScalars R = f.restrictScalars_semilin := rfl

end restrictScalars_sl
