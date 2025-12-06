import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower


section
variable {R S : Type*} [Semiring R] [Semiring S]

variable (σ : R →+* S)

@[nolint unusedArguments, reducible]
def inducedModule (_ : R →+* S) (M₂ : Type*) [AddCommMonoid M₂] [Module S M₂] := M₂

notation M₂ "⟨" σ "⟩" => inducedModule σ M₂

variable (M₂ : Type*) [AddCommMonoid M₂] [Module S M₂]
instance : AddCommMonoid (M₂⟨σ⟩) := by infer_instance
instance : Module S (M₂⟨σ⟩) := by infer_instance
instance RMod : Module R (M₂⟨σ⟩) := by exact Module.compHom (M₂⟨σ⟩) σ

def inducedModuleiso : M₂ ≃ₗ[S] (M₂⟨σ⟩) := by rfl

variable (M : Type*) [AddCommMonoid M] [Module R M]


@[simp]
lemma linearity (r : R) (m : M₂⟨σ⟩) : r • m = σ (r) • m := by rfl

def restrictScalars (f : M →ₛₗ[σ] M₂) : (M →ₗ[R] M₂⟨σ⟩) :=
{
  toFun := f
  map_add' := by exact fun x y ↦ LinearMap.map_add f x y
  map_smul' := by
    intros r m
    rw [linearity]
    exact LinearMap.map_smulₛₗ f r m
}
end





section restrictScalars_alg
variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
{M : Type*} [AddCommMonoid M] [Module R M]
{M₂ : Type*} [AddCommMonoid M₂] [Module S M₂] [Module R M₂] [IsScalarTower R S M₂]

def LinearMap.restrictScalars_alg (f : M →ₛₗ[(Algebra.ofId R S).toRingHom] M₂) : M →ₗ[R] M₂ :=
{
  f with
  map_smul' := by
    intros r m
    simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId, AddHom.toFun_eq_coe, coe_toAddHom,
      LinearMap.map_smulₛₗ, algebraMap_smul, RingHom.id_apply]
}

@[simp]
lemma coe_restrictScalars_alg (f : M →ₛₗ[(Algebra.ofId R S).toRingHom] M₂) (x : M) :
f (x) = (LinearMap.restrictScalars_alg f) x := by rfl

end restrictScalars_alg



------------- ONLY THE ABOVE IS REALLY USED


section restrict_alg
variable {R : Type*} [CommRing R]
variable {S : Type*} [Ring S] [Algebra R S]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]

def LinearMap.restrictScalars_sl (f : M →ₛₗ[(Algebra.ofId R S).toRingHom] M₂) : (M →ₗ[R] M₂) := {
  f with
  map_smul' := by
    intros r m
    simp only [AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId, AddHom.toFun_eq_coe, coe_toAddHom,
      LinearMap.map_smulₛₗ, algebraMap_smul, RingHom.id_apply]
}
end restrict_alg


section restrictScalars_semi2
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {A' : Type*} [CommRing A'] [Algebra R A']
variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] [Module A' M₂] [IsScalarTower R A' M₂]
variable {σ : A →ₐ[R] A'}

variable (f : M →ₛₗ[σ.toRingHom] M₂)

--Here there is a problem about definitional equality
--def LinearMap.restrictScalars_semilin2 (f : M →ₛₗ[σ.toRingHom] M₂) : (M →ₗ[R] M₂) := by
--  haveI h0: Algebra A A' := σ.toAlgebra
--  #check f.restrictScalars_sl
--  sorry


end restrictScalars_semi2
