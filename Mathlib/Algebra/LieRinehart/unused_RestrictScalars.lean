import Mathlib.Algebra.Algebra.Basic

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
