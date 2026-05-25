import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.TransferInstance

namespace Equiv

section
variable {α β : Type*} [AddCommGroup α] [LieRing β]
variable {R : Type*} [CommRing R] [Module R α] [LieAlgebra R β]


/-- Transfer `LieRing` across an `AddEquiv` -/
protected abbrev lieRing (e : α ≃+ β) : LieRing α where
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

lemma bracket_def (e : α ≃+ β) (x y : α) :
    letI := Equiv.lieRing e
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

/-- Transfer `LieAlgebra` across a `LinearEquiv` -/
instance (e : α ≃ₗ[R] β) :
    letI := Equiv.lieRing e.toAddEquiv
    LieAlgebra R α :=
  letI := Equiv.lieRing e.toAddEquiv
  { lie_smul _ _ _ := by simp [bracket_def] }

/-- An equivalence `e : α ≃ₗ[R] β` gives a Lie algebra equivalence `α ≃ₗ⁅R⁆ β` where the Lie Bracket
on `α` is the one obtained by transporting a Lie Bracket on `β` back along `e`. -/
def lieEquiv (e : α ≃ₗ[R] β) :
    letI := Equiv.lieRing e.toAddEquiv
    α ≃ₗ⁅R⁆ β :=
  letI := Equiv.lieRing e.toAddEquiv
  { e with map_lie' := by simp [bracket_def] }


end

section
variable {α β : Type*} [LieRing β] (e : α ≃ β)
variable {R : Type*} [CommRing R] [LieAlgebra R β]

/-- Transfer `LieRing` across an `Equiv` -/
protected abbrev lieRing' [LieRing β] : LieRing α :=
  letI := e.addCommGroup
  Equiv.lieRing (e.addEquiv)

lemma bracket_def' (e : α ≃ β) (x y : α) :
    letI := Equiv.lieRing' e
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl



/-- Transfer `LieAlgebra` across an `Equiv` -/
protected abbrev lieAlgebra' :
    letI := Equiv.lieRing' e
    LieAlgebra R α :=
  letI := Equiv.lieRing' e
  letI := Equiv.module (R:= R) e
  { lie_smul _ _ _ := by simp [Equiv.smul_def, Equiv.bracket_def] }

/-- An equivalence `e : α ≃ₗ β` gives a Lie algebra equivalence `α ≃ₗ⁅R⁆ β` where the algebraic
structures on `α` are obtained by transporting the structures on `β` back along `e`. -/
def lieEquiv' :
    letI := Equiv.lieRing' e
    letI := Equiv.lieAlgebra' (R := R) e
    α ≃ₗ⁅R⁆ β :=
  letI := Equiv.lieRing' e
  letI := Equiv.lieAlgebra' (R := R) e
  { e.linearEquiv (R := R) with map_lie' {x y} := by simp [Equiv.bracket_def, Equiv.linearEquiv]}
   --defeq abuse, a lemma should be added to .linearequiv
end

end Equiv
