import Mathlib.RingTheory.Derivation.Lie

class LieCommModule (L A M : Type*) [LieRing L] [CommRing A] [AddCommGroup M] [Module A M]
[LieRingModule L M] [LieRingModule L A] where
leibniz : ∀ (x : L) (a : A) (m : M),  ⁅x, a•m⁆ = a•⁅x, m⁆ + ⁅x, a⁆•m

class LieRinehartAlgebra (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
[LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
[LieModule R L A] [LieCommModule L A A] [LieCommModule L A L]



section

variable {R : Type} [CommRing R]
variable {A : Type} [CommRing A] [Algebra R A]

instance instDerLieRingModule : LieRingModule (Derivation R A A) A where
bracket:= fun X a ↦X (a)
add_lie:= by simp
lie_add:= by simp
leibniz_lie:=by exact fun x y m ↦ Eq.symm (add_eq_of_eq_sub rfl)

instance : LieModule R (Derivation R A A) A where
smul_lie := by exact fun t x m ↦ rfl
lie_smul := by
  intros r X a
  exact X.map_smul_of_tower r a

@[simp]
lemma bracketmul (X : Derivation R A A) (a : A) : ⁅ X ,a ⁆ = X (a) := by rfl

instance : LieCommModule (Derivation R A A) A A where
leibniz:=by
  intros X a m
  simp
  exact CommMonoid.mul_comm m (X a)

instance : LieCommModule (Derivation R A A) A (Derivation R A A) where
leibniz:= by
  intros X a Y
  ext b
  simp
  repeat rw [Derivation.commutator_apply]
  simp
  ring


instance : LieRinehartAlgebra R A (Derivation R A A) :={}

end
