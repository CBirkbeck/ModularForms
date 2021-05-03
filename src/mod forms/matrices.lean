import algebra.big_operators data.set.finite
import category_theory.category
import linear_algebra.matrix

universes u v

namespace matrix
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : Type v}

section free_module

structure free_module (α : Type v) [semiring α] : Type (v+1) :=
(carrier : Type v)
[fin : fintype carrier]
[deceq : decidable_eq carrier]

instance (α) [semiring α] : has_coe_to_sort (free_module α) := ⟨_, free_module.carrier⟩
instance {α} [semiring α] (n : free_module α) : fintype n := free_module.fin _
instance {α} [semiring α] (n : free_module α) : decidable_eq n := free_module.deceq _

variables [semiring α]

open category_theory

instance : large_category (free_module α) :=
{ hom  := λ m n, matrix m n α,
  id   := λ m, 1,
  comp := λ _ _ _, matrix.mul,
  comp_id' := λ _ _, matrix.mul_one,
  id_comp' := λ _ _, matrix.one_mul,
  assoc'   := λ _ _ _ _, matrix.mul_assoc }

end free_module

section diagonal
variables [decidable_eq n]

@[simp] lemma ite_mul [semiring α] (P Q : Prop) [decidable P] [decidable Q] (a b : α) :
  (ite P a 0) * (ite Q b 0) = ite (P ∧ Q) (a * b) 0 :=
by split_ifs; simp * at *

@[simp] lemma eq_and_eq_symm {α : Type u} (a b : α) : (a = b ∧ b = a) ↔ a = b :=
by simp [eq_comm]

end diagonal

section scalar
variables [decidable_eq n] [has_zero α]

def scalar (a : α) : matrix n n α := diagonal (λ _, a)

@[simp] theorem scalar_val_eq {a : α} {i : n} : (scalar a) i i = a :=
diagonal_val_eq _

@[simp] theorem scalar_val_ne {a : α} {i j : n} (h : i ≠ j) : (scalar a) i j = 0 :=
diagonal_val_ne h

@[simp] theorem scalar_zero : (scalar 0 : matrix n n α) = 0 := diagonal_zero

@[simp] theorem scalar_one  [has_one α] : (scalar 1 : matrix n n α) = 1 := rfl

end scalar

end matrix
