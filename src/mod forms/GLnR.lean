/-

The Genera Linear group $GL(n, R)$
-/
import linear_algebra.matrix
import linear_algebra.nonsingular_inverse

/-!
# The General Linear group $GL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`,
also written `SL(n, R)` or `SLₙ(R)`, consisting of all `n` by `n` `R`-matrices with
determinant `1`.  In addition, we define the group structure on `special_linear_group n R`
and the embedding into the general linear group `GLn R (n → R)`
(i.e. `GL(n, R)` or `GLₙ(R)`).

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with invertible determinant 
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)


## Implementation notes


## References

 
## Tags

matrix group, group, matrix inverse
-/

namespace matrix
universes u v
open_locale matrix
open linear_map


section

variables (n : Type u) [decidable_eq n] [fintype n] (R : Type v) [comm_ring R]

/-- `GLn n R` is the group of `n` by `n` `R`-matrices with invertible .
-/
def GLn := { A : matrix n n R // is_unit (A.det) }

end

namespace GLn

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

instance coe_matrix : has_coe (GLn n R) (matrix n n R) :=
⟨λ A, A.val⟩

instance coe_fun : has_coe_to_fun (GLn n R) :=
{ F   := λ _, n → n → R,
  coe := λ A, A.val }


def to_lin' (A : GLn n R) := matrix.to_lin' A

lemma ext_iff (A B : GLn n R) : A = B ↔ (∀ i j, A i j = B i j) :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : GLn n R) : (∀ i j, A i j = B i j) → A = B :=
(GLn.ext_iff A B).mpr





noncomputable def nonsing_inve (A : GLn n R) := matrix.nonsing_inv A


lemma nonsing_inve_det (A: GLn n R): (det (nonsing_inve A))* (det A.1)=1:=
begin
have h1:= nonsing_inv_det A.1 A.2, convert h1,
end



lemma inv_in_gl (A : GLn n R): is_unit (det (nonsing_inve A)):=

begin
 have h1:=nonsing_inve_det A, rw is_unit_iff_exists_inv, use A.val.det, exact h1,
end  


instance has_mul : has_mul (GLn n R) :=
⟨λ A B, ⟨A.1 ⬝ B.1, by {erw [det_mul], apply is_unit.mul A.2 B.2}⟩⟩

instance has_one : has_one (GLn n R) :=
⟨⟨1, by {simp only [det_one, is_unit_one]}⟩⟩

/--/
instance:  has_scalar (units R) (GLn n R) :=
⟨ λ u M, ⟨ u •  M.1,  ⟩    ⟩ 
-/

noncomputable instance has_inv : has_inv (GLn n R) :=
⟨λ A, ⟨nonsing_inve A, inv_in_gl A⟩ ⟩

/-
lemma nonsing_inve_apply (A: GLn n R) (h : is_unit (det A)) :
  A⁻¹ = (↑h.unit⁻¹ : R) • adjugate A :=
by { change A.nonsing_inv = _, dunfold nonsing_inv, simp only [dif_pos, h], }-/



instance : inhabited (GLn n R) := ⟨1⟩

section coe_lemmas

variables (A B : GLn n R)

@[simp] lemma inv_val : ↑(A⁻¹) = nonsing_inve A := rfl

@[simp] lemma inv_apply : ⇑(A⁻¹) = nonsing_inve A := rfl


@[simp] lemma mul_val : ↑(A * B) = A ⬝ B := rfl

@[simp] lemma mul_apply : ⇑(A * B) = (A ⬝ B) := rfl


@[simp] lemma one_val : ↑(1 : GLn n R) = (1 : matrix n n R) := rfl

@[simp] lemma one_apply : ⇑(1 : GLn n R) = (1 : matrix n n R) := rfl



@[simp] lemma to_lin'_mul :
  to_lin' (A * B) = (to_lin' A).comp (to_lin' B) :=
matrix.to_lin'_mul A B

@[simp] lemma to_lin'_one :
  to_lin' (1 : GLn n R) = linear_map.id :=
matrix.to_lin'_one

end coe_lemmas


lemma is_left_inv (A : GLn n R): A⁻¹ *  A = 1:=

begin
have h1: is_unit (det A), by {have:=A.2, exact this,},
have:=nonsing_inv_mul A A.2, ext, dsimp, rw nonsing_inve, rw nonsing_inv, simp only [dif_pos, h1], rw nonsing_inv_apply at this, rw this,
end  



lemma inv_is_inv (A : GLn n R) : A.nonsing_inve= (↑A)⁻¹:=

begin
have h1: is_unit (det A), by {have:=A.2, exact this,},
have:=is_left_inv A, have:=nonsing_inv_mul A.1 h1, simp at this, have:=nonsing_inv_apply A h1, 
ext, dsimp, rw nonsing_inve, rw nonsing_inv, simp only [dif_pos, h1], cases h1, cases A, cases A_property,
 dsimp at *, simp at *, injections_and_clear, dsimp at *, solve_by_elim, 
end  


@[simp] lemma valor (A : GLn (fin 2) R):  A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1  :=

begin
split, refl, split, refl,split, refl, refl,
end  


noncomputable instance group : group (GLn n R) :=
{ mul_assoc := λ A B C, by { ext, simp [matrix.mul_assoc] },
  one_mul := λ A, by { ext, simp },
  mul_one := λ A, by { ext, simp },
  mul_left_inv := λ A, by {apply  is_left_inv A },
  ..GLn.has_mul,
  ..GLn.has_one,
  ..GLn.has_inv }







@[simp] lemma mat_mul_real  (A B : GLn (fin 2) R) : (A * B) 0 0 =  A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧ (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧ (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧ (A * B) 1 1  = A 1 0 * B 0 1 + A 1 1  * B 1 1:=

begin
split,  simp only [mul_val, subtype.val_eq_coe, valor],
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw finset.sum_range_succ,
rw finset.sum_range_succ,
simp only [nat.succ_pos', lt_self_iff_false, dite_eq_ite, fin.mk_zero, forall_false_left, if_true, finset.sum_empty, not_le,
  finset.range_zero, nat.one_lt_bit0_iff, zero_add, add_right_inj, fin.mk_one, subtype.val_eq_coe, valor,
  ite_eq_left_iff], 
  split,  simp only [mul_val, subtype.val_eq_coe, valor],
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw finset.sum_range_succ,
rw finset.sum_range_succ,
simp only [nat.succ_pos', lt_self_iff_false, dite_eq_ite, fin.mk_zero, forall_false_left, if_true, finset.sum_empty, not_le,
  finset.range_zero, nat.one_lt_bit0_iff, zero_add, add_right_inj, fin.mk_one, subtype.val_eq_coe, valor,
  ite_eq_left_iff],
  split, simp only [mul_val, subtype.val_eq_coe, valor],
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw finset.sum_range_succ,
rw finset.sum_range_succ,
simp only [nat.succ_pos', lt_self_iff_false, dite_eq_ite, fin.mk_zero, forall_false_left, if_true, finset.sum_empty, not_le,
  finset.range_zero, nat.one_lt_bit0_iff, zero_add, add_right_inj, fin.mk_one, subtype.val_eq_coe, valor,
  ite_eq_left_iff], 
simp only [mul_val, subtype.val_eq_coe, valor],
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw finset.sum_range_succ,
rw finset.sum_range_succ,
simp only [nat.succ_pos', lt_self_iff_false, dite_eq_ite, fin.mk_zero, forall_false_left, if_true, finset.sum_empty, not_le,
  finset.range_zero, nat.one_lt_bit0_iff, zero_add, add_right_inj, fin.mk_one, subtype.val_eq_coe, valor,
  ite_eq_left_iff],   
end   




lemma det_of_22 (M: matrix (fin 2) (fin 2) R): M.det= (M 0 0) * (M 1 1) - (M 0 1) * (M 1 0):=

begin 
sorry,
end   







end GLn


end matrix
