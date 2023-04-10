import tactic.ring
import tactic.tidy
import group_theory.group_action
import linear_algebra.matrix.special_linear_group
import linear_algebra.determinant
import data.matrix.notation
import group_theory.group_action.basic
import algebra.hom.group_action
import linear_algebra.matrix
import linear_algebra.matrix.general_linear_group
import data.complex.basic
import mod_forms.modular_group.mat_m


--import .matrix_groups

/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/
open finset
open matrix

open_locale matrix

section
universe u

variables (n : Type* )  [decidable_eq n] [fintype n] (m : ℤ)



namespace modular_group

 local attribute [-instance] matrix.special_linear_group.has_coe_to_fun
local notation `SL2Z`:=special_linear_group (fin 2) ℤ

variables  {R : Type*} [comm_ring R]

lemma det_m (M: integral_matrices_with_determinant (fin 2) m): (M 0 0 * M 1 1 - M 0 1 * M 1 0)= m :=
begin
 have H:= matrix.det_fin_two M.1,
 simp at *,
 have m2:=M.2,
 rw ← H,
 simp_rw ← m2,
 simp,
end

lemma det_one  (M : SL2Z) : (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 1 :=
begin
apply det_m,
end

lemma det_onne  (M : SL2Z) : (M 0 0 * M 1 1 - M 1 0 * M 0 1) = 1 :=
begin
have:= det_one M,
have h1: M 1 0 * M 0 1 = M 0 1 * M 1 0, by {apply mul_comm},
rw h1,
apply this,
end

@[simp] lemma mat_mul_expl  (A B : matrix (fin 2) (fin 2) R) :
  (A * B) 0 0 =  A 0 0 * B 0 0 + A 0 1 * B 1 0 ∧
  (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 ∧
  (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 ∧
  (A * B) 1 1  = A 1 0 * B 0 1 + A 1 1  * B 1 1 :=
begin
  split, work_on_goal 2 {split}, work_on_goal 3 {split},
  all_goals {simp only [mul_eq_mul],
  rw  matrix.mul_apply,
  rw finset.sum_fin_eq_sum_range,
  rw finset.sum_range_succ,
  rw finset.sum_range_succ,
  simp [nat.succ_pos', lt_self_iff_false, dite_eq_ite, fin.mk_zero, if_true, finset.sum_empty, not_le,
    finset.range_zero, nat.one_lt_bit0_iff, zero_add, add_right_inj, fin.mk_one, subtype.val_eq_coe,
    ite_eq_left_iff]},
end

lemma SL2_inv_det_expl (A : SL2Z) : det ![![A.1 1 1, -A.1 0 1], ![-A.1 1 0 , A.1 0 0]] = 1 :=
begin
  rw [matrix.det_fin_two, mul_comm],
  simp only [subtype.val_eq_coe, cons_val_zero, cons_val_one, head_cons, mul_neg, neg_mul, neg_neg],
  have := A.2,
  rw matrix.det_fin_two at this,
  convert this,
end

lemma SL2_inv_expl (A : SL2Z) : A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0 , A.1 0 0]],
    SL2_inv_det_expl A⟩ :=
begin
  ext,
  have := matrix.adjugate_fin_two A.1,
  simp only [subtype.val_eq_coe] at this,
  simp at *,
  simp_rw [this],
  simp,
end

@[simp] lemma SL2Z_inv_a (A : SL2Z) : (A⁻¹).1 0 0 = A.1 1 1 :=
begin
rw SL2_inv_expl, simp,
end

@[simp] lemma SL2Z_inv_b (A : SL2Z) : (A⁻¹).1 0 1 = -A.1 0 1 :=
begin
rw SL2_inv_expl, simp,
end

@[simp] lemma SL2Z_inv_c (A : SL2Z) : (A⁻¹).1 1 0  = -A.1 1 0 :=
begin
rw SL2_inv_expl, simp,
end

@[simp] lemma SL2Z_inv_d (A : SL2Z) : (A⁻¹).1 1 1 = A.1 0 0 :=
begin
rw SL2_inv_expl, simp,
end

lemma m_a_b (m : ℤ) (hm : m ≠ 0) (A : SL2Z) (M N : integral_matrices_with_determinant (fin 2) m):
 (A • M) = N ↔  N 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 ∧
 N 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 ∧
 N 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 ∧
 N 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1 :=
begin
split,
intro h,
have:= mat_mul_expl  A M,  rw ← h, simp ,intro h, ext i j, fin_cases i; fin_cases j, simp at *, rw h.1,
simp  at *, rw h.2.1,simp at *, rw h.2.2.1,simp  at *, rw h.2.2.2,
end


@[simp] lemma SLnZ_M_a (A: SL2Z) (M: integral_matrices_with_determinant (fin 2) m) :
 (A • M) 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 :=
begin
simp [integral_matrices_with_determinante.SLnZ_M, add_mul, mul_add, mul_assoc],
end

@[simp] lemma SLnZ_M_b (A: SL2Z) (M: integral_matrices_with_determinant (fin 2) m) :
(A • M) 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 :=
begin
simp [integral_matrices_with_determinante.SLnZ_M, add_mul, mul_add, mul_assoc],
end

@[simp] lemma SLnZ_M_c (A: SL2Z) (M: integral_matrices_with_determinant (fin 2) m) :
(A • M) 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 :=
begin
simp [integral_matrices_with_determinante.SLnZ_M, add_mul, mul_add, mul_assoc],
end

@[simp] lemma SLnZ_M_d (A: SL2Z) (M: integral_matrices_with_determinant (fin 2) m)  :
 (A • M) 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1 :=
begin
simp [integral_matrices_with_determinante.SLnZ_M, add_mul, mul_add, mul_assoc],
end



def mat_Z_to_R (A : matrix (fin 2) (fin 2) ℤ ) :matrix (fin 2) (fin 2) ℝ :=
![![A 0 0, A 0 1], ![A 1 0 , A 1 1]]


instance Z_to_R: has_coe (matrix (fin 2) (fin 2) ℤ) (matrix (fin 2) (fin 2) ℝ ) :=⟨λ A, mat_Z_to_R A⟩

lemma nonzero_inv (a: ℝ) (h: 0 < a): is_unit (a):=

begin
have h2: a ≠ 0, {simp only [ne.def], by_contradiction h1, rw h1 at h, simp only [lt_self_iff_false] at h, exact h},
rw  is_unit_iff_exists_inv, use a⁻¹, apply mul_inv_cancel h2,
end


@[simp]lemma mat_val (A: SL2Z) (i j : fin 2): (mat_Z_to_R A.1) i j = (A.1 i j : ℝ):=

begin
rw mat_Z_to_R, fin_cases i; fin_cases j, simp only [matrix.cons_val_zero],
simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero],
simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero],
simp only [matrix.head_cons, matrix.cons_val_one],

end

instance SLZ_to_GLZ: has_coe SL2Z (matrix.special_linear_group (fin 2 ) ℝ):=
⟨λ A, ⟨mat_Z_to_R A.1, by {rw mat_Z_to_R, rw matrix.det_fin_two, have:= matrix.det_fin_two A,
  simp at *,
 norm_cast, exact this.symm,}, ⟩⟩

variable (C : GL_pos (fin 2) ℤ)




@[simp]lemma mat_vals (A: SL2Z) (i j : fin 2): ( A : (GL (fin 2) ℝ)) i j = (A.1 i j : ℝ):=

begin
 simp [mat_val, mat_Z_to_R], fin_cases i; fin_cases j, refl,refl,refl,refl,

end

@[simp] lemma det_coe_sl (A: SL2Z): (A: GL (fin 2) ℝ).val.det= (A.val.det: ℝ):=
begin
have:=A.2, rw this, simp, rw ← coe_coe, rw ← coe_coe, simp,
end


end modular_group

end
