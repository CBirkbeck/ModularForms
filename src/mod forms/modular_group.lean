import tactic.ring
import tactic.tidy
import group_theory.group_action
import linear_algebra.special_linear_group
import linear_algebra.determinant
import data.matrix.notation
import group_theory.group_action.basic
import algebra.group_action_hom
import linear_algebra.matrix
--import .matrix_groups

/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/

universe u 

run_cmd mk_simp_attr `SL2Z
 open finset 
 open matrix 
@[tidy] meta def tidy_ring := `[ring]

def MAT2:= matrix (fin 2) (fin 2) ℤ

@[elab_as_eliminator]
def fin2.rec_on {C : fin 2 → Sort*} : ∀ (n : fin 2), C 0 → C 1 → C n
| ⟨0, _⟩ C0 _ := C0
| ⟨1, _⟩ _ C1 := C1
| ⟨n+2, H⟩ _ _ := false.elim $ by cases H with H H; cases H with H H; cases H

@[elab_as_eliminator]
theorem fin2.induction_on {C : fin 2 → Prop} (n : fin 2) (H0 : C 0) (H1 : C 1) : C n :=
fin2.rec_on n H0 H1

section 


open_locale matrix
@[reducible]
def SL2Z := special_linear_group (fin 2) ℤ

instance: group SL2Z:= infer_instance



/-structure-/ 

@[derive decidable_eq]
def  integral_matrices_with_determinant (m : ℤ ) :={ A : matrix (fin 2) (fin 2) ℤ  // A.det = m }




variable (m: ℤ)



instance coe_matrix : has_coe (integral_matrices_with_determinant m) (matrix (fin 2) (fin 2) ℤ) :=
⟨λ A, A.val⟩



instance coe_fun : has_coe_to_fun (integral_matrices_with_determinant m) :=
{ F   := λ _, fin 2 → fin 2 → ℤ,
  coe := λ A, A.val }


def to_lin' (A : integral_matrices_with_determinant m) := matrix.to_lin' A

namespace integral_matrices_with_determinant


lemma ext_iff (A B :  integral_matrices_with_determinant m) : A = B ↔ (∀ i j, A i j = B i j) :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : integral_matrices_with_determinant m) : (∀ i j, A i j = B i j) → A = B :=

begin 
rw ext_iff,
simp,
end
/-(a b c d : ℤ)
(dets : a * d - b * c = m)
-/

end  integral_matrices_with_determinant






/-@[ext]
theorem integral_matrices_with_determinant.ext (m : ℤ) :
  ∀ (A B : integral_matrices_with_determinant m)
  (H1 : A.a = B.a) (H2 : A.b = B.b) (H3 : A.c = B.c) (H4 : A.d = B.d),
  A = B
| ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ rfl rfl rfl rfl := rfl
-/




def N': matrix  (fin 2) (fin 2 ) ℤ:= ![![-1, 0], ![0, -1]]

lemma ND: N'.det =1 :=

begin
rw N',
refl,
end   

def N : SL2Z := ⟨ N', ND ⟩




def Sr: matrix  (fin 2) (fin 2 ) ℤ:= ![![1, 0], ![0, 1]]

lemma SD2: Sr.det =1 :=

begin
rw Sr,
refl,
end   

def Ni : special_linear_group (fin 2) ℤ  := ⟨ Sr, SD2 ⟩



def S2: matrix  (fin 2) (fin 2 ) ℤ:= ![![-2, 0], ![0, -1]]





lemma str (A: SL2Z): det A = 1:= A.2



lemma MND (M: matrix (fin 2) (fin 2) ℤ): M.det= (M 0 0) * (M 1 1) - (M 0 1) * (M 1 0):=

begin 
sorry,
end   

lemma det_onee (A: SL2Z):  det A= A 0 0 * A 1 1 - A 1 0 * A 0 1 :=

begin

sorry,
end  

lemma det_onne (A: SL2Z):  A 0 0 * A 1 1 - A 1 0 * A 0 1=1 :=

begin
rw ← str A,
rw det_onee,
end 

lemma det_m (M: integral_matrices_with_determinant m): (M 0 0 * M 1 1 - M 1 0 * M 0 1)=m:=

begin 
sorry,
end  


lemma det_m''' (M: integral_matrices_with_determinant m) (h: M 1 0 = 0): M 0 0 * M 1 1=m:=

begin 
sorry,
end  

lemma det_m' (M: integral_matrices_with_determinant m): M 0 0 * M 1 1 - M 1 0 * M 0 1= M.val.det:=

begin
sorry,
end 


lemma det_m2 (M: integral_matrices_with_determinant m): M.1 0 0 * M.1 1 1 - M.1 1 0 * M.1 0 1= M.val.det:=

begin
sorry,
end 

/-instance : group SL2Z :=
{ mul := λ A B, ⟨A.a * B.a + A.b * B.c,
                A.a * B.b + A.b * B.d,
                A.c * B.a + A.d * B.c,
                A.c * B.b + A.d * B.d,
    calc  (A.a * B.a + A.b * B.c) * (A.c * B.b + A.d * B.d) - (A.a * B.b + A.b * B.d) * (A.c * B.a + A.d * B.c)
        = (A.a * A.d - A.b * A.c) * (B.a * B.d - B.b * B.c) : by ring
    ... = 1 : by rw [A.det, B.det, mul_one]⟩,
  mul_assoc := λ A B C, by cases A; cases B; cases C; ext; dsimp; ring,
  one := ⟨1, 0, 0, 1, rfl⟩,
  one_mul := λ A, by cases A; ext; change _ + _ = _; simp,
  mul_one := λ A, by cases A; ext; change _ + _ = _; simp,
  inv := λ A, ⟨A.d, -A.b, -A.c, A.a, by simpa [mul_comm] using A.det⟩,
  mul_left_inv := λ A, by cases A; ext; change _ + _ = _; dsimp ; simp [mul_comm]; dsimp  }-/

@[simp, SL2Z] lemma SL2Z_mul_a (A B : SL2Z) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := 

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
--rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end



 


@[simp, SL2Z] lemma SL2Z_mul_b (A B : SL2Z) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 :=

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
--rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end






@[simp, SL2Z] lemma SL2Z_mul_c (A B : SL2Z) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := 

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
--rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end






@[simp, SL2Z] lemma SL2Z_mul_d (A B : SL2Z) : (A * B) 1 1  = A 1 0 * B 0 1 + A 1 1  * B 1 1 :=

begin
simp,
rw  matrix.mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
--rw sum_range_succ,
simp only [nat.succ_pos', fin.mk_zero, dif_pos, nat.one_lt_bit0_iff, sum_singleton, fin.mk_one, range_one],
end

lemma mre: N * N = (1: SL2Z):=

begin
ext i j,
fin_cases i; fin_cases j,
rw SL2Z_mul_a N N, simp, refl,rw SL2Z_mul_b N N, simp, refl, rw SL2Z_mul_c N N, simp, refl, rw SL2Z_mul_d N N, simp, refl,
end   

 lemma ng : Ni = (1: special_linear_group (fin 2) ℤ ):=

 begin
  ext i j,
  fin_cases i; fin_cases j, 
   sorry, sorry,sorry,sorry,
 end   

lemma vale (A : integral_matrices_with_determinant m): A 0 0 = A.1 0 0 ∧ A 0 1 = A.1 0 1 ∧ A 1 0 = A.1 1 0 ∧ A 1 1 = A.1 1 1  :=

begin
split, refl, split, refl,split, refl, refl,
end  


@[simp, SL2Z] lemma SL2Z_one_a : (1 : SL2Z) 0 0 = 1 := rfl
@[simp, SL2Z] lemma SL2Z_one_b : (1 : SL2Z) 0 1 = 0 := rfl
@[simp, SL2Z] lemma SL2Z_one_c : (1 : SL2Z) 1 0 = 0 := rfl
@[simp, SL2Z] lemma SL2Z_one_d : (1 : SL2Z) 1 1 = 1 := rfl


lemma sl2_inv (A: SL2Z) (B: SL2Z)  (h1: B 0 0 = A 1 1)  (h2: B 0 1= - A 0 1) (h3: B 1 0 = - A 1 0) (h4: B 1 1 = A 0 0): A * B= (1: SL2Z) :=

begin
  ext i j,
  simp,
  rw mul_apply,
  rw finset.sum_fin_eq_sum_range,
  rw sum_range_succ,
  rw sum_range_succ,
  simp,
  sorry,

       





end 

 

@[simp, SL2Z] lemma SL2Z_inv_a (A : SL2Z) : (A⁻¹) 0 0 = A 1 1 :=

begin
 rw special_linear_group.inv_apply,
 rw adjugate_def,
 simp,
 rw cramer_apply,
 rw update_column,

 

/-simp,
rw  adjugate_apply, 
rw update_row,
rw det,
simp,-/
sorry,
end 




@[simp, SL2Z] lemma SL2Z_inv_b (A : SL2Z) : (A⁻¹) 0 1 = -A 0 1 := 

begin
sorry,
end  

@[simp, SL2Z] lemma SL2Z_inv_c (A : SL2Z) : (A⁻¹) 1 0  = -A 1 0 := 

begin
sorry,
end




@[simp, SL2Z] lemma SL2Z_inv_d (A : SL2Z) : (A⁻¹) 1 1 = A 0 0 := 

begin
sorry 
end 




def SL2Z_M (m : ℤ) : SL2Z → integral_matrices_with_determinant m → integral_matrices_with_determinant m :=
λ A B, ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩


/-def SL2Z_M (m : ℤ) : SL2Z → integral_matrices_with_determinant m → integral_matrices_with_determinant m :=
λ X Y, {  a := X 0 0 * Y 0 0 + X 0 1 * Y 1 0,
          b := X 0 0 * Y 0 1 + X 0 1 * Y 1 1,
          c := X 1 0 * Y 0 0 + X 1 1 * Y 1 0,
          d := X 1 0 * Y 0 1 + X 1 1 * Y 1 1,
          det := begin
            conv { to_rhs, rw ← one_mul m, congr, rw ← X.det, skip, rw ← Y.det },
            ring
          end}-/




lemma one_smull  : ∀ (M: integral_matrices_with_determinant m ),  SL2Z_M m (1: SL2Z) M= M :=

begin
rw SL2Z_M,
simp,
end

lemma mul_smull : ∀ (A B : SL2Z ), ∀ (M: integral_matrices_with_determinant m ), SL2Z_M m (A * B ) M= SL2Z_M m A (SL2Z_M m B M):=

begin  
simp [SL2Z_M],
intros A B M, 
simp [matrix.mul_assoc],
refl,
end   


/-instance (m: ℤ )  :  has_scalar (SL2Z) (integral_matrices_with_determinant m):=

{smul:= SL2Z_M (m : ℤ)}-/




instance (m: ℤ )  :  mul_action  (SL2Z) (integral_matrices_with_determinant m):=

{ smul := SL2Z_M (m : ℤ),
  one_smul := one_smull (m: ℤ ),
  mul_smul := mul_smull (m:ℤ ) }





/-instance (m: ℤ):  mul_action SL2Z_M m :=
{ mul := λ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩,
    by ext; simp [SL2Z_M, add_mul, mul_add, mul_assoc],
  one := λ ⟨_, _, _, _, _⟩, by ext; simp [SL2Z_M], }-/

section


variables  (A : SL2Z) (M : integral_matrices_with_determinant m)

@[simp, SL2Z] lemma smul_is_mul (A : SL2Z) (M : integral_matrices_with_determinant m): (A • M).1 =A * M :=
begin
simp [SL2Z_M],
refl,
end  

lemma m_a_b (m : ℤ) (hm : m ≠ 0) (A : SL2Z) (M N : integral_matrices_with_determinant m):   (A • M) = N ↔  N 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 ∧ N 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 ∧ N 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 ∧ N 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1:=

begin
split,
intro h,
simp [mul_action] at h,
sorry, sorry,

end  

@[simp, SL2Z] lemma SL2Z_M_a : (SL2Z_M m A M).1 0 0 = A.1 0 0 * M.1 0 0 + A.1 0 1 * M.1 1 0 :=

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end   


@[simp, SL2Z] lemma SL2Z_M_aa: (A • M) 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 :=

begin
apply SL2Z_M_a,
end 



@[simp, SL2Z] lemma SL2Z_M_b : (SL2Z_M m A M).1 0 1 = A.1 0 0 * M.1 0 1 + A.1 0 1 * M.1 1 1 := 

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end


@[simp, SL2Z] lemma SL2Z_M_ba: (A • M) 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 :=

begin
apply SL2Z_M_b,
end 






@[simp, SL2Z] lemma SL2Z_M_c : (SL2Z_M m A M).1 1 0 = A.1 1 0 * M.1 0 0 + A.1 1 1  * M.1 1 0 :=

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end  

@[simp, SL2Z] lemma SL2Z_M_ca: (A • M) 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 :=

begin
apply SL2Z_M_c,
end 


@[simp, SL2Z] lemma SL2Z_M_d : (SL2Z_M m A M).1 1 1 = A.1 1 0 * M.1 0 1 + A.1 1 1 * M.1 1 1 := 

begin
simp [SL2Z_M, add_mul, mul_add, mul_assoc],
rw mul_apply,
rw finset.sum_fin_eq_sum_range,
rw sum_range_succ,
rw sum_range_succ,
simp,
end


@[simp, SL2Z] lemma SL2Z_M_da: (A • M) 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1 :=

begin
apply SL2Z_M_d,
end   




namespace integral_matrices_with_determinant 
 
variables  ( B : integral_matrices_with_determinant m)

def mi (m: ℤ) (M: integral_matrices_with_determinant m) : (matrix (fin 2) (fin 2) ℤ) := ![![-M 0 0,  - M 0 1], ![-M 1 0 , -M 1 1]] 
 


lemma fff (m: ℤ) (M: integral_matrices_with_determinant m): (mi m M).det = m:=

begin
rw mi,
sorry,
end   


def MATINV (m : ℤ) : integral_matrices_with_determinant m → integral_matrices_with_determinant m :=
λ A , ⟨mi m  A, by apply fff⟩

instance (m : ℤ) : has_neg (integral_matrices_with_determinant m) :=
⟨λ A, MATINV m A ⟩



@[simp, SL2Z] lemma neg_a : (-B) 0 0 = -B 0 0 := rfl
@[simp, SL2Z] lemma neg_b : (-B) 0 1 = -B 0 1 := rfl
@[simp, SL2Z] lemma neg_c : (-B) 1 0 = -B 1 0  := rfl
@[simp, SL2Z] lemma neg_d : (-B) 1 1 = -B 1 1 := rfl
@[simp, SL2Z] protected lemma neg_neg : -(-B) = B := sorry

end integral_matrices_with_determinant



namespace SL2Z

variables (C D : SL2Z)


def mis (M: SL2Z) : (matrix (fin 2) (fin 2) ℤ) := ![![-M 0 0,  - M 0 1], ![-M 1 0 , -M 1 1]] 
 


lemma fffs (M: SL2Z): (mis M).det = 1:=

begin
rw mis,
sorry,
end   

def MATINVs  : SL2Z → SL2Z :=
λ A , ⟨mis  A, by apply fffs⟩

instance  : has_neg (SL2Z) :=
⟨λ A, MATINVs  A ⟩

@[simp, SL2Z] protected lemma neg_one_mul : -1 * C = -C := sorry 
@[simp, SL2Z] protected lemma neg_mul_neg : -C * -D = C * D := sorry
@[simp, SL2Z] protected lemma neg_mul : -(C * D) = -C * D := sorry
@[simp, SL2Z] protected lemma neg_neg : -(-C) = C := sorry 

end SL2Z