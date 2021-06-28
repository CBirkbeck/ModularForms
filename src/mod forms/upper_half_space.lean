import data.complex.basic
import tactic.ring
import tactic.tidy
import .modular_group
import .GLnR
import .SL2Z_generators
import tactic.linarith
import linear_algebra.determinant
import group_theory.group_action

open complex
 
/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/ 
noncomputable theory

def upper_half_space := {z : ℂ | z.im > 0}
local notation `ℍ` := upper_half_space
local notation `Mat` := integral_matrices_with_determinant

instance upper_half_space.to_complex : has_coe ℍ ℂ := ⟨λ z, z.val⟩

instance nat.to_fintype : has_coe ℕ Type := ⟨λ n, fin n⟩

section

open matrix


/-What follow are some basic messy lemmas  -/
lemma H_mem (z : ℂ): z ∈ ℍ ↔ 0< z.im:=iff.rfl



lemma a1 (a b c d e f g h: ℂ) : a*((b+d)/c)=((a*b+a*d)/c):=

begin
ring,
end 


@[simp]lemma a2 (a b c d : ℂ) : (a/b)/(c/d)=(a*d)/(b*c):=
begin
exact div_div_div_div_eq a,
end





lemma a3 (a b c d e f: ℂ ) (h1: c ≠ 0): (a*(b/c)+d)/(e*(b/c)+f)=(a*b+d*c)/(e*b+f*c):=

begin
calc (a*(b/c)+d)/(e*(b/c)+f)=(a*(b/c)+d)*(e*(b/c)+f)⁻¹ : by ring
     ...=(a*(b*c⁻¹)+d)*(e*(b*c⁻¹)+f)⁻¹  : by ring
     ...=(a*b*c⁻¹+d)*(e*(b*c⁻¹)+f)⁻¹  : by rw ← mul_assoc
     ...=(a*b*c⁻¹+d)*(e*b*c⁻¹+f)⁻¹ : by rw ← mul_assoc
     ...=((a*b)*c⁻¹+d)*(e*b*c⁻¹+f)⁻¹ : by rw mul_assoc
     ...= ((a*b)*c⁻¹+d)*((e*b)*c⁻¹+f)⁻¹ : by rw mul_assoc
     ...=((a*b)/c+d)*((e*b)*c⁻¹+f)⁻¹ : by rw  div_eq_mul_inv
     ...=((a*b)/c+d)*((e*b)/c+f)⁻¹  : by ring 
     ...=((a*b+d*c)/c)*((e*b)/c+f)⁻¹ : by rw [div_add' (a*b) d c h1]
     ...=((a*b+d*c)/c)*((e*b+f*c)/c)⁻¹ : by rw [div_add' (e*b) f c h1]
     ...=((a*b+d*c)/c)/((e*b+f*c)/c) : by ring
     ...=((a*b+d*c)*c)/(c*(e*b+f*c)) : by rw [a2 (a*b+d*c) c (e*b+f*c) c ]
     ...=((a*b+d*c)*c)*(c*(e*b+f*c))⁻¹ : by ring
     ...=((a*b+d*c)*c)*(c⁻¹ *(e*b+f*c)⁻¹): by rw mul_inv' 
     ...=(a*b+d*c)*c*c⁻¹ *(e*b+f*c)⁻¹ : by  ring 
      ...=(a*b+d*c)*(c*c⁻¹) *(e*b+f*c)⁻¹ : by  ring 
     ...=(a*b+d*c)*1*(e*b+f*c)⁻¹  : by rw [mul_inv_cancel h1]
    ...=(a*b+d*c)*(e*b+f*c)⁻¹  : by ring
     ...=(a*b+d*c)/(e*b+f*c)  : by  rw  div_eq_mul_inv,
end  

lemma a4 (a b c d e f h : ℂ )  : a*(b*(c+d)+e*(f+h))⁻¹ =a*(b*c+b*d+e*f+e*h)⁻¹:=

begin
have h1:  b*(c+d)+e*(f+h)= b*c+b*d+e*f+e*h, by {ring},
rw h1,
end   

lemma a5 (a b c d e f h t r : ℂ )  : a/(b*(c*d)+t+e*(f*h)+r) =a/(b*c*d + e*f*h+t+r):=

begin
have h1: b*(c*d)+t+e*(f*h)+r=b*c*d + e*f*h+t+r, by {ring},
rw h1,
end   


lemma a6 (a b c z d d2 r s: ℂ) : a/(b*r*z+c*s*z+d+d2)=a/((b*r+c*s)*z+d+d2):=

begin
have h1: b*r*z+c*s*z+d+d2=(b*r+c*s)*z+d+d2, by {ring},
rw h1,
end   

lemma a7 (a b z c f d h :ℂ): a/(b*z+c*f+d*h)=a/(b*z+(c*f+d*h)):=

begin
have h1: b*z+c*f+d*h=b*z+(c*f+d*h), by {ring},
rw h1,
end  

lemma alg (a b c d e f g h : ℂ ) (z : ℂ) (h1: ¬ g*z+h = 0)   : (a*((e*z+f)/(g*z+h) )+b)/ (c*((e*z+f)/(g*z+h))+d)=((a*e+b*g)*z+(a*f+b*h))/((c*e+d*g)*z+(c*f+d*h)):=

begin

calc (a*((e*z+f)/(g*z+h) )+b)/ (c*((e*z+f)/(g*z+h))+d) = (a*(e*z+f)+b*(g*z+h))/ (c*(e*z+f)+d*(g*z+h))       : by rw  [a3 a (e*z+f) (g*z+h) b c d h1]
                                       ... = (a*(e*z+f)+b*(g*z+h))* (c*(e*z+f)+d*(g*z+h))⁻¹ : by  rw  div_eq_mul_inv
                                       ...= (a*(e*z)+a*f+b*(g*z)+b*h)* (c*(e*z+f)+d*(g*z+h))⁻¹ : by ring 
                                       ...= (a*(e*z)+a*f+b*(g*z)+b*h)*  (c*((e*z)+f)+d*((g*z)+h))⁻¹ : by ring 
                                        ...= (a*(e*z)+a*f+b*(g*z)+b*h)* (c*(e*z)+c*f+d*(g*z)+d*h)⁻¹  : by rw [a4 (a*(e*z)+a*f+b*(g*z)+b*h) c (e*z) f d (g*z) h]
                                        ...= (a*e*z+a*f+b*g*z+b*h)* (c*(e*z)+c*f+d*(g*z)+d*h)⁻¹  : by ring
                                       ...=((a*e+b*g)*z+a*f+b*h)*(c*(e*z)+c*f+d*(g*z)+d*h)⁻¹  : by ring 
                                       ...=((a*e+b*g)*z+a*f+b*h)/ (c*(e*z)+c*f+d*(g*z)+d*h) : by rw  div_eq_mul_inv
                                       ...=((a*e+b*g)*z+a*f+b*h)/(c*e*z+d*g*z+(c*f)+(d*h)) : by rw [a5 ((a*e+b*g)*z+a*f+b*h) c e z d g z (c*f) (d*h)] 
                                       ...=((a*e+b*g)*z+a*f+b*h)/ ((c*e+d*g)*z+c*f+d*h) : by rw [a6 ((a*e+b*g)*z+a*f+b*h) c d z (c*f) (d*h) e g ]
                                      ...=((a*e+b*g)*z+(a*f+b*h))/ ((c*e+d*g)*z+c*f+d*h) : by rw add_assoc
                                      ...=((a*e+b*g)*z+(a*f+b*h))/ ((c*e+d*g)*z+(c*f+d*h)) : by rw [a7 ((a*e+b*g)*z+(a*f+b*h)) (c*e+d*g) z c f d h],
end

/- definition of what will end up being the action of matrices on the upper half space -/

def mat2_complex (M: GLn (fin 2) ℝ) (z : ℂ) : ℂ :=
(M.1 0 0 * z + M.1 0 1) / (M.1 1 0 * z + M.1 1 1)


/- this lemma will be used later to prove we have an action-/


lemma mul_smul'  (A B : GLn (fin 2) ℝ) (z : ℂ) (h:  ¬ (↑(B.1 1 0) * z + ↑(B.1 1 1)) = 0 ) :  mat2_complex (A * B) z = mat2_complex A (mat2_complex B z):=

begin  
simp only [mat2_complex],
have:= GLn.mat_mul_real A B,  simp only [GLn.valor] at this, simp only [this],
have:= alg   ↑(A.1 0 0)  (A.1 0 1) (A.1 1 0) (A.1 1 1) (B.1 0 0) (B.1 0 1) (B.1 1 0) (B.1 1 1) z h,  
simp at this, simp, rw this, 
end   

/- I dont know why this is a theorem and not a lemma-/
theorem preserve_ℍ.aux (A: GLn (fin 2) ℝ ) (det : det A.1 > 0) (z : ℂ) (hz : z ∈ ℍ) :
  ↑ (A.1 1 0) * z + A.1 1 1 ≠ 0 :=
begin
  intro H,
  have H1 : A.1 1 0 = 0 ∨ z.im = 0, by simpa using congr_arg complex.im H,
  cases H1,
  { simp [H1, of_real_zero] at H, rw GLn.det_of_22 A.1 at det, 
    simp [H, H1] at det,exact det,},
  change z.im > 0 at hz,
  linarith,
end


lemma preserve_ℍ (A: GLn (fin 2) ℝ ) (det : det A.1 > 0) (z : ℂ) (h : z.im > 0) :
(mat2_complex A z).im > 0 :=

begin
  have det': A.1.det > 0, by {apply det,},
   rw GLn.det_of_22 A.1 at det,
have h2: (mat2_complex A z).im = (A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0) * z.im * (norm_sq (↑ (A.1 1 0) * z + ↑ (A.1 1 1)))⁻¹ ,
 by {simp [mat2_complex, div_eq_mul_inv, -add_comm], dsimp [norm_sq], simp, ring_nf,}, 
 have h3: (A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0) * z.im >0 , by {apply mul_pos det h,  },
 have h4: 0 < norm_sq (↑ (A.1 1 0) * z + ↑ (A.1 1 1)) , by{apply norm_sq_pos.2 (preserve_ℍ.aux A  det' z h), },
 have h5: 0< (norm_sq (↑ (A.1 1 0) * z + ↑ (A.1 1 1)))⁻¹ , by {simp, simp at h4, exact h4, }, rw h2, apply mul_pos h3 h5,

 
end 

theorem GL2R_H.aux (A:  GLn (fin 2) ℝ) (h : det A > 0) : (A.1 0 0) * A.1 1 1 - A.1 0 1 * A.1 1 0 > 0 :=
begin
rw [GLn.det_of_22] at h, simp at h, simp only [gt_iff_lt, sub_pos, subtype.val_eq_coe], exact h,
end  


/-more basic matrix lemmas due to me being crap at lean-/

lemma one_meme: det (1:GLn (fin 2) ℝ ) > 0:=
begin
simp only [det_one, gt_iff_lt, GLn.one_apply], norm_cast, exact dec_trivial, 
end 

lemma mul_meme (A B :GLn (fin 2) ℝ ) (h1: det A >0 ) (h2: det B >0): det (A*B)>0:=

begin
simp only [gt_iff_lt, det_mul, mul_eq_mul], apply mul_pos h1 h2,
end

lemma stupd (A: GLn (fin 2) ℝ ) : det A = A.1.det:=
begin
simp only [subtype.val_eq_coe], refl,
end  

lemma det_in (A: GLn (fin 2) ℝ) : A.1.det * (A.1.det)⁻¹=1:=

begin
simp only [subtype.val_eq_coe], 
have h1: A.1.det ≠ 0, {have:=A.2, simp only [subtype.val_eq_coe] at this, rw is_unit_iff_exists_inv at this, by_contradiction, simp only [not_not, subtype.val_eq_coe] at h,
 rw h at this, simp only [zero_mul, exists_false, zero_ne_one] at this, exact this },
simp only [ne.def, subtype.val_eq_coe] at h1, apply mul_inv_cancel h1, 

end  


lemma det_ive2 (A B : GLn (fin 2) ℝ ) (h: det A * det B =1) : det A= (det B)⁻¹ :=

begin
simp only [stupd, subtype.val_eq_coe],simp only [stupd, subtype.val_eq_coe] at h, have h1: A.1.det * B.1.det* (B.1.det)⁻¹ = 1 * (B.1.det)⁻¹, simp, rw h, simp only [one_mul], simp only [one_mul, subtype.val_eq_coe] at h1, rw ←  h1, rw mul_assoc, simp only, have:=det_in B, 
simp only [subtype.val_eq_coe] at this, rw this, simp only [mul_one],
end  


lemma det_inv (A: GLn (fin 2) ℝ )  (h: det A >0) : (det A)⁻¹ = det (A⁻¹):=

begin
have h1: is_unit(det A), by {have:= inv_pos.2 h, rw is_unit_iff_exists_inv, use (det A)⁻¹, rw mul_inv_cancel, simp only [ne.def], 
intro hh, rw hh at h, simp only [lt_self_iff_false, gt_iff_lt] at h, exact h,},
have:= nonsing_inv_det A.1 h1,simp only [subtype.val_eq_coe] at this, rw stupd, 
have h5: A.nonsing_inve= (↑A)⁻¹, {apply GLn.inv_is_inv,},
have h3: (A.1.det)⁻¹ = (A.1⁻¹).det, {simp only [subtype.val_eq_coe], have:= det_ive2 A⁻¹ A this, simp only [stupd, GLn.inv_apply, subtype.val_eq_coe] at this, 
rw ← this, dsimp, rw h5}, rw h3, refl,


end  

lemma inv_meme (A:GLn (fin 2) ℝ ) (h: det A >0): det A⁻¹ >0:=

begin 
have h2: (det A)⁻¹ = det (A⁻¹), by {apply det_inv A h,},
 rw ← h2, apply inv_pos.2 h,
end  


/-- This is the subgroup of 2x2 matrices with real entries and positive determinant-/
def GL2R_pos : subgroup  (GLn (fin 2) ℝ) :=
{carrier:={M  | det M > 0},
 one_mem':=one_meme,
 mul_mem':=λ A B h1 h2, mul_meme A B h1 h2,
 inv_mem':=λ A h1, inv_meme A h1,
}

@[simp] lemma mem_GL2R_pos (A:GLn (fin 2) ℝ ) :
  A  ∈ GL2R_pos ↔ A.1.det > 0 := iff.rfl



/- basic map from matrix over Z to matrix over R and some lemmas-/

def mat_Z_to_R (A:matrix (fin 2) (fin 2) ℤ ) :matrix (fin 2) (fin 2) ℝ :=
![![A 0 0, A 0 1], ![A 1 0 , A 1 1]]



lemma SL_det_inv (A : SL2Z): is_unit (A.1.det : ℝ) :=

begin
have:=A.2, rw this, cases A, dsimp at *, simp at *,
end  

lemma SL_det_pos (A : SL2Z): (A.1.det: ℝ) > 0:=

begin
have:=A.2, rw this, cases A, dsimp at *, simp at *, norm_cast, exact dec_trivial,
end  

lemma nonzero_inv (a: ℝ) (h: 0 < a): is_unit (a):=

begin
have h2: a ≠ 0, {simp only [ne.def], by_contradiction h1, rw h1 at h, simp only [lt_self_iff_false] at h, exact h},
rw  is_unit_iff_exists_inv, use a⁻¹, apply mul_inv_cancel h2, 
end

instance Z_to_R: has_coe (matrix (fin 2) (fin 2) ℤ) (matrix (fin 2) (fin 2) ℝ ) :=⟨λ A, mat_Z_to_R A⟩ 

lemma det_coes (A: matrix (fin 2) (fin 2) ℤ ): det (A : matrix (fin 2) (fin 2) ℝ )= ((A.det): ℝ):=
begin
rw MND, rw GLn.det_of_22, simp only [int.cast_mul, int.cast_sub], refl,
end  

instance SL_to_GL: has_coe SL2Z (GLn (fin 2) ℝ):= ⟨λ A, ⟨ A.1, by {have:= SL_det_pos A,   have:= nonzero_inv (A.1.det: ℝ ) this, 
simp at this, simp [det_coes], exact this}⟩ ⟩ 

lemma SL_det_pos' (A : SL2Z): (A : GLn (fin 2) ℝ).1.det > 0:=

begin
have:=A.2, simp only [gt_iff_lt, subtype.val_eq_coe], simp only [subtype.val_eq_coe] at this, have h2:= det_coes (A.1), 
simp only [subtype.val_eq_coe] at h2, rw this at h2, rw ← coe_coe at h2, rw ← coe_coe, rw h2, 
cases A, dsimp at *, simp at *, norm_cast, exact dec_trivial,
end  

instance SL_to_GL_pos: has_coe SL2Z (GL2R_pos):= ⟨λ A, ⟨ (A: GLn (fin 2) ℝ), by {have:= SL_det_pos' A,
 simp only [gt_iff_lt, mem_GL2R_pos, subtype.val_eq_coe], simp only [gt_iff_lt, subtype.val_eq_coe] at this, 
rw ← coe_coe, exact this  }⟩ ⟩ 

instance GL2R_pos_to_GL2R : has_coe (GL2R_pos)  (GLn (fin 2) ℝ) := ⟨λ A, A.val⟩ 





/-- This is the Moebius action on the upper half plane, defined as follows: Given a `2 × 2`matrix `M=![![a, b], ![c, d]]` 
with positive determinant, it sends `z ∈ ℍ` to `(a*z+b)/(c*z+d)` -/
def moeb:  (GL2R_pos) → ℍ → ℍ :=
λ M z, ⟨mat2_complex M z, preserve_ℍ M.1 M.2 z z.property⟩




lemma one_smul''  : ∀ (z : ℍ  ),  moeb (1: GL2R_pos) z= z :=

begin
 intro z, 
simp only [moeb], simp only [mat2_complex, nat.one_ne_zero, add_zero, one_mul, of_real_zero, fin.one_eq_zero_iff, GLn.one_val, zero_mul,
  fin.zero_eq_one_iff, one_apply_eq, ne.def, zero_add, not_false_iff, subtype.coe_eta, of_real_one, div_one,
  subgroup.coe_one, subtype.val_eq_coe, one_apply_ne],
end

variable (v: ℍ)



lemma mul_smul''  (A B : GL2R_pos) (z : ℍ)  :  moeb (A * B) z = moeb A (moeb B z):=

begin 
have h:  ¬ (↑(B.1 1 0) * z.1 + ↑(B.1 1 1)) = 0, have:= preserve_ℍ.aux B B.2 z.1 z.2, simp only [ne.def, subtype.val_eq_coe] at this, exact this, 
simp only [moeb, subtype.mk_eq_mk, subgroup.coe_mul, subtype.coe_mk],   apply mul_smul' A B z.1 h, 
end   


/-finally, here is the action of GL_2R^+ on the H-/

instance : mul_action (GL2R_pos) (ℍ) :=
{ smul:= moeb,
  one_smul := one_smul'',
  mul_smul :=  mul_smul''}




end   