import tactic.ring
import tactic.pi_instances
import .holomorphic_functions
import linear_algebra.determinant
import .modular_group
import .GLnR
import .modular_forms
import ring_theory.coprime
import ring_theory.int.basic
import .upper_half_space
import data.matrix.notation

universes u v w

open complex

open_locale big_operators

local notation `ℍ` := upper_half_space
noncomputable theory
/-

def Ind:={x : ℤ × ℤ | x ≠ (0,0)}

@[simp]lemma Ind_mem (x: ℤ × ℤ): x ∈ Ind ↔ x ≠ (0,0):=iff.rfl 

--gcd_eq_zero_iff






--intro h2, have h2: gcd z1 z2 =0, by {have hh:= int.gcd_eq_gcd_ab z1 z2, convert hh,  sorry,},  rw gcd_eq_zero_iff at h2, exact h2,


lemma ridic (a b c d : ℤ): a*d-b*c=1 → a*d-c*b=1:=
begin
intro h, linarith,
end

lemma SL2z_entries_coprime (A: SL2Z): is_coprime (A.1 0 0) (A.1 1 0):=
begin
rw is_coprime, have h1:= det_onne A,  simp only [vale] at h1, use (A.1 1 1), use (-A.1 0 1), simp, simp at h1, ring_nf,
cases A, dsimp at *, simp at *, ring_nf, assumption,  
end

lemma r0 (a b z1 z2 x : ℤ) (h: z1*a+z2*b=0): z1*a*x+z2*b*x=0:=

begin
have h1: z1*a*x+z2*b*x=(z1*a+z2*b)*x, by {ring,}, rw h1, rw h, simp only [zero_mul],
end  

lemma r1 (a b c d z1 z2 : ℤ) (h1: a*d-c*b=1) (h2:z1*a*d+z2*c*d=0) (h3: z1*b*c+z2*d*c=0 ): z1=0:=
begin
rw ← h2 at h3, have h0: z2*d*c=z2*c*d, by {ring,}, rw h0 at h3, simp at h3, have h4: z1 * a*d-z1*b*c =0 , by {rw h3, simp,},
have h5:  z1 * (a * d -  b * c) = z1*a*d-z1*b*c, by { ring, }, rw h4 at h5, have h6: a*d-b*c=a*d-c*b, by {ring,}, rw h6 at h5, 
rw h1 at h5, simp at h5, exact h5,
end

lemma r2 (a b c d z1 z2 : ℤ) (h1: a*d-c*b=1) (h2:z1*a*b+z2*c*b=0) (h3: z1*b*a+z2*d*a=0 ): z2=0:=

begin
rw add_comm at h2, rw add_comm at h3, have h0: z1*b*a=z1*a*b, by {ring}, rw h0 at h3, rw ← h2 at h3, simp at h3, 
have h4: z2 * d*a-z2*c*b =0 , by {rw h3, simp,}, have h5:  z2 * (d * a -  c * b) = z2*d*a-z2*c*b, by {ring,}, rw h4 at h5,
have h6: a*d-c*b=d*a-c*b, by {ring}, rw  ← h6 at h5, rw h1 at h5, simp at h5, exact h5, 
end  

def Ind_perm' (A : SL2Z ): Ind →  Ind:=
λ z, ⟨(z.1.1* (A.1 0 0) +z.1.2* (A.1 1 0), z.1.1*(A.1 0 1)+z.1.2* (A.1 1 1)), by {simp only [Ind_mem, not_and, prod.mk.inj_iff, ne.def, subtype.val_eq_coe],
have h1:=z.property, simp at *, have h2:= det_onne A, simp [vale] at *, intros H1 H2, rw ← subtype.val_eq_coe at h2, 
have ha: z.val.fst * A.val 0 0 * A.val 1 1+ z.val.snd * A.val 1 0 * A.val 1 1 = 0:= by {apply r0, simp only [subtype.val_eq_coe], exact H1,},
have hb: z.val.fst * A.val 0 1 * A.val 1 0+ z.val.snd * A.val 1 1 * A.val 1 0 = 0:= by {apply r0, simp, exact H2,},
have hab: z.val.fst =0:= by {apply r1 (A.val 0 0) (A.val 0 1) (A.val 1 0) (A.val 1 1) z.val.fst z.val.snd  h2  ha hb,},
have ha': z.val.fst * A.val 0 0 * A.val 0 1+ z.val.snd * A.val 1 0 * A.val 0 1 = 0:= by {apply r0, simp, exact H1,},
have hb': z.val.fst * A.val 0 1 * A.val 0 0+ z.val.snd * A.val 1 1 * A.val 0 0 = 0:= by {apply r0, simp, exact H2,},
have hab: z.val.snd =0:= by {apply r2 (A.val 0 0) (A.val 0 1) (A.val 1 0) (A.val 1 1) z.val.fst z.val.snd  h2  ha' hb',},
cases z, cases A, cases z_val, dsimp at *, simp at *, solve_by_elim,
},⟩




lemma Ind_equiv' (A : SL2Z): Ind ≃ Ind:={
to_fun:=Ind_perm' A,
inv_fun:=Ind_perm' A⁻¹,
left_inv:=λ z, by {rw Ind_perm', rw Ind_perm', 
have ha:= SL2Z_inv_a A, simp only [vale] at ha, 
have hb:= SL2Z_inv_b A, simp only [vale] at hb, 
have hc:= SL2Z_inv_c A, simp only [vale] at hc, 
have hd:= SL2Z_inv_d A, simp only [vale] at hd, 
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf, rw mul_comm at hdet, simp only [hdet], 
have ht: A.val 1 1 * A.val 1 0 - A.val 1 0 * A.val 1 1=0, by {ring, }, simp only [ht], 
have ht2: -(A.val 0 1 * A.val 0 0) + A.val 0 0 * A.val 0 1=0, by {ring,}, simp only [ht2],
have ht3: -(A.val 0 1 * A.val 1 0) + A.val 0 0 * A.val 1 1 =1, by {rw add_comm,  rw mul_comm at hdet, simp, 
simp at *, ring_nf, rw ridic, exact hdet, }, simp only [ht3], ring_nf,
 cases z, cases A, cases z_val, dsimp at *, simp at *,},
right_inv:= λ z, by { rw Ind_perm', rw Ind_perm', 
have ha:= SL2Z_inv_a A, simp only [vale] at ha, 
have hb:= SL2Z_inv_b A, simp only [vale] at hb, 
have hc:= SL2Z_inv_c A, simp only [vale] at hc, 
have hd:= SL2Z_inv_d A, simp only [vale] at hd, 
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf, 
have hz1:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.val.fst hdet, simp only [hz1], 
have hz2:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.val.snd hdet, simp only [hz2], 
cases z, cases A, cases z_val, dsimp at *, simp at *, } ,
}







def Eis' (k: ℤ) (z : ℍ) : Ind →  ℂ:=
λ x, 1/(x.1.1*z+x.1.2)^k  


lemma Eis'_moeb (k: ℤ) (z : ℍ) (A : SL2Z) (i : Ind): Eis' k (moeb A z) i=  ((A.1 1 0*z+A.1 1 1)^k)*(Eis' k z (Ind_equiv' A i ) ):=

begin
rw Eis', rw Eis', rw moeb, simp, rw mat2_complex, simp, dsimp, sorry,
end  



def Eisenstein_series_weight_' (k: ℤ) : ℍ → ℂ:=
 λ z, ∑' (x : Ind), (Eis' k z x) 




lemma Eis_is_summable (A: SL2Z) (k : ℤ) (z : ℍ) : summable (Eis' k z) :=

begin
--rw summable, use (0: ℂ), rw has_sum, rw Eis', simp, sorry, 
--rw summable_iff_cauchy_seq_finset, rw cauchy_seq,


sorry,
end  


lemma Eis_is_summable' (A: SL2Z) (k : ℤ) (z : ℍ) : summable (Eis' k z ∘⇑(Ind_equiv' A)) :=
begin
rw equiv.summable_iff (Ind_equiv' A), exact Eis_is_summable A k z,

end


lemma Eis_is_Pet (k: ℤ):  (Eisenstein_series_weight_' k) ∈ is_Petersson_weight_ k :=

begin
rw is_Petersson_weight_, rw Eisenstein_series_weight_', simp only [set.mem_set_of_eq], 
intros A z, have h1:= Eis'_moeb k z A,  have h2:=tsum_congr h1, convert h2, simp only [subtype.val_eq_coe], 
have h3:=equiv.tsum_eq (Ind_equiv' A) (Eis' k z), 
have h5:= summable.tsum_mul_left ((((A.1 1 0): ℂ) * z + ((A.1 1 1): ℂ)) ^ k) (Eis_is_summable' A k z),
 simp only [prod.forall, function.comp_app, set_coe.forall, subtype.val_eq_coe] at *,  
 rw ← h3, simp only [vale, subtype.val_eq_coe], convert h5, rw h5,
end
-/


/-! ### Eisenstein series -/

namespace Eisenstein_series


lemma ridic (a b c d : ℤ): a*d-b*c=1 → a*d-c*b=1:=
begin
intro h, linarith,
end


lemma ridic2 (a b c d z : ℤ) (h: a*d-b*c=1):  z*d*a-z*c*b=z:=
begin
ring_nf, rw h, rw one_mul,
end





def Ind_perm (A : SL2Z ): ℤ × ℤ →  ℤ × ℤ:=
λ z, (z.1* (A.1 0 0) +z.2* (A.1 1 0), z.1*(A.1 0 1)+z.2* (A.1 1 1))



def Ind_equiv (A : SL2Z): ℤ × ℤ ≃ ℤ × ℤ:={
to_fun:=Ind_perm A,
inv_fun:=Ind_perm A⁻¹,
left_inv:=λ z, by {rw Ind_perm, rw Ind_perm, 
have ha:= SL2Z_inv_a A, simp only [vale] at ha, 
have hb:= SL2Z_inv_b A, simp only [vale] at hb, 
have hc:= SL2Z_inv_c A, simp only [vale] at hc, 
have hd:= SL2Z_inv_d A, simp only [vale] at hd, 
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf, rw mul_comm at hdet, simp only [hdet], 
have ht: A.val 1 1 * A.val 1 0 - A.val 1 0 * A.val 1 1=0, by {ring, }, simp only [ht], 
have ht2: -(A.val 0 1 * A.val 0 0) + A.val 0 0 * A.val 0 1=0, by {ring,}, simp only [ht2],
have ht3: -(A.val 0 1 * A.val 1 0) + A.val 0 0 * A.val 1 1 =1, by {rw add_comm,  rw mul_comm at hdet, simp, 
simp at *, ring_nf, rw ridic, exact hdet, }, simp only [ht3], ring_nf, simp only [prod.mk.eta, add_zero, zero_mul, zero_add], },
right_inv:= λ z, by { rw Ind_perm, rw Ind_perm, 
have ha:= SL2Z_inv_a A, simp only [vale] at ha, 
have hb:= SL2Z_inv_b A, simp only [vale] at hb, 
have hc:= SL2Z_inv_c A, simp only [vale] at hc, 
have hd:= SL2Z_inv_d A, simp only [vale] at hd, 
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf, 
have hz1:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.fst hdet, simp only [hz1], 
have hz2:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.snd hdet, simp only [hz2], simp only [prod.mk.eta],} ,
}



@[simp]lemma ind_simp (A: SL2Z) (z : ℤ × ℤ): Ind_equiv A z=(z.1* (A.1 0 0) +z.2* (A.1 1 0), z.1*(A.1 0 1)+z.2* (A.1 1 1)):=
begin
refl, 
end



/- Note that here we are using that 1/0=0, so there is nothing wrong with this defn or the resulting sum-/

def Eise (k: ℤ) (z : ℍ) : ℤ × ℤ →  ℂ:=
λ x, 1/(x.1*z+x.2)^k  

lemma wa (a b c: ℂ) (h: a ≠ 0) :  b=c → a*b⁻¹=a*c⁻¹ :=
begin
simp [h], 
end 



lemma calc_lem (k: ℤ) (a b c d i1 i2: ℂ) (z : ℍ) (h: c*z+d ≠ 0) : ((i1* ((a*z+b)/(c*z+d))+i2)^k)⁻¹=(c*z+d)^k* (  ((i1 * a + i2 * c) * z + (i1 * b + i2 * d))^k   )⁻¹:=
begin
have h1: i1*((a*z+b)/(c*z+d))+i2=(i1*(a*z+b)/(c*z+d)+i2), by {ring  }, rw h1,
have h2:  (i1*(a*z+b)/(c*z+d)+i2)=((i1*(a*z+b))/(c*z+d)+i2), by {ring}, rw h2,
have h3:=div_add' (i1*(a*z+b)) i2 (c*z+d) h, rw h3, simp [inv_pow], rw div_eq_inv_mul, 
have h4: (((c * ↑z + d) ^ k)⁻¹ * (i1 * (a * ↑z + b) + i2 * (c * ↑z + d)) ^ k)⁻¹ =(c * ↑z + d) ^ k * ((i1 * (a * ↑z + b) + i2 * (c * ↑z + d)) ^ k)⁻¹, by {rw ← div_eq_inv_mul, rw inv_div, rw div_eq_inv_mul, ring,},
rw h4, have h5: (c*z+d)^k ≠ 0, by {apply fpow_ne_zero _ h,  }, have:=mul_left_cancel'  h5 ,apply wa _ _ _ h5, ring_nf, tauto, tauto,
end



@[simp]lemma mat_val (A: SL2Z) (i j : fin 2): (mat_Z_to_R A.1) i j = (A.1 i j : ℝ):=

begin
rw mat_Z_to_R, fin_cases i; fin_cases j, simp only [matrix.cons_val_zero], 
simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero],
simp only [matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero],
simp only [matrix.head_cons, matrix.cons_val_one],

end  


lemma coe_chain (A: SL2Z) (i j : fin (2)): (A.1 i j : ℂ)= ((A.1 : (matrix (fin 2) (fin 2) ℝ) ) i j : ℂ):=
begin

simp, rw ← coe_coe, cases j, cases i, cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
 work_on_goal 0 { dsimp at *, simp at *, unfold_coes },  
work_on_goal 1 { dsimp at *, simp at * }, have h1:= mat_val ⟨A_val, A_property⟩ , rw h1, simp, refl,

end  



lemma Eise_moeb (k: ℤ) (z : ℍ) (A : SL2Z) (i : ℤ × ℤ ): Eise k (moeb A z) i=  ((A.1 1 0*z+A.1 1 1)^k)*(Eise k z (Ind_equiv A i ) ):=

begin
rw Eise, rw Eise, rw moeb, simp, rw mat2_complex, simp, dsimp, rw ← coe_coe, rw ← coe_coe, rw calc_lem, have h1:= coe_chain A, simp at h1, rw h1, rw h1, rw h1, rw h1, rw ← coe_coe, 
have hh:= preserve_ℍ.aux A, apply hh, have:=A.2,  have h2:= SL_det_pos' A, exact h2,simp only [subtype.coe_prop], 
end  


/--This defines the Eisenstein series of weight k and level one. At the moment there is no restriction on the weight, but in order to make it an actual
modular form some constrainst will be needed -/
def Eisenstein_series_weight_ (k: ℤ) : ℍ → ℂ:=
 λ z, ∑' (x : ℤ × ℤ), (Eise k z x) 


def square (n: ℕ):= { x: ℤ × ℤ | max (x.1).nat_abs (x.2).nat_abs=n}  

@[simp]lemma square_mem' (n: ℕ) (x : ℤ × ℤ):x ∈ square n ↔ max (x.1).nat_abs (x.2).nat_abs=n:=iff.rfl 

lemma max_aux' (a b : ℕ): max a b = a ∨ max a b =b:=
begin
apply max_choice,
end  

lemma max_aux (a b : ℕ):a= max a b  ∨  b=max a b :=
begin
have:= (max_aux' a b),  cases this, work_on_goal 0 { simp at * }, work_on_goal 1 { simp at * }, 
have h1: max a b = a, apply max_eq_left this, rw h1, simp only [true_or, eq_self_iff_true],rw max_comm, 
have h2: max b a=b, apply max_eq_left this, rw h2, simp only [eq_self_iff_true, or_true],
end  

lemma square_is_fin (n: ℕ): fintype (square n):=
begin
sorry,
end


lemma square_card (n: ℕ): finset.card (square_is_fin n).1=8*n:=
begin
sorry,
end

def sup_func_aux (k: ℤ) (n: ℕ) : square n → ℝ:=
λ x, 1/n^k 

def sup_func (k : ℤ) (n : ℕ): ℝ:=
∑' (x : square n), sup_func_aux k n x

def index_fun' (x : ℤ × ℤ): ℕ:=
max (x.1).nat_abs (x.2).nat_abs

lemma equiv_fun' (x: ℤ × ℤ) : x ∈ square  ( index_fun' x):=
begin
rw index_fun', simp only [square_mem'],
end  

lemma equiv_fun (x: ℤ × ℤ): x ∈ set.Union square:=
begin
simp only [set.mem_Union, square_mem', exists_eq'], 
end  


def index_union: ℤ × ℤ ≃ set.Union square:=
{
to_fun:=λ x, ⟨x,equiv_fun x⟩,
inv_fun:=λ x, x.1,
left_inv:=sorry,
right_inv:=sorry,


}

def coef (s : fintype (ℤ × ℤ)): set (ℤ × ℤ):=
(s.1: set (ℤ × ℤ))


variables {α : Type u} {β : Type v} {γ : Type w} {i : α → set β}

instance ww (a: α): has_lift_t (i a) (set.Union i):=
begin
fsplit, intros ᾰ, cases ᾰ, fsplit, work_on_goal 1 { simp at *, fsplit, work_on_goal 1 { assumption } },
end



lemma tsum_union_disjoint' [add_comm_monoid γ] [topological_space γ] (i : α → set β) (hd: ∀ (a b : α), disjoint (i a) (i b)) (g : set.Union i → γ )
(hs: summable g ): ∑' (x : set.Union i), g x= ∑' (a : α), (∑' x : (i a),   (g ∘ coe) x):=

begin
sorry,
end


lemma tsum_summable [add_comm_monoid β] [topological_space β] (f g : α → β) (h: (∑' (a: α), f) = (∑' (a: α), g) ): summable f ↔ summable g:=
begin
rw summable, rw summable, simp, sorry,
end  


lemma sum_rearrange (f: ℕ → fintype (ℤ × ℤ)) (e:  set.Union (coef ∘ f) ≃ ℤ × ℤ  ) (g: ℤ × ℤ → ℝ): summable g ↔ summable  (λ (x : ℕ) , (∑ y in  (f x).1, g y)) :=
begin
 have h: summable g ↔ summable (g ∘ e), rw equiv.summable_iff e,
rw h, 
have H0: ∀ (i j : ℕ), disjoint ((coef ∘ f) i) ((coef ∘ f) j), by {sorry,},
have H:=tsum_union_disjoint' (coef ∘ f) H0 (g ∘ e),
split,
intro H1,
 simp [H1] at H,  
  sorry,
end



-- prod_bUnion 


lemma Eise_is_summable (A: SL2Z) (k : ℤ) (z : ℍ) (h : k ≥ 4) (h2: even k) : summable (Eise k z) :=

begin
--rw summable, use (0: ℂ), rw has_sum, rw Eis', simp, sorry, 
--rw summable_iff_cauchy_seq_finset, rw cauchy_seq,
--summable_of_nonneg_of_le 
 
sorry,
end  



lemma Eise_is_summable' (A: SL2Z) (k : ℤ) (z : ℍ) (h : k ≥ 4) (h2: even k)  : summable (Eise k z ∘⇑(Ind_equiv A)) :=
begin
rw equiv.summable_iff (Ind_equiv A), exact Eise_is_summable A k z h h2,

end




lemma Eise_is_Pet (k: ℤ)  :  (Eisenstein_series_weight_ k) ∈ is_Petersson_weight_ k :=

begin
rw is_Petersson_weight_, rw Eisenstein_series_weight_, simp only [set.mem_set_of_eq], 
intros A z, have h1:= Eise_moeb k z A,  have h2:=tsum_congr h1, convert h2, simp only [subtype.val_eq_coe], 
have h3:=equiv.tsum_eq (Ind_equiv A) (Eise k z), 
rw tsum_mul_left, rw h3,refl,
end


end Eisenstein_series

#lint