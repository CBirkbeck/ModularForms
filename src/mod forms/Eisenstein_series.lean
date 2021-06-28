import tactic.ring
import tactic.choose 
import tactic.pi_instances
import .modular_group
import .GLnR
import .modular_forms
import ring_theory.coprime
import ring_theory.int.basic
import .upper_half_space
import data.matrix.notation
import data.setoid.partition
import topology.instances.ennreal
import topology.instances.nnreal
import .Riemann_zeta_fin



universes u v w

open complex

open_locale big_operators nnreal classical

local notation `ℍ` := upper_half_space
noncomputable theory


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




/- This is the permutation of the summation index coming from the moebius action-/
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

lemma Eise_is_nonneg (k: ℤ) (z : ℍ) (y : ℤ × ℤ): 0 ≤ abs (Eise k z y):=
begin
unfold Eise, simp, apply complex.abs_nonneg, 
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


/- How the Eise function changes under the Moebius action-/
lemma Eise_moeb (k: ℤ) (z : ℍ) (A : SL2Z) (i : ℤ × ℤ ): Eise k (moeb A z) i=  ((A.1 1 0*z+A.1 1 1)^k)*(Eise k z (Ind_equiv A i ) ):=

begin
rw Eise, rw Eise, rw moeb, simp, rw mat2_complex, simp, dsimp, rw ← coe_coe, rw ← coe_coe, rw calc_lem, have h1:= coe_chain A, simp at h1, rw h1, rw h1, rw h1, rw h1, rw ← coe_coe, 
have hh:= preserve_ℍ.aux A, apply hh, have:=A.2,  have h2:= SL_det_pos' A, exact h2,simp only [subtype.coe_prop], 
end  


/--This defines the Eisenstein series of weight k and level one. At the moment there is no restriction on the weight, but in order to make it an actual
modular form some constraints will be needed -/
def Eisenstein_series_of_weight_ (k: ℤ) : ℍ → ℂ:=
 λ z, ∑' (x : ℤ × ℤ), (Eise k z x) 







lemma Eisenstein_is_Petersson (k: ℤ)  :  (Eisenstein_series_of_weight_ k) ∈ is_Petersson_weight_ k :=

begin
rw is_Petersson_weight_, rw Eisenstein_series_of_weight_, simp only [set.mem_set_of_eq], 
intros A z, have h1:= Eise_moeb k z A,  have h2:=tsum_congr h1, convert h2, simp only [subtype.val_eq_coe], 
have h3:=equiv.tsum_eq (Ind_equiv A) (Eise k z), 
rw tsum_mul_left, rw h3,refl,
end




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

lemma max_aux'' (a b n : ℕ) (h: max a b =n): a=n ∨ b =n :=
begin
rw ← h,
apply max_aux,
end  






def Square (m: ℕ): finset (ℤ × ℤ):=((finset.Ico_ℤ (-m) (m+1)).product (finset.Ico_ℤ (-m) (m+1))).filter (λ x, max (x.1).nat_abs (x.2).nat_abs = m)

lemma find (a : ℤ ) (h: a = -a): a=0:=
begin
exact eq_zero_of_neg_eq (eq.symm h),
end  

def Square2 (m: ℕ): finset (ℤ × ℤ):= 
(finset.Ico_ℤ (-m) (m+1)).product {m } ∪ (finset.Ico_ℤ (-m) (m+1)).product {-(m: ℤ)} ∪    ({m} : finset (ℤ)).product (finset.Ico_ℤ (-m+1) (m)) ∪   ({-m} : finset (ℤ)).product (finset.Ico_ℤ (-m+1) (m))

lemma square2_card (n: ℕ) (h: 1 ≤ n): finset.card (Square2 n)=8*n:=
begin
rw Square2, rw finset.card_union_eq, rw finset.card_union_eq,rw finset.card_union_eq, rw finset.card_product,
 rw finset.card_product,rw finset.card_product, rw finset.card_product, simp, ring, sorry,
 rw finset.disjoint_iff_ne,  intros a ha, intros b hb, simp at *, by_contra H, have haa:=ha.2, have hbb:=hb.2,
  rw H at haa, rw hbb at haa, have hv:=eq_zero_of_neg_eq haa, simp at hv, rw hv at h, simp at h, exact h,

  
end  

@[simp]lemma square_mem (n : ℕ) (x : ℤ × ℤ ) : x ∈ (Square n) ↔ max (x.1).nat_abs (x.2).nat_abs=n:=
begin
split,
intro x,
rw Square at x, simp at x, simp_rw x,
intro hx, rw Square, simp, simp [hx], 
 
sorry,
end

lemma square_mem' (n : ℕ) (x : ℤ × ℤ ) : x ∈ (Square n) ↔  (x.1).nat_abs=n ∨ (x.2).nat_abs=n:=
begin
sorry,
end



def square_map: ℤ × ℤ → ℤ × ℤ:=
λ x, if max (x.1).nat_abs (x.2).nat_abs=x.1.nat_abs ∧ x.2.nat_abs < x.1.nat_abs then (x.1+int.sign (x.1),x.2) 
else if max (x.1).nat_abs (x.2).nat_abs=x.2.nat_abs ∧ x.1.nat_abs < x.2.nat_abs then (x.1,x.2+int.sign(x.2))
else (x.1+int.sign x.1, x.2+int.sign x.2 )

lemma inj_sqr_map: function.injective square_map:=
begin
unfold function.injective,
intros a b hab, rw square_map at hab, simp at hab, tidy, sorry,
end

def Corners (n: ℕ): finset (ℤ × ℤ):=
{(-(n: ℤ), (n: ℤ)+1),(-(n: ℤ), -(n: ℤ)-1), ((n: ℤ), (n: ℤ)+1),((n: ℤ), -(n: ℤ)-1), (-(n: ℤ)-1, (n: ℤ)),((n: ℤ)+1, (n: ℤ)), (-(n: ℤ)-1, -(n: ℤ)),((n: ℤ)+1, -(n: ℤ))}



lemma card_corn (n: ℕ) : finset.card (Corners (n+1))=8:=
begin
rw finset.card_eq_sum_ones, rw Corners, simp, sorry,
--induction n with m hm, simp, refl, rw nat.succ_eq_add_one, ring, rw Corners at *, ring, 
end


lemma sqr_alt (n: ℕ) (h : 1 ≤ n): Square (n+1)= finset.image square_map( Square n) ∪ (Corners n):=

begin
dsimp at *, ext1, cases a, rw square_mem', simp at *, fsplit, intro h1, cases h1, by_cases a_snd < n,


/-work_on_goal 0 { intros h1 },
 work_on_goal 1 { intros ᾰ, cases ᾰ, work_on_goal 0 { cases ᾰ, cases ᾰ_h, cases ᾰ_h_h, induction ᾰ_h_h_left, simp at *, cases h } },  -/
sorry,
end




lemma Square_size (n : ℕ) : finset.card (Square (n+1))=8*(n+1):=
begin
induction n with m hm, simp, refl,

  rw nat.succ_eq_add_one, ring_nf, rw sqr_alt, rw finset.card_union_eq, 
have:= card_corn m,rw this, rw finset.card_image_of_injective, rw hm, ring, apply inj_sqr_map, sorry, linarith,

end  

lemma Squares_are_disjoint: ∀ (i j : ℕ), i ≠ j → disjoint (Square i) (Square j):=
begin
sorry,
end

lemma Squares_cover_all :  ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ Square (i) :=
begin
sorry,
end  



lemma Square_zero : Square (0: ℕ)={(0,0)}:=
begin
refl,  
end  

lemma Square_zero_card: finset.card (Square 0)=1:=
begin
rw Square_zero, refl,
end  




/- Some summable lemmas-/

variables {α : Type u} {β : Type v} {γ : Type w} {i : α → set β}

instance  (a: α): has_lift_t (i a) (set.Union i):=
begin
fsplit, intros ᾰ, cases ᾰ, fsplit, work_on_goal 1 { simp at *, fsplit, work_on_goal 1 { assumption } },
end



instance: has_coe_t  (finset (ℤ × ℤ))  (set (ℤ × ℤ)):=infer_instance

def coef (s : finset (ℤ × ℤ)): set (ℤ × ℤ):=
(s: set (ℤ × ℤ ))

def fn (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) (x : ℤ × ℤ): x ∈  (⋃ (s: ℕ), coef (In s)):=
begin
  
have h1:=HI x, 
rw set.mem_Union, cases h1, cases x, cases h1_h, dsimp at *, simp at *, fsplit, work_on_goal 1 { assumption },
end

def fnn  (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) (x:  ℤ × ℤ)  : (⋃ (s: ℕ), coef (In s)):=
⟨x, fn In HI x⟩


def union_equiv (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) : (⋃ (s: ℕ), coef (In s)) ≃ ℤ × ℤ:=
{
to_fun:=λ x, x.1 ,
inv_fun:=λ x,   fnn In HI x,
left_inv:= by {simp, intros x, cases x, refl},
right_inv:=by {simp, intros x, refl}
}





lemma unionmem (i: α → set β) (x : α) (y : i x): (coe y)  ∈ (⋃ x, i x):=
begin
simp, use x, cases y, assumption,
end




lemma summable_disjoint_union_of_nonneg {i : α →  set β} {f : (⋃ x, i x) → ℝ} (h: ∀ a b, a ≠ b →  disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
  summable f ↔ (∀ x, summable (λ (y : i x), f ⟨y, unionmem i x y⟩ )) ∧ summable (λ x, ∑' (y : i x), f ⟨y , unionmem i x y⟩) :=
 begin
let h0:=(set.Union_eq_sigma_of_disjoint h).symm,
have h01: summable f ↔ summable ( f ∘ h0 ), by {have:= equiv.summable_iff h0 , rw this, },
have h22: ∀ y : (Σ (s: α ), i s), 0 ≤ (f ∘ h0) y:= by {simp_rw h0, 
 rw set.Union_eq_sigma_of_disjoint, simp only [equiv.symm_symm, function.comp_app, sigma.forall, equiv.of_bijective_apply], simp_rw set.sigma_to_Union, simp_rw hf, simp only [forall_2_true_iff],}, 
have h1:=summable_sigma_of_nonneg h22 ,
rw h01, rw h1, 
have H1: ∀ (x : α), summable (λ (y : (λ (s : α), ↥(i s)) x), f (h0 ⟨x, y⟩)) ↔ summable (λ (y : ↥(i x)), f ⟨y,  unionmem i x y⟩),
 by {
  intro x, dsimp, simp_rw h0, rw set.Union_eq_sigma_of_disjoint, simp only [equiv.symm_symm, equiv.of_bijective_apply], simp_rw set.sigma_to_Union, },
simp_rw H1, simp only [ and.congr_right_iff], intro hfin, 
have H2: ∀  (x : α), ∑' (y : (λ (s : α), ↥(i s)) x), (f ∘ ⇑h0) ⟨x, y⟩=∑' (y : ↥(i x)), f ⟨↑y, unionmem i x y⟩, by {
  intro x, simp only [function.comp_app], simp_rw h0,  rw set.Union_eq_sigma_of_disjoint, simp only [equiv.symm_symm, equiv.of_bijective_apply], simp_rw set.sigma_to_Union,}, 

simp_rw H2,
 end

lemma disjoint_aux (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) : ∀ (i j : ℕ), i ≠ j → disjoint (In i) (In j):=
begin
intros i j h, intros a α, cases a, dsimp at *, simp at *, cases α, 
have HI0:=HI a_fst a_snd,
have:= exists_unique.unique HI0 α_left α_right, rw this at h, simp at *, exact h,
end



lemma sum_lemma (f: ℤ × ℤ → ℝ) (h: ∀ y : ℤ × ℤ, 0 ≤ f y) (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) )  :
summable f ↔ summable (λ ( n : ℕ), ∑ x in In (n), f x)  :=
begin
let h2:= union_equiv In HI,
have h22: ∀ y : (⋃ (s: ℕ), coef (In s)), 0 ≤ (f ∘ h2) y:= by {simp_rw h2, simp_rw union_equiv, simp, 
simp_rw coef, simp_rw h, simp only [forall_const, implies_true_iff],}, 
have hdis':=disjoint_aux In HI,
have h5: ∀ (x : ℕ), finset ((coef (In x))), by {intro x, rw coef, exact finset.univ,},
have hg:∀ (x : ℕ), (coef (In x))={y : ℤ × ℤ | y ∈ In x}, by {intros x, refl,},
have hdis:∀ (a b : ℕ) , a ≠ b →  disjoint (coef (In a)) (coef (In b)), by {intros a b hab, simp_rw coef, 
rw ← finset.disjoint_iff_disjoint_coe, apply hdis', exact hab,},
have h3:=summable_disjoint_union_of_nonneg  hdis h22 ,
have h4: summable f ↔ summable (f ∘ h2), by {have:= equiv.summable_iff h2 , rw this, }, 
rw h4, rw h3, simp only [function.comp_app], dsimp, 

have h6: ∀ (x : ℕ), ∑' (y : ↥(coef (In x))), f (h2 ⟨y,_⟩) = ∑ y in  (In x), f y, by {
  simp only, intro x, apply finset.tsum_subtype', },
simp_rw h6,  simp only [and_iff_right_iff_imp], simp_rw h2, rw union_equiv,  simp only [equiv.coe_fn_mk, subtype.coe_mk], 
intros H x, rw hg, apply finset.summable,
 apply unionmem, 

end



lemma realpow (n : ℕ ) (k : ℤ): (n: ℝ)^((k : ℝ)-1)= n^(k-1):=
begin
have:=real.rpow_int_cast (n: ℝ) (k-1), rw ← this, simp,
end




lemma summable_if_complex_abs_summable {f : α → ℂ} :
  summable (λ x, complex.abs (f x)) →  summable f :=
begin
intro h,
apply summable_of_norm_bounded  (λ x, complex.abs (f x))  h,
intro i,
unfold norm, exact complete_of_proper,
end

lemma upper_gt_zero (z: ℍ) : 0<(z: ℂ ).im:=
begin
 have H:= z.property, rw H_mem at H, simp at H,  apply H,
end

def lb (z: ℍ): ℝ:=((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2

lemma lb_pos (z : ℍ): 0 < lb z :=
begin
rw lb, simp, 
have H1: 0 < ((z.1.2)^4 + (z.1.1*z.1.2)^2), by {rw add_comm, apply add_pos_of_nonneg_of_pos,   nlinarith, 
have h1: z.1.2^4=z.1.2^2*z.1.2^2, ring, rw h1, apply mul_pos, simp, have:=upper_gt_zero z, rw pow_two, apply mul_pos, exact this, exact this,
simp, have:=upper_gt_zero z, rw pow_two, apply mul_pos, exact this, exact this, }, 
have H2: 0 < (z.1.1^2+z.1.2^2)^2, by {nlinarith,},
have H3: ((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2=((z.1.2)^4 + (z.1.1*z.1.2)^2)*((z.1.1^2+z.1.2^2)^2)⁻¹ , by {ring,},
simp at H3, rw H3,
have H4: 0 < ((z.1.1^2+z.1.2^2)^2)⁻¹, by {rw inv_pos, exact H2,},
apply mul_pos H1 H4,
end  

def rfunct (z: ℍ): ℝ:=
min (real.sqrt((z.1.2)^2)) (real.sqrt(lb z))

lemma rfunct_pos (z : ℍ): 0 < (rfunct z):=
begin
 have H:= z.property, rw H_mem at H, simp at H,  
rw rfunct, simp, split, rw pow_two, apply mul_pos, exact H, exact H, apply lb_pos,
end


lemma alem (a b c : ℝ): (a-b) ≤ a+c ↔ -b ≤ c:=
begin
have: a-b= a+(-b), by {ring,},
split, 
rw this, simp_rw add_le_add_iff_left, simp,
rw this, simp_rw add_le_add_iff_left, simp,
end

lemma ineq1 (x y d: ℝ  ): 0 ≤ d^2*(x^2+y^2)^2+2*d*x*(x^2+y^2)+x^2:=
begin
have h1: d^2*(x^2+y^2)^2+2*d*x*(x^2+y^2)+x^2 =(d*(x^2+y^2)+x)^2, by {ring,},
rw h1,
nlinarith,
end

lemma lowbound (z : ℍ) (δ : ℝ): ((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2 ≤ (δ*z.1.1+1)^2+(δ*z.1.2)^2:=
begin
simp, 
have H1: (δ*z.1.1+1)^2+(δ*z.1.2)^2=δ^2*(z.1.1^2+z.1.2^2)+2*δ*z.1.1+1, by {ring,}, simp at H1, rw H1, rw div_le_iff, simp,
have H2: (δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) + 2 * δ *  (z: ℂ).re + 1) * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2=δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2)^3 + 2 * δ *  (z: ℂ).re* ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2+   ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2,
by {ring,}, rw H2, rw ← sub_nonneg, 
have H3:( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2-((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=((z: ℂ).re)^2*( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2), by {ring,},


have H4: δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 3 + 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 + ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 - ((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=(((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2))*(δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 + 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {ring,},
rw H4,
have H5: 0 ≤ (δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 + 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {apply ineq1,},
have H6: 0 ≤ (((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)), by {nlinarith,},
apply mul_nonneg H6 H5, 
have H7:= z.property, rw H_mem at H7, simp at H7, 
have H8:0 < (z: ℂ).im ^ 2, by {simp [H7], },
have H9: 0 <((z: ℂ).im ^ 2+(z: ℂ).re ^ 2), by {nlinarith,},
nlinarith,
end





lemma auxlem (z : ℍ) (δ : ℝ) : (rfunct z) ≤ complex.abs ( (z: ℂ)+δ ) ∧ (rfunct z) ≤ complex.abs ( δ*(z: ℂ) +1):=
begin
split,
{
rw rfunct, rw complex.abs, rw norm_sq, simp only [add_zero, of_real_im, monoid_with_zero_hom.coe_mk, of_real_re, add_re, add_im, min_le_iff, subtype.val_eq_coe],
have H1: real.sqrt (((z: ℂ).im)^2) ≤ real.sqrt (((z: ℂ).re + δ) * ((z: ℂ).re + δ) + (z: ℂ).im * (z: ℂ).im), by {
  rw real.sqrt_le, nlinarith,nlinarith,
},
simp_rw H1, simp,

},

{
  rw rfunct, rw complex.abs, rw norm_sq, simp,
 have H1:  real.sqrt (lb z) ≤ real.sqrt ((δ*(z: ℂ).re  + 1) * (δ*(z: ℂ).re  + 1) + δ*(z: ℂ).im *  (δ*(z: ℂ).im )), by {
   rw lb, rw real.sqrt_le, have:= lowbound z δ, rw ← pow_two, rw ← pow_two,  simp at *, apply this,nlinarith,},
  simp_rw H1, simp,
  },



/-  
split,
{
 rw rfunct, unfold rfunct', unfold complex.abs, unfold norm_sq, simp, 
by_cases c1:  0 ≤ ((z: ℂ).re - 1), 
have H: real.sqrt (((z: ℂ).re - 1) * ((z: ℂ).re - 1) + (z: ℂ).im * (z: ℂ).im) ≤ real.sqrt (((z: ℂ).re + δ) * ((z: ℂ).re + δ) + (z: ℂ).im * (z: ℂ).im), 
by {rw real.sqrt_le, simp only [add_le_add_iff_right], 
have i1: ((z:ℂ).re - 1) ≤  ((z: ℂ).re + δ), by {rw alem, norm_cast at h2, rw abs_le at h2 , apply h2.1,} ,
apply mul_self_le_mul_self, apply c1, apply i1, nlinarith,},
have h3: (rfunct z) ≤ real.sqrt (((z: ℂ).re - 1) * ((z: ℂ).re - 1) + (z: ℂ).im * (z: ℂ).im) ,
by {sorry,},
rw rfunct at h3, unfold rfunct' at h3, unfold complex.abs at h3, unfold norm_sq at h3, simp at h3,
apply le_trans h3 H,
simp at c1,
  sorry,   },  




{sorry,},-/
end

lemma complex_abs_pow' (k : ℕ) (a : ℂ): complex.abs (a^k)= (complex.abs (a))^k:=
begin
induction k with n hd, simp, rw [pow_succ, pow_succ], have h1:= complex.abs_mul (a) (a^n), rw hd at h1, apply h1,
end  

lemma complex_abs_pow (k : ℤ) (a : ℂ): complex.abs (a^k)= (complex.abs (a))^k:=
begin
induction k with n hd, apply complex_abs_pow', simp only [fpow_neg_succ_of_nat, inv_inj', complex.abs_inv], apply complex_abs_pow', 
end  

lemma le_of_pow' (a b : ℝ) (k: ℕ)(h : 0 ≤ a) (h2: 0 ≤ b) (h3: a ≤ b): a^k ≤ b^k:=
begin
exact pow_le_pow_of_le_left h h3 k,
end  




lemma baux (a : ℝ) (k : ℕ) (b : ℂ) (h: 0 ≤ a) (h2: a ≤ complex.abs b): a^k ≤ complex.abs (b^k):=
begin
rw complex_abs_pow', apply le_of_pow', exact h, apply complex.abs_nonneg, exact h2,

end  


lemma baux2 (z : ℍ) (k: ℕ): complex.abs ((rfunct z)^k)=(rfunct z)^k:=
begin
norm_cast,
let a:=rfunct z, simp, 
have ha: 0 ≤ a, by {simp_rw a, have:= rfunct_pos z , apply le_of_lt this, },
have:= complex.abs_of_nonneg ha, norm_cast at this, simp_rw a at this, rw this,
end

lemma auxlem2 (z : ℍ) (n : ℕ)  (x: ℤ × ℤ) (h2: x ∈ Square n) (k : ℕ)  :   complex.abs (((rfunct z): ℂ)^k) ≤   complex.abs (( (z: ℂ)+(x.2: ℂ)/(x.1 : ℂ) )^k):=

begin
norm_cast, 
have H1: complex.abs ((rfunct z)^k)=(rfunct z)^k, by {apply baux2,}, norm_cast at H1, rw H1,  apply baux, have:= rfunct_pos z, apply le_of_lt this,
have:= auxlem z ((x.2/x.1): ℝ), norm_cast at this, apply this.1,
end  


lemma auxlem3 (z : ℍ) (n : ℕ)  (x: ℤ × ℤ) (h2: x ∈ Square n) (k : ℕ)  :   complex.abs (((rfunct z): ℂ)^k) ≤   complex.abs (( ((x.1: ℂ)/(x.2 : ℂ))*(z: ℂ) +1)^k):=

begin
norm_cast,
have H1:= (baux2 z k), norm_cast at H1, rw H1,  apply baux, have:= rfunct_pos z, apply le_of_lt this,
have:= auxlem z ((x.1/x.2): ℝ), norm_cast at *, apply this.2,
end

lemma Eise_on_square_is_bounded ( k : ℕ) (z : ℍ) (n : ℕ) (x: ℤ × ℤ) (h: x ∈ Square n) (hn: 1 ≤ n):  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=  
begin
by_cases C1: complex.abs (x.1: ℂ)=n,
rw inv_le_inv,
have h0: (x.1:ℂ) ≠ 0, by {norm_cast, intro hx, rw hx at C1, simp only [int.cast_zero, complex.abs_zero] at C1, norm_cast at C1, rw ← C1 at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn,},
have h1:(↑(x.fst) * ↑z + ↑(x.snd)) ^ k =  (↑(x.fst))^k* ((z: ℂ)+(x.2: ℂ)/(↑(x.fst)))^k, by { rw ← mul_pow, rw div_eq_mul_inv, 
have: (x.fst: ℂ) * ((z: ℂ)  + (x.snd: ℂ) * ((x.fst: ℂ))⁻¹)=(x.fst: ℂ) * (z: ℂ) + (x.snd: ℂ), by {
 have p1: (x.fst: ℂ) * ((z: ℂ)  + (x.snd: ℂ) * ((x.fst: ℂ))⁻¹)= ((x.fst: ℂ) * (z: ℂ)  + (x.fst : ℂ) * ((x.fst: ℂ))⁻¹ * (x.snd: ℂ)),
 ring,  rw mul_inv_cancel at p1, simp only [one_mul] at p1,rw p1, exact h0,},rw this,


},
rw h1, rw complex.abs_mul, rw complex.abs_mul,  
have h3: complex.abs (↑(x.fst) ^ k)=  (complex.abs (↑(x.fst)))^k , by {apply complex_abs_pow', },
rw h3, rw C1,
have h4: complex.abs (↑n ^ k)=↑n ^ k, by {norm_cast, },


rw h4, rw mul_comm, apply mul_le_mul_of_nonneg_left,
have:=auxlem2 z n  x h k , apply this, norm_cast, simp only [zero_le'], simp only [complex.abs_pos, ne.def],
have hh : ((x.fst): ℂ) * (z: ℂ) + (x.snd: ℂ) ≠ 0, by {
intro H,
have H1 : x.1 = 0 ∨ (z: ℂ).im = 0, by simpa using congr_arg complex.im H, 
cases H1, {rw H1 at C1, simp only [int.cast_zero, complex.abs_zero] at C1, norm_cast at C1, rw ← C1 at hn, simp only [nat.one_ne_zero, square_mem, le_zero_iff] at *, exact hn,},
have HH:= z.property, rw H_mem at HH, simp only [subtype.val_eq_coe] at HH, rw H1 at HH, simp at HH, exact HH,}, 
apply pow_ne_zero, exact hh, simp only [complex.abs_mul], apply mul_pos, rw complex.abs_pos, apply pow_ne_zero, have:= rfunct_pos z, 
norm_cast, intro np, rw np at this, simp only [lt_self_iff_false] at this, exact this, simp only [complex.abs_pos], apply pow_ne_zero, norm_cast, 
intro Hn, rw Hn at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn, 

have C2: complex.abs (x.2: ℂ)=n, by {simp only [square_mem] at h, have:=max_aux'' x.1.nat_abs x.2.nat_abs n h, norm_cast,
cases this, by_contra, norm_cast at C1, rw ← this at C1, rw int.abs_eq_nat_abs at C1, simp only [eq_self_iff_true, not_true] at C1, exact C1, 
rw ← this, rw int.abs_eq_nat_abs,},


 rw inv_le_inv,
have h0: (x.2: ℂ ) ≠ 0, by {norm_cast, intro hx, rw hx at C2,simp only [int.cast_zero, complex.abs_zero] at C2, norm_cast at C2, rw ← C2 at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn,},
have h1:(↑(x.fst) * ↑z + ↑(x.snd)) ^ k =  (↑(x.snd))^k* (((x.1:ℂ)/(x.2: ℂ))*(z: ℂ)+1)^k, by {
  rw ← mul_pow,simp only, rw div_eq_mul_inv, 
  have: (x.snd: ℂ) * ((x.fst: ℂ) * ((x.snd: ℂ))⁻¹ * (z:ℂ) + 1)=((x.snd: ℂ ) * ((x.snd : ℂ))⁻¹ * (x.fst : ℂ )* (z: ℂ) + (x.snd: ℂ)), by {ring,},
  rw this, rw mul_inv_cancel, simp only [one_mul], exact h0,},
rw h1, rw complex.abs_mul, rw complex.abs_mul, 
have h3: complex.abs (↑(x.2) ^ k)=  (complex.abs (↑(x.2)))^k , by {apply complex_abs_pow', },
rw h3, rw C2,
have h4: complex.abs (↑n ^ k)=↑n ^ k, by {norm_cast, }, rw h4, rw mul_comm, apply mul_le_mul_of_nonneg_left, 
have:=auxlem3 z n  x h k , apply this, norm_cast, simp only [zero_le'],
have hh : ((x.fst): ℂ) * (z: ℂ) + (x.snd: ℂ) ≠ 0, by {
 intro H,
 have H1 : x.1 = 0 ∨ (z: ℂ).im = 0, by simpa using congr_arg complex.im H, 
 cases H1,
 {rw H1 at H, simp only [int.cast_eq_zero, int.cast_zero, zero_mul, zero_add] at H, rw H at C2, simp only [int.cast_zero, complex.abs_zero] at C2, norm_cast at C2, rw ← C2 at hn, simp only [nat.one_ne_zero, square_mem, le_zero_iff] at *, exact hn},
 have HH:= z.property, rw H_mem at HH, simp only [subtype.val_eq_coe] at HH, rw H1 at HH, simp only [lt_self_iff_false] at HH, exact HH,},
rw complex.abs_pos, apply pow_ne_zero, exact hh,simp only [complex.abs_mul], apply mul_pos,  rw complex.abs_pos, apply pow_ne_zero, have:= rfunct_pos z, 
norm_cast, intro np, rw np at this,  simp only [lt_self_iff_false] at this, exact this, simp only [complex.abs_pos], apply pow_ne_zero, norm_cast, 
intro Hn, rw Hn at hn, simp only [nat.one_ne_zero, le_zero_iff] at hn, exact hn, 

end



lemma Eise_on_square_is_bounded' ( k : ℕ) (z : ℍ) (n : ℕ) (hn: 1 ≤ n): ∀ (x: ℤ × ℤ),  x ∈ (Square n) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
intros x hx,
apply Eise_on_square_is_bounded k z n x hx hn,
end



lemma Eise_on_zero_Square (k : ℕ) (z : ℍ) (h: 1 ≤ k) :∀ (x: ℤ × ℤ),  x ∈ (Square 0) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* 0^k))⁻¹ :=
begin
intros x hx, rw Square_zero at hx, simp only [finset.mem_singleton] at hx, simp_rw hx, simp only [add_zero, int.cast_zero, zero_mul, complex.abs_mul], 
have h1: (0: ℂ)^k=0, by {rw zero_pow_eq_zero, linarith,}, rw h1, rw complex.abs_zero, simp only [mul_zero],
end

lemma Eise_on_square_is_bounded'' ( k : ℕ) (z : ℍ) (n : ℕ) (hn: 1 ≤ k): ∀ (x: ℤ × ℤ),  x ∈ (Square n) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
by_cases h0: n=0,
{rw h0, apply Eise_on_zero_Square k z hn, },
have Hn: 1 ≤ n, by {have:=nat.pos_of_ne_zero, simp at this, work_on_goal 0 { cases z, solve_by_elim },},
intros x hx,
apply Eise_on_square_is_bounded k z n x hx Hn,
end




instance: field ℝ:=infer_instance

lemma natpows (x : ℝ) (n : ℤ)  (h2: x ≠ 0): x^(n-1)=x^n*x⁻¹:=
begin
apply fpow_sub_one, apply h2,


end

lemma natpowsinv (x : ℝ) (n : ℤ)  (h2: x ≠ 0): (x^(n-1))⁻¹=(x^n)⁻¹*x:=
begin
have:=natpows x n  h2, rw this, have h3:=mul_fpow (x^n) (x⁻¹) (-1), rw fpow_neg at h3, simp at h3, exact h3,
end  

lemma wut (k: ℤ) (h: 3 ≤ k): 1 < k-1:=
begin
nlinarith,
end  

lemma Eisenstein_series_is_summable (A: SL2Z) (k : ℕ) (z : ℍ) (h : 3 ≤ k) : summable (Eise k z) :=

begin
let In:=Square,
have HI:=Squares_cover_all,
have Hpos:= Eise_is_nonneg k z,
let f:=(Eise k z),
have sum_Eq:  summable (λ x, abs (f x)) → summable f, by {apply summable_if_complex_abs_summable,},

simp_rw ← f,
apply sum_Eq,
let g:= λ (y : ℤ × ℤ), abs (f y),
have gpos: ∀ (y : ℤ × ℤ), 0 ≤ g y, by {simp_rw g,intro y, apply complex.abs_nonneg,},
simp_rw ← g,
have index_lem:= sum_lemma g  gpos In HI,

rw  index_lem,

let e:=λ (x: ℕ), ∑ (y : ℤ × ℤ) in (In x), g y,




have BIGCLAIM: ∀ (n : ℕ), ∑ (y : ℤ × ℤ) in (In n), g y ≤(8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹, by {
intro n,
simp_rw g, simp_rw f, rw Eise, simp only [one_div, complex.abs_inv, fpow_coe_nat],
have k0: 1 ≤ k, by {linarith,},
have BO:=  Eise_on_square_is_bounded'' ( k : ℕ) (z : ℍ) (n : ℕ) k0,
by_cases n0: n=0, {simp_rw In, rw n0, rw Square_zero, 
simp only [add_zero, int.cast_zero, nat.cast_zero, zero_mul, finset.sum_singleton], 
have H0: (0: ℂ)^k=0, by {rw zero_pow_eq_zero, linarith,}, rw H0, simp only [complex.abs_zero, inv_zero],
have H00: (0: ℝ)^((k: ℤ)-1)=0, by { rw zero_fpow, linarith,}, rw H00, simp only [inv_zero, mul_zero],},
have:= finset.sum_le_sum BO, simp only [finset.sum_const, complex.abs_mul, nsmul_eq_mul] at this,

have hfin:= (Square_size (n-1)), have hnzo: n-1+1=n, by {rw nat.sub_add_cancel, have:= nat.pos_of_ne_zero n0, linarith,}, rw hnzo at hfin,
 rw hfin at this,
norm_cast at this, simp_rw In, 
have ne:( (8 * n) * (complex.abs (rfunct z ^ k) * ((n ^ k): ℝ))⁻¹ : ℝ)= (8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹, 
by {rw complex_abs_pow', rw complex.abs_of_nonneg, rw ← mul_pow, rw div_eq_inv_mul, 
have:8* ↑n * ((rfunct z * ↑n) ^ k)⁻¹= 8*((rfunct z)^k)⁻¹ * (↑n^((k: ℤ)-1))⁻¹, by { 
 have dis: ((rfunct z * ↑n) ^ k)⁻¹=((rfunct z)^k)⁻¹* (↑n^k)⁻¹, by {rw mul_pow, 
 rw [← fpow_neg_one,← fpow_neg_one,← fpow_neg_one], rw ← mul_fpow,},
 simp [dis], rw natpowsinv, ring, norm_cast,  intro hN, rw hN at n0, 
 simp only [eq_self_iff_true, not_true] at n0, exact n0,},
rw this, ring, have rpos:= rfunct_pos z, apply le_of_lt rpos,},
norm_cast at ne, rw ne at this, norm_cast,  apply this, 
},

have smallerclaim:  ∀ (n : ℕ), e n ≤  (8/(rfunct z)^k) * ((rie (k-1)) n), by {
simp_rw e, simp only at BIGCLAIM, rw rie, simp only [one_div], intro n,
 have tr :((↑n ^ ((k: ℤ) - 1))⁻¹: ℝ)=((↑n ^ ((k: ℝ) - 1))⁻¹: ℝ), by {simp only [inv_inj'], 
 have:= realpow n k, 
 norm_cast at this, rw ← this, simp only [int.cast_coe_nat, int.cast_one, int.cast_sub],},
 rw ← tr, apply BIGCLAIM n,
},

have epos: ∀ (x : ℕ), 0 ≤ e x, by {simp_rw e, simp_rw g, intro x, 
apply finset.sum_nonneg,  intros i hi, apply complex.abs_nonneg, },

have hk: 1 < ((k-1): ℤ), by { linarith, },
have nze: ((8/((rfunct z)^k)): ℝ)  ≠ 0, by {apply div_ne_zero, simp, apply pow_ne_zero,
 simp, by_contra HR, have:=rfunct_pos z, rw HR at this, simp at this, exact this, },
have riesum:=int_Riemann_zeta_is_summmable (k-1) hk,

have riesum': summable (λ (n : ℕ), (8 / (rfunct z)^k) * rie (↑k - 1) n), by {
  rw (summable_mul_left_iff nze).symm, simp at riesum, apply riesum,},
have:=summable_of_nonneg_of_le epos smallerclaim, 

apply this,
apply riesum',



end  








end Eisenstein_series





