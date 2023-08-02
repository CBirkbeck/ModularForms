import data.complex.exponential
import mod_forms.Eisenstein_Series.Eisen_is_holo
import mod_forms.Eisenstein_Series.exp_summable_lemmas
import mod_forms.Eisenstein_Series.auxp_lemmas
import analysis.special_functions.trigonometric.euler_sine_prod
import analysis.complex.locally_uniform_limit
import analysis.special_functions.trigonometric.bounds

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)

local notation `ℍ` := upper_half_plane

def cot (z : ℂ) := (complex.cos z)/(complex.sin z)

lemma cot_exp (z : ℍ) : cot (↑π* z) =
  (complex.exp ( 2 *↑π * I * z) + 1)/(I* (1- complex.exp ( 2 *↑π * I * z))) :=
begin
rw [cot,sin,cos],
field_simp,
have h1 : (exp (↑π * ↑z * I) + exp (-(↑π * ↑z * I))) =  exp (-(↑π * ↑z * I)) * (exp (2* ↑π * ↑z * I) + 1),
by{rw mul_add,
rw ←exp_add,
simp,
apply congr_arg,
ring,},
have h2 : ((exp (-(↑π * ↑z * I)) - exp (↑π * ↑z * I)) * I) = I * exp (-(↑π * ↑z * I)) * (1 -exp (2* ↑π * ↑z * I)),
by {rw mul_sub,
simp_rw mul_assoc,
rw ←exp_add,
ring_nf,},
rw [h1,h2],
have h22: I * exp (-(↑π * ↑z * I)) * (1 -exp (2* ↑π * ↑z * I)) =
exp (-(↑π * ↑z * I)) * (I * (1 -exp (2* ↑π * ↑z * I))), by {ring},
rw h22,
rw mul_div_mul_left,
have h3 : complex.exp ( 2 *↑π * I * z) = complex.exp ( 2 *↑π * z * I), by {apply congr_arg,
ring,},
simp_rw h3,
apply exp_ne_zero,
end

lemma div_one_sub_exp (z : ℍ) : 1/ (1- complex.exp ( 2 *↑π * I * z)) =
  ∑'(n : ℕ), complex.exp ( 2 *↑π * I * z * n) :=
begin
simp,
apply symm,
have h :  ∑'(n : ℕ), complex.exp ( 2 *↑π * I * z * n) =  ∑'(n : ℕ), complex.exp ( 2 *↑π * I * z )^n,
by {apply tsum_congr,
intro b,
rw  ←exp_nat_mul,
ring_nf,},
rw h,
apply tsum_geometric_of_norm_lt_1,
apply exp_upper_half_plane_lt_one,
end


variables {R : Type*} [normed_ring R] [complete_space R]

lemma geo_succ (x : R) (h : ‖x‖ < 1) : ∑' i:ℕ, x^(i+1)=  (∑' i:ℕ, x^i) -1 :=
begin
  apply symm,
  rw sub_eq_iff_eq_add,
  rw tsum_eq_zero_add,
  simp only [pow_zero],
  apply add_comm,
  apply normed_ring.summable_geometric_of_norm_lt_1 x h,
end

lemma geom_series_mul_add (x : R) (h : ‖x‖ < 1) :
 x * (∑' i:ℕ, x ^ i)  = ∑' i:ℕ, x^(i+1)  :=
begin
have := ((normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_left (x)),
  refine tendsto_nhds_unique this.tendsto_sum_nat _,
  have : tendsto (λ (n : ℕ), (∑ i in finset.range (n+1), x ^ i)-1) at_top (𝓝 ∑' i:ℕ, x^(i+1)),
  by {have hu :=(normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum,
     have hj := geo_succ x h,
     rw hj,
     apply tendsto.sub_const,
     simp_rw finset.sum_range_succ,
     have hp : (tsum (pow x)) = (tsum (pow x)) + 0, by {simp},
     rw hp,
     apply tendsto.add,
     apply  has_sum.tendsto_sum_nat,
     apply summable.has_sum,
     apply normed_ring.summable_geometric_of_norm_lt_1 x h,
     apply (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h),},
  convert ←this,
  ext n,
  have hh:= @geom_sum_succ _ _ x n,
  rw hh,
  simp only [add_sub_cancel],
  exact finset.mul_sum,
end




lemma geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
(1+ x) * (∑' i:ℕ, x ^ i) = 2* (∑' i:ℕ, x ^ i) - 1 :=
begin
rw add_mul,
simp only [one_mul],
rw geom_series_mul_add x h,
rw geo_succ x h,
rw two_mul,
abel,
end

lemma pi_cot_q_exp (z : ℍ) : ↑π * cot (↑π* z) =
  ↑π * I- (2 *  ↑π * I)* ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) :=
begin
rw cot_exp,
have h1: ↑π * ((exp (2 * ↑π * I * ↑z) + 1) / (I * (1 - exp (2 * ↑π * I * ↑z)))) =
-↑π * I * ((exp (2 * ↑π * I * ↑z) + 1)* (1 /  ((1 - exp (2 * ↑π * I * ↑z))))),
by {rw div_mul_eq_div_mul_one_div,
simp,
ring,},
rw h1,
rw div_one_sub_exp z,
rw add_comm,
have :=geom_series_mul_one_add (exp (2 * ↑π * I * ↑z)) (exp_upper_half_plane_lt_one _),
have hh : ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) =
∑' (n : ℕ), complex.exp ( 2 *↑π * I * z)^n, by {
  apply tsum_congr,
  intro b,
  rw ←exp_nat_mul,
  ring_nf,
},
rw hh,
rw this,
ring,
end



def log_deriv (f : ℂ  → ℂ) := deriv f / f

lemma cot_log_derv_sin (z : ℍ) : cot (π *z) = ((deriv sin) (π * z))/ sin (π * z) :=
begin
rw cot,
simp,
end

/-
lemma log_derv_eq_derv_log (f : ℂ  → ℂ) (x : ℂ) (hf : f x ≠ 0): (log_deriv f) x =
(deriv ((complex.log) ∘ f) x) :=
begin
sorry,
end
-/


lemma log_deriv_one : log_deriv 1 = 0 :=
begin
rw log_deriv,
simp,
ext1,
simp,
apply (deriv_const x (1 : ℂ)),
end

lemma log_derv_mul (f g: ℂ → ℂ) (x : ℂ) (hfg : f x * g x ≠ 0) (hdf : differentiable_at ℂ f x)
 (hdg : differentiable_at ℂ g x) :
log_deriv (λz, f z * g z) x = log_deriv(f) x + log_deriv (g) x:=
begin
simp_rw log_deriv,
simp,
rw deriv_mul hdf hdg,
have h1 := (mul_ne_zero_iff.1 hfg).1,
have h2 := (mul_ne_zero_iff.1 hfg).2,
field_simp,
apply mul_comm,
end

lemma log_deriv_prod {α : Type*} (s : finset  α) (f : α → ℂ → ℂ) (t : ℂ) (hf : ∀ x ∈ s, f x t ≠ 0)
   (hd : ∀ x ∈ s, differentiable_at ℂ (f x) t) :
  log_deriv (∏ i in s, f i) t = ∑ i in s, log_deriv (f i) t :=
begin
  induction s using finset.cons_induction_on with a s ha ih,
  { simp [log_deriv_one] },
  { rw [finset.forall_mem_cons] at hf,
    simp [ih hf.2], rw finset.prod_insert, rw finset.sum_insert,
    --rw log_derv_mul,

    sorry, sorry, sorry,
   -- apply log_derv_mul,
   }
end

/-
lemma log_derv_diff (f : ℂ → ℂ) (s : set ℂ) (hs : is_open s) (hf : differentiable_on ℂ f s) (x : s)
 (hf2 : ∀ x ∈ s, f x ≠ 0) : differentiable_on ℂ (log_deriv f) s :=
begin
rw log_deriv,
apply differentiable_on.div,
all_goals{sorry},


end
-/

lemma log_deriv_congr (f g : ℂ → ℂ)  (hfg : f = g) : log_deriv f = log_deriv g :=
begin
apply congr,
refl,
exact hfg,
end

lemma log_deriv_comp (f g : ℂ → ℂ) (x : ℂ) (hf : differentiable_at ℂ f (g x) )
(hg : differentiable_at ℂ g x) : log_deriv (f ∘ g) x = ((log_deriv f) (g x)) * deriv g x :=
begin
simp_rw log_deriv,
simp,
rw (deriv.comp _ hf hg),
simp_rw mul_comm,
apply mul_assoc,
end


lemma log_deriv_of_sin_pi_mul (z : ℍ) (n : ℕ): log_deriv (complex.sin ∘  (λt, π * t)) =
log_deriv (λ x,  π * x * (∏ j in finset.range n, (1 - x ^ 2 / (j + 1) ^ 2)) *
(∫ y in 0..π/2, complex.cos (2 * x * y) * real.cos y ^ (2 * n)) / ↑∫ y in 0..π/2, real.cos y ^ (2 * n))  :=
begin
apply log_deriv_congr,
ext1,
apply euler_sine.sin_pi_mul_eq x n,
end

lemma log_deriv_sine (z : ℍ): log_deriv (complex.sin ∘  (λt, π * t)) z = π * cot(π * z) :=
begin
rw log_deriv_comp,
simp,
rw log_deriv,
simp,
rw cot,
apply mul_comm,
simp,
simp,
end



lemma log_deriv_eq_1 (x : ℍ) (n : ℕ) : log_deriv (λ z, (1 - z ^ 2 / (n + 1) ^ 2)) x =
  (1/(x-(n+1))+1/(x+(n+1))) :=
begin
have h1 :  log_deriv (λ z, (1 - z ^ 2 / (n + 1) ^ 2)) x = -2*x/((n+1)^2 - x^2),
  by {rw log_deriv,
      simp,
      field_simp,
      congr,
      rw mul_one_sub,
      simp,
      apply mul_div_cancel',
      apply pow_ne_zero,
      norm_cast,
      linarith,},
rw h1,
sorry,

end

lemma log_deriv_pi_z (x : ℂ) : log_deriv (λ z : ℂ, π * z) x = 1/x :=
begin
rw log_deriv,
simp,
field_simp,
apply div_mul_right,
norm_cast,
apply real.pi_ne_zero,

end

lemma func_prod_fun {α : Type*} (s : finset  α) (f : α → ℂ → ℂ) : ∏ i in s, f i =
  (λ z, ∏ i in s, f i z):=
begin
exact finset.prod_fn s (λ (c : α), f c),

end


lemma upper_half_ne_nat_pow_two (z : ℍ) : ∀ (n : ℕ), (z : ℂ)^2 ≠ n^2 :=
begin
by_contra h,
simp at h,
obtain ⟨n, hn⟩:= h,
have := abs_pow_two_upp_half z n,
rw hn at this,
simp at this,
exact this,
end

lemma factor_ne_zero (x : ℍ) (n : ℕ) : ((1 : ℂ) - x ^ 2 / (n + 1) ^ 2) ≠ 0 :=
begin
by_contra,
rw sub_eq_zero at h,
have hs :=h.symm,
rw div_eq_one_iff_eq at hs,
have hr := upper_half_ne_nat_pow_two x (n+1),
simp only [nat.cast_add, algebra_map.coe_one, ne.def] at *,
apply absurd hs hr,
apply pow_ne_zero,
norm_cast,
linarith,
end

lemma differentiable_on.product (F : ℕ → ℂ → ℂ) (n : ℕ) (s : set ℂ)
  (hd : ∀ (i : finset.range n), differentiable_on ℂ (λ z, F i z ) s):
  differentiable_on ℂ (λ z, ∏ i in finset.range n, F i z ) s :=
begin
induction n,
simp,
apply (differentiable_const (1 : ℂ)).differentiable_on,
simp_rw finset.prod_range_succ,
apply differentiable_on.mul,
apply n_ih,
intro i,
have hi := i.2,
simp at *,
apply hd,
apply lt_trans hi,
apply nat.lt_succ_self,
simp at *,
apply hd,
apply nat.lt_succ_self,
end

lemma prod_diff_on' (n : ℕ ) : differentiable_on ℂ
  (λ z : ℂ,  (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) ℍ' :=
begin
apply differentiable_on.product,
intros i,
apply differentiable_on.sub,
apply (differentiable_const (1 : ℂ)).differentiable_on,
apply differentiable_on.div_const,
apply differentiable_on.pow,
apply differentiable_id.differentiable_on,
end

lemma product_diff_on_H (n : ℕ) : differentiable_on ℂ
  (λ z, ↑π * (z : ℂ)  * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) ℍ' :=
begin
apply differentiable_on.mul,
apply differentiable_on.const_mul,
apply differentiable_id.differentiable_on,
apply  prod_diff_on',
end

lemma log_deriv_of_prod (x : ℍ) (n : ℕ) :
  log_deriv  (λ z, (↑π * z )  * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) x =
  1/x + ∑ j in finset.range n, (1/(x-(j+1))+1/(x+(j+1))) :=
begin
rw log_derv_mul,
rw log_deriv_pi_z,
simp only [one_div, add_right_inj],
have:= log_deriv_prod (finset.range n) (λ n : ℕ, λ z : ℂ, (1 - z ^ 2 / (n + 1) ^ 2)) ,
simp at this,
rw ←finset.prod_fn,
rw this,
simp_rw log_deriv_eq_1,
congr,
ext1,
field_simp,
intros m hm,
apply factor_ne_zero x m,
apply mul_ne_zero,
apply mul_ne_zero,
norm_cast,
apply (real.pi_ne_zero),
apply (upper_half_plane.ne_zero x),
rw finset.prod_ne_zero_iff,
intros a ha,
apply factor_ne_zero x a,
apply differentiable_at.const_mul,
apply differentiable_id.differentiable_at,
apply  (prod_diff_on' n).differentiable_at,
apply is_open_iff_mem_nhds.1,
apply upper_half_plane_is_open,
apply x.2,
end


--lemma log_of_prod  (z : ℍ) (n : ℕ) :
 --log_deriv (λ x,  π * x * (∏ j in finset.range n, (1 - x ^ 2 / (j + 1) ^ 2))) =

lemma log_der_tendsto (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (x : ℍ') (hF : tendsto_locally_uniformly_on f g at_top ℍ')
  (hf : ∀ᶠ (n : ℕ) in at_top, differentiable_on ℂ (f n) ℍ') (hg : g x ≠0 ):
tendsto (λ n : ℕ, (log_deriv (f n) x)) at_top (𝓝 ((log_deriv g) x)) :=
begin
--have := continuous_at.tendsto,
--rw tendsto_at_top_nhds,
simp_rw log_deriv,
apply tendsto.div,
swap,
apply hF.tendsto_at,
apply x.2,
have := (hF.deriv) _ _,
have hf2 := this.tendsto_at,
apply hf2,
apply x.2,
apply hf,
apply upper_half_plane_is_open,
apply hg,
end

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section has_prod
variables [comm_monoid α] [topological_space α]

def has_prod (f : ℕ → β  → α) (a : β → α) : Prop := tendsto (λ n : ℕ, ∏ b in finset.range n, f b) at_top (𝓝 a)

def prodable (f : ℕ → β → α) : Prop := ∃a, has_prod f a

@[irreducible] def tprod {β} (f : ℕ → β → α) := if h : prodable f then classical.some h else 1

notation `∏'` binders `, ` r:(scoped:67 f, tprod f) := r

noncomputable theory

lemma prodable.has_prod {f : ℕ → β → α} (ha : prodable f) : has_prod f (∏'b, f b) :=
by simp [ha, tprod]; exact classical.some_spec ha

lemma prod_be_exp (f : ℕ → ℂ) (s : finset ℕ) : (∏ i in s,  (1 + complex.abs (f i))) ≤
real.exp ( ∑ i in s, complex.abs (f i) ) :=
begin
rw real.exp_sum,
apply finset.prod_le_prod,
intros i hi,
apply add_nonneg,
linarith,
apply complex.abs.nonneg,
intros i hi,
rw add_comm,
apply real.add_one_le_exp_of_nonneg (complex.abs.nonneg _),
end



lemma prod_le_prod_abs (f : ℕ → ℂ) (n : ℕ)  : complex.abs ((∏ i in finset.range (n), ((f i) + 1)) - 1) ≤
  (∏ i in finset.range (n), (complex.abs (f i) + 1)) - 1 :=
begin
induction n with h,
simp only [finset.range_zero, finset.prod_empty, sub_self, absolute_value.map_zero],
have HH : ((∏ i in finset.range (h + 1), ((f i) + 1)) - 1) =
  ((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h) + 1)+ f (h), by {
    simp_rw finset.prod_range_succ,
    ring},
rw HH,
have  H3: complex.abs (((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h ) + 1) + f (h )) ≤
complex.abs(((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h) + 1))+ complex.abs (f (h)),
by {
  apply le_trans (complex.abs.add_le _ _),
  simp only},
apply le_trans H3,
have H4: complex.abs(((∏ i in finset.range (h), ((f i) + 1)) - 1) * (f (h) + 1))+
  complex.abs (f (h)) ≤  ((∏ i in finset.range (h), (complex.abs (f i) + 1)) - 1) *
  (complex.abs ((f (h))) + 1) +  complex.abs (f (h)), by {
    simp only [absolute_value.map_mul, add_le_add_iff_right],
    have h1: complex.abs(((∏ i in finset.range (h), ((f i) + 1)) - 1)) ≤
    ((∏ i in finset.range (h), (complex.abs (f i) + 1)) - 1), by {
      apply n_ih},
    have h2 : complex.abs (f (h) + 1) ≤  (complex.abs ((f (h))) + 1), by {
        apply le_trans (complex.abs.add_le _ _),
        simp only [absolute_value.map_one],
       },
    apply mul_le_mul h1 h2,
    apply complex.abs.nonneg,
    apply le_trans _ n_ih,
    apply complex.abs.nonneg,},
apply le_trans H4,
ring_nf,
rw finset.prod_range_succ,
rw mul_comm,
end

--rw ←finset.prod_range_mul_prod_Ico

lemma prod_le_prod_abs_Ico (f : ℕ → ℂ) (n m: ℕ) : complex.abs ((∏ i in finset.Ico m n, ((f i) + 1)) - 1) ≤
  (∏ i in finset.Ico m n, (complex.abs (f i) + 1)) - 1 :=
begin
simp_rw finset.prod_Ico_eq_prod_range,
apply prod_le_prod_abs,
end

lemma prod_le_prod_abs_Ico_ond_add (f : ℕ → ℂ) (n m: ℕ) : complex.abs ((∏ i in finset.Ico m n, (1+ (f i))) - 1) ≤
  (∏ i in finset.Ico m n, (1 + complex.abs ((f i)))) - 1 :=
begin
convert prod_le_prod_abs_Ico f n m,
repeat {apply add_comm},
end


lemma unif_prod_bound (F : ℕ → ℂ → ℂ) (K : set ℂ)
  (hb : ∃ (T : ℝ), ∀ (x : ℂ), x ∈ K →   ∑' (n : ℕ), complex.abs (F n x) ≤ T)
   (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∃ (C : ℝ), 0 < C  ∧  ∀ (s : finset ℕ) (x : ℂ), x ∈ K →
  (∏ i in s,  (1 + complex.abs (F i x))) ≤ C :=
begin
obtain ⟨T, ht⟩:= hb,
have HB : ∀ (s : finset ℕ) (a : ℂ), ∑ i in s, complex.abs (F i a) ≤  ( ∑' (n : ℕ), complex.abs (F n a)),
by {intros n a,
    apply sum_le_tsum,
    intros b hb,
    apply complex.abs.nonneg,
    apply hs a},
have hexp : 0 < real.exp(T), by {have := (real.exp_pos T), apply this,},
refine ⟨real.exp (T),  _, ⟩ ,
simp [hexp],
intros n x hx,
apply le_trans (prod_be_exp _ _),
simp,
apply le_trans (HB n x),
exact ht x hx,
end

lemma fin_prod_le_exp_sum (F : ℕ → ℂ → ℂ)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∀ (s : finset ℕ) (x : ℂ),
  (∏ i in s,  (1 + complex.abs (F i x))) ≤ real.exp ( ∑' i : ℕ, complex.abs (F i x) ) :=
begin
have HB : ∀ (s : finset ℕ) (a : ℂ), ∑ i in s, complex.abs (F i a) ≤  ( ∑' (n : ℕ), complex.abs (F n a)),
by {intros n a,
    apply sum_le_tsum,
    intros b hb,
    apply complex.abs.nonneg,
    apply hs a},
intros s x,
apply le_trans (prod_be_exp _ _),
simp,
apply HB s x,
end



lemma tsum_unif  (F : ℕ → ℂ → ℂ) (K : set ℂ)  (hf :  tendsto_uniformly_on
  (λ (n : ℕ), (λ (a : ℂ), ∑ i in (finset.range n), complex.abs (F i a)))
  ( (λ (a : ℂ), ∑' (n : ℕ), complex.abs (F n a))) filter.at_top K)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∀ ε : ℝ , 0 < ε → ∃ (N : ℕ), ∀ (n : ℕ) (x : ℂ), x ∈ K → N ≤ n →
  complex.abs (∑' i : ℕ, complex.abs (F (i + N) x)) < ε  :=
begin
rw tendsto_uniformly_on_iff at hf,
simp at hf,
intros ε hε,
have HF := hf ε hε,
obtain ⟨N, hN⟩:= HF,
refine ⟨N,_⟩,
intros n x hx hn,
have hnn : N ≤ N, by {linarith},
have HN2 := hN N hnn x hx,
simp_rw dist_eq_norm at *,
convert HN2,
rw tsum_coe,
rw ← norm_eq_abs,
rw complex.norm_real,
congr,
have hy := sum_add_tsum_nat_add N (hs x),
simp at hy,
rw ←hy,
ring,
end


lemma abs_tsum_of_poss (F : ℕ → ℂ → ℝ ) (h : ∀ (n : ℕ) (c : ℂ), 0 ≤ F n c) : ∀ x : ℂ,
 |(∑'(i : ℕ), F i x) | = ∑' (i : ℕ), F i x :=
begin
intro x,
simp only [abs_eq_self],
apply tsum_nonneg,
intro b,
apply h b x,
end


lemma abs_tsum_of_pos (F: ℕ → ℂ → ℂ) : ∀ (x : ℂ) (N : ℕ),
  complex.abs ((∑' (i : ℕ), complex.abs (F (i + N) x)) : ℂ) = ∑' (i : ℕ), complex.abs (F (i + N) x) :=
begin
intros x N,
have := abs_tsum_of_poss (λ n : ℕ, λ x : ℂ, complex.abs (F (n + N) x)) _ x,
rw ←this,
simp,
rw ←abs_of_real _,
congr,
rw tsum_coe,
intros n c,
apply complex.abs.nonneg,
end


lemma add_eq_sub_add (a b c d : ℝ) : b = c - a +d  ↔  a + b = c + d :=
begin
split,
repeat {intro h,
linarith [h]},
end


lemma sum_subtype_le_tsum (f: ℕ → ℝ) (m n N : ℕ) (hmn : m ≤ n ∧ N ≤ m)
 (hg: ∀ b , 0 ≤ f b) (hf : summable f) :
∑(i : ℕ) in finset.Ico m n, f i ≤ ∑' (i : ℕ), f (i + N) :=
begin
have h1 : ∑(i : ℕ) in finset.Ico m n, f i  ≤ ∑(i : ℕ) in finset.Ico N n, f i, by {
  have := finset.Ico_union_Ico_eq_Ico hmn.2 hmn.1,
  rw ←this,
  rw finset.sum_union,
  simp,
  apply finset.sum_nonneg,
  intros i hi,
  apply hg i,
  exact finset.Ico_disjoint_Ico_consecutive N m n,
},
apply le_trans h1,
have h2 :  ∑' (i : ℕ), f (i + N) = ∑(i : ℕ) in finset.Ico N n, f i + ∑' (i : ℕ), f (i + n),
by {
  have hh1 := sum_add_tsum_nat_add N hf,
  have hh2 := sum_add_tsum_nat_add n hf,
  rw ←hh2 at hh1,
  rw ←add_eq_sub_add at hh1,
  rw hh1,
  simp,
  have hNn : N ≤ n, by {exact le_trans hmn.2 hmn.1, },
  have :=  finset.sum_range_add_sum_Ico f hNn,
  rw ← this,
  simp,},
rw h2,
simp,
apply tsum_nonneg,
intro b,
apply hg (b+n),
end


lemma tsum_unifo  (F : ℕ → ℂ → ℂ) (K : set ℂ)  (hf :  tendsto_uniformly_on
  (λ (n : ℕ), (λ (a : ℂ), ∑ i in (finset.range n), complex.abs (F i a)))
  ( (λ (a : ℂ), ∑' (n : ℕ), complex.abs (F n a))) filter.at_top K)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) )):
  ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ), ∀ (n m: ℕ) (x : ℂ), x ∈ K →  N ≤ n ∧ N ≤ m ∧ m ≤ n →
  (∏ i in finset.Ico (m) (n),  (1 + complex.abs (F i x))) - 1 ≤ ε  :=
begin
intros ε hε,
have hl : 0 < real.log(1 + ε), by {apply real.log_pos, linarith,},
have H2:= tsum_unif  F K hf hs (real.log( 1+ ε)) hl,
obtain ⟨N, hN⟩:= H2,
use N,
intros n m x hK h,
have HN2:= hN n x hK h.1,
apply le_trans (sub_le_sub_right (prod_be_exp _ _) 1),
rw ←real.exp_lt_exp at HN2,
have hll : 0 < 1 + ε, by {linarith},
rw (real.exp_log hll) at HN2,
rw tsub_le_iff_left,
apply le_trans _ (HN2.le),
simp,
have hss : summable (λ n : ℕ, ( (complex.abs (F (n + N) x))) ), by {have := hs x,
  rw  ← (summable_nat_add_iff N) at this,
  apply this,
  exact topological_add_group.mk,},
have := (abs_tsum _ (hss)),
rw (abs_tsum_of_pos F x N),
have := sum_add_tsum_nat_add N (hs x),
apply sum_subtype_le_tsum,
split,
apply h.2.2,
apply h.2.1,
intro b,
apply complex.abs.nonneg,
exact hs x,
end



lemma auxreal (e : ℂ) : complex.abs (1- e) = complex.abs(e -1):=
begin
exact map_sub_rev abs 1 e,
end



lemma sum_prod_unif_conv (F : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (K : set ℂ) (hf :  tendsto_uniformly_on
  (λ (n : ℕ), (λ (a : ℂ), ∑ i in (finset.range n), complex.abs (F i a)))
  ( (λ (a : ℂ), ∑' (n : ℕ), complex.abs (F n a))) filter.at_top K)
  (hb : ∃ (T : ℝ), ∀ (x : ℂ), x ∈ K →   ∑' (n : ℕ), complex.abs (F n x) ≤ T)
  (hs : ∀ x : ℂ, summable (λ n : ℕ, ( (complex.abs (F n x))) ))
  (hp : ∀ x : ℂ, x ∈ K → tendsto (λ (n : ℕ), ( ∏ i in (finset.range n),  (1 + F i x) )) at_top (𝓝 (g x))):
  tendsto_uniformly_on  (λ (n : ℕ), (λ (a : ℂ), ∏ i in (finset.range n),  (1 + F i a) ))
   ( g ) filter.at_top K:=
begin
apply uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto,
rw uniform_cauchy_seq_on_iff,
intros ε hε,
have H := tsum_unifo F K hf hs,
have H2 := unif_prod_bound F K hb hs,
obtain ⟨C, hCp, hC⟩:= H2,
have hdelta:= exists_pos_mul_lt hε C,
obtain ⟨δ, hδ⟩ := hdelta,
have HH := H (δ) hδ.1,
obtain ⟨N, HN⟩:= HH,
refine  ⟨N,_⟩,
intros n hn m hm x hx,
have hCm := hC (finset.range (m)) x,
have hCn := hC (finset.range (n)) x,
rw dist_eq_norm,
simp only [norm_eq_abs],
by_cases hmn:  m ≤ n,
rw ←finset.prod_range_mul_prod_Ico _ hmn,
rw ←mul_sub_one,
simp only [absolute_value.map_mul, abs_prod],
have A : ∏ (i : ℕ) in finset.range m, complex.abs(1 + F i x) ≤ C, by {
  apply le_trans _ (hCm hx),
  apply finset.prod_le_prod,
  intros i hi,
  apply complex.abs.nonneg,
  intros i hi,
  apply le_trans (complex.abs.add_le _ _),
  simp only [absolute_value.map_one],},
have B: complex.abs((∏ (i : ℕ) in  (finset.Ico m n), (1 + (F i x))) -1) ≤ δ, by {
  have HI := HN n m x hx,
  simp only [ and_imp] at HI,
  have HI2:= HI hn hm hmn,
  have:= (prod_le_prod_abs_Ico_ond_add (λ (i : ℕ), F i x) n m),
  simp at this,
  apply le_trans this,
  exact HI2,},
have AB := mul_le_mul A B _ hCp.le,
apply lt_of_le_of_lt AB,
apply hδ.2,

apply complex.abs.nonneg,
simp at hmn,
rw ←finset.prod_range_mul_prod_Ico _ hmn.le,
rw ←mul_one_sub,
simp only [absolute_value.map_mul, abs_prod],
have A : ∏ (i : ℕ) in finset.range n, complex.abs(1 + F i x) ≤ C, by {
  apply le_trans _ (hCn hx),
  apply finset.prod_le_prod,
  intros i hi,
  apply complex.abs.nonneg,
  intros i hi,
  apply le_trans (complex.abs.add_le _ _),
  simp only [absolute_value.map_one],},
have B: complex.abs((∏ (i : ℕ) in  (finset.Ico n m), (1 + (F i x))) -1) ≤ δ, by {
  have HI := HN m n x hx,
  simp only [ and_imp] at HI,
  have HI2:= HI hm hn hmn.le,
  have:= (prod_le_prod_abs_Ico_ond_add (λ (i : ℕ), F i x) m n),
  simp at this,
  apply le_trans this,
  exact HI2,},
have AB := mul_le_mul A B _ hCp.le,
rw auxreal _,
apply lt_of_le_of_lt AB,
apply hδ.2,

apply complex.abs.nonneg,


exact hp,
end

lemma tendsto_unif_on_restrict (f: ℕ → ℂ → ℝ ) (g : ℂ → ℝ) (K : set ℂ) :
 tendsto_uniformly_on f g at_top K ↔ tendsto_uniformly (λ n : ℕ,  λ k : K,  f n k)
 (λ k : K, g k) at_top :=
begin
rw tendsto_uniformly_iff,
rw tendsto_uniformly_on_iff,
simp,
end

lemma tendst_unif_coe (K : set ℂ) (f: ℕ → K → ℝ ) (g : K → ℝ)  :
tendsto_uniformly (λ n : ℕ,  λ k : K,  ((f n k) : ℂ)) (λ n : K, ((g n) : ℂ)) at_top
  ↔ tendsto_uniformly (λ n : ℕ,  λ k : K,  f n k) (λ k : K, g k) at_top :=
begin
simp_rw tendsto_uniformly_iff,
simp_rw dist_eq_norm at *,
simp,
split,
repeat{ intro h,
intros e he,
have hh:= h e he,
obtain ⟨a, ha⟩:= hh,
refine ⟨a,_⟩,
intros b hb x hx,
have H:= ha b hb x hx,
convert H,
rw ←abs_of_real,
congr,
simp only [of_real_sub],},
end

#exit

lemma assa (r : ℝ) (z :  ℂ) (x : ball z r) : complex.abs(x) < complex.abs(z) +r :=
begin
have hx : (x : ℂ) = (x - z) + z, by {ring},
rw hx,
apply lt_of_le_of_lt (complex.abs.add_le (x - z) z),
rw add_comm,
simp only [add_lt_add_iff_left],
have hxx := x.2,
simp only [subtype.val_eq_coe, mem_ball] at hxx,
rw dist_eq_norm at hxx,
simpa only using hxx,
end

lemma summable_rie_twist (x : ℂ):  summable (λ (n : ℕ), complex.abs (x ^ 2 / (↑n + 1) ^ 2)) :=
begin
simp,
simp_rw div_eq_mul_inv,
apply summable.mul_left,
have hs : summable (λ (n : ℕ), ((n : ℝ) + 1) ^ 2)⁻¹, by {
  norm_cast,
  simp,
  have h2 : (1 : ℤ)  < 2, by {linarith},
  have := int_Riemann_zeta_is_summmable 2 h2,
  rw rie at this,
  rw  ←(summable_nat_add_iff 1) at this,
  norm_cast at this,
  simpa using this,
  exact topological_add_group.mk,
  },
apply summable.congr hs,
intros b,
simp,
rw ←complex.abs_pow,
norm_cast,
end

lemma rie_twist_bounded_on_ball (z : ℂ) (r: ℝ) (hr : 0 < r):
 ∃ (T : ℝ), ∀ (x : ℂ), x ∈ ball z r → ∑' (n : ℕ), complex.abs (-x ^ 2 / (↑n + 1) ^ 2) ≤ T :=
begin
refine ⟨ (∑' (n : ℕ), (complex.abs(z) +r)^2 /complex.abs ((n+1)^2)), _  ⟩,
intros x hx,
simp only [map_div₀, absolute_value.map_neg, complex.abs_pow],
have := summable_rie_twist x,
apply tsum_le_tsum,
intro b,
simp only,
apply div_le_div_of_le,
apply pow_two_nonneg,
apply pow_le_pow_of_le_left,
apply complex.abs.nonneg,
apply (assa r z ⟨x, hx⟩).le,
convert this,
ext1,
field_simp,
simp_rw div_eq_mul_inv,
apply summable.mul_left,
convert (summable_rie_twist (1 : ℂ)),
ext1,
field_simp,
end

lemma euler_sin_prod' (x : ℂ) (h0 : x ≠ 0):
tendsto (λ (n : ℕ), ∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2)) at_top
(𝓝 ((λ (t : ℂ), sin (↑π * t) / (↑π * t)) x)) :=
begin
have := tendsto_euler_sin_prod x,
rw metric.tendsto_at_top at *,
intros ε hε,
have hh : ↑π * x ≠ 0, by {apply mul_ne_zero, norm_cast, apply real.pi_ne_zero, apply h0,},
have hex: 0 < ε * complex.abs(π * x), by {apply mul_pos, apply hε, apply complex.abs.pos, apply hh},
have h1:= this (ε * complex.abs(π * x)) hex,
obtain ⟨N, hN⟩:= h1,
refine ⟨N,_⟩,
intros n hn,
have h2:= hN n hn,
simp,
rw dist_eq_norm at *,
have : ∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x) / (↑π * x) =
 (↑π * x * ∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2) - sin (↑π * x)) / (↑π * x),
 by {
    have := sub_div' (sin (↑π * x) ) (∏ (i : ℕ) in finset.range n, (1 + -x ^ 2 / (↑i + 1) ^ 2))
      ( ↑π * x) hh,
    simp at *,
    rw this,
    ring,
       },
rw this,
--have hpix : 0 ≠ complex.abs (↑π * x), by {sorry},
field_simp,
rw div_lt_iff,
convert h2,
ext1,
rw sub_eq_add_neg,
field_simp,
simp only [absolute_value.map_mul, abs_of_real],
apply mul_pos,
simpa using real.pi_ne_zero,
apply complex.abs.pos,
exact h0,
end



lemma tendsto_locally_uniformly_euler_sin_prod' (z : ℍ') (r : ℝ) (hr : 0 < r) :
  tendsto_uniformly_on
  (λ n:ℕ, λ z : ℂ,  (∏ j in finset.range n, (1 + - z ^ 2 / (j + 1) ^ 2)))
  (λ t, (complex.sin (π * t))/ (↑π * t)) at_top  ((ball z r) ∩ ℍ'):=
begin
apply sum_prod_unif_conv _ (λ t, (complex.sin (π * t))/ (↑π * t)) ((ball z r) ∩ ℍ'),
have := tendsto_unif_on_restrict _ _ ((ball z r) ∩ ℍ'),
rw this,
simp only [map_div₀, absolute_value.map_neg, complex.abs_pow],
set s : ℝ := complex.abs(z)+r,
have HH:= M_test_uniform _ (λ (n : ℕ) (x : (ball (z : ℂ)  r) ∩ ℍ'), complex.abs(x^2/(n+1)^2)) (λ (n : ℕ),
  complex.abs(s^2/(n+1)^2)) _ _,
rw ←tendst_unif_coe _ _ _,
convert HH,
simp only [coe_finset_sum, map_div₀, complex.abs_pow],
funext,
rw tsum_coe,
congr,
simp only [map_div₀, complex.abs_pow],
simp  [hr, nonempty_coe_sort, nonempty_ball],
rw nonempty_def,
refine ⟨z,_⟩,
simp [hr, z.2],
exact z.2,
intros n x,
simp only [map_div₀, complex.abs_pow, of_real_div, of_real_pow, abs_of_real, complex.abs_abs, of_real_add],
apply div_le_div_of_le,
apply pow_two_nonneg,
apply pow_le_pow_of_le_left (complex.abs.nonneg _),
have hxx : (x : ℂ ) ∈ ball (z : ℂ) r, by {have :=x.2, rw mem_inter_iff at this, apply this.1, },
have A:= assa r z (⟨x, hxx⟩ : ball (z : ℂ) r),
norm_cast at A,
simp at *,
apply le_trans A.le,
norm_cast,
apply le_abs_self,
apply (summable_rie_twist s),
have B:= rie_twist_bounded_on_ball z r hr,
obtain ⟨T, hT⟩:= B,
refine ⟨T,_⟩,
intros x hx,
apply hT x,
rw mem_inter_iff at hx,
apply hx.1,
intro x,
convert (summable_rie_twist x),
ext1,
field_simp,
intros x hx,
have := (euler_sin_prod' x),
apply this,
rw mem_inter_iff at hx,
apply upper_half_plane.ne_zero (⟨x, hx.2⟩ : ℍ),
end

lemma sub_add_prod_aux (n : ℕ) (z : ℂ):
 (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)) =
 (∏ j in finset.range n, (1 + -z ^ 2 / (j + 1) ^ 2)) :=
begin
congr,
ext1,
ring,
end

example (a b  : ℝ) (ha : 0 ≤ a) (hb: 0 < b): 0  < a + b:=
begin
exact lt_add_of_le_of_pos ha hb,
end

lemma aux_ineq (ε : ℝ) (hε : 0 < ε) (x y: ℍ) (hxy : complex.abs (y - x) < ε) :
  (ε / (|π| * complex.abs x + |π|* ε)) * (|π| * complex.abs y) < ε :=
begin
have : (ε / (|π| * complex.abs x + |π|* ε)) * (|π| * complex.abs y) =
ε * (((|π| * complex.abs y)) / (|π| * complex.abs x + |π|* ε)) , by {
  field_simp,},
rw this,
have hp : 0 < |π|, by {rw abs_pos, exact real.pi_ne_zero},
have h1: ((|π| * complex.abs y)) / (|π| * complex.abs x + |π|* ε) < 1, by {
  rw div_lt_one,
  rw ←mul_add,
  have hh : complex.abs ↑y < (complex.abs ↑x + ε), by {have :=assa ε (x : ℂ),
   simp at this,
   apply this y,
   simpa using hxy,},
  nlinarith,
  rw ←mul_add,
  apply mul_pos,
  exact hp,
  exact lt_add_of_le_of_pos (complex.abs.nonneg x) hε,},
apply mul_lt_of_lt_one_right hε h1,
end



lemma sin_pi_z_ne_zero (z : ℍ) : complex.sin (π * z) ≠ 0 :=
begin
apply (complex.sin_ne_zero_iff.2),
intro k,
rw mul_comm,
by_contradiction,
simp at h,
cases h,
have hk : (k : ℂ).im = 0, by {simp,},
have hz : 0 < (z : ℂ).im, by {simpa using z.2},
rw [h,hk] at hz,
simpa using hz,
have := real.pi_ne_zero,
exact this h,
end

lemma tendsto_euler_log_derv_sin_prodd (x : ℍ):
  tendsto  ( (λ n:ℕ,  log_deriv  (λ z, ↑π * (z : ℂ)  * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) x))
  at_top (𝓝 $ log_deriv (complex.sin ∘ (λ t, π * t)) x) :=
begin
have := log_der_tendsto
  ( (λ n:ℕ,  (λ z, ↑π * (z : ℂ)  * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) ))
  (complex.sin ∘ (λ t, π * t)) (x) ,
apply this,
rw metric.tendsto_locally_uniformly_on_iff,
intros ε hε  x hx,
have H := tendsto_locally_uniformly_euler_sin_prod' ⟨x, hx⟩ ε hε,
rw tendsto_uniformly_on_iff at H,
have hxe : 0 <  ε/(complex.abs (π * x)+ |π| * ε), by {
  apply div_pos hε,
  simp,
  rw ←mul_add,
  apply mul_pos,
  {rw abs_pos, exact real.pi_ne_zero},
  exact lt_add_of_le_of_pos (complex.abs.nonneg x) hε,},
have HH := H (ε/(complex.abs (π * x) +|π |* ε ) ) hxe,
refine ⟨(ball x ε ∩ ℍ'),_⟩,
simp only [subtype.coe_mk, eventually_at_top, ge_iff_le, mem_inter_iff, mem_ball, comp_app, and_imp, exists_prop,
  ne.def, forall_exists_index, gt_iff_lt] at *,

split,
rw mem_nhds_within_iff,
refine ⟨ε, hε,_⟩,
refl,
obtain ⟨N, hN⟩ := HH,
refine ⟨N,_⟩,
intros b hb y hy hyy,
have:= hN b hb y hy hyy,
rw dist_eq_norm at *,
rw div_sub' at this,
simp only [norm_eq_abs, subtype.coe_mk, absolute_value.map_mul, abs_of_real, map_div₀] at *,
rw div_lt_iff at this,
rw sub_add_prod_aux b y,
apply lt_trans this,
apply aux_ineq ε hε ⟨x, hx⟩ ⟨y, hyy⟩ hy,
apply mul_pos,
{rw abs_pos, exact real.pi_ne_zero},
{apply complex.abs.pos, apply upper_half_plane.ne_zero ⟨y,hyy⟩},
apply mul_ne_zero,
norm_cast,
apply (real.pi_ne_zero),
apply (upper_half_plane.ne_zero ⟨y,hyy⟩),
simp only [subtype.coe_mk, eventually_at_top, ge_iff_le],
refine ⟨1,_⟩,
intros b hn,
apply product_diff_on_H b,
simp only [comp_app],
exact sin_pi_z_ne_zero x,
end


lemma tendsto_euler_log_derv_sin_prodd' (x : ℍ):
  tendsto  ( (λ n:ℕ,   1/(x : ℂ) + ∑ j in finset.range n, (1/(x-(j+1))+1/(x+(j+1)))))
  at_top (𝓝 $  π * cot(π * x)) :=
begin
have := tendsto_euler_log_derv_sin_prodd x,
have h1:= log_deriv_of_prod x,
have h2 := log_deriv_sine x,
rw ←h2,
simp_rw ←h1,
simp at *,
exact this,
end



lemma cot_series_rep' (z : ℍ) : ↑π * cot (↑π* z) - 1/z =
 ∑' (n : ℕ), (1/(z-(n+1))+1/(z+(n+1))) :=
begin
rw (has_sum.tsum_eq _),
exact t2_5_space.t2_space,
rw summable.has_sum_iff_tendsto_nat,
have h:= tendsto_euler_log_derv_sin_prodd' z,
have := tendsto.sub_const (1/(z : ℂ)) h,
simp at *,
apply this,
have H:= lhs_summable z,
have HH := nat_pos_tsum2' (λ n, (1/((z : ℂ)-(n))+1/(z+(n)))),
simp at *,
rw ← HH,
exact H,
end


lemma cot_series_rep (z : ℍ) : ↑π * cot (↑π* z) - 1/z =
 ∑' (n : ℕ+), (1/(z-n)+1/(z+n)) :=
begin
have := tsum_pnat' (λ n, (1/(z-n)+1/(z+n))),
have h1 := cot_series_rep' z,
simp only [one_div, coe_coe, nat.cast_add, algebra_map.coe_one] at *,
rw this,
apply h1,
end

end has_prod


--lemma logder (f : ℕ → ℂ → ℂ) (x a : ℂ) (hx : f x ≠ 0) (hf : tendsto f at_top (𝓝 a))
/-
lemma tendsto_euler_log_sin_prod' (z : ℍ) :
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (filter.map complex.log ((𝓝 $ (complex.sin (π * z))))) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply tendsto_map,
end



lemma clog_der11 (f : ℂ → ℂ) {f' x : ℂ} (h₁ : has_deriv_at f f' x)  (h₂ : f x ≠ 0)
 (h3 : (f x).re < 0 ∧ (f x).im = 0) :
 has_deriv_within_at (λ t, log (complex.abs (f t))) (f' / f x) {z : ℂ | 0 ≤ x.im} x :=
begin
have h1 : 0 < complex.abs (f x).re ∨ complex.abs(f x).im ≠ 0, by {sorry},
have h2: has_deriv_within_at (λ y, (complex.abs (f y) : ℂ)) (complex.abs f')  {z : ℂ | 0 ≤ x.im} x, by {sorry},
have h4:= has_deriv_within_at.clog h2 ,

sorry,
end


lemma clog_der1 (f : ℂ → ℂ) {f' x : ℂ} (h₁ : has_deriv_at f f' x)  (h₂ : f x ≠ 0)
 (h3 : (f x).re < 0 ∧ (f x).im = 0) :
 has_deriv_within_at (λ t, log (f t)) (f' / f x) {z : ℂ | 0 ≤ x.im} x :=
begin
rw has_deriv_within_at_iff_tendsto,
have h1:= tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero h3.1 h3.2,

have h23 := clog_der11 f h₁ h₂ h3,
rw has_deriv_within_at_iff_tendsto at h23,
apply tendsto.congr' _ h23,


end

lemma clog_der (f : ℂ → ℂ) {f' x : ℂ} (h₁ : has_deriv_at f f' x)  (h₂ : f x ≠ 0) :
 has_deriv_at (λ t, log (f t)) (f' / f x) x :=
begin

by_cases 0 ≤  (f x).re ∨ (f x).im ≠ 0,
sorry,
--apply has_deriv_at.clog h₁ h,
rw decidable.not_or_iff_and_not at h,
simp at h,
have h1:= tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero h.1 h.2,
have h2:= tendsto_log_nhds_within_im_neg_of_re_neg_of_im_zero h.1 h.2,
have hh :  has_deriv_within_at (λ t, log (f t)) (f' / f x) {z : ℂ | 0 ≤ x.im} x, by {sorry},




end


lemma has_strict_deriv_at_logg {x : ℂ} (h : x ≠ 0) :
  has_strict_deriv_at log x⁻¹ x :=
begin
by_cases 0 ≤ x.re ∨ x.im ≠ 0,
sorry,
rw decidable.not_or_iff_and_not at h,
simp at h,

end


lemma der_log_sin_eq_cott (x : ℍ') : has_deriv_at (complex.log ∘ (λ z, sin (π * z)) ) ((π : ℂ) * cot(π * x))  x:=
begin
rw has_deriv_at_iff_tendsto,
simp,
sorry,
end


lemma tendsto_der_euler_log_sin_prod' (z : ℍ) :
  tendsto  (deriv complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ deriv (complex.log  ∘ complex.sin) (π * z))  :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply continuous_at.tendsto,


sorry,
end


lemma tendsto_euler_log_sin_prod (z : ℍ)
(hz : 0 < (complex.sin (π * z)).re ∨ (complex.sin (π * z)).im ≠ 0 ) :
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ complex.log (complex.sin (π * z))) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply continuous_at.tendsto,
apply continuous_at_clog,
apply hz,
end

lemma tendsto_euler_log_sin_prodd (z : ℍ):
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ complex.log (complex.sin (π * z))) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
apply continuous_at.tendsto,
by_cases 0 ≤ (complex.sin (π * z)).re ∨ (complex.sin (π * z)).im ≠ 0,
sorry,
--apply continuous_at_clog h,
apply continuous_within_at.continuous_at,
apply continuous_within_at_log_of_re_neg_of_im_zero,
rw decidable.not_or_iff_and_not at h,
simp at h,
apply h.1,
rw decidable.not_or_iff_and_not at h,
simp at h,
apply h.2,
rw decidable.not_or_iff_and_not at h,
simp at h,
rw mem_nhds_subtype_iff_nhds_within,

end

lemma tendsto_euler_log_sin_prod'' (z : ℍ)
(hz : (complex.sin (π * z)).re < 0 ∧ (complex.sin (π * z)).im = 0 ) :
  tendsto  (complex.log ∘  (λ n:ℕ, (↑π * z * (∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2)))))
  at_top (𝓝 $ (real.log (complex.abs((complex.sin (π * z)))) + I*π)) :=
begin
apply tendsto.comp,
swap,
apply tendsto_euler_sin_prod,
have := tendsto_log_nhds_within_im_nonneg_of_re_neg_of_im_zero hz.1 hz.2,

sorry,
end

-/
