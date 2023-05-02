import data.complex.exponential
import mod_forms.Eisenstein_Series.Eisen_is_holo

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

lemma exp_upper_half_plane_lt_one (z : ℍ) : complex.abs (complex.exp ( 2 *↑π * I * z)) < 1 :=
begin
rw ←upper_half_plane.re_add_im,
rw mul_add,
rw exp_add,
simp only [absolute_value.map_mul],
have h1 : complex.abs (exp (2 * ↑π * I * ↑(z.re))) = complex.abs (exp ((2 * ↑π  * ↑(z.re)) * I )),
  by {ring_nf},
rw h1,
norm_cast,
have := abs_exp_of_real_mul_I (2 * π * z.re),
rw this,
simp only [of_real_mul, of_real_bit0, of_real_one, one_mul],
have h2 :  complex.abs (exp (2 * ↑π * I * (↑(z.im) * I))) =
  complex.abs (exp (2 * ↑π * (↑(z.im) * I^2))), by {ring_nf,},
rw h2,
simp only [I_sq, mul_neg, mul_one],
norm_cast,
simp only [real.abs_exp, real.exp_lt_one_iff, right.neg_neg_iff],
apply mul_pos,
apply real.two_pi_pos,
exact z.2,
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
