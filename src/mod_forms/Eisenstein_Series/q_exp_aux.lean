import mod_forms.Eisenstein_Series.Eisen_is_holo
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import mod_forms.Riemann_zeta_fin
import analysis.calculus.iterated_deriv
import analysis.calculus.series
import mod_forms.Eisenstein_Series.cot_iden
import mod_forms.Eisenstein_Series.tsum_lemmas
import mod_forms.Eisenstein_Series.auxp_lemmas
import mod_forms.Eisenstein_Series.exp_summable_lemmas
--import mod_forms.Eisenstein_Series.Eisenstein_series_q_expansions

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)

local notation `ℍ` := upper_half_plane


lemma iter_eq_on_cong (f g : ℂ → ℂ) (hfg : eq_on f g ℍ') (k : ℕ) :
eq_on (iterated_deriv_within k f ℍ') (iterated_deriv_within k g ℍ') ℍ'  :=
begin
induction k with k hk,
intros x hx,
simp,
apply hfg hx,
intros x hx,
rw iterated_deriv_within_succ,
rw iterated_deriv_within_succ,
apply deriv_within_congr,
intros y hy,
apply hk hy,
apply hk hx,
repeat{apply is_open.unique_diff_within_at upper_half_plane_is_open,
exact hx,},
end

lemma iter_exp_eq_on (k : ℕ+) : eq_on
(iterated_deriv_within k (λ z, ↑π * I - (2 *  ↑π * I) • ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ')
(λ (x : ℂ),  -(2 *  ↑π * I)*∑' (n : ℕ), (2 *  ↑π * I*n)^(k : ℕ) *complex.exp ( 2 *↑π * I * n * x)) ℍ' :=
begin
intros z hz,
apply iter_der_within_add k ⟨z,hz⟩,

end

lemma pos_sum_eq (k : ℕ) (hk : 0 < k):
(λ (x : ℂ),  -(2 *  ↑π * I)*∑' (n : ℕ), (2 *  ↑π * I*n)^(k : ℕ) *complex.exp ( 2 *↑π * I * n * x)) =
(λ (x : ℂ),  -(2 *  ↑π * I)*∑' (n : ℕ+), (2 *  ↑π * I*n)^(k : ℕ) *complex.exp ( 2 *↑π * I * n * x)) :=
begin
ext1,
simp,
left,
apply symm,
have := tsum_pnat (λ (n : ℕ), (2 *  ↑π * I*n)^(k : ℕ) *complex.exp ( 2 *↑π * I * n * x)),
simp at this,
apply this hk,
end



lemma series_eql' (z : ℍ) :   ↑π * I- (2 *  ↑π * I)* ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) =
  1/z + ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n))) :=
begin
rw ←pi_cot_q_exp z,
have h := cot_series_rep z,
rw sub_eq_iff_eq_add' at h,
exact h,
end


lemma q_exp_iden'' (k : ℕ) (hk : 3 ≤ k ): eq_on
(λ (z : ℂ), ((-1 : ℂ )^(k - 1) *(k - 1 )!) * ∑' (d : ℤ), 1/((z : ℂ) + d)^k)
(λ (z : ℂ), (-(2 *  ↑π * I)) * ∑' (n : ℕ+), ((2 *  ↑π * I *n)^(k-1)) *  complex.exp ( 2 *↑π * I * n * z)) ℍ' :=
begin
have := (aux_iter_der_tsum_eq_on k hk).symm,
apply eq_on.trans this,
have hkpos : 0 < k -1, by {apply nat.sub_pos_of_lt,
linarith,},
have h2:= (iter_exp_eq_on (⟨k-1, hkpos⟩ : ℕ+)).symm,
simp only [one_div, coe_coe, subtype.coe_mk, neg_mul, algebra.id.smul_eq_mul] at *,
have h3:= pos_sum_eq (k-1) hkpos,
simp at h3,
rw h3 at h2,
apply eq_on.symm,
apply eq_on.trans h2,
apply iter_eq_on_cong,
intros z hz,
have H:= series_eql' ⟨z, hz⟩,
simp only [pi.add_apply, tsub_pos_iff_lt, subtype.coe_mk, one_div, coe_coe] at *,
convert H,
ext1,
apply congr_arg,
ring,
end

lemma exp_comm (n  : ℕ) ( z : ℍ'): exp (2 * ↑π * I * ↑z * n) = exp (2 * ↑π * I * n * z) :=
begin
apply congr_arg,
ring,
end

lemma q_exp_iden (k : ℕ) (hk : 3 ≤ k ) (z : ℍ):  ∑' (d : ℤ), 1/((z : ℂ) + d)^k =
  ((-2 *  ↑π * I)^k/(k-1)!) * ∑' (n : ℕ+), ((n)^(k-1)) *  complex.exp ( 2 *↑π * I * z* n) :=
begin
have := q_exp_iden'' k hk z.2,
simp only [one_div, neg_mul, coe_coe, subtype.val_eq_coe] at *,
have hk2 : ((-1 : ℂ )^(k - 1) *(k - 1 )!)  ≠ 0, by {simp only [nat.factorial_ne_zero, ne.def,
neg_one_pow_mul_eq_zero_iff, nat.cast_eq_zero, not_false_iff]},
rw ←mul_right_inj' hk2,
rw this,
have h3 : (-1) ^ (k - 1) * ↑(k - 1)! * ((-(2 * ↑π * I)) ^ k / ↑(k - 1)!) =  -(2 * ↑π * I)^k,
by {rw mul_div, rw div_eq_mul_one_div, rw div_eq_inv_mul, simp_rw ←mul_assoc, nth_rewrite 1 neg_pow,
 ring_nf, nth_rewrite 1 mul_comm, simp_rw ←mul_assoc, rw mul_inv_cancel, simp,
 have hf : (-1 : ℂ) ^ k * (-1) ^ (k - 1) = -1, by { rw ←pow_add,
 have hkk : k + (k-1) = 2*k - 1, by {rw ←nat.add_sub_assoc,
rw two_mul,
linarith,},
 rw hkk,
 apply odd.neg_one_pow,
 apply nat.even.sub_odd,
  nlinarith,
  rw nat.even_mul,
  left,
  exact even_two,
  exact odd_one,},
 rw mul_assoc,
 rw hf,
 ring,
 norm_cast,
 apply nat.factorial_ne_zero,},
rw ←mul_assoc,
rw h3,
have hee : ∑' (n : ℕ+), (2 * ↑π * I * ((n : ℕ) : ℂ) ) ^ (k - 1) * exp (2 * ↑π * I * ((n : ℕ) : ℂ) * ↑z) =
(2 * ↑π * I)^(k-1) * ∑' (n : ℕ+),  (n) ^ (k - 1) * exp (2 * ↑π * I * ↑z * n), by {
  rw ←tsum_mul_left,
  apply tsum_congr,
  intros b,
  rw ← mul_assoc,
  rw ←mul_pow,
  simp only [coe_coe, mul_eq_mul_left_iff],
  left,
  exact (exp_comm b z).symm,},
rw hee,
rw ←mul_assoc,
have he2 : 2 * ↑π * I * (2 * ↑π * I) ^ (k - 1) = (2 * ↑π * I) ^ (k),
by  {have hke : k = 1 + (k- 1), by {apply symm, apply nat.add_sub_of_le,
linarith},
nth_rewrite 1 hke,
rw pow_add,
simp,},
rw he2,
simp,
end
