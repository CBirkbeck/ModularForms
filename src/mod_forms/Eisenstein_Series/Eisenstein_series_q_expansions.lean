import mod_forms.Eisenstein_Series.Eisen_is_holo
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import mod_forms.Riemann_zeta_fin
import analysis.calculus.iterated_deriv
import analysis.calculus.series
import mod_forms.Eisenstein_Series.tsum_lemmas
import mod_forms.Eisenstein_Series.iterated_deriv_lemmas
import mod_forms.Eisenstein_Series.exp_summable_lemmas
import mod_forms.Eisenstein_Series.auxp_lemmas
import mod_forms.Eisenstein_Series.cot_iden
import mod_forms.Eisenstein_Series.q_exp_aux

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)


def Eisenstein_Series_of_wt_ (k : ℤ) := if h : 3 ≤ k then (Eisenstein_series_is_modular_form k h) else 0

local notation `G[` k `]` :=  (Eisenstein_Series_of_wt_ k)

def Eisenstein_4 := 60 • G[4]

def Eisenstein_6 := 140 • G[6]

local notation `E₄` := Eisenstein_4

local notation `E₆` := Eisenstein_6


open_locale direct_sum big_operators

local notation `ℍ` := upper_half_plane


lemma q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2: even k) (z : ℍ):
∑' (x : ℤ × ℤ),  1/(((x.1 : ℂ)*z+x.2)^k) = 2 * (Riemann_zeta k) +
  2 * (∑' (c : ℕ+), (∑' (d : ℤ), 1/(c*z + d)^k)) :=
begin
rw Riemann_zeta,
rw tsum_prod,
rw sum_int_even,
simp only [algebra_map.coe_zero, zero_mul, zero_add, one_div, coe_coe, int.cast_coe_nat, add_left_inj],
rw rie,
rw sum_int_even,
simp only [algebra_map.coe_zero, coe_coe, int.cast_coe_nat, real.rpow_nat_cast, one_div],
have h0 : ((0 : ℂ)^k)⁻¹ = 0, by {convert inv_zero, norm_cast, apply zero_pow', linarith,},
have h00 : ((0^k : ℕ) : ℝ)⁻¹ = 0, by {convert inv_zero, norm_cast, apply zero_pow', linarith,},
rw h0,
simp only [zero_add, mul_eq_mul_left_iff, bit0_eq_zero, one_ne_zero, or_false],
rw ←tsum_coe,
rw ←tsum_pnat,
congr,
funext,
norm_cast,
simp only [of_real_inv, of_real_nat_cast],
norm_cast,
apply h00,
intro n,
apply congr_arg,
apply symm,
norm_cast,
apply even.neg_pow hk2,
have H := int_Riemann_zeta_is_summmable k _,
rw rie at H,
apply summable_int_of_summable_nat,
apply complex_rie_summable k hk,
have HG : (λ (n : ℕ), (((-(n: ℤ)): ℂ)^k)⁻¹) =  (λ (n : ℕ), ((n : ℂ)^k)⁻¹),
  by {funext,
    apply congr_arg,
    rw ←coe_coe,
    apply even.neg_pow hk2},
simp only [int.cast_neg, int.cast_coe_nat, real.rpow_nat_cast, one_div, real.summable_nat_pow_inv] at *,
rw HG,
apply complex_rie_summable k hk,
norm_cast,
linarith,
intro n,
simp only [one_div, int.cast_neg, neg_mul],
apply symm,
rw int_sum_neg,
congr,
funext,
simp only [int.cast_neg, inv_inj],
ring_nf,
convert even.neg_pow hk2 ((z : ℂ)* n + d),
ring,
apply summable_factor n z k hk,
have h1 := Eisenstein_series_is_summable k z hk,

apply prod_sum _ h1,
apply Eisenstein_series_is_summable k z hk,
end


def sigma_fn (k n : ℕ) : ℕ := ∑ (d : ℕ)  in nat.divisors n, d^k

def sigma_fn' (k n : ℕ) : ℕ := ∑ (d : ℕ)  in nat.divisors n, (n/d)^k

lemma sigma_fn_eql (k n : ℕ) : sigma_fn k n = sigma_fn' k n :=
begin
simp_rw sigma_fn,
simp_rw sigma_fn',
rw ←nat.sum_div_divisors,
end

def sigma' (k n : ℕ) : ℤ:= ∑ x in nat.divisors_antidiagonal n, x.1^k

lemma sigme_fn_one (k : ℕ) : sigma_fn k 1 = 1 :=
begin
rw sigma_fn,
rw nat.divisors_one,

simp_rw finset.sum_singleton,
simp,
end

lemma sigma_fn_nonneg (k n: ℕ) : 0 ≤ sigma_fn k n :=
begin
rw sigma_fn,
apply finset.sum_nonneg,
intros i hi,
apply pow_nonneg,
linarith,
end

lemma eisen_iden (k : ℕ) (hk : 3 ≤  (k : ℤ)) (hk2 : even k) (z : ℍ):
(Eisenstein_Series_of_wt_ k) z = Eisenstein_series_of_weight_ k  z :=
begin
simp_rw Eisenstein_Series_of_wt_,
simp [hk],
rw Eisenstein_series_is_modular_form,
simp_rw Eisenstein_is_slash_inv,
refl,
end



instance nat_pos_mul : mul_action ℕ+ ℍ :=
{ smul := λ x z, upper_half_plane.mk (x  * z) $ by {simp, apply z.2},
  one_smul := λ z, by {simp, },
  mul_smul := λ x y z, by {dsimp, simp, simp_rw ←mul_assoc, } }

lemma auxnpm (c: ℕ+) (z : ℍ) : (((c • z) : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) :=
begin
refl,
end




lemma ine (a b k: ℕ) (hb : 0 < b) (h : a ≤ b): a^k ≤ 2* b^(k+1):=
begin
have h1 : a^k ≤ b^k, by {exact pow_mono_right k h,},
apply le_trans h1,
have h2: b^k ≤ b^(k+1), by {apply nat.pow_le_pow_of_le_right hb, linarith,},
apply le_trans h2,
apply le_mul_of_one_le_left,
apply pow_nonneg,
simp only [zero_le'],
linarith,
end




lemma ineqauxx (z : ℍ) (k : ℕ) (n : (Σ (x : ℕ+), nat.divisors_antidiagonal x))  :
 ‖(  (n.2.1.1 : ℂ)^k * complex.exp ( 2 *↑π * I * z * n.2.1.1*n.2.1.2))‖
 ≤ complex.abs (2* n.1^(k+1) * complex.exp ( 2 *↑π * I * z * n.1) ) :=
 begin
simp,
have hn := n.2.2,
simp at *,
norm_cast,
simp_rw ←hn,
have gt : ∀ (a b : ℕ), ((a * b : ℕ) : ℂ)= (a : ℂ) * (b : ℂ ), by {exact nat.cast_mul,},
rw gt,
rw ←mul_assoc,
simp,
rw (mul_le_mul_right _),
have J := nat.fst_mem_divisors_of_mem_antidiagonal n.2.2,
simp at J,
have J2:= nat.le_of_dvd _ J,
norm_cast,
apply ine,
apply n.1.2,
exact J2,
apply n.1.2,
exact real.has_zero,
exact ordered_semiring.to_mul_pos_mono,
exact mul_pos_reflect_lt.to_mul_pos_mono_rev,
simp,
apply complex.exp_ne_zero,
 end




lemma anti_diag_card_le  (n : ℕ+) : (nat.divisors_antidiagonal n).card ≤ n^2 :=
begin
classical!,
simp_rw nat.divisors_antidiagonal,
apply le_trans (finset.card_filter_le _  _),
simp,
rw pow_two,
end

lemma summable1 {k : ℕ} (z : ℍ)  :  summable (λ (p : Σ (b : ℕ+), ↥(nat.divisors_antidiagonal b)),
  ((sigma_antidiagonal_equiv_prod p).fst : ℂ) ^ k *
    exp (2 * ↑π * I * ↑z * ((sigma_antidiagonal_equiv_prod p).fst) * ((sigma_antidiagonal_equiv_prod p).snd))) :=
begin
have :=summable_of_norm_bounded _ _ (ineqauxx z k),
apply this,
rw summable_sigma_of_nonneg,
split,
apply (λ n, (has_sum_fintype _).summable) ,
exact fintype_of_option,
simp only [coe_coe, absolute_value.map_mul, complex.abs_two, complex.abs_pow, abs_cast_nat],
apply summable_of_nonneg_of_le _ _ (@summable_pow_mul_exp (k+2) z),
intro x,
rw tsum_fintype,
simp only [finset.univ_eq_attach, finset.sum_const, finset.card_attach, nsmul_eq_mul],
norm_cast,
apply mul_nonneg,
exact (nat.divisors_antidiagonal x).card.cast_nonneg,
apply mul_nonneg,
simp only [nat.cast_mul, nat.cast_bit0, algebra_map.coe_one, zero_le_mul_right, nat.cast_pos,
  pnat.pos, zero_le_bit0, zero_le_one],
apply complex.abs.nonneg,
intro b,
rw tsum_fintype,
simp only [finset.univ_eq_attach, finset.sum_const, finset.card_attach, nsmul_eq_mul, coe_coe,
  absolute_value.map_mul, complex.abs_two, complex.abs_pow, abs_cast_nat],
have hk : 2 * (b : ℝ) ^ (k + 2 + 1) * complex.abs (exp (2 * ↑π * I * ↑z * b)) =
  b^2 * (2 * b ^ (k + 1) * complex.abs (exp (2 * ↑π * I * ↑z * b))) , by {ring_exp},
simp_rw ←coe_coe,
rw hk,
have ht := anti_diag_card_le b,
refine mul_le_mul _ _ _ _,
simp only [coe_coe],
norm_cast,
apply ht,
refine eq.le _,
refl,
simp only [coe_coe, zero_le_mul_left, zero_lt_mul_right, pow_pos, nat.cast_pos, pnat.pos,
zero_lt_bit0, zero_lt_one, map_nonneg],
nlinarith,
intro x,
apply complex.abs.nonneg,

end

lemma sum_sigma_fn_eq  {k : ℕ} (z : ℍ) :
  ∑' (c  : ℕ+ × ℕ+), (c.1^k : ℂ) * (complex.exp ( 2 *↑π * I * z * c.1 * c.2)) =
  ∑' (e : ℕ+),
    ∑ (x : nat.divisors_antidiagonal e),  x.1.1^k * complex.exp ( 2 *↑π * I * z * x.1.1*x.1.2) :=
begin
rw ←sigma_antidiagonal_equiv_prod.tsum_eq,
rw tsum_sigma',
congr,
funext,
rw tsum_fintype,
congr,
apply (λ n, (has_sum_fintype _).summable),
exact fintype_of_option,
apply summable1,
exact t2_5_space.t2_space,
end

lemma div_mul_aux  {k : ℕ} (z : ℍ) (n : ℕ) :
  ∑ (x : ℕ) in n.divisors, ↑(n/x) ^ k * exp (2 * (↑π * (I * (↑z * ( ↑(n / x) * ↑x ))))) =
  ∑ (x : ℕ) in n.divisors, ↑(n/x) ^ k * exp (2 * (↑π * (I * (↑z * n)))) :=
begin
apply finset.sum_congr,
refl,
funext,
intros x hx,
congr,
norm_cast,
apply nat.div_mul_cancel,
rw nat.mem_divisors at hx,
exact hx.1,
end


lemma sum_sigma_fn_eqn  {k : ℕ} (z : ℍ) :
 ∑' (c  : ℕ+ × ℕ+), (c.1^k : ℂ) * (complex.exp ( 2 *↑π * I * z * c.1 * c.2)) =
  ∑' (e : ℕ+), (sigma_fn k e)* complex.exp ( 2 *↑π * I * z * e) :=
begin
simp_rw sigma_fn_eql,
rw sum_sigma_fn_eq z,
congr,
funext,
rw sigma_fn',
have :=nat.sum_divisors_antidiagonal' (λ x, λ y, ((x) : ℂ)^k* complex.exp ( 2 *↑π * I * z * x* y)),
simp only [subtype.val_eq_coe, nat.cast_sum, nat.cast_pow, coe_coe] at *,
simp_rw mul_assoc at *,
rw div_mul_aux _ _ at this,

rw ← coe_coe,
have hr : (∑ (x : ℕ) in (e : ℕ).divisors, ↑(↑e / x) ^ k) * exp (2 * (↑π * (I * (↑z * ↑e)))) =
  ∑ (x : ℕ) in (e : ℕ).divisors, ↑(↑e / x) ^ k * exp (2 * (↑π * (I * (↑z * (e : ℕ))))) , by {
    rw ←coe_coe,
    apply finset.sum_mul,},
rw hr,
rw ← this,
have := sumaux  (λ x, ((x.1) : ℂ)^k* complex.exp ( 2 *↑π * I * z * x.1* x.2)) e,
convert this,
repeat{
funext,
simp_rw mul_assoc},
end

lemma a1 {k : ℕ} (e : ℕ+)  (z : ℍ) :
  summable (λ (c : ℕ+), (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * ↑z * e * c)) :=
begin
  have h2ne : (e : ℂ)^(k-1) ≠ 0, by {apply pow_ne_zero, simp,},
  rw (summable_mul_left_iff h2ne),
  have hv1 : ∀ (b : ℕ+),  (complex.exp ( 2 *↑π * I * z * e * b)) =
    ( (complex.exp ( 2 *↑π * I * z * e)))^(b : ℕ), by {intro b,
      rw ←exp_nat_mul, ring_nf},
  simp_rw hv1,
  apply nat_pos_tsum',
  simp only [coe_coe, summable_geometric_iff_norm_lt_1, norm_eq_abs],
  have hv2 : ∀ (b : ℕ+), complex.abs (complex.exp ( 2 *↑π * I * z * b)) =
    (complex.abs (complex.exp ( 2 *↑π * I * z)))^(b : ℕ), by {intro b,
    rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf},
  simp only [coe_coe, ne.def] at *,
  rw hv2 e,
  apply pow_lt_one,
  apply complex.abs.nonneg,
  apply exp_upper_half_plane_lt_one,
  simp only [ne.def, pnat.ne_zero, not_false_iff],
end

lemma a2 {k : ℕ} (e : ℕ+)  (z : ℍ) :
  summable (λ (c : ℕ+), (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * c*  ↑z * e)) :=
begin
  have := @a1 k e z,
  convert this,
  funext,
  simp only [coe_coe, mul_eq_mul_left_iff],
  left,
  ring_nf,
end

lemma a3 {k : ℕ} (h : 2 ≤ k) (e : ℕ+)  (z : ℍ) :
  summable (λ (c : ℕ+), (c : ℂ) ^ (k - 1) * exp (2 * ↑π * I * e*  ↑z * c)) :=
begin
  have hv1 : ∀ (b : ℕ+),  (complex.exp ( 2 *↑π * I * e *z * b)) =
    ( (complex.exp ( 2 *↑π * I * e * z)))^(b : ℕ), by {intro b,
    rw ←exp_nat_mul, ring_nf},
  simp_rw hv1,
  simp_rw coe_coe,
  have lj :=nat_pos_tsum2 (λ (x : ℕ), (x : ℂ)^(k-1)* ( (complex.exp ( 2 *↑π * I * e * z)))^x ),
  simp only [algebra_map.coe_zero, coe_coe, pow_zero, mul_one, zero_pow_eq_zero,
    tsub_pos_iff_lt] at lj,
  have hk : 1 < k, by {linarith,},
  have hl:= lj hk,
  simp only [coe_coe] at *,
  have H:= summable_pow_mul_geometric_of_norm_lt_1 (k-1) ,
  have H2:= hl.2 (H _),
  exact H2,
  simp only [norm_eq_abs],
  have hv2 : ∀ (b : ℕ+), complex.abs (complex.exp ( 2 *↑π * I * b * z)) =
    (complex.abs (complex.exp ( 2 *↑π * I * z)))^(b : ℕ), by {intro b,
    rw ←complex.abs_pow, congr, rw ←exp_nat_mul, simp, rw ←mul_assoc, ring_nf,},
  simp only [norm_eq_abs, coe_coe] at *,
  rw hv2 e,
  apply pow_lt_one,
  apply complex.abs.nonneg,
  apply exp_upper_half_plane_lt_one,
  simp only [ne.def, pnat.ne_zero, not_false_iff],
  exact complete_of_proper,
end

lemma a4 {k : ℕ} (z : ℍ) :
  summable (uncurry (λ (b c : ℕ+), ↑b ^ (k - 1) * exp (2 * ↑π * I * ↑c * ↑z * ↑b))) :=
begin
  rw summable_mul_prod_iff_summable_mul_sigma_antidiagonall,
  rw uncurry,
  simp,
  have:= @summable1 (k-1) z,
  rw sigma_antidiagonal_equiv_prod at this,
  simp at *,
  convert this,
  funext,
  simp_rw mapdiv,
  have hg : 2 * ↑π * I * x.2.1.2 * ↑z * x.2.1.1 =
    2 * ↑π * I * z* x.2.1.1 * x.2.1.2, by {simp,ring,},
  simp at *,
  left,
  rw hg,
end


lemma Eisenstein_Series_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : even k) (z : ℍ) :
  (Eisenstein_Series_of_wt_ k) z =  2* (Riemann_zeta k) +
  2 * ((-2 *  ↑π * I)^k/(k-1)!) * ∑' (n : ℕ+),  (sigma_fn (k-1) (n))*(complex.exp ( 2 *↑π * I * z * n)) :=
begin
  rw eisen_iden k hk hk2,
  rw Eisenstein_series_of_weight_,
  simp_rw Eise,
  norm_cast at hk,
  have:= q_exp_iden_2 k hk hk2 z,
  have t2:=q_exp_iden k _ ,
  have t4 : (∑' (c : ℕ+), (∑' (d : ℤ), 1/(((((c • z) : ℍ) : ℂ) + d)^k))) =
  ∑' (e : ℕ+), ((-2 *  ↑π * I)^k/(k-1)!) * ∑' (n : ℕ+), ((n)^(k-1))*complex.exp ( 2 *↑π * I * e *z* n),
  by { congr, funext, rw t2 (c • z : ℍ),  rw auxnpm c z, rw ←mul_assoc, },
  norm_cast,
  rw this,
  simp only [auxnpm, coe_coe, one_div, of_real_mul, of_real_bit0, int.cast_neg, int.cast_bit0, algebra_map.coe_one, neg_mul,
    of_real_neg, add_right_inj] at *,
  rw mul_assoc,
  congr,
  rw t4,
  simp only,
  rw tsum_mul_left,
  apply congr_arg,
  have H := @sum_sigma_fn_eqn (k-1) z,
  simp_rw ←coe_coe ,
  rw ←H,
  rw tsum_comm',
  rw tsum_prod',
  simp only [coe_coe],
  congr',
  funext,
  congr,
  funext,
  have ho :2 * ↑π * I * c * ↑z * b = 2 * ↑π * I * z * b * c , by {ring},
  simp at ho,
  rw ho,
  rw summable_mul_prod_iff_summable_mul_sigma_antidiagonall,
  apply summable1,
  intro e,
  simp,
  apply a1,
  exact a4 z,
  intro b,
  apply a2,
  intro c,
  apply a3,
  repeat{linarith},
end


lemma I_pow_4 : I^4 = 1 :=
begin
simp only [I_pow_bit0, neg_one_sq],
end





lemma auxeq (r : ℝ) (hr : 0 < r) : (r : ℂ) ≠ 0 :=
begin
  by_contra,
  rw complex.ext_iff at h,
  simp at h,
  rw h at hr,
  simp at hr,
  exact hr,
end

lemma ineq : 0 ≤ 16 * π ^ 4 / ((2 + 1) * 2) :=
begin
apply div_nonneg,
simp,
apply pow_nonneg,
apply real.pi_pos.le,
linarith,
end

lemma Eisen_4_non_zero : G[(4 : ℕ)] ≠ 0 :=
begin
by_contra,
have H : (G[(4 : ℕ)] : ℍ → ℂ) = 0, by {simp only [h, coe_zero]},
rw funext_iff at H,
have H2 := H (⟨I, by {simp only [I_im, zero_lt_one]}⟩ : ℍ),
have hk : 3 ≤ (4 : ℤ), by {linarith},
have hk2 : even 4, by {simp only [even_bit0]},
have H3 := Eisenstein_Series_q_expansion 4 hk hk2 (⟨I, by {simp}⟩ : ℍ),
simp only [pi.zero_apply] at H2,

have r1 : ((-2 *  ↑π * I)^4/(4-1)!)= (16 * π^4)/(3!), by {ring_exp, rw I_pow_4, simp only [one_mul],},
rw r1 at H3,
have r2 : ∀ (n : ℤ),
  complex.exp ( 2 *↑π * I * I * n) = complex.exp (-2 * π * n),
by {intro n, simp only [neg_mul], congr, have : 2 * ↑π * I * I * ↑n = 2 * ↑π * (I * I) * ↑n, by {ring}, rw this, rw I_mul_I, ring,},
simp only [nat.cast_bit0, algebra_map.coe_one, nat.factorial_succ, nat.factorial_two, nat.cast_mul, nat.cast_add,
  nat.succ_sub_succ_eq_sub, tsub_zero, subtype.coe_mk] at H3,
have r3 : ∑' (n : ℕ+),  ↑(sigma_fn (3) (n))*(complex.exp ( 2 *↑π * I * I * n)) =
  ∑' (n : ℕ+),  (sigma_fn (3) (n))*(complex.exp ( -2 *↑π * n)),
by{congr', funext, simp, left, convert (r2 n), ring},
rw r3 at H3,
norm_cast at H3,
have H4 : 0 ≤ ∑' (n : ℕ+), (↑(sigma_fn 3 (n)) * real.exp (↑(-2 : ℤ) * π * ↑n)),
by {apply tsum_nonneg, intro b, apply mul_nonneg, norm_cast, apply sigma_fn_nonneg, apply (real.exp_pos _).le,},

have H5: 0 < 2 * Riemann_zeta 4,
by {apply mul_pos, linarith, apply Riemann_zeta_pos, linarith,},

let ε := (2 * Riemann_zeta 4) +
  ((2 * (16 * π ^ 4 / ↑((2 + 1) * 2))))* ∑' (n : ℕ+), (↑(sigma_fn 3 (n)) * real.exp (↑(-2 : ℤ) * π * ↑n)),

have H7: G[(4 : ℕ)] (⟨I, by {simp only [I_im, zero_lt_one]}⟩ : ℍ) = ↑ε,
  by {rw H3,},

 have H5: 0 < ε,
 by{ apply left.add_pos_of_pos_of_nonneg H5, apply mul_nonneg, simp, apply ineq, apply H4,
 },

have H8:=auxeq ε H5,
rw ←H7 at H8,
apply absurd H8,
simpa using H2,
end
