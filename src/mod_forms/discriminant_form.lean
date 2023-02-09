import mod_forms.Eisen_is_holo
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import mod_forms.Riemann_zeta_fin

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat

def Eisenstein_series (k : ℤ) := if h : 3 ≤ k then (Eisenstein_series_is_modular_form k h) else 0

local notation `G[` k `]` :=  (Eisenstein_series k)

def Eisenstein_4 := 60 • G[4]

def Eisenstein_6 := 140 • G[6]

local notation `E₄` := Eisenstein_4

local notation `E₆` := Eisenstein_6

def discriminant_form : modular_form ⊤ 12 := (E₄).mul ((E₄).mul E₄) - 27 • ((E₆).mul E₆)

open_locale direct_sum big_operators

local notation `ℍ` := upper_half_plane

example  : comm_ring (⨁ (n : ℤ),  modular_form ⊤ n) := by apply_instance


variable (v :(⨁ (n : ℕ),  modular_form ⊤ n))

def E4:= direct_sum.of _ 4 Eisenstein_4

def E6:= direct_sum.of _ 6 Eisenstein_6

lemma gmul_eq_mul {a b : ℤ} (f : modular_form ⊤ a) (g : modular_form ⊤ b) :
  graded_monoid.ghas_mul.mul f g = f.mul g :=
begin
refl,
end

def Delta := E4^3-27*E6^2

lemma eqvs_of_defs : direct_sum.of _ 12 discriminant_form = Delta :=
begin
  rw Delta,
  rw E4,
  rw E6,
  rw discriminant_form,
  simp only [map_sub, map_nsmul, nsmul_eq_mul, nat.cast_bit1, nat.cast_bit0, algebra_map.coe_one],
  congr,
  rw pow_three,
  simp_rw direct_sum.of_mul_of,
  simp_rw gmul_eq_mul,
  congr,
  rw pow_two,
  simp_rw direct_sum.of_mul_of,
  simp_rw gmul_eq_mul,
  congr,
end

def cot (z : ℂ) := (complex.cos z)/(complex.sin z)

lemma cot_series_rep (z : ℍ) : ↑π * cot (↑π* z) - 1/z =
 ∑' (n : ℕ+), (1/(z-n)-1/(z+n)) :=
begin
apply symm,
refine (has_sum.tsum_eq _),
sorry,
end

lemma series_eql (z : ℂ) :   ↑π * I- (2 *  ↑π * I)* ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) =
  1/z + ∑' (n : ℕ), (1/(z-(n+1))-1/(z+(n+1))) :=
begin
sorry,
end

lemma q_exp_iden (k : ℕ) (hn : 2 ≤ k ) (z : ℍ):  ∑' (d : ℤ), 1/((z : ℂ) + d)^k =
  ((-2 *  ↑π * I)^k/(k-1)!) * ∑' (n : ℕ+), ((n)^(k-1)) *  complex.exp ( 2 *↑π * I * z* n) :=
begin
sorry,
end

lemma q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2: even k) (z : ℍ):
∑' (x : ℤ × ℤ),  1/(((x.1 : ℂ)*z+x.2)^k) = 2 * (Riemann_zeta k) +
  2 * (∑' (c : ℕ+), (∑' (d : ℤ), 1/(c*z + d)^k)) :=
begin
rw Riemann_zeta,
sorry,
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
(Eisenstein_series k) z = Eisenstein_series_of_weight_ k  z :=
begin
simp_rw Eisenstein_series,
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

def mapdiv (n : ℕ+) : (nat.divisors_antidiagonal n) → ℕ+ × ℕ+ :=
begin
intro x,
have h1 := x.1.1,
have h11:= nat.fst_mem_divisors_of_mem_antidiagonal x.2,
have h111:= nat.pos_of_mem_divisors h11,
have h2 := x.1.2,
have h22:= nat.snd_mem_divisors_of_mem_antidiagonal x.2,
have h222:= nat.pos_of_mem_divisors h22,
set n1 : ℕ+ := ⟨x.1.1, h111⟩,
set n2 : ℕ+ := ⟨x.1.2, h222⟩,
use ⟨n1,n2⟩,
end

variable (f : Σ (n : ℕ+), nat.divisors_antidiagonal n)


def sigma_antidiagonal_equiv_prod : (Σ (n : ℕ+), nat.divisors_antidiagonal n) ≃ ℕ+ × ℕ+ :=
{ to_fun := λ x, mapdiv x.1 x.2,
  inv_fun := λ x, ⟨⟨x.1.1 * x.2.1, by {apply mul_pos x.1.2 x.2.2} ⟩, ⟨x.1,x.2⟩,
    by {rw nat.mem_divisors_antidiagonal, simp, }⟩,
  left_inv :=
    begin
      rintros ⟨n, ⟨k, l⟩, h⟩,
      rw nat.mem_divisors_antidiagonal at h,
      simp_rw mapdiv,
      simp only [h, pnat.mk_coe, eq_self_iff_true, subtype.coe_eta, true_and],
      cases h, cases n, dsimp at *, induction h_left, refl,
    end,
  right_inv := by {
    rintros ⟨n, ⟨k, l⟩, h⟩,
    simp_rw mapdiv,
    exfalso,
    simp only [not_lt_zero'] at h,
    exact h,
    simp_rw mapdiv,
    simp only [eq_self_iff_true, subtype.coe_eta],}, }




lemma ine (a b k: ℕ) (h : a ≤ b): a^k ≤ 2* b^(k+1):=
begin
have h1 : a^k ≤ b^k, by {exact pow_mono_right k h,},
apply le_trans h1,
have h2: b^k ≤ b^(k+1), by {sorry,},
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
exact J2,
apply n.1.2,
exact real.has_zero,
exact ordered_semiring.to_mul_pos_mono,
exact mul_pos_reflect_lt.to_mul_pos_mono_rev,
simp,
apply complex.exp_ne_zero,
 end

#exit

lemma summable_mul_prod_iff_summable_mul_sigma_antidiagonall {f  : ℕ+ × ℕ+ → ℂ} :
  summable (λ x : ℕ+ × ℕ+, f x ) ↔
  summable (λ x : (Σ (n : ℕ+), nat.divisors_antidiagonal n), f ⟨(mapdiv x.1 x.2).1,  (mapdiv x.1 x.2).2⟩) :=
begin
simp_rw mapdiv,
apply  sigma_antidiagonal_equiv_prod.summable_iff.symm,
end





lemma nat_pos_tsum (f : ℕ → ℝ) (hf : f 0 = 0 ) : summable (λ (x : ℕ+), f x) ↔   summable f :=
begin
rw function.injective.summable_iff,
simp,
exact pnat.coe_injective,
intros x hx,
simp at hx,
rw hx,
exact hf,

end

lemma nat_pos_tsum2 (f : ℕ → ℂ) (hf : f 0 = 0 ) : summable (λ (x : ℕ+), f x) ↔  summable f :=
begin
rw function.injective.summable_iff,
simp,
exact pnat.coe_injective,
intros x hx,
simp at hx,
rw hx,
exact hf,

end

lemma nat_pos_tsum' (ξ : ℂ) :  summable (λ n : ℕ, ξ ^ n) → summable (λ n : ℕ+, ξ ^ (n : ℕ)) :=
begin
intro h,
apply h.subtype,
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


lemma summable_pow_mul_exp  {k : ℕ} (z : ℍ) :
  summable (λ (i : ℕ+), complex.abs (2 * ↑i ^ (k + 1) * exp (2 * ↑π * I * ↑z * ↑i))) :=
begin
simp,
have h2ne : (2 : ℝ) ≠ 0, by {exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw ←(summable_mul_left_iff h2ne),
simp_rw ←coe_coe,
have hv1 : ∀ (b : ℕ+), complex.abs (complex.exp ( 2 *↑π * I * z * b)) =
  (complex.abs (complex.exp ( 2 *↑π * I * z)))^(b : ℕ), by {intro b,
  rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf},
simp_rw ←mul_assoc,
simp_rw hv1,
simp_rw coe_coe,
have lj :=nat_pos_tsum (λ (x : ℕ), (x : ℝ)^(k+1)* (complex.abs (complex.exp ( 2 *↑π * I * z)))^x ),
simp at lj,
rw lj,
apply summable_pow_mul_geometric_of_norm_lt_1,
simp,
apply exp_upper_half_plane_lt_one,
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

lemma sumaux (f : ℕ × ℕ → ℂ) (e : ℕ+) : ∑ (x : nat.divisors_antidiagonal e), f x =
  ∑ (x : ℕ × ℕ) in nat.divisors_antidiagonal e, f x :=
begin
simp only [finset.univ_eq_attach],
apply finset.sum_finset_coe,
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

lemma djhg (a b c : ℂ) (h : a = b) : c*a=c*b :=
begin
exact congr_arg (has_mul.mul c) h
end

lemma a1 {k : ℕ} (e : ℕ+)  (z : ℍ) : summable (λ (c : ℕ+), (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * ↑z * e * c)) :=
begin

have h2ne : (e : ℂ)^(k-1) ≠ 0, by {apply pow_ne_zero, simp,},
rw ←(summable_mul_left_iff h2ne),

have hv1 : ∀ (b : ℕ+),  (complex.exp ( 2 *↑π * I * z * e * b)) =
  ( (complex.exp ( 2 *↑π * I * z * e)))^(b : ℕ), by {intro b,
    rw ←exp_nat_mul, ring_nf},
simp_rw hv1,
apply nat_pos_tsum',
simp,
have hv2 : ∀ (b : ℕ+), complex.abs (complex.exp ( 2 *↑π * I * z * b)) =
  (complex.abs (complex.exp ( 2 *↑π * I * z)))^(b : ℕ), by {intro b,
  rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf},
simp at *,
rw hv2 e,
apply pow_lt_one,
apply complex.abs.nonneg,
apply exp_upper_half_plane_lt_one,
simp,
end

lemma a2 {k : ℕ} (e : ℕ+)  (z : ℍ) : summable (λ (c : ℕ+), (e : ℂ) ^ (k - 1) * exp (2 * ↑π * I * c*  ↑z * e)) :=
begin
have := @a1 k e z,
convert this,
funext,
simp,
left,
ring_nf,
end

lemma a3 {k : ℕ} (h : 2 ≤ k) (e : ℕ+)  (z : ℍ) : summable (λ (c : ℕ+), (c : ℂ) ^ (k - 1) * exp (2 * ↑π * I * e*  ↑z * c)) :=
begin

have hv1 : ∀ (b : ℕ+),  (complex.exp ( 2 *↑π * I * e *z * b)) =
  ( (complex.exp ( 2 *↑π * I * e * z)))^(b : ℕ), by {intro b,
   rw ←exp_nat_mul, ring_nf},

simp_rw hv1,
simp_rw coe_coe,
have lj :=nat_pos_tsum2 (λ (x : ℕ), (x : ℂ)^(k-1)* ( (complex.exp ( 2 *↑π * I * e * z)))^x ),
simp at lj,
have hk : 1 < k, by {linarith,},
have hl:= lj hk,
simp at *,



have H:= summable_pow_mul_geometric_of_norm_lt_1 (k-1) ,

have H2:= hl.2 (H _),
exact H2,
simp,
have hv2 : ∀ (b : ℕ+), complex.abs (complex.exp ( 2 *↑π * I * b * z)) =
  (complex.abs (complex.exp ( 2 *↑π * I * z)))^(b : ℕ), by {intro b,
  rw ←complex.abs_pow, congr, rw ←exp_nat_mul, simp, rw ←mul_assoc, ring,},
simp at *,
rw hv2 e,
apply pow_lt_one,
apply complex.abs.nonneg,
apply exp_upper_half_plane_lt_one,
simp,
exact complete_of_proper,
end

lemma a4 {k : ℕ} (z : ℍ) :  summable (uncurry (λ (b c : ℕ+), ↑b ^ (k - 1) * exp (2 * ↑π * I * ↑c * ↑z * ↑b))) :=
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


lemma Eisen_q_exp (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : even k) (z : ℍ) :
  (Eisenstein_series k) z =  2* (Riemann_zeta k) +
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

lemma embedding_coer : embedding (coe : ℝ → ℂ) :=
begin
apply isometry.embedding,
apply isometry_of_real,
end

@[norm_cast] lemma tendsto_coe { α : Type*} {f : filter α} {m : α → ℝ} {a : ℝ} :
  tendsto (λa, (m a : ℂ)) f (𝓝 ↑a) ↔ tendsto m f (𝓝 a) :=
embedding_coer.tendsto_nhds_iff.symm


@[simp, norm_cast] lemma coe_finset_sum { α : Type*} {s : finset α} {f : α → ℝ} :
  ↑(∑ a in s, f a) = (∑ a in s, f a : ℂ) :=
of_real.map_sum f s

@[norm_cast] protected lemma has_sum_coe { α : Type*} {f : α → ℝ} {r : ℝ} :
  has_sum (λa, (f a : ℂ)) ↑r ↔ has_sum f r :=
have (λs:finset α, ∑ a in s, ↑(f a)) = (coe : ℝ → ℂ) ∘ (λs:finset α, ∑ a in s, f a),
  from funext $ assume s, coe_finset_sum.symm,
by unfold has_sum; rw [this, tendsto_coe]

protected lemma tsum_coe_eq { α : Type*} {f : α → ℝ} {r : ℝ} (h : has_sum f r) : ∑'a, (f a : ℂ) = r :=
(has_sum_coe.2 h).tsum_eq

protected lemma coe_tsum { α : Type*} {f : α → ℝ} : summable f → ↑(tsum f) = ∑'a, (f a : ℂ)
| ⟨r, hr⟩ := by rw [hr.tsum_eq, tsum_coe_eq hr]


lemma coe_summable { α : Type*} (f : α → ℝ) : summable ((coe : ℝ → ℂ) ∘ f) ↔ summable f :=
begin
  apply summable.map_iff_of_left_inverse complex.of_real complex.re_add_group_hom,
  exact complex.continuous_of_real,
  exact complex.continuous_re,
  intro, refl,
end


lemma tsum_coe { α : Type*} (f : α → ℝ) :   ∑' i, (f i : ℂ) = ((∑' i, f i) : ℝ) :=
begin
by_cases hf : summable f,
apply (coe_tsum hf).symm,
have := tsum_eq_zero_of_not_summable hf,
rw this,
simp,
have h2:= coe_summable f,
apply tsum_eq_zero_of_not_summable,
rw h2,
apply hf,


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
have H3 := Eisen_q_exp 4 hk hk2 (⟨I, by {simp}⟩ : ℍ),
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
  by {rw H3, simp only [of_real_mul, of_real_bit0, nat.cast_mul, nat.cast_add, nat.cast_bit0,
  algebra_map.coe_one, of_real_div, of_real_add,
  int.cast_neg, int.cast_bit0, neg_mul, of_real_int_cast, of_real_exp, of_real_neg, of_real_nat_cast, add_right_inj,
  mul_eq_mul_left_iff, mul_eq_zero, bit0_eq_zero, one_ne_zero, div_eq_zero_iff, pow_eq_zero_iff, nat.succ_pos',
  of_real_eq_zero, false_or, or_false], left, norm_cast, apply tsum_coe,},

 have H5: 0 < ε,
 by{ apply left.add_pos_of_pos_of_nonneg H5, apply mul_nonneg, simp, apply ineq, apply H4,
 },

have H8:=auxeq ε H5,
rw ←H7 at H8,
apply absurd H8,
simpa using H2,
end
