import mod_forms.Eisen_is_holo
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import mod_forms.Riemann_zeta_fin

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topological_space big_operators nat

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

lemma cot_series_rep (z : ℂ) : ↑π * cot (↑π* z) =
1/z + ∑' (n : ℕ), (1/(z-(n+1))-1/(z+(n+1))) :=
begin
sorry,
end

lemma series_eql (z : ℂ) :   ↑π * I- (2 *  ↑π * I)* ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) =
  1/z + ∑' (n : ℕ), (1/(z-(n+1))-1/(z+(n+1))) :=
begin
sorry,
end

lemma q_exp_iden (k : ℕ) (hn : 2 ≤ k ) (z : ℍ):  ∑' (d : ℤ), 1/((z : ℂ) + d)^k =
  ((-2 *  ↑π * I)^k/(k-1)!) * ∑' (n : ℕ), ((n+1)^(k-1)) *  complex.exp ( 2 *↑π * I * z* n) :=
begin
sorry,
end

lemma q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2: even k) (z : ℍ):
∑' (x : ℤ × ℤ),  1/(((x.1 : ℂ)*z+x.2)^k) = 2 * (Riemann_zeta k) +
  2 * (∑' (c : ℕ), (∑' (d : ℤ), 1/(c*z + d)^k)) :=
begin
rw Riemann_zeta,
sorry,
end


def sigma_fn (k n : ℕ) : ℤ := ∑ (d : ℕ)  in nat.divisors n, d^k

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

lemma Eisen_q_exp (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : even k) (z : ℍ) :
  (Eisenstein_series k) z =  2* (Riemann_zeta k) +
  2 * ((-2 *  ↑π * I)^k/(k-1)!) * ∑' (n : ℕ),  (sigma_fn (k-1) (n+1))*(complex.exp ( 2 *↑π * I * z * n)) :=
begin
rw eisen_iden k hk hk2,
rw Eisenstein_series_of_weight_,
simp_rw Eise,
norm_cast at hk,
have:= q_exp_iden_2 k hk hk2 z,
norm_cast,
rw this,
simp,
have :=q_exp_iden k _ _,
sorry,
sorry,
sorry,
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
have hk : 3 ≤ 4, by {linarith},
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
have r3 : ∑' (n : ℕ),  ↑(sigma_fn (3) (n+1))*(complex.exp ( 2 *↑π * I * I * n)) =
  ∑' (n : ℕ),  (sigma_fn (3) (n+1))*(complex.exp ( -2 *↑π * n)),
by{congr', funext, simp, left, convert (r2 n), ring},
rw r3 at H3,
norm_cast at H3,
have H4 : 0 ≤ ∑' (n : ℕ), (↑(sigma_fn 3 (n + 1)) * real.exp (↑(-2 : ℤ) * π * ↑n)),
by {apply tsum_nonneg, intro b, apply mul_nonneg, norm_cast, apply sigma_fn_nonneg, apply (real.exp_pos _).le,},

have H5: 0 < 2 * Riemann_zeta 4,
by {apply mul_pos, linarith, apply Riemann_zeta_pos, linarith,},

let ε := (2 * Riemann_zeta 4) +
  ((2 * (16 * π ^ 4 / ↑((2 + 1) * 2))))* ∑' (n : ℕ), (↑(sigma_fn 3 (n + 1)) * real.exp (↑(-2 : ℤ) * π * ↑n)),

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
