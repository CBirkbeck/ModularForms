import mod_forms.Eisenstein_Series.Eisen_is_holo
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import mod_forms.Riemann_zeta_fin
import analysis.calculus.iterated_deriv
import analysis.calculus.series

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)

def Eisenstein_series (k : ℤ) := if h : 3 ≤ k then (Eisenstein_series_is_modular_form k h) else 0

local notation `G[` k `]` :=  (Eisenstein_series k)

def Eisenstein_4 := 60 • G[4]

def Eisenstein_6 := 140 • G[6]

local notation `E₄` := Eisenstein_4

local notation `E₆` := Eisenstein_6

open_locale direct_sum big_operators

local notation `ℍ` := upper_half_plane

def cot (z : ℂ) := (complex.cos z)/(complex.sin z)

lemma cot_series_rep (z : ℍ) : ↑π * cot (↑π* z) - 1/z =
 ∑' (n : ℕ+), (1/(z-n)-1/(z+n)) :=
begin
apply symm,
refine (has_sum.tsum_eq _),
sorry,
end


lemma exp_iter_deriv (n m : ℕ)  :
  iterated_deriv n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s)) =
  (λ t, (2 *↑π * I * m)^n * complex.exp ( 2 *↑π * I * m * t)) :=
begin
induction n with n IH,
simp,
funext x,
rw iterated_deriv_succ,
rw IH,
simp,
ring_exp,
end

lemma upper_ne_int (x : ℍ') (d : ℤ) : (x : ℂ) + d ≠ 0 :=
begin
by_contra,
rw add_eq_zero_iff_eq_neg at h,
have h1: 0 < (x : ℂ).im, by {simp [x.2], exact im_pos x, },
rw h at h1,
simp at h1,
exact h1,
end

lemma aut_iter_deriv (d : ℤ) (k : ℕ) :
  eq_on (iterated_deriv_within k (λ (z : ℂ), 1/(z + d)) ℍ')
    (λ (t : ℂ),  (-1)^k*(k)! * (1/(t + d)^(k+1))) ℍ' :=
begin
intros x hx,
induction k with k IH generalizing x,
simp only [iterated_deriv_within_zero, pow_zero, nat.factorial_zero, algebra_map.coe_one, pow_one,
  one_mul],
rw iterated_deriv_within_succ,
rw deriv_within_congr _ IH,
simp,
rw differentiable_at.deriv_within,
simp,
rw deriv_inv'',
simp only [deriv_pow'', differentiable_at_add_const_iff, differentiable_at_id', nat.cast_add,
  algebra_map.coe_one, nat.add_succ_sub_one, add_zero, deriv_add_const', deriv_id'', mul_one],
rw ←pow_mul,
have : (-((↑k + 1) * (x + ↑d) ^ k) / (x + ↑d) ^ ((k + 1) * 2)) =
  (-((↑k + 1)) / (x + ↑d) ^ ((k + 2))), by {
    rw div_eq_div_iff,
    ring_exp,
    apply  (pow_ne_zero ((k+1)*2) (upper_ne_int ⟨x, hx⟩ d)),
      apply  (pow_ne_zero ((k+2)) (upper_ne_int ⟨x, hx⟩ d))},
rw this,
ring_exp,
simp,
apply  (pow_ne_zero (k+1) (upper_ne_int ⟨x, hx⟩ d)),
apply differentiable_at.const_mul,
apply differentiable_at.inv,
simp,
apply  (pow_ne_zero (k+1) (upper_ne_int ⟨x, hx⟩ d)),
apply is_open.unique_diff_within_at upper_half_plane_is_open hx,
apply IH hx,
repeat {apply is_open.unique_diff_within_at upper_half_plane_is_open hx},
end

lemma aut_iter_deriv' (d : ℤ) (k : ℕ) :
  eq_on (iterated_deriv_within k (λ (z : ℂ), 1/(z - d)) ℍ')
    (λ (t : ℂ),  (-1)^k*(k)! * (1/(t - d)^(k+1))) ℍ' :=
begin
intros x hx,

have h1 : (λ z : ℂ, 1/(z-d)) = (λ z : ℂ, 1/(z + -d)), by {refl},
rw h1,
have h2: x-d= x+ -d, by {refl},
simp_rw h2,
simpa using aut_iter_deriv (-d : ℤ) k hx,
end

lemma iterated_deriv_within_of_is_open (n m : ℕ)  :
  eq_on (iterated_deriv_within n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s)) ℍ')
    (iterated_deriv n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s))) ℍ' :=
begin
 induction n with n IH,
  { assume x hx,
    simp  },
  { assume x hx,
    rw [iterated_deriv_succ, iterated_deriv_within_succ],
    dsimp,
    rw deriv_within_of_open  upper_half_plane_is_open,
    apply filter.eventually_eq.deriv_eq,
    filter_upwards [upper_half_plane_is_open.mem_nhds hx],
    apply IH,
    exact hx,
    apply is_open.unique_diff_within_at upper_half_plane_is_open hx,

    }

end

lemma exp_iter_deriv_within (n m : ℕ)   :
  eq_on (iterated_deriv_within n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s)) ℍ')
  (λ t, (2 *↑π * I * m)^n * complex.exp ( 2 *↑π * I * m * t)) ℍ':=
begin
apply eq_on.trans (iterated_deriv_within_of_is_open n m),
rw eq_on,
intros x hx,
apply congr_fun (exp_iter_deriv n m),
end

lemma exp_iter_deriv_apply (n m : ℕ) (x : ℂ) :
  (iterated_fderiv ℂ n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s))) x (λ(i : fin n), 1) =
   (2 *↑π * I * m)^n * complex.exp ( 2 *↑π * I * m * x) :=
begin
  apply congr_fun (exp_iter_deriv n m),
end

lemma int_nat_sum (f : ℤ → ℂ) : summable f →  summable (λ (x : ℕ), f x)   :=
begin
have : is_compl (set.range (coe : ℕ → ℤ)) (set.range int.neg_succ_of_nat),
  { split,
    { rw disjoint_iff_inf_le,
      rintros _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩ },
    { rw codisjoint_iff_le_sup,
      rintros (i | j) h,
      exacts [or.inl ⟨_, rfl⟩, or.inr ⟨_, rfl⟩] } },
  intro h,
  rw ←@summable_subtype_and_compl _ _ _ _ _ f _ (set.range (coe : ℕ → ℤ))   at h,
  cases h,
  rw ←(equiv.of_injective (coe : ℕ → ℤ) nat.cast_injective).symm.summable_iff ,
  apply summable.congr h_left,
  intro b,
  funext,
  simp_rw equiv.apply_of_injective_symm,
  simp,
  apply congr_arg,
  cases b, cases h_right, cases h_left, cases b_property, induction b_property_h, dsimp at *,
  simp at *,
end

lemma sum_int_even (f : ℤ → ℂ) (hf : ∀ (n : ℤ), f n = f (-n)) (hf2 : summable f) :
 ∑' n, f n = f 0 + 2 * ∑' (n : ℕ+), f n :=
begin
have hpos : has_sum (λ n:ℕ, f(n + 1)) (∑' (n : ℕ+), f n), by {
  have:= (_root_.equiv.pnat_equiv_nat).has_sum_iff,
  simp_rw equiv.pnat_equiv_nat at *,
  simp at *,
  rw ←this,
  have hf3 : summable ((λ (n : ℕ), f (↑n + 1)) ∘ pnat.nat_pred), by {
    have hs : summable (λ (n : ℕ+), f n), by  {apply (int_nat_sum f hf2).subtype},
    apply summable.congr hs,
    intro b, simp, congr, simp },
  rw (summable.has_sum_iff hf3),
  congr,
  funext,
  simp,
  congr,
  norm_cast,
  simp,},
have hneg : has_sum (λ (n : ℕ), f (-n.succ)) (∑' (n : ℕ+), f n), by {
  have h1 : (λ (n : ℕ), f (-↑(n.succ))) = (λ (n : ℕ), f (↑(n.succ))) , by {
    funext,
    apply hf,
  },
  rw h1,
  convert hpos,},

have:=(has_sum.pos_add_zero_add_neg hpos hneg).tsum_eq,
rw this,
ring,
end

def neg_equiv : ℤ ≃ ℤ :=
{to_fun := λ n, -n,
 inv_fun := λ n, -n,
 left_inv := by {apply neg_neg,},
 right_inv:= by {apply neg_neg,},
}

def succ_equiv : ℤ ≃ ℤ :=
{to_fun := λ n, n.succ,
 inv_fun := λ n, n.pred,
 left_inv := by {apply int.pred_succ,},
 right_inv:= by {apply int.succ_pred,},
}

lemma summable_neg (f : ℤ → ℂ) (hf : summable f) : summable (λ d, f (-d)) :=
begin
have h : (λ d, f (-d)) = (λ d, f d) ∘ neg_equiv.to_fun, by {funext,
  simp,
  refl,},
rw h,
have := neg_equiv.summable_iff.mpr hf,
apply this,
end

lemma int_sum_neg (f : ℤ → ℂ) (hf : summable f) : ∑' (d : ℤ), f d = ∑' d, f (-d) :=
begin
have h : (λ d, f (-d)) = (λ d, f d) ∘ neg_equiv.to_fun, by {funext,
  simp,
  refl,},
rw h,
apply symm,
apply neg_equiv.tsum_eq,
exact t2_5_space.t2_space,
end

lemma int_tsum_pnat (f : ℤ → ℂ) (hf2 : summable f) :
  ∑' n, f n = f 0 + (∑' (n : ℕ+), f n) + ∑' (m : ℕ+), f (-m) :=
begin
have hpos : has_sum (λ n:ℕ, f(n + 1)) (∑' (n : ℕ+), f n), by {
  have:= (_root_.equiv.pnat_equiv_nat).has_sum_iff,
  simp_rw equiv.pnat_equiv_nat at *,
  simp at *,
  rw ←this,
  have hf3 : summable ((λ (n : ℕ), f (↑n + 1)) ∘ pnat.nat_pred), by {
    have hs : summable (λ (n : ℕ+), f n), by  {apply (int_nat_sum f hf2).subtype},
    apply summable.congr hs,
    intro b, simp, congr, simp },
  rw (summable.has_sum_iff hf3),
  congr,
  funext,
  simp,
  congr,
  norm_cast,
  simp,},
have hneg : has_sum (λ (n : ℕ), f (-n.succ)) (∑' (n : ℕ+), f (-n)), by {
  have:= (_root_.equiv.pnat_equiv_nat).has_sum_iff,
  simp_rw equiv.pnat_equiv_nat at *,
  rw ←this,
   rw (summable.has_sum_iff _),
   congr,
   funext,
   simp,
   congr,
   simp_rw pnat.nat_pred,
   simp,
   ring,
   exact t2_5_space.t2_space,
   rw equiv.summable_iff,
   have H : summable (λ (d : ℤ), f (d.pred)), by {
    have := succ_equiv.symm.summable_iff.2 hf2,
    apply this},
   have H2:= summable_neg _ H,

   have := int_nat_sum _ H2,
   apply summable.congr this,
   intro b,
   simp,
   congr,
   simp_rw int.pred,
   ring,
   exact add_comm_group.to_add_comm_monoid ℂ,
   exact uniform_space.to_topological_space,
   },
have:=(has_sum.pos_add_zero_add_neg hpos hneg).tsum_eq,
rw this,
ring_nf,

end

lemma ineq11 (x y d: ℝ  ): 0 ≤ d^2*(x^2+y^2)^2-2*d*x*(x^2+y^2)+x^2:=
begin
  have h1: d^2*(x^2+y^2)^2-2*d*x*(x^2+y^2)+x^2 =(d*(x^2+y^2)-x)^2, by {ring,},
  rw h1,
  nlinarith,
end

lemma lowboundd (z : ℍ) (δ : ℝ): ((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2 ≤
  (δ*z.1.1-1)^2+(δ*z.1.2)^2:=
begin
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re],
  have H1: (δ*z.1.1-1)^2+(δ*z.1.2)^2=δ^2*(z.1.1^2+z.1.2^2)-2*δ*z.1.1+1, by {ring,},
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re] at H1,
  rw H1,
  rw div_le_iff,
  simp only,
  have H2: (δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) - 2 * δ *  (z: ℂ).re + 1) *
  ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2=δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2)^3 - 2 * δ *
  (z: ℂ).re* ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2+   ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2,
  by {ring,},
  simp only [upper_half_plane.coe_im, upper_half_plane.coe_re] at H2,
  rw H2,
  rw ← sub_nonneg,
  have H3:( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2-((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=
  ((z: ℂ).re)^2*( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2), by {ring,},
  have H4: δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 3 - 2 * δ *
  (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 + ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 -
  ((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=
  (((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2))*(δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 - 2 * δ *
  (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {ring,},
  simp only [upper_half_plane.coe_im, upper_half_plane.coe_re] at H4,
  rw H4,
  have H5: 0 ≤ (δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 - 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 +
  (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {apply ineq11,},
  have H6: 0 ≤ (((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)), by {nlinarith,},
  apply mul_nonneg H6 H5,
  have H7:= z.property, simp at H7,
  have H8:0 < (z: ℂ).im ^ 2, by {simp only [H7, pow_pos, upper_half_plane.coe_im], },
  have H9: 0 <((z: ℂ).im ^ 2+(z: ℂ).re ^ 2), by {nlinarith,},
  apply pow_two_pos_of_ne_zero,
  nlinarith,
end

lemma rfunt_bnd  (z : ℍ) (δ : ℝ) :
  (rfunct z) ≤ complex.abs ( δ*(z: ℂ) -1):=
begin
  {rw rfunct,
  rw complex.abs,
  simp,
  have H1:  real.sqrt (lb z) ≤
  real.sqrt ((δ*(z: ℂ).re  - 1) * (δ*(z: ℂ).re  - 1) + δ*(z: ℂ).im *  (δ*(z: ℂ).im )),
  by { rw lb,
  rw real.sqrt_le_sqrt_iff,
  have:= lowboundd z δ,
  rw ← pow_two,
  rw ← pow_two,
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re] at *,
  apply this,
  nlinarith,},
  simp only [upper_half_plane.coe_im, upper_half_plane.coe_re] at H1,
  rw norm_sq_apply,
  right,
  simp,
  simp_rw H1,},
end




lemma upbnd (z : ℍ) (d : ℤ) : (d^2 : ℝ) * rfunct(z )^2 ≤ complex.abs (z^2-d^2) :=
begin
by_cases hd : d ≠ 0,
have h1 : (z^2 : ℂ)-d^2 = d^2 * ((1/d^2)* z^2-1), by {ring_nf, simp[hd],},
rw h1,
simp only [one_div, absolute_value.map_mul, complex.abs_pow],
have h2 := rfunt_bnd z (1/d),
have h3 := (Eisenstein_series.auxlem z (1/d)).2,
have h4 := mul_le_mul h2 h3  (rfunct_pos z).le (complex.abs.nonneg _),
rw ←absolute_value.map_mul at h4,
rw ←pow_two at h4,
have h5 : complex.abs ↑d ^ 2 = d^2, by {norm_cast, rw pow_abs, rw abs_eq_self, nlinarith, },
rw h5,
refine mul_le_mul _ _ _ _,
simp,
convert h4,
ring_exp,
simp,
apply pow_nonneg,
apply (rfunct_pos z).le,
nlinarith,
simp at hd,
rw hd,
simp [complex.abs.nonneg],
end

lemma upp_half_not_ints (z : ℍ) (n : ℤ ): (z : ℂ) ≠ n :=
begin
simp,
intro h,
have h1 := upper_half_plane.im_pos z,
have h2 : complex.im (n) = 0, by {exact int_cast_im n,},
rw upper_half_plane.im at h1,
rw h at h1,
rw h2 at h1,
simp at *,
exact h1,
end


lemma abs_pow_two_upp_half (z : ℍ) (n : ℤ) : 0 < complex.abs((z : ℂ)^2 -n^2) :=
begin
simp,
intro h,
have h1 : (z : ℂ)^2-n^2=(z-n)*(z+n), by {ring},
rw h1 at h,
simp at h,
cases h,
have:= upp_half_not_ints z n,
rw sub_eq_zero at h,
apply absurd h this,
have:= upp_half_not_ints z (-n),
rw add_eq_zero_iff_eq_neg at h,
simp at *,
apply absurd h this,

end


lemma lhs_summable (z : ℍ) : summable (λ(n : ℕ+), (1/((z : ℂ)-n)+1/(z+n))) :=
begin
have h1 : (λ n : ℕ+, (1/((z : ℂ)-n)+1/(z+n))) = (λ (n : ℕ+), (2*z)*(1/(z^2-n^2))), by {
  funext,
  field_simp,
  rw one_div_add_one_div,
  ring_nf,
  have h2 :=upp_half_not_ints z (n),
  simp  [h2] at *,
  rw sub_eq_zero,
  exact h2,
  have h1 :=upp_half_not_ints z (-n),
  simp at *,
  rw add_eq_zero_iff_eq_neg,
  exact h1},
rw h1,
apply summable.mul_left,
apply _root_.summable_if_complex_abs_summable,
simp,
have hs : summable (λ (n : ℕ+), (rfunct(z)^2*n^2)⁻¹), by {
simp,
rw ←summable_mul_right_iff,
have h12 : (1 : ℤ) < 2, by {linarith},
have h1 := int_Riemann_zeta_is_summmable 2 h12,
simp_rw rie at h1,
simp_rw one_div at h1,
simp_rw ←coe_coe,
norm_cast at *,
have h3 : (λ (b : ℕ+), (↑b ^ 2)⁻¹) = (λ (b : ℕ+), (((b ^ 2) : ℕ) : ℝ)⁻¹), by {
  funext,
  congr,
  simp,
},
rw h3,
apply h1.subtype,
apply inv_ne_zero,
apply pow_ne_zero,
apply norm_num.ne_zero_of_pos,
apply rfunct_pos,
},
apply summable_of_nonneg_of_le _ _ hs,
intro b,
rw inv_nonneg,
apply complex.abs.nonneg,
intro b,
rw inv_le_inv,
rw mul_comm,
apply upbnd z _,
apply abs_pow_two_upp_half z _,
apply mul_pos,
apply pow_pos,
apply rfunct_pos,
have hb:= b.2,
apply pow_pos,
simp only [coe_coe, nat.cast_pos, pnat.pos],
end

lemma aux_rie_sum (z : ℍ) (k : ℕ) (hk : 2 ≤ k) :
 summable (λ (n : ℕ+), complex.abs (rfunct(z)^k* n^k)⁻¹) :=
begin
simp only [coe_coe, mul_inv_rev, absolute_value.map_mul, map_inv₀, complex.abs_pow, abs_cast_nat,
abs_of_real],
rw ← summable_mul_right_iff,
have hk2 : 1 < (k : ℤ), by {linarith},
have := int_Riemann_zeta_is_summmable k hk2,
rw rie at this,
simp only [int.cast_coe_nat, real.rpow_nat_cast, one_div] at this,
apply this.subtype,
simp,
apply pow_ne_zero,
have hr := (rfunct_pos z),
norm_num,
apply norm_num.ne_zero_of_pos _ hr,
end


lemma lhs_summable_2 (z : ℍ) (k : ℕ) (hk : 2 ≤ k) : summable (λ(n : ℕ+), (1/((z : ℂ)-n)^k)) :=
begin
have := Eise_on_square_is_bounded k z,
have h1 : summable (λ (n : ℕ+), complex.abs (rfunct(z)^k* n^k)⁻¹), by {exact aux_rie_sum z k hk},
apply summable_of_norm_bounded _ h1,
intros i,
simp only [coe_coe, one_div, norm_eq_abs, map_inv₀, complex.abs_pow, mul_inv_rev,
absolute_value.map_mul, abs_cast_nat, abs_of_real],
have h2 := this (i : ℕ) (⟨1,-i⟩: ℤ × ℤ),
simp only [coe_coe, square_mem, int.nat_abs_one, int.nat_abs_neg, int.nat_abs_of_nat,
max_eq_right_iff, algebra_map.coe_one,one_mul, int.cast_neg, int.cast_coe_nat, complex.abs_pow,
absolute_value.map_mul, abs_of_real, abs_cast_nat, mul_inv_rev] at h2,
apply h2,
exact pnat.one_le i,
exact pnat.one_le i,
exact complete_of_proper,

end

lemma lhs_summable_2' (z : ℍ) (k : ℕ) (hk : 2 ≤ k) : summable (λ(n : ℕ+), (1/((z : ℂ)+n)^k)) :=
begin
have := Eise_on_square_is_bounded k z,
have h1 : summable (λ (n : ℕ+), complex.abs (rfunct(z)^k* n^k)⁻¹), by {exact aux_rie_sum z k hk},
apply summable_of_norm_bounded _ h1,
intros i,
simp only [coe_coe, one_div, norm_eq_abs, map_inv₀, complex.abs_pow, mul_inv_rev,
absolute_value.map_mul, abs_cast_nat, abs_of_real],
have h2 := this (i : ℕ) (⟨1,i⟩: ℤ × ℤ),
simp only [coe_coe, square_mem, int.nat_abs_one, int.nat_abs_neg, int.nat_abs_of_nat,
max_eq_right_iff, algebra_map.coe_one,one_mul, int.cast_neg, int.cast_coe_nat, complex.abs_pow,
absolute_value.map_mul, abs_of_real, abs_cast_nat, mul_inv_rev] at h2,
apply h2,
exact pnat.one_le i,
exact pnat.one_le i,
exact complete_of_proper,

end


lemma tsums_added (k : ℕ) (hk : 3 ≤ k)(z : ℍ ):
  ∑' (n : ℕ+), (1/((z : ℂ)-n)^k+1/(z+n)^k) = ∑' (d : ℤ), 1/(z-d)^k :=
begin


sorry,
end



def uexp (n : ℕ) : ℍ' → ℂ :=
λ z, complex.exp ( 2 *↑π * I * z * n)


def funn (K: set ℂ) (hk1 : K ⊆ upper_half_space) (hk2 : is_compact K) : continuous_map K ℂ :={
  to_fun := (λ (r : K),  complex.exp ( 2 *↑π * I * r ))
}

def funn_n (K: set ℂ) (hk1 : K ⊆ upper_half_space) (hk2 : is_compact K) (n k : ℕ) : continuous_map K ℂ :={
  to_fun := (λ (r : K), (2 * π * I * n)^k * complex.exp ( 2 *↑π * I * r ))
}


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




lemma sum_aux (r : ℝ) (hr : r < 1) (hr2 : 0 ≤ r) :
  summable (λ (n : ℕ),  complex.abs (( 2 *↑π * I * n) * r^n)) :=
begin
simp,
have h2ne : (2 : ℝ) ≠ 0, by {exact ne_zero.ne 2},
simp_rw mul_assoc,
rw ←(summable_mul_left_iff h2ne),
rw ←summable_mul_left_iff,
have H : ‖ r ‖ < 1, by {simp  [hr, hr2], rw _root_.abs_of_nonneg hr2, exact hr},
have := summable_norm_pow_mul_geometric_of_norm_lt_1  1 H,
simpa using this,
simpa using real.pi_ne_zero,
end

--EXPERIMENTAL THINGS
lemma cray (n : ℕ) : 0 ≤ 2 * |π| * n :=
begin
apply mul_nonneg,
apply mul_nonneg,
linarith,
simp,
apply nat.cast_nonneg,
end

lemma has_deriv_at_tsum_fun {α : Type*} [ne_bot (at_top : filter (finset α))] (f : α → ℂ → ℂ) {s : set ℂ} (hs : is_open s) (x : ℂ) (hx  : x ∈ s)
   (hf : ∀ (y : ℂ), y ∈ s → summable (λ (n : α), f n y ))
   (hu : ∀ K ⊆ s, is_compact K →
    (∃ (u : α   → ℝ), ( summable u ∧ ∀ (n : α ) (k : K), (complex.abs (deriv (f n) k)) ≤ u n )))
    (hf2 : ∀ (n : α ) (r : s), differentiable_at ℂ (f n) r ):
  has_deriv_at (λ z, ∑' (n : α ), f n z)
    (∑' (n : α ), (deriv (λ z, f n z) x) ) x:=
begin
 have A : ∀ (x : ℂ), x ∈ s→  tendsto (λ (t : finset α ), ∑ n in t, (λ z,f n z) x)
    at_top (𝓝 (∑' (n : α), (λ z, f n z) x)),
  { intros y hy,
    apply summable.has_sum,
    simp,
    apply hf y hy},
 apply has_deriv_at_of_tendsto_locally_uniformly_on hs _ _ A,
 exact hx,
 use (λ n : finset α, λ  a, (∑ i in n, (deriv (λ z, f i z) a) )),
 rw tendsto_locally_uniformly_on_iff_forall_is_compact hs,
 intros K hK1 hK2,
 have HU := hu K hK1 hK2,
  obtain ⟨u, hu1,hu2⟩:= HU,
 apply tendsto_uniformly_on_tsum hu1,
 intros n x hx,
simp,
apply hu2 n ⟨x, hx⟩,
 exact complete_of_proper,
 apply eventually_of_forall,
 intros t r hr,
 apply has_deriv_at.sum,
 intros q w,
 rw has_deriv_at_deriv_iff,
 simp,
 apply hf2 q ⟨r, hr⟩,
end

lemma has_deriv_within_at_tsum_fun {α : Type*} [ne_bot (at_top : filter (finset α))]
  (f : α  → ℂ → ℂ) {s : set ℂ} (hs : is_open s) (x : ℂ) (hx  : x ∈ s)
   (hf : ∀ (y : ℂ), y ∈ s → summable (λ (n : α), f n y ))
   (hu : ∀ K ⊆ s, is_compact K →
    (∃ (u : α → ℝ), ( summable u ∧ ∀ (n : α ) (k : K), (complex.abs (deriv (f n) k)) ≤ u n )))
    (hf2 : ∀ (n : α ) (r : s), differentiable_at ℂ (f n) r ):
  has_deriv_within_at (λ z, ∑' (n : α ), f n z)
    (∑' (n : α ), (deriv (λ z, f n z) x) ) s x:=
begin
exact (has_deriv_at_tsum_fun f hs x hx hf hu hf2).has_deriv_within_at,
end

lemma has_deriv_within_at_tsum_fun' {α : Type*} [ne_bot (at_top : filter (finset α))]
   (f : α  → ℂ → ℂ) {s : set ℂ} (hs : is_open s) (x : ℂ)
  (hx  : x ∈ s)
  (hf : ∀ (y : ℂ), y ∈ s → summable (λ (n : α ), f n y ))
  (hu : ∀ K ⊆ s, is_compact K →
  (∃ (u : α  → ℝ), ( summable u ∧ ∀ (n : α ) (k : K), (complex.abs (deriv (f n) k)) ≤ u n )))
  (hf2 : ∀ (n : α ) (r : s), differentiable_at ℂ (f n) r ):
  has_deriv_within_at (λ z, ∑' (n : α ), f n z)
  (∑' (n : α ), (deriv_within (λ z, f n z) s x) ) s x:=
begin
have := has_deriv_within_at_tsum_fun f hs x hx hf hu hf2,
convert this,
simp,
ext1 n,
apply differentiable_at.deriv_within ,
apply hf2 n ⟨x,hx⟩,
apply (is_open.unique_diff_within_at hs hx),
end

lemma deriv_tsum_fun'  {α : Type*} [ne_bot (at_top : filter (finset α))]
   (f : α  → ℂ → ℂ) {s : set ℂ} (hs : is_open s) (x : ℂ) (hx  : x ∈ s)
   (hf : ∀ (y : ℂ), y ∈ s → summable (λ (n : α ), f n y ))
   (hu : ∀ K ⊆ s, is_compact K →
    (∃ (u : α  → ℝ), ( summable u ∧ ∀ (n : α ) (k : K), (complex.abs (deriv (f n) k)) ≤ u n )))
    (hf2 : ∀ (n : α ) (r : s), differentiable_at ℂ (f n) r ):
  deriv_within (λ z, ∑' (n : α  ), f n z) s x =
    (∑' (n : α ), (deriv_within (λ z, f n z) s x) ):=
begin
apply has_deriv_within_at.deriv_within (has_deriv_within_at_tsum_fun' f hs x hx hf hu hf2)
 (is_open.unique_diff_within_at hs hx),
end

lemma summable_iter_derv' (k : ℕ) (y : ℍ'):
  summable (λ (n : ℕ), (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * y)) :=
begin
apply summable_of_summable_norm,
simp,
have hv1 : ∀ b : ℕ ,   (b : ℝ)^k * (complex.abs (complex.exp ( 2 *↑π * I * y)))^(b : ℕ) =
 b^k * complex.abs (complex.exp ( 2 *↑π * I * b * y)), by {intro b,
  rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf},
simp_rw mul_pow,
have h2ne : (2 : ℝ)^k ≠ 0, by {apply pow_ne_zero, exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw ←(summable_mul_left_iff h2ne),
rw ←(summable_mul_left_iff _),
simp_rw ←mul_assoc,
apply summable.congr _ hv1,
apply summable_pow_mul_geometric_of_norm_lt_1,
simp,
apply exp_upper_half_plane_lt_one,
exact topological_ring.mk,
apply pow_ne_zero,
simpa using real.pi_ne_zero,
end

lemma der_iter_eq_der_aux2 (k n : ℕ) (r : ↥upper_half_space) :
  differentiable_at ℂ (λ (z : ℂ), iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) upper_half_space z) ↑r :=
begin
simp at *,
have hh : differentiable_on ℂ (λ t, (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * t)) ℍ', by {
  apply differentiable.differentiable_on, simp,},
apply differentiable_on.differentiable_at,
apply differentiable_on.congr  hh,
intros x hx,
apply exp_iter_deriv_within k n hx,
apply upper_half_plane_is_open.mem_nhds r.2,
end

lemma der_iter_eq_der2 (k n : ℕ) (r : ↥upper_half_space) :
 deriv (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ') ↑r =
 deriv_within (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ' ) ℍ' ↑r :=
begin
simp,
apply symm,
apply differentiable_at.deriv_within,
apply der_iter_eq_der_aux2,
apply is_open.unique_diff_on upper_half_plane_is_open ,
apply r.2,
end

lemma der_iter_eq_der2' (k n : ℕ) (r : ↥upper_half_space) :
 deriv (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ') ↑r =
 iterated_deriv_within (k+1) (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ'  ↑r :=
begin
rw der_iter_eq_der2 k n r,
rw iterated_deriv_within_succ,
apply is_open.unique_diff_on upper_half_plane_is_open ,
apply r.2,
end


lemma iter_deriv_comp_bound2 (K : set ℂ) (hK1 : K ⊆ ℍ') (hK2 : is_compact K) (k : ℕ) :
(∃ (u : ℕ → ℝ), ( summable u ∧
∀ (n : ℕ) (r : K),
(complex.abs (deriv (iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ') r)) ≤ u n )) :=
begin
  haveI : compact_space K, by {rw ←is_compact_univ_iff, rw is_compact_iff_is_compact_univ at hK2, apply hK2, },
  have hg := bounded_continuous_function.mk_of_compact (funn K hK1 hK2),
  set r : ℝ := ‖bounded_continuous_function.mk_of_compact (funn K hK1 hK2) ‖,
  have hr : ‖ bounded_continuous_function.mk_of_compact (funn K hK1 hK2)‖ < 1,
  by {rw bounded_continuous_function.norm_lt_iff_of_compact,
    intro x, rw bounded_continuous_function.mk_of_compact_apply, simp_rw funn,
    simp only [continuous_map.coe_mk, norm_eq_abs],
    apply exp_upper_half_plane_lt_one ⟨x.1 ,(hK1 x.2)⟩, linarith, },
have hr2 : 0 ≤ r, by {simp only [norm_nonneg], },
  have hu : summable (λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k+1) * r^n)),
 by {
  simp,
  simp_rw mul_pow,
  have h2ne : (2 : ℝ)^(k+1) ≠ 0, by {apply pow_ne_zero, exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw ←(summable_mul_left_iff h2ne),
rw ←(summable_mul_left_iff _),
apply summable_pow_mul_geometric_of_norm_lt_1,
simp at *,
apply hr,
exact topological_ring.mk,
apply pow_ne_zero,
simpa using real.pi_ne_zero,},
refine ⟨λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k+1) * r^n), hu,_⟩,
intros n t,
have go:= (der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩),
simp at *,
simp_rw go,
have h1:= exp_iter_deriv_within (k+1) n (hK1 t.2),
simp only [subtype.coe_mk, absolute_value.map_mul, complex.abs_pow, complex.abs_two, abs_of_real, abs_I, mul_one, abs_cast_nat,
  abs_norm_eq_norm, bounded_continuous_function.norm_mk_of_compact, norm_nonneg, subtype.val_eq_coe] at *,
rw h1,
simp,
have ineqe : complex.abs (complex.exp (2 * π * I * n * t)) ≤ ‖ r ‖^n, by {
  have hw1 : complex.abs (complex.exp (2 * π * I * n * t)) = complex.abs (complex.exp (2 * π * I * t))^n,
  by { rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf,},
  rw hw1,
  apply le_of_pow',
  apply complex.abs.nonneg,
  simp only [norm_nonneg],
  have := bounded_continuous_function.norm_coe_le_norm
    (bounded_continuous_function.mk_of_compact (funn K hK1 hK2)) t,
    simp at *,
   exact this},
apply mul_le_mul,
simp,
simp at ineqe,
convert ineqe,
apply complex.abs.nonneg,
apply pow_nonneg (cray n),
end

lemma iter_deriv_comp_bound3 (K : set ℂ) (hK1 : K ⊆ ℍ') (hK2 : is_compact K) (k : ℕ) :
(∃ (u : ℕ → ℝ), ( summable u ∧
∀ (n : ℕ) (r : K),
( (2 * |π| * n)^k * complex.abs (complex.exp ( 2 *↑π * I * n * r))) ≤ u n )) :=
begin
  haveI : compact_space K, by {rw ←is_compact_univ_iff, rw is_compact_iff_is_compact_univ at hK2,
  apply hK2, },
  have hg := bounded_continuous_function.mk_of_compact (funn K hK1 hK2),
  set r : ℝ := ‖bounded_continuous_function.mk_of_compact (funn K hK1 hK2) ‖,
  have hr : ‖ bounded_continuous_function.mk_of_compact (funn K hK1 hK2)‖ < 1,
  by {rw bounded_continuous_function.norm_lt_iff_of_compact,
    intro x, rw bounded_continuous_function.mk_of_compact_apply, simp_rw funn,
    simp only [continuous_map.coe_mk, norm_eq_abs],
    apply exp_upper_half_plane_lt_one ⟨x.1 ,(hK1 x.2)⟩, linarith, },
have hr2 : 0 ≤ r, by {simp only [norm_nonneg], },
  have hu : summable (λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k) * r^n)),
 by {simp only [absolute_value.map_mul, complex.abs_pow, complex.abs_two, abs_of_real, abs_I,
 mul_one, abs_cast_nat, abs_norm_eq_norm,
  bounded_continuous_function.norm_mk_of_compact],
  simp_rw mul_pow,
  have h2ne : (2 : ℝ)^(k) ≠ 0, by {apply pow_ne_zero, exact ne_zero.ne 2,},
simp_rw mul_assoc,
rw ←(summable_mul_left_iff h2ne),
rw ←(summable_mul_left_iff _),
apply summable_pow_mul_geometric_of_norm_lt_1,
simp at *,
apply hr,
exact topological_ring.mk,
apply pow_ne_zero,
simpa using real.pi_ne_zero,},
refine ⟨λ (n : ℕ),  complex.abs (( 2 *↑π * I * n)^(k) * r^n), hu,_⟩,
intros n t,
have ineqe : complex.abs (complex.exp (2 * π * I * n * t)) ≤ ‖ r ‖^n, by {
  have hw1 : complex.abs (complex.exp (2 * π * I * n * t)) =
    complex.abs (complex.exp (2 * π * I * t))^n,
  by { rw ←complex.abs_pow, congr, rw ←exp_nat_mul, ring_nf,},
  rw hw1,
  apply le_of_pow',
  apply complex.abs.nonneg,
  simp only [norm_nonneg],
  have := bounded_continuous_function.norm_coe_le_norm
    (bounded_continuous_function.mk_of_compact (funn K hK1 hK2)) t,
    simp only [norm_norm, bounded_continuous_function.norm_mk_of_compact, norm_nonneg,
    absolute_value.map_mul, complex.abs_pow,
  complex.abs_two, abs_of_real, abs_I, mul_one, abs_cast_nat, abs_norm_eq_norm,
  bounded_continuous_function.mk_of_compact_apply, norm_eq_abs] at *,
   exact this},
simp only [absolute_value.map_mul, complex.abs_pow, complex.abs_two, abs_of_real,
abs_I, mul_one, abs_cast_nat, abs_norm_eq_norm,
  bounded_continuous_function.norm_mk_of_compact],
apply mul_le_mul,
simp only,
simp only [norm_norm, bounded_continuous_function.norm_mk_of_compact] at ineqe,
convert ineqe,
apply complex.abs.nonneg,
apply pow_nonneg (cray n),
end


lemma exp_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ')  :
  iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' x =
   (∑' (n : ℕ), iterated_deriv_within k (λ (s : ℂ),  complex.exp ( 2 *↑π * I * n * s)) ℍ' x ) :=
begin
induction k with k IH generalizing x,
simp only [iterated_deriv_within_zero],
simp only [subtype.coe_mk] at *,
rw iterated_deriv_within_succ,
have HH: deriv_within (iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' ) ℍ' x =
  deriv_within (λ z,
  (∑' (n : ℕ), iterated_deriv_within k (λ (s : ℂ), complex.exp ( 2 *↑π * I * n * s)) ℍ' z)) ℍ' x,
 by {
  apply deriv_within_congr,
  apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
  intros y hy,
  apply IH ⟨y,hy⟩,
  apply IH x,},
simp only [subtype.coe_mk] at *,
simp_rw HH,
rw deriv_tsum_fun',
simp only,
apply tsum_congr,
intro b,
rw iterated_deriv_within_succ,
apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
exact upper_half_plane_is_open,
exact x.2,
intros y hy,
apply summable.congr (summable_iter_derv' k ⟨y,hy⟩ ),
intro b,
apply symm,
apply exp_iter_deriv_within k b hy,
intros K hK1 hK2,
simp only,
apply iter_deriv_comp_bound2 K hK1 hK2 k,
apply der_iter_eq_der_aux2,
apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
end


lemma exp_series_ite_deriv_uexp'' (k : ℕ) (x : ℍ')  :
  iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' x =
   (∑' (n : ℕ), (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * x)) :=
begin
rw exp_series_ite_deriv_uexp2 k x,
apply tsum_congr,
intro b,
apply exp_iter_deriv_within k b x.2,
end

lemma exp_series_ite_deriv_uexp''' (k : ℕ)   :
  eq_on (iterated_deriv_within k (λ z, ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ')
   (λ (x : ℂ), (∑' (n : ℕ), (2 *↑π * I * n)^k * complex.exp ( 2 *↑π * I * n * x))) ℍ' :=
begin
intros x hx,
apply exp_series_ite_deriv_uexp'' k ⟨x,hx⟩,
end

lemma iter_der_eq_on_cong (f g : ℂ → ℂ) (k : ℕ) (S : set ℂ) (hs : is_open S)
(hfg : eq_on f g S ) : eq_on (iterated_deriv_within k f S) (iterated_deriv_within k g S) S :=
begin
induction k with k IH generalising f g,
simp only [iterated_deriv_within_zero],
apply hfg,
intros x hx,
rw iterated_deriv_within_succ,
rw iterated_deriv_within_succ,
apply deriv_within_congr,
apply is_open.unique_diff_within_at hs hx,
apply IH,
apply IH hx,
all_goals {apply is_open.unique_diff_within_at hs hx},
end


lemma iter_deriv_within_add (k : ℕ) (x : ℍ') (f g : ℂ → ℂ)
(hf : cont_diff_on ℂ k f ℍ')  (hg : cont_diff_on ℂ k g ℍ') :
 iterated_deriv_within k (f + g) ℍ' x =  iterated_deriv_within k f ℍ' x +
  iterated_deriv_within k g ℍ' x :=
begin
simp_rw iterated_deriv_within,
rw iterated_fderiv_within_add_apply,
simp,
apply hf,
apply hg,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,

end


lemma iter_der_within_const_neg (k : ℕ) (hk : 0 < k) (x : ℍ') (c : ℂ) (f : ℂ → ℂ) :
 iterated_deriv_within k (λ z : ℂ, c - f z) ℍ' x =  iterated_deriv_within k (λ z, - f z) ℍ' x :=
begin
simp,
induction k with k IH,
exfalso,
simpa using hk,
rw iterated_deriv_within_succ',
rw iterated_deriv_within_succ',
apply iter_der_eq_on_cong,
apply upper_half_plane_is_open,
intros y hy,
rw deriv_within.neg,
apply deriv_within_const_sub,
repeat {apply is_open.unique_diff_within_at upper_half_plane_is_open hy},
apply x.2,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,
end

lemma iter_der_within_const_mul (k : ℕ)  (x : ℍ') (c : ℂ) (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (c • f) ℍ' x =  c • (iterated_deriv_within k f ℍ' x) :=
begin
simp_rw iterated_deriv_within,
rw iterated_fderiv_within_const_smul_apply,
simp only [continuous_multilinear_map.smul_apply] at *,
apply hf,
apply is_open.unique_diff_on upper_half_plane_is_open,
apply x.2,
end

lemma iter_der_within_const_mul' (k : ℕ)  (x : ℍ') (c : ℂ) (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (λ z, c * f z) ℍ' x =  c * (iterated_deriv_within k f ℍ' x) :=
begin
simpa using (iter_der_within_const_mul k x c f hf),

end


lemma iter_der_within_neg (k : ℕ)  (x : ℍ') (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (-f) ℍ' x =  - (iterated_deriv_within k f ℍ' x) :=
begin
rw neg_eq_neg_one_mul,
nth_rewrite 1 neg_eq_neg_one_mul,
rw ← smul_eq_mul,
rw ← smul_eq_mul,
apply iter_der_within_const_mul k x (-1),
apply hf,
end

lemma iter_der_within_neg' (k : ℕ)  (x : ℍ') (f : ℂ → ℂ)
  (hf : cont_diff_on ℂ k f ℍ') :
 iterated_deriv_within k (λ z, -f z) ℍ' x =  - (iterated_deriv_within k f ℍ' x) :=
begin
convert iter_der_within_neg k x f hf,
end

lemma iter_deriv_within_sub (k : ℕ) (x : ℍ') (f g : ℂ → ℂ)
(hf : cont_diff_on ℂ k f ℍ')  (hg : cont_diff_on ℂ k g ℍ') :
 iterated_deriv_within k (f - g) ℍ' x =  iterated_deriv_within k f ℍ' x -
  iterated_deriv_within k g ℍ' x :=
begin
have h1 : f - g = f + (-g), by {refl},
rw h1,
rw iter_deriv_within_add k x,
rw iter_der_within_neg  k x g hg,
refl,
apply hf,
apply cont_diff_on.neg hg,
end



lemma uexp_cont_diff_on (k n : ℕ) :
cont_diff_on ℂ k (λ(z : ℂ), complex.exp ( 2 *↑π * I * n * z)) ℍ' :=
begin
apply cont_diff.cont_diff_on,
apply cont_diff.cexp,
apply cont_diff.mul,
apply cont_diff_const,
apply cont_diff_id,
end

lemma aut_cont_diff_on (d : ℤ) (k : ℕ): cont_diff_on ℂ k (λ z : ℂ, 1/(z-d)) ℍ' :=
begin
simp,
apply cont_diff_on.inv ,
apply cont_diff_on.sub,
apply cont_diff_on_id,
apply cont_diff_on_const,
intros x hx,
have := upper_ne_int ⟨x, hx⟩ (-d),
convert this,
simp,
refl,
end

lemma continuous_on_tsum'
  {f : ℕ → ℂ → ℂ} {s : set ℂ}  (hf : ∀ i, continuous_on (f i) s) (hs : is_open s)
  (hu : ∀ K ⊆ s, is_compact K →
    (∃ (u : ℕ → ℝ), ( summable u ∧ ∀ (n : ℕ) (k : K), (complex.abs ((f n) k)) ≤ u n ))):
  continuous_on (λ x, ∑' n, f n x) s :=
begin
  have : tendsto_locally_uniformly_on (λ N, (λ x, ∑ n in finset.range N, f n x))
  (λ x, ∑' n, f n x) at_top s, by {
   rw tendsto_locally_uniformly_on_iff_forall_is_compact,
   intros K hK1 hK2,
   have HU := hu K hK1 hK2,
   obtain ⟨u, h1, h2⟩ := HU,
   apply tendsto_uniformly_on_tsum_nat,
   apply h1,
   simp at *,
   intros n x hx,
   apply h2 n ⟨x, hx⟩,
   exact hs,},
  apply this.continuous_on,
  apply (eventually_of_forall _),
  assume t,
  simp,
  apply continuous_on_finset_sum,
  intros i hi,
  apply hf,
end

lemma tsum_uexp_cont_diff_on (k : ℕ) :
cont_diff_on ℂ k (λ(z : ℂ), ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' :=
begin
apply  cont_diff_on_of_differentiable_on_deriv,
intros m hm,
apply differentiable_on.congr _ (exp_series_ite_deriv_uexp''' m),
intros x hx,
apply has_deriv_within_at.differentiable_within_at,
apply has_deriv_within_at_tsum_fun _ (upper_half_plane_is_open),
apply hx,
intros y hy,
apply summable_iter_derv' m ⟨y, hy⟩,
intros K hK1 hK2,
have := iter_deriv_comp_bound3 K hK1 hK2 (m+1),
obtain ⟨u, hu, hu2⟩ := this,
refine ⟨u, hu, _⟩,
intros n r,
have HU2 := hu2 n r,
simp,
apply le_trans _ HU2,
apply le_of_eq,
ring_exp,
intros n r,
apply differentiable.differentiable_at,
simp only [differentiable.mul, differentiable_const, differentiable.cexp, differentiable_id'],
exact at_top_ne_bot,
end


lemma iter_der_within_add (k : ℕ+) (x : ℍ') :
iterated_deriv_within k
  (λ z, ↑π * I - (2 *  ↑π * I) • ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)) ℍ' x =
  -(2 *  ↑π * I)*∑' (n : ℕ), (2 *  ↑π * I*n)^(k : ℕ) *complex.exp ( 2 *↑π * I * n * x) :=
begin
rw iter_der_within_const_neg k k.2 x,
simp,
have := iter_der_within_neg' k x (λ z, (2 *  ↑π * I) • ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)),
simp at this,
rw this,
rw neg_eq_neg_one_mul,
have t2:=  iter_der_within_const_mul' k x (2 *  ↑π * I)
  (λ z,  ∑' (n : ℕ), complex.exp ( 2 *↑π * I * n * z)),
simp at t2,
rw t2,
simp,
have h3:= exp_series_ite_deriv_uexp'' k x,
simp at h3,
left,
apply h3,
apply tsum_uexp_cont_diff_on k,
have := cont_diff_on.const_smul (2 *  ↑π * I) (tsum_uexp_cont_diff_on k),
simpa using this,
end



lemma iter_div_aut_add (d : ℤ) (k : ℕ) :
 eq_on (iterated_deriv_within k (λ z : ℂ, 1/(z-d) + 1/(z+d)) ℍ')
  ((λ (t : ℂ),  (-1)^k*(k)! * (1/(t - d)^(k+1))) +
  (λ (t : ℂ),  (-1)^k*(k)! * (1/(t + d)^(k+1)))) ℍ' :=
begin
intros x hx,
have h1 : (λ z : ℂ, 1/(z-d) + 1/(z+d))  = (λ z : ℂ, 1/(z-d)) + (λ (z : ℂ),  1/(z+d)), by {refl},
rw h1,
have:= iter_deriv_within_add k ⟨x, hx⟩ (λ z : ℂ, 1/(z-d)) (λ z : ℂ, 1/(z+d)),
simp at *,
rw this,
have h2 := aut_iter_deriv d k hx,
have h3:= aut_iter_deriv' d k hx,
simp at *,
rw [h2, h3],
have h4:= aut_cont_diff_on d k,
simp at h4,
apply h4,
have h5 := aut_cont_diff_on (-d) k,
simp at h5,
apply h5,
end

lemma summable_iter_aut  (k : ℕ) (z : ℍ):
 summable (λ (n : ℕ+), iterated_deriv_within k (λ (z : ℂ), (1/(z-(n))+1/(z+(n)))) ℍ' z) :=
begin
have :=λ (d : ℕ+), (iter_div_aut_add d k z.2),
simp only [coe_coe, subtype.coe_mk, int.cast_coe_nat, subtype.val_eq_coe,
  pi.add_apply] at *,
rw summable_congr this,
by_cases hk : 1 ≤ k,
apply summable.add,
rw ←summable_mul_left_iff,
apply lhs_summable_2 z (k+1),
linarith,
simp only [ne.def, neg_one_pow_mul_eq_zero_iff, nat.cast_eq_zero],
apply nat.factorial_ne_zero ,
rw ←summable_mul_left_iff,
apply lhs_summable_2' z (k+1),
linarith,
simp only [ne.def, neg_one_pow_mul_eq_zero_iff, nat.cast_eq_zero],
apply nat.factorial_ne_zero ,
simp at hk,
simp_rw hk,
simp,
simpa using (lhs_summable z),
end


#exit

lemma aut_series_ite_deriv_uexp2 (k : ℕ) (x : ℍ')  :
  iterated_deriv_within k (λ (z : ℂ), ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n)))) ℍ' x =
   (∑' (n : ℕ+), iterated_deriv_within k (λ (z : ℂ), (1/(z-(n))+1/(z+(n)))) ℍ' x ) :=
begin
induction k with k IH generalizing x,
simp only [iterated_deriv_within_zero],
simp only [subtype.coe_mk] at *,
rw iterated_deriv_within_succ,
have HH:
deriv_within (iterated_deriv_within k (λ (z : ℂ),∑' (n : ℕ+), (1/(z-(n))+1/(z+(n)))) ℍ' ) ℍ' x =
deriv_within (λ z,
  (∑' (n : ℕ+), iterated_deriv_within k (λ (z : ℂ), (1/(z-(n))+1/(z+(n)))) ℍ' z)) ℍ' x,
 by {
  apply deriv_within_congr,
  apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
  intros y hy,
  apply IH ⟨y,hy⟩,
  apply IH x,},
simp only [subtype.coe_mk] at *,
simp_rw HH,
simp,
rw deriv_tsum_fun',
simp only,
apply tsum_congr,
intro b,
rw iterated_deriv_within_succ,
apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
exact upper_half_plane_is_open,
exact x.2,
intros y hy,
simpa using (summable_iter_aut k ⟨y, hy⟩),
/-
have :=λ (d : ℕ+), (iter_div_aut_sub d k hy),
simp at this,
rw summable_congr this,
apply summable.sub,
rw ←summable_mul_left_iff,
have hs1:= summablemente_nat_pos (k+1),-/
all_goals{sorry},

/-apply summable.congr (summable_iter_derv' k ⟨y,hy⟩ ),
intro b,
apply symm,
apply exp_iter_deriv_within k b hy,
intros K hK1 hK2,
simp only,
apply iter_deriv_comp_bound2 K hK1 hK2 k,
apply der_iter_eq_der_aux2,
apply (is_open.unique_diff_within_at upper_half_plane_is_open x.2 ),
-/

end

#exit
lemma aux_iter_der_tsum (k : ℕ) (hk : 3 ≤ k) (x : ℍ') :
iterated_deriv_within k ((λ (z : ℂ), 1/z) +(λ (z : ℂ), ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n))))) ℍ' x =
((-1)^(k : ℕ) *(k : ℕ)!) * ∑' (n : ℤ), 1/((x : ℂ) + n)^(k +1 : ℕ) :=
begin
rw iter_deriv_within_add,
have h1 := aut_iter_deriv 0 k x.2,
simp at *,
rw h1,
all_goals{sorry},
end




#exit

lemma series_eql (z : ℍ) :   ↑π * I- (2 *  ↑π * I)* ∑' (n : ℕ), complex.exp ( 2 *↑π * I * z * n) =
  1/z + ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n))) :=
begin
sorry,
end



lemma q_exp_iden (k : ℕ) (hn : 2 ≤ k ) (z : ℍ):  ∑' (d : ℤ), 1/((z : ℂ) + d)^k =
  ((-2 *  ↑π * I)^k/(k-1)!) * ∑' (n : ℕ+), ((n)^(k-1)) *  complex.exp ( 2 *↑π * I * z* n) :=
begin


sorry,
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

lemma tsum_pnat (f : ℕ → ℂ) (hf : f 0 = 0) : ∑' (n : ℕ+), f n = ∑' n, f n :=
begin
by_cases hf2: summable f,
rw tsum_eq_zero_add,
rw hf,
simp,
have hpos : has_sum (λ n:ℕ, f(n + 1)) (∑' (n : ℕ+), f n), by {
  have:= (_root_.equiv.pnat_equiv_nat).has_sum_iff,
  simp_rw equiv.pnat_equiv_nat at *,
  simp at *,
  rw ←this,
  have hf3 : summable ((λ (n : ℕ), f (n + 1)) ∘ pnat.nat_pred), by {
    have hs : summable (λ (n : ℕ+), f n), by  {apply (hf2).subtype},
    apply summable.congr hs,
    intro b, simp,},
  rw (summable.has_sum_iff hf3),
  congr,
  funext,
  simp,},
apply symm,
apply hpos.tsum_eq,
apply hf2,
have h1 := tsum_eq_zero_of_not_summable hf2,
rw ←(nat_pos_tsum2 f hf) at hf2,
have h2:= tsum_eq_zero_of_not_summable hf2,
simp [h1,h2],
end

lemma neg_even_pow (n : ℤ) (k : ℕ) (hk : even k) : (-n)^k = n^ k :=
begin
exact even.neg_pow hk n,
end



lemma complex_rie_summable (k : ℕ) (hk : 3 ≤ k) :
  summable (λ (n : ℕ), (( n : ℂ)^k)⁻¹) :=
begin
have hk1: 1 < (k : ℤ), by {linarith},
have H:= int_Riemann_zeta_is_summmable k hk1,
rw rie at H,
simp_rw inv_eq_one_div,
have H2: (λ (n : ℕ), 1/(n : ℂ)^k)=  (coe : ℝ → ℂ) ∘ (λ n, 1/ ((n : ℝ))^k), by {
  funext,
  simp},
rw H2,
rw coe_summable,
apply summable.congr H,
intro b,
simp,
end



lemma prod_sum (f : ℤ × ℤ → ℂ) (hf : summable f) : summable (λ a, ∑' b, f ⟨a,b⟩ ) :=
begin
have := equiv.summable_iff (equiv.sigma_equiv_prod ℤ ℤ) ,
rw ←this at hf,
have H:= summable.sigma hf,
simp at H,
apply summable.congr H,
intro b,
simp,
end





lemma summable_factor (n : ℤ) (z : ℍ)  (k : ℕ) (hk : 3 ≤ k) :
  summable (λ (d : ℤ), ((-((n : ℂ)*z) +d)^k)⁻¹) :=
begin
have H := Eis_summ k hk z,
have H2:= H.prod_factor (-n),
simp at *,
exact H2,
end

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
norm_cast,
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
have h1 := Eis_summ k hk z,
apply prod_sum _ h1,
apply Eis_summ k hk z,
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



lemma nat_pos_tsum' (ξ : ℂ) :  summable (λ n : ℕ, ξ ^ n) → summable (λ n : ℕ+, ξ ^ (n : ℕ)) :=
begin
intro h,
apply h.subtype,
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
