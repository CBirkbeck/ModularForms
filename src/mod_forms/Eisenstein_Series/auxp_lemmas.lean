import data.complex.exponential
import analysis.calculus.iterated_deriv
import analysis.calculus.series
import mod_forms.Eisenstein_Series.tsum_lemmas
import for_mathlib.mod_forms2
import mod_forms.holomorphic_functions
import analysis.complex.upper_half_plane.basic
import mod_forms.Eisenstein_Series.Eisen_is_holo
import mod_forms.Eisenstein_Series.iterated_deriv_lemmas

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set  metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ` := upper_half_plane
local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)



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


/-
lemma exp_iter_deriv_apply (n m : ℕ) (x : ℂ) :
  (iterated_fderiv ℂ n (λ (s : ℂ), complex.exp ( 2 *↑π * I * m * s))) x (λ(i : fin n), 1) =
   (2 *↑π * I * m)^n * complex.exp ( 2 *↑π * I * m * x) :=
begin
  apply congr_fun (exp_iter_deriv n m),
end
-/

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


/-
lemma tsums_added (k : ℕ) (hk : 3 ≤ k)(z : ℍ ):
  ∑' (n : ℕ+), (1/((z : ℂ)-n)^k+1/(z+n)^k) = ∑' (d : ℤ), 1/(z-d)^k :=
begin
sorry,
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
-/

--EXPERIMENTAL THINGS




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

/-
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

-/




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


lemma mem_uhs (x : ℂ) : x ∈ ℍ'.1 ↔ 0 < x.im :=
begin
refl,
end


lemma compact_in_slice' (S : set  ℂ) (hne : set.nonempty S) (hs : S ⊆ ℍ') (hs2 : is_compact S) :
  ∃ (A B : ℝ), 0 < B ∧ (image (inclusion hs) ⊤)  ⊆ (upper_half_space_slice A B) :=
begin
have hcts:  continuous_on (λ t, complex.im t) S, by {
apply continuous.continuous_on, continuity,},
have := is_compact.exists_forall_le hs2 hne hcts,
obtain ⟨b, hb, HB⟩:= this,
have hh : is_compact (image (inclusion hs) ⊤), by {apply is_compact.image_of_continuous_on,
 simp, exact is_compact_iff_is_compact_univ.mp hs2, apply (continuous_inclusion hs).continuous_on, },
let  t := (⟨complex.I, by {simp,} ⟩ : ℍ),
have hb2:=  bounded.subset_ball_lt  hh.bounded 0 t,
obtain ⟨r, hr, hr2⟩ := hb2,
refine ⟨r + 1, b.im,_ ⟩,
split,
have hbim := hs hb,
simp only [subtype.coe_mk] at hbim,
rw mem_uhs b at hbim,
exact hbim,
intros z hz,
simp only [slice_mem, subtype.val_eq_coe, coe_re, abs_of_real, coe_im, ge_iff_le, top_eq_univ,
  image_univ, range_inclusion,mem_set_of_eq] at *,
split,
have hr3 := hr2 hz,
simp only [mem_closed_ball] at hr3,
apply le_trans (abs_re_le_abs z),
  have:= complex.abs.sub_le (z : ℂ) (t : ℂ) 0,
simp only [sub_zero, subtype.coe_mk, abs_I] at this,
have hds: dist z t = complex.abs((z : ℂ) - t), by {refl},
rw hds at hr3,
apply le_trans this,
simp only [add_le_add_iff_right],
apply hr3,
have hbz := HB (z : ℂ) hz,
convert hbz,
simp,
have hhf := hs hz,
simp at hhf,
rw mem_uhs _ at hhf,
apply hhf.le,
end

lemma diff_on_aux (k : ℕ) (n : ℕ+):
  differentiable_on ℂ  ((λ (t : ℂ),  (-1 : ℂ)^k*(k)! * (1/(t - n)^(k+1))) +
  (λ (t : ℂ),  (-1)^k*(k)! * (1/(t + n)^(k+1)))) ℍ' :=
begin
apply differentiable_on.add,
apply differentiable_on.const_mul,
apply differentiable_on.div,
apply differentiable_on_const,
apply differentiable_on.pow,
simp only [subtype.coe_mk, differentiable_on_sub_const_iff],
apply differentiable_on_id,
intros x hx,
apply pow_ne_zero,
have := upper_ne_int ⟨x, hx⟩ (-n : ℤ),
simp at *,
exact this,
apply differentiable_on.const_mul,
apply differentiable_on.div,
apply differentiable_on_const,
apply differentiable_on.pow,
simp only [subtype.coe_mk, differentiable_on_add_const_iff],
apply differentiable_on_id,
intros x hx,
apply pow_ne_zero,
have := upper_ne_int ⟨x, hx⟩ (n : ℤ),
simp at *,
exact this,
end

lemma diff_at_aux (s : ℍ') (k : ℕ) (n : ℕ+) : differentiable_at ℂ
  (λ (z : ℂ), iterated_deriv_within k (λ (z : ℂ), (z - ↑n)⁻¹ + (z + ↑n)⁻¹) upper_half_space z) ↑s :=
begin
 have := iter_div_aut_add n k,
 apply differentiable_on.differentiable_at,
 apply differentiable_on.congr (diff_on_aux k n),
 intros r hr,
 have ht := this hr,
 simp at *,
 apply ht,
 apply is_open.mem_nhds,
 apply upper_half_plane_is_open,
 apply s.2,
end

lemma der_of_iter_der (s : ℍ'.1) (k : ℕ) (n : ℕ+):
    (deriv (λ (z : ℂ), iterated_deriv_within k (λ (z : ℂ), (z - (n : ℂ))⁻¹ + (z + n)⁻¹)
    upper_half_space z) s) =   (-1)^(k+1)*(k+1)! * (1/(s - n)^(k+2)) +
  (-1)^(k+1)*(k+1)! * (1/(s + n)^(k+2)) :=
begin
 have h: (deriv (λ (z : ℂ), iterated_deriv_within k (λ (z : ℂ), (z - (n : ℂ))⁻¹ + (z + n)⁻¹)
    upper_half_space z) s) =
    (deriv_within (λ (z : ℂ), iterated_deriv_within k (λ (z : ℂ), (z - (n : ℂ))⁻¹ + (z + n)⁻¹)
    upper_half_space z) ℍ' s), by {apply symm, apply differentiable_at.deriv_within,
    apply diff_at_aux,
    apply is_open.unique_diff_on upper_half_plane_is_open ,
    apply s.2,},
rw h,
simp,
rw ←iterated_deriv_within_succ,
have h2 :=iter_div_aut_add n (k+1) s.2,
simp at h2,
exact h2,
apply is_open.unique_diff_on upper_half_plane_is_open ,
apply s.2,
end

lemma rfunct_abs_pos (z : ℍ') : 0  < |(rfunct(z))| :=
begin
have := rfunct_pos z,
simp,
linarith,

end


lemma sub_bound (s : ℍ'.1)  (A B : ℝ) (hB : 0 < B) (hs : s ∈ upper_half_space_slice A B)
(k : ℕ) (n : ℕ+) : complex.abs ((-1)^(k+1)*(k+1)! * (1/(s - n)^(k+2)))
 ≤  complex.abs (((k+1)!)/(rfunct(lbpoint A B hB))^(k+2))* ((rie (k+2)) n) :=
begin
simp only [nat.factorial_succ, nat.cast_mul, nat.cast_add, algebra_map.coe_one, coe_coe, one_div,
absolute_value.map_mul, complex.abs_pow, absolute_value.map_neg, absolute_value.map_one, one_pow,
abs_cast_nat, one_mul, map_inv₀, map_div₀, abs_of_real],
rw div_eq_mul_inv,
simp_rw mul_assoc,
rw mul_le_mul_left,
rw mul_le_mul_left,
have hk : 1 ≤ k+2, by {linarith},
have := Eise_on_square_is_bounded'' (k+2) s n hk ⟨1,-(n : ℤ) ⟩,
simp only [int.nat_abs, coe_coe, square_mem, int.nat_abs_one, int.nat_abs_neg, int.nat_abs_of_nat, max_eq_right_iff,
  algebra_map.coe_one, one_mul, int.cast_neg, int.cast_coe_nat, complex.abs_pow, absolute_value.map_mul, abs_of_real,
  abs_cast_nat, mul_inv_rev] at this,
have hn : 1 ≤ (n : ℕ), by { have hn2:= n.2, norm_cast, exact pnat.one_le n, },
have ht := this hn,
apply le_trans ht,
simp_rw rie,
rw div_eq_mul_inv,
nth_rewrite 1 mul_comm,
simp,
norm_cast,
rw mul_le_mul_left,
rw inv_le_inv,
apply pow_le_pow_of_le_left,
apply (rfunct_abs_pos _).le,
have hss := rfunct_lower_bound_on_slice A B hB ⟨s, hs⟩,
rw abs_of_pos (rfunct_pos _),
rw abs_of_pos (rfunct_pos _),
apply hss,
apply pow_pos (rfunct_abs_pos _),
apply pow_pos (rfunct_abs_pos _),
rw inv_pos,
norm_cast,
apply pow_pos,
linarith,
norm_cast,
apply nat.factorial_pos,
simp only [absolute_value.pos_iff, ne.def],
norm_cast,
linarith,
end

lemma add_bound (s : ℍ'.1)  (A B : ℝ) (hB : 0 < B) (hs : s ∈ upper_half_space_slice A B)
(k : ℕ) (n : ℕ+) : complex.abs ((-1)^(k+1)*(k+1)! * (1/(s + n)^(k+2)))
 ≤  complex.abs (((k+1)!)/(rfunct(lbpoint A B hB))^(k+2))* ((rie (k+2)) n) :=
begin
simp only [nat.factorial_succ, nat.cast_mul, nat.cast_add, algebra_map.coe_one, coe_coe, one_div,
absolute_value.map_mul, complex.abs_pow, absolute_value.map_neg, absolute_value.map_one, one_pow,
abs_cast_nat, one_mul, map_inv₀, map_div₀, abs_of_real],
rw div_eq_mul_inv,
simp_rw mul_assoc,
rw mul_le_mul_left,
rw mul_le_mul_left,
have hk : 1 ≤ k+2, by {linarith},
have := Eise_on_square_is_bounded'' (k+2) s n hk ⟨1,(n : ℤ) ⟩,
simp only [int.nat_abs, coe_coe, square_mem, int.nat_abs_one, int.nat_abs_neg, int.nat_abs_of_nat, max_eq_right_iff,
  algebra_map.coe_one, one_mul, int.cast_neg, int.cast_coe_nat, complex.abs_pow, absolute_value.map_mul, abs_of_real,
  abs_cast_nat, mul_inv_rev] at this,
have hn : 1 ≤ (n : ℕ), by { have hn2:= n.2, norm_cast, exact pnat.one_le n, },
have ht := this hn,
apply le_trans ht,
simp_rw rie,
rw div_eq_mul_inv,
nth_rewrite 1 mul_comm,
simp,
norm_cast,
rw mul_le_mul_left,
rw inv_le_inv,
apply pow_le_pow_of_le_left,
apply (rfunct_abs_pos _).le,
have hss := rfunct_lower_bound_on_slice A B hB ⟨s, hs⟩,
rw abs_of_pos (rfunct_pos _),
rw abs_of_pos (rfunct_pos _),
apply hss,
apply pow_pos (rfunct_abs_pos _),
apply pow_pos (rfunct_abs_pos _),
rw inv_pos,
norm_cast,
apply pow_pos,
linarith,
norm_cast,
apply nat.factorial_pos,
simp only [absolute_value.pos_iff, ne.def],
norm_cast,
linarith,
end


lemma upper_bnd_summable  (A B : ℝ) (hB : 0 < B) (k : ℕ) :
summable (λ (a : ℕ+), 2 * complex.abs (((k+1)!)/(rfunct(lbpoint A B hB))^(k+2))* ((rie (k+2)) a)) :=
begin
rw ←summable_mul_left_iff,
have hk : 1 < (k : ℝ) + 2, by {norm_cast, linarith,},
have := Riemann_zeta_is_summmable (k + 2) hk,
apply summable.subtype this,
simp only [ nat.cast_mul, nat.cast_add, algebra_map.coe_one, map_div₀, complex.abs_pow, abs_of_real, ne.def,
  mul_eq_zero, bit0_eq_zero, one_ne_zero, div_eq_zero_iff, absolute_value.eq_zero, nat.cast_eq_zero, pow_eq_zero_iff,
  nat.succ_pos', abs_eq_zero, false_or],
apply not_or,
apply nat.factorial_ne_zero,
have hr := rfunct_pos (lbpoint A B hB),
linarith,
end


lemma aut_bound_on_comp (K : set ℂ) (hk : K ⊆ ℍ'.1) (hk2 : is_compact K) (k : ℕ) :
  ∃ (u : ℕ+ → ℝ), summable u ∧ ∀ (n : ℕ+) (s : K),
  complex.abs (deriv (λ (z : ℂ), iterated_deriv_within k (λ (z : ℂ), (z - (n : ℂ))⁻¹ + (z + n)⁻¹)
    upper_half_space z) s) ≤ u n :=
begin
  by_cases h1 : set.nonempty K,
  have H:= compact_in_slice' K h1 hk hk2,
  obtain ⟨ A, B, hB, hAB⟩ := H,
  refine ⟨ (λ (a : ℕ+), 2 * complex.abs (((k+1)!)/(rfunct(lbpoint A B hB))^(k+2))* ((rie (k+2)) a) ), _,_⟩,
  exact upper_bnd_summable A B hB k,
  intros n s,
  have hr := der_of_iter_der ⟨s.1, hk s.2⟩  k n,
  simp only [coe_coe,  nat.cast_mul, nat.cast_add, algebra_map.coe_one,
  top_eq_univ, image_univ, range_inclusion, subtype.val_eq_coe, subtype.coe_mk, one_div] at *,
  rw hr,
  apply le_trans (complex.abs.add_le _ _),
  simp_rw mul_assoc,
  rw two_mul,
  apply add_le_add,
  have he1:= sub_bound ⟨s.1, hk s.2⟩ A B hB _ k n,
  simp_rw div_eq_mul_inv at *,
  simp only [nat.cast_mul, nat.cast_add, algebra_map.coe_one, subtype.val_eq_coe, subtype.coe_mk, coe_coe,
  one_mul, absolute_value.map_mul, complex.abs_pow, absolute_value.map_neg, absolute_value.map_one, one_pow,
  abs_cast_nat, map_inv₀, abs_of_real] at *,
  exact he1,
  apply hAB,
  simp only [subtype.val_eq_coe, mem_set_of_eq, subtype.coe_mk, subtype.coe_prop],
  have he1:= add_bound ⟨s.1, hk s.2⟩ A B hB _ k n,
  simp_rw div_eq_mul_inv at *,
  simp only [nat.cast_mul, nat.cast_add, algebra_map.coe_one, subtype.val_eq_coe, subtype.coe_mk, coe_coe,
  one_mul, absolute_value.map_mul, complex.abs_pow, absolute_value.map_neg, absolute_value.map_one, one_pow,
  abs_cast_nat, map_inv₀, abs_of_real] at *,
  exact he1,
  apply hAB,
  simp only [subtype.val_eq_coe, mem_set_of_eq, subtype.coe_mk, subtype.coe_prop],
  simp only [slice_mem, abs_of_real, ge_iff_le, nat.factorial_succ, nat.cast_mul, nat.cast_add, algebra_map.coe_one] at *,
  refine ⟨ (λ x, 0), _,_ ⟩,
  apply summable_zero,
  intro n ,
  rw not_nonempty_iff_eq_empty at h1,
  intros r,
  exfalso,
  have hr:= r.2,
  simp_rw h1 at hr,
  simp at hr,
  apply hr,
end


lemma aut_bound_on_comp' (K : set ℂ) (hk : K ⊆ ℍ'.1) (hk2 : is_compact K) (k : ℕ) :
  ∃ (u : ℕ+ → ℝ), summable u ∧ ∀ (n : ℕ+) (s : K),
  complex.abs (deriv (λ (z : ℂ),
    ((-1 : ℂ) ^ k * ↑k!/(z - (n : ℂ))^(k+1)) + (-1) ^ k * ↑k!/(z + n)^(k+1)) s)  ≤ u n :=
begin
have := aut_bound_on_comp K hk hk2 k,
obtain ⟨u, hu, H⟩ := this,
refine ⟨u, hu, _⟩ ,
intros n s,
have H2:= H n s,
simp only [coe_coe, int.cast_coe_nat, one_div, subtype.coe_mk, subtype.val_eq_coe, pi.add_apply] at *,
have H4: complex.abs (deriv (λ (z : ℂ), (-1) ^ k * ↑k! / (z - ↑↑n) ^ (k + 1) + (-1) ^ k * ↑k! / (z + ↑↑n) ^ (k + 1)) ↑s) =
complex.abs (deriv (iterated_deriv_within k (λ (z : ℂ), (z - ↑↑n)⁻¹ + (z + ↑↑n)⁻¹) upper_half_space) ↑s),
by {apply congr_arg,
  apply filter.eventually_eq.deriv_eq,
  rw eventually_eq_iff_exists_mem,
  use ℍ',
  split,
  apply is_open.mem_nhds upper_half_plane_is_open,
  apply hk s.2,
  apply eq_on.symm,
  simpa using  (iter_div_aut_add n k),},
rw H4,
apply H2,
end

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
intros K hK hK2,
apply aut_bound_on_comp K hK hK2 k,
intros n r,
apply diff_at_aux r k n,
apply is_open.unique_diff_within_at upper_half_plane_is_open,
exact x.2,
end




lemma tsum_ider_der_eq (k : ℕ) (x : ℍ') :
∑' (n : ℕ+), iterated_deriv_within k (λ (z : ℂ), (1/(z-(n))+1/(z+(n)))) ℍ' x = ∑' (n : ℕ+),
 ((-1 : ℂ)^k*(k)! * (1/(x - n)^(k+1)) + (-1)^k*(k)! * (1/(x + n)^(k+1))) :=
begin
apply tsum_congr,
intros b,
have h2 := iter_div_aut_add b k x.2,
simpa using h2,
end

lemma auxp_series_ite_deriv_uexp''' (k : ℕ)   :
  eq_on (iterated_deriv_within k (λ (z : ℂ), ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n)))) ℍ')
   (λ (x : ℂ),  ∑' (n : ℕ+),
 ((-1 : ℂ)^k*(k)! * (1/(x - n)^(k+1)) + (-1)^k*(k)! * (1/(x + n)^(k+1)))) ℍ' :=
begin
intros x hx,
have := aut_series_ite_deriv_uexp2 k ⟨x,hx⟩,
simp at *,
rw this,
have h2:= tsum_ider_der_eq k ⟨x, hx⟩,
simpa using h2,
end

lemma summable_3 (m : ℕ) (y : ℍ') : summable (λ (n : ℕ+), (-1 : ℂ) ^ m * ↑m! * (1 / (y - ↑n) ^ (m + 1)) +
(-1) ^ m * ↑m! * (1 / (y + ↑n) ^ (m + 1))) :=
begin
by_cases hm : m = 0,
simp_rw hm,
simp,
have := lhs_summable y,
simpa using this,
have hm2 : 2 ≤ m + 1, by { have : 1 ≤ m, by {apply nat.one_le_iff_ne_zero.mpr hm} , linarith,},
simp_rw ←mul_add,
rw ←summable_mul_left_iff,
apply summable.add,
apply lhs_summable_2 y (m+1) hm2,
apply lhs_summable_2' y (m+1) hm2,
simp [nat.factorial_ne_zero],
end


lemma tsum_aexp_cont_diff_on (k : ℕ) :
cont_diff_on ℂ k (λ(z : ℂ), ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n)))) ℍ' :=
begin
apply  cont_diff_on_of_differentiable_on_deriv,
intros m hm,
have h1:= (auxp_series_ite_deriv_uexp'''  m),
apply differentiable_on.congr _ (h1),
intros x hx,
apply has_deriv_within_at.differentiable_within_at,
apply has_deriv_within_at_tsum_fun _ (upper_half_plane_is_open),
apply hx,
intros y hy,
apply summable_3 m ⟨y, hy⟩,
intros K hK1 hK2,
have := (aut_bound_on_comp' K hK1 hK2 m),
obtain ⟨u, hu, H⟩ := this,
refine ⟨u, hu, _⟩,
intros n s,
simpa using  (H n s),
intros n r,
have hN : ℍ'.1 ∈  𝓝 r.1, by {apply is_open.mem_nhds upper_half_plane_is_open, exact r.2, },
have := (diff_on_aux m n).differentiable_at hN,
simp at *,
convert this,
exact at_top_ne_bot,
end



lemma summable_factor (n : ℤ) (z : ℍ)  (k : ℕ) (hk : 3 ≤ k) :
  summable (λ (d : ℤ), ((-((n : ℂ)*z) +d)^k)⁻¹) :=
begin
have H := Eisenstein_series_is_summable k z hk,
have H2:= H.prod_factor (-n),
rw Eise at H2,
simp at *,
exact H2,
end


lemma aux_iter_der_tsum (k : ℕ) (hk : 2 ≤ k) (x : ℍ') :
iterated_deriv_within k ((λ (z : ℂ), 1/z) +(λ (z : ℂ), ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n))))) ℍ' x =
((-1)^(k : ℕ) *(k : ℕ)!) * ∑' (n : ℤ), 1/((x : ℂ) + n)^(k +1 : ℕ) :=
begin
rw iter_deriv_within_add,
have h1 := aut_iter_deriv 0 k x.2,
simp only [one_div, subtype.coe_mk, coe_coe, algebra_map.coe_zero, add_zero, subtype.val_eq_coe] at *,
rw h1,
have := aut_series_ite_deriv_uexp2 k x,
simp only [coe_coe, one_div, subtype.coe_mk] at *,
rw this,
have h2:=tsum_ider_der_eq k x,
simp only [coe_coe, one_div, subtype.coe_mk] at h2,
rw h2,
rw int_tsum_pnat,
simp only [algebra_map.coe_zero, add_zero, coe_coe, int.cast_coe_nat, int.cast_neg],
rw tsum_add,
rw tsum_mul_left,
rw tsum_mul_left,
rw mul_add,
rw mul_add,
ring_nf,
rw ← summable_mul_left_iff,
have hk2 : 2 ≤ k+1, by {linarith},
simpa using (lhs_summable_2 x (k+1) hk2),
simp only [nat.factorial_ne_zero, ne.def, neg_one_pow_mul_eq_zero_iff, nat.cast_eq_zero, not_false_iff],
rw ← summable_mul_left_iff,
have hk2 : 2 ≤ k+1, by {linarith},
simpa using (lhs_summable_2' x (k+1) hk2),
simp only [nat.factorial_ne_zero, ne.def, neg_one_pow_mul_eq_zero_iff, nat.cast_eq_zero, not_false_iff],
have hk3 : 3 ≤ k+1, by {linarith},
have := summable_factor (-1 : ℤ) x (k+1) hk3,
simpa using this,
have := aut_cont_diff_on 0 k,
simpa using this,
apply tsum_aexp_cont_diff_on k,
end



lemma aux_iter_der_tsum_eq_on (k : ℕ) (hk : 3 ≤ k) : eq_on
(iterated_deriv_within (k-1) ((λ (z : ℂ), 1/z) +(λ (z : ℂ), ∑' (n : ℕ+), (1/(z-(n))+1/(z+(n))))) ℍ')
(λ (z : ℂ), ((-1)^(k -1) *(k -1)!) * ∑' (n : ℤ), 1/(z + n)^(k  : ℕ)) ℍ' :=
begin
intros z hz,
have hk0 : 2 ≤ k - 1, by {exact le_tsub_of_add_le_left hk,},
have := aux_iter_der_tsum (k-1) hk0 ⟨z, hz⟩,
have hk1 : k - 1 + 1 = k, by {apply nat.sub_add_cancel,
linarith,},
rw hk1 at this,
exact this,

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
