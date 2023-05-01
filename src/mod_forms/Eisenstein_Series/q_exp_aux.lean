import mod_forms.Eisenstein_Series.Eisen_is_holo
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import mod_forms.Riemann_zeta_fin
import analysis.calculus.iterated_deriv
import analysis.calculus.series
import mod_forms.Eisenstein_Series.Eisenstein_series_q_expansions

noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)

local notation `ℍ` := upper_half_plane

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

lemma diff_on_aux (s : ℍ') (k : ℕ) (n : ℕ+):
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
 apply differentiable_on.congr (diff_on_aux s k n),
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

all_goals{sorry},
/-
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
-/
end



lemma aux_iter_der_tsum (k : ℕ) (hk : 3 ≤ k) (x : ℍ') :
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
--ring_nf,
sorry,
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

all_goals{sorry},
end
