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

lemma aut_bound_on_comp (K : set ℂ) (hk : K ⊆ ℍ'.1) (hk2 : is_compact K) (k : ℕ) :
  ∃ (u : ℕ+ → ℝ), summable u ∧ ∀ (n : ℕ+) (s : K),
  complex.abs (deriv (λ (z : ℂ), iterated_deriv_within k (λ (z : ℂ), (z - (n : ℂ))⁻¹ + (z + n)⁻¹)
    upper_half_space z) s) ≤ u n :=
begin
  by_cases h1 : set.nonempty K,
  have H:= compact_in_slice' K h1 hk hk2,
  obtain ⟨ A, B, hB, hAB⟩ := H,
  refine ⟨ (λ (a : ℕ+), ((-1)^k*(k)!)/(rfunct(lbpoint A B hB))^(k+1) ), _,_⟩,
  sorry,
  intros n s,
  have hr := der_of_iter_der ⟨s.1, hk s.2⟩  k n,
  simp at *,
  rw hr,










  sorry,
  simp at *,
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
  --have H:= compact_in_slice' K hk hk2

end
