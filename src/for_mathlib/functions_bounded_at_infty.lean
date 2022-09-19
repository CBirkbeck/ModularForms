/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import algebra.module.submodule.basic
import analysis.complex.upper_half_plane.basic
import for_mathlib.zero_and_bounded_at_filter

/-!
# Bounded at infinity
For complex valued functions on the upper half plane, this file defines the filter `at_I_infty`
required for defining when functions are bounded at infinity and zero at infinity.
Both of which are relevant for defining modular forms.
-/

open complex filter

open_locale topological_space upper_half_plane

noncomputable theory

namespace upper_half_plane

/--Filter for approaching `i∞`-/
def at_I_infty := filter.at_top.comap upper_half_plane.im

lemma at_I_infty_basis : (at_I_infty).has_basis (λ _, true) (λ (i : ℝ), im ⁻¹' set.Ici i) :=
filter.has_basis.comap upper_half_plane.im filter.at_top_basis

lemma at_I_infty_mem (S : set ℍ) : S ∈ at_I_infty ↔ (∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S) :=
begin
  simp only [at_I_infty, filter.mem_comap', filter.mem_at_top_sets, ge_iff_le, set.mem_set_of_eq,
    upper_half_plane.coe_im],
  split,
  { intro h, cases h with a h, refine ⟨a, (λ z hz, by {apply h (im z) hz , refl})⟩ },
  { refine (λ h, by {cases h with A h,
    refine ⟨A, (λ b hb x hx, by {apply (h x), rw hx, exact hb})⟩}) }
end

/--A function ` f : ℍ → ℂ` is bounded at infinity if there exist real numbers `M, A` such that
for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ M`,
 i.e. the function is bounded as you approach `i∞`. -/
def is_bound_at_infty (f : ℍ → ℂ) : Prop := asymptotics.is_O at_I_infty f (1 : ℍ → ℂ)

/--A function ` f : ℍ → ℂ` is zero at infinity if for any `ε > 0` there exist a real
number `A` such that for all `z ∈ ℍ` with `im z ≥ A` we have `abs(f (z)) ≤ ε`,
 i.e. the function tends to zero as you approach `i∞`. -/
def is_zero_at_infty (f : ℍ → ℂ) : Prop := filter.tendsto f at_I_infty (𝓝 0)

lemma zero_form_is_bounded_at_infty : is_bound_at_infty 0 :=
begin
  apply zero_is_bounded_at_filter,
end

/--Module of functions that are zero at infinity.-/
def zero_at_infty_submodule : submodule ℂ (ℍ → ℂ) := zero_at_filter_submodule at_I_infty

/--Module of functions that are bounded at infinity.-/
def bounded_at_infty_submodule : submodule ℂ (ℍ → ℂ) := bounded_filter_submodule at_I_infty

/--Subalgebra of functions that are bounded at infinity.-/
def bounded_at_infty_subalgebra : subalgebra ℂ (ℍ → ℂ) := bounded_filter_subalgebra at_I_infty

lemma prod_of_bound_is_bound {f g : ℍ → ℂ} (hf : is_bound_at_infty f) (hg : is_bound_at_infty g) :
  is_bound_at_infty (f * g) := by {have := hf.mul hg, simp only [pi.one_apply, mul_one,
     norm_eq_abs, complex.abs_mul] at this, convert this,}

@[simp]lemma bound_mem (f : ℍ → ℂ) :
  is_bound_at_infty f ↔ ∃ (M A : ℝ), ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M :=
begin
  simp [is_bound_at_infty, asymptotics.is_O_iff, filter.eventually, at_I_infty_mem],
end

lemma zero_at_im_infty (f : ℍ → ℂ) :
  is_zero_at_infty f ↔ ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → abs (f z) ≤ ε :=
begin
   simp [is_zero_at_infty],
   rw tendsto_iff_forall_eventually_mem,
    split,
   {simp_rw [filter.eventually, at_I_infty_mem],
   intro h,
   intros ε hε,
   have :=  metric.closed_ball_mem_nhds (0 : ℂ) hε,
   have h2 := h (metric.closed_ball (0 : ℂ) ε) (this),
   simp at h2,
   apply h2},
   {simp_rw metric.mem_nhds_iff,
    intro h,
    intros s hs,
    simp at *,
    simp_rw [filter.eventually, at_I_infty_mem],
    obtain ⟨ε, h1, h2⟩ := hs,
    have h11 : 0 < (ε/2), by {linarith,},
    have h3 := h (ε/2) h11,
    obtain ⟨A, hA⟩:= h3,
    use A,
    intros z hz,
    have ha2 := hA z hz,
    have hzs : f z ∈ s, by {apply h2, simp, apply lt_of_le_of_lt ha2, simp, linarith,},
    apply hzs,}
end

end upper_half_plane
