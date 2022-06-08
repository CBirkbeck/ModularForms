import for_mathlib.mod_forms2
import mod_forms.modular
import mod_forms.q_expansion

/-! **Bounds for the integrand of the Petersson product**

The main result here is that if f is a cusp form of level 1, then
`abs (f z) ^ 2 * (im z) ^ k` is uniformly bounded on the upper half-plane.

FIXME : The code here depends on a couple of lemmas at the end of `mod_forms2.lean`, which ought
to be trivial but are gnarly because of the coercion issues around SL2Z actions. For some reason
that code stops working if I transplant it to this file. -/

open modular_forms complex filter asymptotics
open_locale real topological_space manifold filter modular_forms

noncomputable theory

local notation `ℍ` := upper_half_plane
local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

/-- The Petersson function of a cuspform is continuous. -/
lemma pet_cts {f : ℍ → ℂ} {k : ℤ} (hf : f ∈ S(k, ⊤)) : continuous (pet_self f k) :=
begin
  apply continuous.mul,
  { continuity,
    exact (is_modular_form_of_weight_and_level_of_is_cusp_form_of_weight_and_level hf).hol.continuous },
  { continuity, exact or.inl a.2.ne',}
end

/-- The image of a trunction of the fundamental domain, under the inclusion `ℍ → ℂ`, defined by `≤`
inequalities (so it will be a closed subset of `ℂ`). -/
lemma image_fd (A : ℝ) : ( coe '' { x : ℍ | x ∈ modular_group.fd ∧ x.im ≤ A} : set ℂ) =
  { x : ℂ | (0 ≤ x.im) ∧ (|x.re| ≤ 1/2) ∧ (1 ≤ abs x) ∧ (im x ≤ A)} :=
begin
  ext1 z, rw modular_group.fd, dsimp,
  split,
  { intro hz, simp only [set.mem_image] at hz,
    obtain ⟨x, ⟨⟨hx1, hx2⟩, hx3⟩, hzx⟩ := hz,
    rw ←hzx,
    refine ⟨x.2.le, hx2, _, hx3⟩,
    rw [←one_le_sq_iff, ←norm_sq_eq_abs], exact hx1, apply complex.abs_nonneg, },
  { intro hz, obtain ⟨hz1, hz2, hz3, hz4⟩ := hz,
    rw [set.mem_image],
    rcases le_or_lt (im z) 0,
    -- This is a clumsy way of showing that im z = 0 leads to a contradiction.
    -- Todo: improve this by comparison with three_lt_four_mul_im_sq_of_mem_fdo in modular.lean.
    { have : im z = 0 := by linarith,
      have t := (one_le_sq_iff (abs_nonneg _)).mpr hz3,
      rw ←norm_sq_eq_abs at t, rw norm_sq at t, simp only [monoid_with_zero_hom.coe_mk] at t,
      rw this at t, simp only [mul_zero, add_zero] at t,
      rw ←abs_mul_self at t, rw ←pow_two at t, rw _root_.abs_pow at t,
      have tt : |re z| ^ 2 ≤ (1 / 2) ^ 2,
      { rw sq_le_sq, rw _root_.abs_abs,
        have : 0 < (1/2 : ℝ) := by simp,
        conv begin to_rhs, rw abs_of_pos this, end,
        exact hz2, },
      have t3 := le_trans t tt, exfalso, field_simp at t3, rw le_one_div at t3,
      { simp at t3, linarith }, { linarith }, { linarith }, },
    -- Now the main argument.
    use ⟨z, h⟩, refine ⟨⟨⟨_, hz2⟩, hz4⟩, by simp⟩,
    rw norm_sq_eq_abs, rw one_le_sq_iff (complex.abs_nonneg _), exact hz3,
  }
end

/-- The standard fundamental domain, truncated at some finite height, is compact. -/
lemma compact_trunc_fd (A : ℝ) : is_compact {x : ℍ | x ∈ modular_group.fd ∧ x.im ≤ A} :=
begin
  rw [embedding_subtype_coe.is_compact_iff_is_compact_image, image_fd A,
    metric.compact_iff_closed_bounded],
  split,
  { apply_rules [is_closed.inter],
    { apply is_closed_Ici.preimage continuous_im, },
    { have : continuous (λ u, |re u| : ℂ → ℝ) := by { continuity, exact continuous_abs },
      refine is_closed.preimage this (@is_closed_Iic _ _ _ _ (1/2)) },
    { apply is_closed_Ici.preimage complex.continuous_abs, },
    { apply is_closed_Iic.preimage continuous_im, } },
  { rw bounded_iff_exists_norm_le, use real.sqrt (A ^ 2 + (1 / 2) ^ 2),
    intros x hx, rw set.mem_set_of_eq at hx,
    rw norm_eq_abs, rw complex.abs, apply real.le_sqrt_of_sq_le,
    rw real.sq_sqrt (norm_sq_nonneg _),
    rw norm_sq, dsimp, rw add_comm, apply add_le_add,
    { rw ←pow_two, rw sq_le_sq, apply abs_le_abs,
      { exact hx.2.2.2 }, { exact le_trans (by linarith) (le_trans hx.1 hx.2.2.2), } },
    { rw ←pow_two, rw sq_le_sq, apply abs_le_abs,
      { exact le_trans (le_abs_self (re x)) hx.2.1 },
      { exact le_trans (neg_le_abs_self (re x)) hx.2.1 } } }
end

/-- The Petersson function is bounded on the standard fundamental domain. -/
lemma pet_bound_on_fd {f : ℍ → ℂ} {k : ℤ} (hf : f ∈ S(k, ⊤)) :
  ∃ (C : ℝ), ∀ (z : ℍ), (z ∈ modular_group.fd) → |pet_self f k z| ≤ C :=
begin
  obtain ⟨A, C1, H1⟩ := pet_bounded_large hf,
  have := (compact_trunc_fd A).exists_bound_of_continuous_on (pet_cts hf).continuous_on,
  cases this with C2 H2, use max C1 C2, intros z hz,
  rcases le_or_lt (im z) A,
  { exact le_trans (H2 z ⟨hz, h⟩) (le_max_right _ _), },
  { convert le_trans (H1 z h.le) (le_max_left C1 C2),
    apply _root_.abs_of_nonneg,
    rw pet_self, apply mul_nonneg,
    { apply pow_nonneg, apply complex.abs_nonneg},
    { apply zpow_nonneg, exact z.2.le }, }
end

/-- The Petersson function is bounded everywhere. -/
theorem pet_bound {f : ℍ → ℂ} {k : ℤ} (hf : f ∈ S(k, ⊤)) :
  ∃ (C : ℝ), ∀ (z : ℍ), |pet_self f k z| ≤ C :=
begin
  obtain ⟨C, HC⟩ := pet_bound_on_fd hf, use C, intro z,
  obtain ⟨g, hg⟩ := modular_group.exists_smul_mem_fd z,
  replace HC := HC (g • z) hg,
  have : pet_self f k (g • z) = pet_self f k z,
  { apply pet_self_is_invariant,
    exact (is_modular_form_of_weight_and_level_of_is_cusp_form_of_weight_and_level hf).transf,
      tauto, },
  rwa this at HC
end
