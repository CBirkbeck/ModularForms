import .SL2Z_generators
import .modular_forms

local notation `ℍ` := upper_half_space
local notation `Mat` := integral_matrices_with_determinant

lemma pos_det' {m : ℤ}  (h : m > 0) {A : Mat m} : ↑(A.a) * ↑(A.d) - ↑(A.b) * ↑(A.c) > (0 : ℝ) :=
begin
  cases A with a b c d det,
  rw ←det at h,
  rw [←int.cast_mul, ←int.cast_mul, ←int.cast_sub],
  suffices : (0 : ℝ) < ↑(a * d - b * c), exact this,
  rwa int.cast_pos
end

lemma aux_10 {m : ℤ} (h : m > 0) (A : Mat m) (z : ℍ) : (↑(A.c) * ↑z + ↑(A.d)) ≠ (0 : ℂ) :=
have H1 : (↑(A.a) : ℝ) * ↑(A.d) - ↑(A.b) * ↑(A.c) > 0,
  by rw [← int.cast_mul, ← int.cast_mul, ← int.cast_sub];
  from int.cast_pos.2 (trans_rel_left _ h A.det.symm),
have _ := preserve_ℍ.aux H1 z.2,
by simpa only [complex.of_real_int_cast]

theorem M_trans_SL2Z_M {m : ℤ} {h : m > 0} {M : SL2Z} {A : Mat m} :
M_trans h (SL2Z_M m M A) = SL2Z_H M ∘ (M_trans h A) :=
begin
  funext z, apply subtype.eq,
  change _/_=_/_,
  have H3 := aux_10 h A z,
  have H4 := aux_10 zero_lt_one M (M_trans h A z),
  unfold M_trans «Möbius_transform» at H4 ⊢,
  simp only [subtype.coe_mk, complex.of_real_int_cast] with SL2Z at H3 H4 ⊢,
  rw ← mul_div_mul_right _ H4 H3,
    conv { to_rhs,
      rw [add_mul, add_mul, mul_assoc, mul_assoc],
      rw [div_mul_cancel _ H3] },
  simp only [int.cast_add, int.cast_mul],
  congr' 1; simp only [add_mul, mul_add, mul_assoc, add_left_comm, add_assoc]
end

set_option eqn_compiler.zeta true
noncomputable def Hecke_operator {k : ℕ} (m : ℤ) (h : m > 0) (f : is_Petersson_weight_ k) :
  is_Petersson_weight_ k :=
begin
  let orbits := quotient (action_rel (SL2Z_M m)),
  letI h_orbits : fintype orbits := SL2Z_M.finiteness m (ne_of_gt h),
  refine ⟨λz:ℍ,
    (m^k : ℂ) * (finset.univ : finset orbits).sum (λo, quotient.lift_on' o _ _), _⟩,
  refine λA, 1 / (A.c * z + A.d)^k * f.1 (M_trans h A z),
  { rcases f with ⟨f, weight_f⟩,
    rintros A B ⟨M, H⟩,

    change 1 / (↑(A.c) * ↑z + ↑(A.d)) ^ k * f (M_trans h A z) = 1 / (↑(B.c) * ↑z + ↑(B.d)) ^ k * f (M_trans h B z),

    rw ← H,
    rw M_trans_SL2Z_M,
    simp [-one_div_eq_inv],
    rw (weight_f M _),
    rw ← mul_assoc,
    congr' 1,
    dsimp[M_trans, «Möbius_transform»],
    ring,
    rw pow_inv,
    rw pow_inv,
    rw ← mul_pow,
    congr' 1,
    -- Patrick claims this goal is true -- and so does Johan
    repeat {sorry} },
  { dsimp [is_Petersson_weight_],
    intros M z,
    conv { to_rhs, rw ← mul_assoc, congr, rw mul_comm },
    conv { to_rhs, rw mul_assoc, rw finset.mul_sum, },
    congr' 1,
    refine finset.sum_bij _ _ _ _ _,
    -- Define the function given by right multiplication with M
    -- The other goals should be straightforward
    
    -- funext o,
    -- rcases o with ⟨A⟩,
    -- dsimp [quotient.lift_on',quotient.lift_on,quot.lift_on],
    -- rcases f with ⟨f, weight_f⟩,
    -- dsimp [is_Petersson_weight_] at weight_f,
    -- simp,
    -- dsimp [SL2Z_H,M_trans,«Möbius_transform»],
    -- simp,
    sorry }
end

