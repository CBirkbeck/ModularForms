/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/

import mod_forms.upper_half_plane
import linear_algebra.general_linear_group
import analysis.matrix

/-!
# The action of the modular group SL(2, โค) on the upper half-plane

We define the action of `SL(2,โค)` on `โ` (via restriction of the `SL(2,โ)` action in
`analysis.complex.upper_half_plane`). We then define the standard fundamental domain
(`modular_group.fd`, `๐`) for this action and show
(`modular_group.exists_smul_mem_fd`) that any point in `โ` can be
moved inside `๐`.

## Main definitions

The standard (closed) fundamental domain of the action of `SL(2,โค)` on `โ`, denoted `๐`:
`fd := {z | 1 โค (z : โ).norm_sq โง |z.re| โค (1 : โ) / 2}`

The standard open fundamental domain of the action of `SL(2,โค)` on `โ`, denoted `๐แต`:
`fdo := {z | 1 < (z : โ).norm_sq โง |z.re| < (1 : โ) / 2}`

These notations are localized in the `modular` locale and can be enabled via `open_locale modular`.

## Main results

Any `z : โ` can be moved to `๐` by an element of `SL(2,โค)`:
`exists_smul_mem_fd (z : โ) : โ g : SL(2,โค), g โข z โ ๐`

If both `z` and `ฮณ โข z` are in the open domain `๐แต` then `z = ฮณ โข z`:
`eq_smul_self_of_mem_fdo_mem_fdo {z : โ} {g : SL(2,โค)} (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : z = g โข z`

# Discussion

Standard proofs make use of the identity

`g โข z = a / c - 1 / (c (cz + d))`

for `g = [[a, b], [c, d]]` in `SL(2)`, but this requires separate handling of whether `c = 0`.
Instead, our proof makes use of the following perhaps novel identity (see
`modular_group.smul_eq_lc_row0_add`):

`g โข z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`

where there is no issue of division by zero.

Another feature is that we delay until the very end the consideration of special matrices
`T=[[1,1],[0,1]]` (see `modular_group.T`) and `S=[[0,-1],[1,0]]` (see `modular_group.S`), by
instead using abstract theory on the properness of certain maps (phrased in terms of the filters
`filter.cocompact`, `filter.cofinite`, etc) to deduce existence theorems, first to prove the
existence of `g` maximizing `(gโขz).im` (see `modular_group.exists_max_im`), and then among
those, to minimize `|(gโขz).re|` (see `modular_group.exists_row_one_eq_and_min_re`).
-/

/- Disable these instances as they are not the simp-normal form, and having them disabled ensures
we state lemmas in this file without spurious `coe_fn` terms. -/
local attribute [-instance] matrix.special_linear_group.has_coe_to_fun
local attribute [-instance] matrix.general_linear_group.has_coe_to_fun

open complex (hiding abs_one abs_two abs_mul abs_add)
open matrix (hiding mul_smul) matrix.special_linear_group upper_half_plane
noncomputable theory

local notation `SL(` n `, ` R `)`:= special_linear_group (fin n) R
local prefix `โโ`:1024 := @coe _ (matrix (fin 2) (fin 2) โค) _

open_locale upper_half_plane complex_conjugate

local attribute [instance] fintype.card_fin_even

namespace modular_group

variables {g : SL(2, โค)} (z : โ)

section bottom_row

/-- The two numbers `c`, `d` in the "bottom_row" of `g=[[*,*],[c,d]]` in `SL(2, โค)` are coprime. -/
lemma bottom_row_coprime {R : Type*} [comm_ring R] (g : SL(2, R)) :
  is_coprime ((โg : matrix (fin 2) (fin 2) R) 1 0) ((โg : matrix (fin 2) (fin 2) R) 1 1) :=
begin
  use [- (โg : matrix (fin 2) (fin 2) R) 0 1, (โg : matrix (fin 2) (fin 2) R) 0 0],
  rw [add_comm, neg_mul, โsub_eq_add_neg, โdet_fin_two],
  exact g.det_coe,
end

/-- Every pair `![c, d]` of coprime integers is the "bottom_row" of some element `g=[[*,*],[c,d]]`
of `SL(2,โค)`. -/
lemma bottom_row_surj {R : Type*} [comm_ring R] :
  set.surj_on (ฮป g : SL(2, R), @coe _ (matrix (fin 2) (fin 2) R) _ g 1) set.univ
    {cd | is_coprime (cd 0) (cd 1)} :=
begin
  rintros cd โจbโ, a, gcd_eqnโฉ,
  let A := ![![a, -bโ], cd],
  have det_A_1 : det A = 1,
  { convert gcd_eqn,
    simp [A, det_fin_two, (by ring : a * (cd 1) + bโ * (cd 0) = bโ * (cd 0) + a * (cd 1))] },
  refine โจโจA, det_A_1โฉ, set.mem_univ _, _โฉ,
  ext; simp [A]
end

end bottom_row

section tendsto_lemmas

open filter continuous_linear_map
local attribute [instance] matrix.normed_group matrix.normed_space
local attribute [simp] coe_smul

/-- The function `(c,d) โ |cz+d|^2` is proper, that is, preimages of bounded-above sets are finite.
-/
lemma tendsto_norm_sq_coprime_pair :
  filter.tendsto (ฮป p : fin 2 โ โค, ((p 0 : โ) * z + p 1).norm_sq)
  cofinite at_top :=
begin
  let ฯโ : (fin 2 โ โ) โโ[โ] โ := linear_map.proj 0,
  let ฯโ : (fin 2 โ โ) โโ[โ] โ := linear_map.proj 1,
  let f : (fin 2 โ โ) โโ[โ] โ := ฯโ.smul_right (z:โ) + ฯโ.smul_right 1,
  have f_def : โf = ฮป (p : fin 2 โ โ), (p 0 : โ) * โz + p 1,
  { ext1,
    dsimp only [linear_map.coe_proj, real_smul,
      linear_map.coe_smul_right, linear_map.add_apply],
    rw mul_one, },
  have : (ฮป (p : fin 2 โ โค), norm_sq ((p 0 : โ) * โz + โ(p 1)))
    = norm_sq โ f โ (ฮป p : fin 2 โ โค, (coe : โค โ โ) โ p),
  { ext1,
    rw f_def,
    dsimp only [function.comp],
    rw [of_real_int_cast, of_real_int_cast], },
  rw this,
  have hf : f.ker = โฅ,
  { let g : โ โโ[โ] (fin 2 โ โ) :=
      linear_map.pi ![im_lm, im_lm.comp ((z:โ) โข (conj_ae  : โ โโ[โ] โ))],
    suffices : ((z:โ).imโปยน โข g).comp f = linear_map.id,
    { exact linear_map.ker_eq_bot_of_inverse this },
    apply linear_map.ext,
    intros c,
    have hz : (z:โ).im โ? 0 := z.2.ne',
    rw [linear_map.comp_apply, linear_map.smul_apply, linear_map.id_apply],
    ext i,
    dsimp only [g, pi.smul_apply, linear_map.pi_apply, smul_eq_mul],
    fin_cases i,
    { show ((z : โ).im)โปยน * (f c).im = c 0,
      rw [f_def, add_im, of_real_mul_im, of_real_im, add_zero, mul_left_comm,
        inv_mul_cancel hz, mul_one], },
    { show ((z : โ).im)โปยน * ((z : โ) * conj (f c)).im = c 1,
      rw [f_def, ring_hom.map_add, ring_hom.map_mul, mul_add, mul_left_comm, mul_conj,
        conj_of_real, conj_of_real, โ of_real_mul, add_im, of_real_im, zero_add,
        inv_mul_eq_iff_eq_mulโ hz],
      simp only [of_real_im, of_real_re, mul_im, zero_add, mul_zero] } },
  have hโ := (linear_equiv.closed_embedding_of_injective hf).tendsto_cocompact,
  have hโ : tendsto (ฮป p : fin 2 โ โค, (coe : โค โ โ) โ p) cofinite (cocompact _),
  { convert tendsto.pi_map_Coprod (ฮป i, int.tendsto_coe_cofinite),
    { rw Coprod_cofinite },
    { rw Coprod_cocompact } },
  exact tendsto_norm_sq_cocompact_at_top.comp (hโ.comp hโ)
end


/-- Given `coprime_pair` `p=(c,d)`, the matrix `[[a,b],[*,*]]` is sent to `a*c+b*d`.
  This is the linear map version of this operation.
-/
def lc_row0 (p : fin 2 โ โค) : (matrix (fin 2) (fin 2) โ) โโ[โ] โ :=
((p 0:โ) โข linear_map.proj 0 + (p 1:โ) โข linear_map.proj 1 : (fin 2 โ โ) โโ[โ] โ).comp
  (linear_map.proj 0)

@[simp] lemma lc_row0_apply (p : fin 2 โ โค) (g : matrix (fin 2) (fin 2) โ) :
  lc_row0 p g = p 0 * g 0 0 + p 1 * g 0 1 :=
rfl

/-- Linear map sending the matrix [a, b; c, d] to the matrix [acโ + bdโ, - adโ + bcโ; c, d], for
some fixed `(cโ, dโ)`. -/
@[simps] def lc_row0_extend {cd : fin 2 โ โค} (hcd : is_coprime (cd 0) (cd 1)) :
  (matrix (fin 2) (fin 2) โ) โโ[โ] matrix (fin 2) (fin 2) โ :=
linear_equiv.Pi_congr_right
![begin
    refine linear_map.general_linear_group.general_linear_equiv โ (fin 2 โ โ)
      (general_linear_group.to_linear (plane_conformal_matrix (cd 0 : โ) (-(cd 1 : โ)) _)),
    norm_cast,
    rw neg_sq,
    exact hcd.sq_add_sq_ne_zero
  end,
  linear_equiv.refl โ (fin 2 โ โ)]

/-- The map `lc_row0` is proper, that is, preimages of cocompact sets are finite in
`[[* , *], [c, d]]`.-/
theorem tendsto_lc_row0 {cd : fin 2 โ โค} (hcd : is_coprime (cd 0) (cd 1)) :
  tendsto (ฮป g : {g : SL(2, โค) // โโg 1 = cd}, lc_row0 cd โ(โg : SL(2, โ)))
    cofinite (cocompact โ) :=
begin
  let mB : โ โ (matrix (fin 2) (fin 2)  โ) := ฮป t, ![![t, (-(1:โค):โ)], coe โ cd],
  have hmB : continuous mB,
  { simp only [continuous_pi_iff, fin.forall_fin_two],
    have : โ c : โ, continuous (ฮป x : โ, c) := ฮป c, continuous_const,
    exact โจโจcontinuous_id, @this (-1 : โค)โฉ, โจthis (cd 0), this (cd 1)โฉโฉ },
  refine filter.tendsto.of_tendsto_comp _ (comap_cocompact_le hmB),
  let fโ : SL(2, โค) โ matrix (fin 2) (fin 2) โ :=
    ฮป g, matrix.map (โg : matrix _ _ โค) (coe : โค โ โ),
  have cocompact_โ_to_cofinite_โค_matrix :
    tendsto (ฮป m : matrix (fin 2) (fin 2) โค, matrix.map m (coe : โค โ โ)) cofinite (cocompact _),
  { simpa only [Coprod_cofinite, Coprod_cocompact]
      using tendsto.pi_map_Coprod (ฮป i : fin 2, tendsto.pi_map_Coprod
        (ฮป j : fin 2, int.tendsto_coe_cofinite)) },
  have hfโ : tendsto fโ cofinite (cocompact _) :=
    cocompact_โ_to_cofinite_โค_matrix.comp subtype.coe_injective.tendsto_cofinite,
  have hfโ : closed_embedding (lc_row0_extend hcd) :=
    (lc_row0_extend hcd).to_continuous_linear_equiv.to_homeomorph.closed_embedding,
  convert hfโ.tendsto_cocompact.comp (hfโ.comp subtype.coe_injective.tendsto_cofinite) using 1,
  ext โจg, rflโฉ i j : 3,
  fin_cases i; [fin_cases j, skip],
  -- the following are proved by `simp`, but it is replaced by `simp only` to avoid timeouts.
  { simp only [mB, mul_vec, dot_product, fin.sum_univ_two, _root_.coe_coe, coe_matrix_coe,
      int.coe_cast_ring_hom, lc_row0_apply, function.comp_app, cons_val_zero, lc_row0_extend_apply,
      linear_map.general_linear_group.coe_fn_general_linear_equiv,
      general_linear_group.to_linear_apply, coe_plane_conformal_matrix, neg_neg, mul_vec_lin_apply,
      cons_val_one, head_cons] },
  { convert congr_arg (ฮป n : โค, (-n:โ)) g.det_coe.symm using 1,
    simp only [fโ, mul_vec, dot_product, fin.sum_univ_two, matrix.det_fin_two, function.comp_app,
      subtype.coe_mk, lc_row0_extend_apply, cons_val_zero,
      linear_map.general_linear_group.coe_fn_general_linear_equiv,
      general_linear_group.to_linear_apply, coe_plane_conformal_matrix, mul_vec_lin_apply,
      cons_val_one, head_cons, map_apply, neg_mul, int.cast_sub, int.cast_mul, neg_sub],
    ring },
  { refl }
end

/-- This replaces `(gโขz).re = a/c + *` in the standard theory with the following novel identity:
  `g โข z = (a c + b d) / (c^2 + d^2) + (d z - c) / ((c^2 + d^2) (c z + d))`
  which does not need to be decomposed depending on whether `c = 0`. -/
lemma smul_eq_lc_row0_add {p : fin 2 โ โค} (hp : is_coprime (p 0) (p 1)) (hg : โโg 1 = p) :
  โ(g โข z) = ((lc_row0 p โ(g : SL(2, โ))) : โ) / (p 0 ^ 2 + p 1 ^ 2)
    + ((p 1 : โ) * z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1)) :=
begin
  have nonZ1 : (p 0 : โ) ^ 2 + (p 1) ^ 2 โ? 0 := by exact_mod_cast hp.sq_add_sq_ne_zero,
  have : (coe : โค โ โ) โ p โ? 0 := ฮป h, hp.ne_zero ((@int.cast_injective โ _ _ _).comp_left h),
  have nonZ2 : (p 0 : โ) * z + p 1 โ? 0 := by simpa using linear_ne_zero _ z this,
  field_simp [nonZ1, nonZ2, denom_ne_zero, -upper_half_plane.denom, -denom_apply],
  rw (by simp : (p 1 : โ) * z - p 0 = ((p 1) * z - p 0) * โ(det (โg : matrix (fin 2) (fin 2) โค))),
  rw [โhg, det_fin_two],
  simp only [int.coe_cast_ring_hom, coe_matrix_coe, int.cast_mul, of_real_int_cast, map_apply,
  denom, int.cast_sub, _root_.coe_coe,coe_GL_pos_coe_GL_coe_matrix],
  ring,
end

lemma tendsto_abs_re_smul {p : fin 2 โ โค} (hp : is_coprime (p 0) (p 1)) :
  tendsto (ฮป g : {g : SL(2, โค) // โโg 1 = p}, |((g : SL(2, โค)) โข z).re|)
    cofinite at_top :=
begin
  suffices : tendsto (ฮป g : (ฮป g : SL(2, โค), โโg 1) โปยน' {p}, (((g : SL(2, โค)) โข z).re))
    cofinite (cocompact โ),
  { exact tendsto_norm_cocompact_at_top.comp this },
  have : ((p 0 : โ) ^ 2 + p 1 ^ 2)โปยน โ? 0,
  { apply inv_ne_zero,
    exact_mod_cast hp.sq_add_sq_ne_zero },
  let f := homeomorph.mul_rightโ _ this,
  let ff := homeomorph.add_right (((p 1:โ)* z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re,
  convert ((f.trans ff).closed_embedding.tendsto_cocompact).comp (tendsto_lc_row0 hp),
  ext g,
  change ((g : SL(2, โค)) โข z).re = (lc_row0 p โ(โg : SL(2, โ))) / (p 0 ^ 2 + p 1 ^ 2)
  + (((p 1:โ )* z - p 0) / ((p 0 ^ 2 + p 1 ^ 2) * (p 0 * z + p 1))).re,
  exact_mod_cast (congr_arg complex.re (smul_eq_lc_row0_add z hp g.2))
end

end tendsto_lemmas

section fundamental_domain

local attribute [simp] coe_smul re_smul

/-- For `z : โ`, there is a `g : SL(2,โค)` maximizing `(gโขz).im` -/
lemma exists_max_im :
  โ g : SL(2, โค), โ g' : SL(2, โค), (g' โข z).im โค (g โข z).im :=
begin
  classical,
  let s : set (fin 2 โ โค) := {cd | is_coprime (cd 0) (cd 1)},
  have hs : s.nonempty := โจ![1, 1], is_coprime_one_leftโฉ,
  obtain โจp, hp_coprime, hpโฉ :=
    filter.tendsto.exists_within_forall_le hs (tendsto_norm_sq_coprime_pair z),
  obtain โจg, -, hgโฉ := bottom_row_surj hp_coprime,
  refine โจg, ฮป g', _โฉ,
  rw [special_linear_group.im_smul_eq_div_norm_sq, special_linear_group.im_smul_eq_div_norm_sq,
    div_le_div_left],
  { simpa [โ hg] using hp (โโg' 1) (bottom_row_coprime g') },
  { exact z.im_pos },
  { exact norm_sq_denom_pos g' z },
  { exact norm_sq_denom_pos g z },
end

/-- Given `z : โ` and a bottom row `(c,d)`, among the `g : SL(2,โค)` with this bottom row, minimize
  `|(gโขz).re|`.  -/
lemma exists_row_one_eq_and_min_re {cd : fin 2 โ โค} (hcd : is_coprime (cd 0) (cd 1)) :
  โ g : SL(2,โค), โโg 1 = cd โง (โ g' : SL(2,โค), โโg 1 = โโg' 1 โ
  |(g โข z).re| โค |(g' โข z).re|) :=
begin
  haveI : nonempty {g : SL(2, โค) // โโg 1 = cd} :=
    let โจx, hxโฉ := bottom_row_surj hcd in โจโจx, hx.2โฉโฉ,
  obtain โจg, hgโฉ := filter.tendsto.exists_forall_le (tendsto_abs_re_smul z hcd),
  refine โจg, g.2, _โฉ,
  { intros g1 hg1,
    have : g1 โ ((ฮป g : SL(2, โค), โโg 1) โปยน' {cd}),
    { rw [set.mem_preimage, set.mem_singleton_iff],
      exact eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2)) },
    exact hg โจg1, thisโฉ },
end

/-- The matrix `T = [[1,1],[0,1]]` as an element of `SL(2,โค)` -/
def T : SL(2,โค) := โจ![![1, 1], ![0, 1]], by norm_num [matrix.det_fin_two]โฉ

/-- The matrix `S = [[0,-1],[1,0]]` as an element of `SL(2,โค)` -/
def S : SL(2,โค) := โจ![![0, -1], ![1, 0]], by norm_num [matrix.det_fin_two]โฉ

lemma coe_S : โโS = ![![0, -1], ![1, 0]] := rfl

lemma coe_T : โโT = ![![1, 1], ![0, 1]] := rfl

lemma coe_T_inv : โโ(Tโปยน) = ![![1, -1], ![0, 1]] := by simp [coe_inv, coe_T, adjugate_fin_two]

lemma coe_T_zpow (n : โค) : โโ(T ^ n) = ![![1, n], ![0,1]] :=
begin
  induction n using int.induction_on with n h n h,
  { ext i j, fin_cases i; fin_cases j;
    simp, },
  { rw [zpow_add, zpow_one, coe_mul, h, coe_T],
    ext i j, fin_cases i; fin_cases j;
    simp [matrix.mul_apply, fin.sum_univ_succ, add_comm (1 : โค)], },
  { rw [zpow_sub, zpow_one, coe_mul, h, coe_T_inv],
    ext i j, fin_cases i; fin_cases j;
    simp [matrix.mul_apply, fin.sum_univ_succ, neg_add_eq_sub (1 : โค)], },
end

variables {z}

lemma coe_T_zpow_smul_eq {n : โค} : (โ((T^n) โข z) : โ) = z + n :=
by simp [coe_T_zpow]

-- If instead we had `g` and `T` of type `PSL(2, โค)`, then we could simply state `g = T^n`.
lemma exists_eq_T_zpow_of_c_eq_zero (hc : โโg 1 0 = 0) :
  โ (n : โค), โ (z : โ), g โข z = T^n โข z :=
begin
  have had := g.det_coe,
  replace had : โโg 0 0 * โโg 1 1 = 1, { rw [det_fin_two, hc] at had, linarith, },
  rcases int.eq_one_or_neg_one_of_mul_eq_one' had with โจha, hdโฉ | โจha, hdโฉ,
  { use โโg 0 1,
    suffices : g = T^(โโg 0 1), { intros z, conv_lhs { rw this, }, },
    ext i j, fin_cases i; fin_cases j;
    simp [ha, hc, hd, coe_T_zpow], },
  { use -โโg 0 1,
    suffices : g = -T^(-โโg 0 1), { intros z, conv_lhs { rw [this, SL_neg_smul], }, },
    ext i j, fin_cases i; fin_cases j;
    simp [ha, hc, hd, coe_T_zpow], },
end

/- If `c = 1`, then `g` factorises into a product terms involving only `T` and `S`. -/
lemma g_eq_of_c_eq_one (hc : โโg 1 0 = 1) :
  g = T^(โโg 0 0) * S * T^(โโg 1 1) :=
begin
  have hg := g.det_coe.symm,
  replace hg : โโg 0 1 = โโg 0 0 * โโg 1 1 - 1, { rw [det_fin_two, hc] at hg, linarith, },
  ext i j, fin_cases i; fin_cases j;
  simp [coe_S, coe_T_zpow, matrix.mul_apply, fin.sum_univ_succ, hg, hc],
end

/-- If `1 < |z|`, then `|S โข z| < 1`. -/
lemma norm_sq_S_smul_lt_one (h: 1 < norm_sq z) : norm_sq โ(S โข z) < 1 :=
by simpa [coe_S] using (inv_lt_inv z.norm_sq_pos zero_lt_one).mpr h

/-- If `|z| < 1`, then applying `S` strictly decreases `im`. -/
lemma im_lt_im_S_smul (h: norm_sq z < 1) : z.im < (S โข z).im :=
begin
  have : z.im < z.im / norm_sq (z:โ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  simp only [special_linear_group.im_smul_eq_div_norm_sq],
  field_simp [norm_sq_denom_ne_zero, norm_sq_ne_zero, S]
end

/-- The standard (closed) fundamental domain of the action of `SL(2,โค)` on `โ`. -/
def fd : set โ :=
{z | 1 โค (z : โ).norm_sq โง |z.re| โค (1 : โ) / 2}

/-- The standard open fundamental domain of the action of `SL(2,โค)` on `โ`. -/
def fdo : set โ :=
{z | 1 < (z : โ).norm_sq โง |z.re| < (1 : โ) / 2}

localized "notation `๐` := modular_group.fd" in modular

localized "notation `๐แต` := modular_group.fdo" in modular

lemma abs_two_mul_re_lt_one_of_mem_fdo (h : z โ ๐แต) : |2 * z.re| < 1 :=
begin
  rw [abs_mul, abs_two, โ lt_div_iff' (@two_pos โ _ _)],
  exact h.2,
end

lemma three_lt_four_mul_im_sq_of_mem_fdo (h : z โ ๐แต) : 3 < 4 * z.im^2 :=
begin
  have : 1 < z.re * z.re + z.im * z.im := by simpa [complex.norm_sq_apply] using h.1,
  have := h.2,
  cases abs_cases z.re;
  nlinarith,
end

/-- If `z โ ๐แต`, and `n : โค`, then `|z + n| > 1`. -/
lemma one_lt_norm_sq_T_zpow_smul (hz : z โ ๐แต) (n : โค) : 1 < norm_sq (((T^n) โข z) : โ) :=
begin
  have hzโ : 1 < z.re * z.re + z.im * z.im := hz.1,
  have hzn := int.nneg_mul_add_sq_of_abs_le_one n (abs_two_mul_re_lt_one_of_mem_fdo hz).le,
  have : 1 < (z.re + โn) * (z.re + โn) + z.im * z.im, { linarith, },
  simpa [coe_T_zpow, norm_sq],
end

lemma eq_zero_of_mem_fdo_of_T_zpow_mem_fdo {n : โค} (hz : z โ ๐แต) (hg : (T^n) โข z โ ๐แต) : n = 0 :=
begin
  suffices : |(n : โ)| < 1,
  { rwa [โ int.cast_abs, โ int.cast_one, int.cast_lt, int.abs_lt_one_iff] at this, },
  have hโ := hz.2,
  have hโ := hg.2,
  rw [โ coe_re, coe_T_zpow_smul_eq, add_re, int_cast_re, coe_re] at hโ,
  calc |(n : โ)| โค |z.re| + |z.re + (n : โ)| : abs_add' (n : โ) z.re
             ... < 1/2 + 1/2 : add_lt_add hโ hโ
             ... = 1 : add_halves 1,
end

/-- Any `z : โ` can be moved to `๐` by an element of `SL(2,โค)`  -/
lemma exists_smul_mem_fd (z : โ) : โ g : SL(2,โค), g โข z โ ๐ :=
begin
  -- obtain a gโ which maximizes im (g โข z),
  obtain โจgโ, hgโโฉ := exists_max_im z,
  -- then among those, minimize re
  obtain โจg, hg, hg'โฉ := exists_row_one_eq_and_min_re z (bottom_row_coprime gโ),
  refine โจg, _โฉ,
  -- `g` has same max im property as `gโ`
  have hgโ' : โ (g' : SL(2,โค)), (g' โข z).im โค (g โข z).im,
  { have hg'' : (g โข z).im = (gโ โข z).im,
    { rw [special_linear_group.im_smul_eq_div_norm_sq, special_linear_group.im_smul_eq_div_norm_sq,
      denom_apply, denom_apply, hg]},
    simpa only [hg''] using hgโ },
  split,
  { -- Claim: `1 โค โnorm_sq โ(g โข z)`. If not, then `Sโขgโขz` has larger imaginary part
    contrapose! hgโ',
    refine โจS * g, _โฉ,
    rw mul_action.mul_smul,
    exact im_lt_im_S_smul hgโ' },
  { show |(g โข z).re| โค 1 / 2, -- if not, then either `T` or `T'` decrease |Re|.
    rw abs_le,
    split,
    { contrapose! hg',
      refine โจT * g, by simp [T, matrix.mul, matrix.dot_product, fin.sum_univ_succ], _โฉ,
      rw mul_action.mul_smul,
      have : |(g โข z).re + 1| < |(g โข z).re| :=
        by cases abs_cases ((g โข z).re + 1); cases abs_cases (g โข z).re; linarith,
      convert this,
      simp [T] },
    { contrapose! hg',
      refine โจTโปยน * g, by simp [coe_T_inv, matrix.mul, matrix.dot_product, fin.sum_univ_succ], _โฉ,
      rw mul_action.mul_smul,
      have : |(g โข z).re - 1| < |(g โข z).re| :=
        by cases abs_cases ((g โข z).re - 1); cases abs_cases (g โข z).re; linarith,
      convert this,
      simp [coe_T_inv, sub_eq_add_neg] } }
end

section unique_representative

variables {z}

/-- An auxiliary result en route to `modular_group.c_eq_zero`. -/
lemma abs_c_le_one (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : |โโg 1 0| โค 1 :=
begin
  let c' : โค := โโg 1 0,
  let c : โ := (c' : โ),
  suffices : 3 * c^2 < 4,
  { rw [โ int.cast_pow, โ int.cast_three, โ int.cast_four, โ int.cast_mul, int.cast_lt] at this,
    replace this : c' ^ 2 โค 1 ^ 2, { linarith, },
    rwa [sq_le_sq, abs_one] at this },
  suffices : c โ? 0 โ 9 * c^4 < 16,
  { rcases eq_or_ne c 0 with hc | hc,
    { rw hc, norm_num, },
    { refine (abs_lt_of_sq_lt_sq' _ (by norm_num)).2,
      specialize this hc,
      linarith, }, },
  intros hc,
  replace hc : 0 < c^4, { rw pow_bit0_pos_iff; trivial, },
  have hโ := mul_lt_mul_of_pos_right (mul_lt_mul'' (three_lt_four_mul_im_sq_of_mem_fdo hg)
      (three_lt_four_mul_im_sq_of_mem_fdo hz) (by linarith) (by linarith)) hc,
  have hโ : (c * z.im) ^ 4 / norm_sq (denom โg z) ^ 2 โค 1 :=
    div_le_one_of_le (pow_four_le_pow_two_of_pow_two_le
      (upper_half_plane.c_mul_im_sq_le_norm_sq_denom z g)) (sq_nonneg _),
  let nsq := norm_sq (denom g z),
  calc 9 * c^4 < c^4 * z.im^2 * (g โข z).im^2 * 16 : by linarith
           ... = c^4 * z.im^4 / nsq^2 * 16 : by { rw [special_linear_group.im_smul_eq_div_norm_sq,
            div_pow], ring, }
           ... โค 16 : by { rw โ mul_pow, linarith, },
end

/-- An auxiliary result en route to `modular_group.eq_smul_self_of_mem_fdo_mem_fdo`. -/
lemma c_eq_zero (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : โโg 1 0 = 0 :=
begin
  have hp : โ {g' : SL(2, โค)} (hg' : g' โข z โ ๐แต), โโg' 1 0 โ? 1,
  { intros,
    by_contra hc,
    let a := โโg' 0 0,
    let d := โโg' 1 1,
    have had : T^(-a) * g' = S * T^d, { rw g_eq_of_c_eq_one hc, group, },
    let w := T^(-a) โข (g' โข z),
    have hโ : w = S โข (T^d โข z), { simp only [w, โ mul_smul, had], },
    replace hโ : norm_sq w < 1 := hโ.symm โธ norm_sq_S_smul_lt_one (one_lt_norm_sq_T_zpow_smul hz d),
    have hโ : 1 < norm_sq w := one_lt_norm_sq_T_zpow_smul hg' (-a),
    linarith, },
  have hn : โโg 1 0 โ? -1,
  { intros hc,
    replace hc : โโ(-g) 1 0 = 1, { simp [eq_neg_of_eq_neg hc], },
    replace hg : (-g) โข z โ ๐แต := (SL_neg_smul g z).symm โธ hg,
    exact hp hg hc, },
  specialize hp hg,
  rcases (int.abs_le_one_iff.mp $ abs_c_le_one hz hg);
  tauto,
end

/-- Second Main Fundamental Domain Lemma: if both `z` and `g โข z` are in the open domain `๐แต`,
where `z : โ` and `g : SL(2,โค)`, then `z = g โข z`. -/
lemma eq_smul_self_of_mem_fdo_mem_fdo (hz : z โ ๐แต) (hg : g โข z โ ๐แต) : z = g โข z :=
begin
  obtain โจn, hnโฉ := exists_eq_T_zpow_of_c_eq_zero (c_eq_zero hz hg),
  rw hn at hg โข,
  simp [eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hz hg, one_smul],
end

end unique_representative

end fundamental_domain

end modular_group
