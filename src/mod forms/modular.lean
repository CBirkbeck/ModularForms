import analysis.complex.automorphisms_half_plane
import analysis.complex.basic
import data.matrix.notation
import data.int.basic
import data.int.parity
import data.nat.gcd
import algebra.ordered_ring
import ring_theory.int.basic
import data.real.sqrt
import linear_algebra.affine_space.affine_subspace

open complex
open matrix
open matrix.special_linear_group
noncomputable theory


local notation `|` x `|` := _root_.abs x
local notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

-- special linear group over ℤ

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance SL2Z_action : mul_action SL(2, ℤ) H :=
mul_action.comp_hom H (SL_n_insertion (int.cast_ring_hom ℝ))

@[simp]
lemma smul_def_int (g : SL(2,ℤ)) (z : H) : ↑(g • z) = smul_aux g z :=
begin
  refl,
end

lemma smul_neg_SL2_int (g : SL(2,ℤ)) (z : H) : -g • z = g • z :=
begin
  rw subtype.ext_iff,
  simp only [smul_def_int, smul_aux_def, top, bottom],
  rw ← neg_div_neg_eq,
  congr' 1; simp; ring,
end


@[simp]
lemma bottom_def {g : SL(2,ℤ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 := by simp

@[simp]
lemma top_def {g : SL(2,ℤ)} {z : ℂ} : top g z = g.1 0 0 * z + g.1 0 1 := by simp



lemma im_smul_SL' (g : SL(2, ℤ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (g.1 1 0 * z + g.1 1 1)) :=
by simpa using im_smul_SL g z

lemma im_smul_SL'' (g : SL(2, ℤ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (bottom g z)) :=
im_smul_mat_complex


@[simp]
lemma smul_sound {g : SL(2,ℤ)} {z : H} : ((g:SL(2,ℝ)) • z).1 = smul_aux g z :=
rfl

-- T and S

def T : SL(2,ℤ) := { val := ![![1, 1], ![0, 1]], property := by simp [det2] }

def S : SL(2,ℤ) := { val := ![![0, -1], ![1, 0]], property := by simp [det2] }

example : T⁻¹ * T = 1 := inv_mul_self T

example { R : SL(2,ℤ) } : R * T = 1 → R = T⁻¹ := eq_inv_of_mul_eq_one

example { R : SL(2,ℤ) } : T * R = 1 → T⁻¹ = R := inv_eq_of_mul_eq_one

example { x y : SL(2,ℤ)} (h : x.1 = y.1) : x = y := subtype.eq h

@[simp]
lemma mat_congr_SL { x y : SL(2,ℤ) } : x = y ↔ x.val = y.val := subtype.ext_iff_val

@[simp]
lemma mat_ext_iff  {F : Type*} [comm_ring F] (x y : matrix (fin 2) (fin 2) F) :
  x = y ↔ x 0 0 = y 0 0 ∧ x 0 1 = y 0 1 ∧ x 1 0 = y 1 0 ∧ x 1 1 = y 1 1 :=
begin
  rw ←matrix.ext_iff,
  split,
  {
    intro h,
    rw h,
    tauto },
  {
    rintros ⟨h1, h2, h3, h4⟩ i j,
    fin_cases i; fin_cases j; assumption,
  }
end

@[simp]
lemma mat_one {F : Type*} [comm_ring F] : (![![1,0], ![0,1]] : matrix (fin 2) (fin 2) F)
  = (1 : matrix (fin 2) (fin 2) F) := by {simp}


lemma T_inv : T⁻¹ = { val := ![![1, -1], ![0, 1]], property := by simp [det2] } :=
begin
  suffices : T * { val := ![![1, -1], ![0, 1]], property := by simp [det2] } = 1,
  { exact inv_eq_of_mul_eq_one this},
  simp [T],
end

lemma T_n_def {n : ℤ} :  T^(-n) = (T⁻¹)^n := by {simp [inv_gpow, gpow_neg]}

lemma T_pow_ℕ {n : ℕ} : T ^ n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  induction n with n hn,
  { simp },
  { rw [pow_succ', hn, T],
    simp [add_comm] }
end

lemma T_inv_pow_ℕ {n : ℕ} : (T⁻¹)^n = { val := ![![1, -n], ![0, 1]], property := by simp [det2] } :=
begin
  induction n with n hn,
  simp,
  have : (T⁻¹) ^ n.succ = ((T⁻¹)^n)* (T⁻¹),
  {
    exact pow_succ' (T⁻¹) n,
  },
  rw this,
  rw hn,
  rw T_inv,
  simp,
end


lemma T_pow {n : ℤ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  by_cases n_ge_0 : 0 ≤ n,
  lift n to ℕ with n_ge_0,
  refine T_pow_ℕ,
  exact n_ge_0,
  have : T ^ n = T ^ (- (-n)) := by simp,
  rw this,
  rw T_n_def,
  generalize' hk : -n=k,
  have k_ge_0 : 0 ≤ k,
  {
    rw ← hk,
    linarith,
  },
  have : n = -k,
  {
    rw ← hk,
    ring,
  },
  rw this,
  lift k to ℕ using k_ge_0,
  rw gpow_coe_nat,
  norm_cast,
  rw T_inv_pow_ℕ,
end

lemma T_action {z : H} : (T • z).1 = z + 1 :=
begin
  convert @smul_sound T z,
  simp only [smul_aux_def, top, bottom, T, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
end


lemma Tn_action {z : H} {n : ℤ} : (T^n • z).1 = z + n :=
begin
  have := @smul_sound (T^n) z,
  convert this,
  rw smul_aux,
  rw T_pow,
  rw top,
  rw bottom,
  simp,
end

lemma S_action (z : H) : (S • z).1 = -z⁻¹ :=
begin
  convert @smul_sound S z,
  simp only [smul_aux_def, top, bottom, S, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
  ring,
end

def fundamental_domain : set H :=
{ z | 1 < (complex.norm_sq z) ∧ |(complex.re z)| < (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟c` := closure 𝒟


lemma whatever : 𝒟c = { z | 1 ≤ (complex.norm_sq z) ∧ |(complex.re z)| ≤ (1 :ℝ)/ 2 } :=
begin

  sorry,
end

def coprime_ints := { cd :  ℤ × ℤ //  int.gcd cd.1 cd.2 = 1 }

instance : has_coe coprime_ints (ℤ×ℤ) := ⟨ λ x, x.val⟩

section finite_pairs

open filter continuous_linear_map

lemma tendsto_at_top_norm_sq : tendsto norm_sq (cocompact ℂ) at_top :=
begin
  convert tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top,
  { simp [mul_self_abs] },
  { apply_instance },
  { apply_instance }
end

lemma tendsto_cocompact_of_left_inverse {α β : Type*} [topological_space α] [topological_space β]
  {f : α → β} {g : β → α} (hg : continuous g) (hfg : function.left_inverse g f) :
  tendsto f (cocompact α) (cocompact β) :=
begin
  rw tendsto_iff_eventually,
  simp only [mem_cocompact, eventually_iff_exists_mem],
  rintros p ⟨v, hv, hvp⟩,
  rw mem_cocompact at hv,
  obtain ⟨t, ht, htv⟩ := hv,
  refine ⟨(g '' t)ᶜ, _, _⟩,
  { rw mem_cocompact,
    refine ⟨g '' t, ht.image hg, rfl.subset⟩ },
  intros x hx,
  have : f x ∈ v,
  { apply htv,
    intros h,
    apply hx,
    have h₁ : g (f x) ∈ g '' t := ⟨f x, h, rfl⟩,
    convert h₁,
    calc x = id x : by simp
    ... = (g ∘ f) x : by { congr, rw hfg } },
  exact hvp (f x) this
end

lemma finite_pairs (z : H) :
  filter.tendsto (λ cd : coprime_ints , (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ).2 : ℂ)).norm_sq)
  cofinite at_top :=
begin
  have h₁ : tendsto (λ c : ℝ × ℝ, ↑c.1 * (z:ℂ) + c.2) (cocompact _) (cocompact _),
  { let g : ℂ →L[ℝ] ℝ×ℝ := im_clm.prod
      (im_clm.comp (((z:ℂ)• conj_clm ))),
    apply tendsto_cocompact_of_left_inverse ((z:ℂ).im⁻¹ • g).continuous,
    rintros ⟨c₁, c₂⟩,
    have hz : 0 < (z:ℂ).im := z.2,
    have : (z:ℂ).im ≠ 0 := hz.ne.symm,
    field_simp [g],
    ring },
  have h₂ : tendsto (λ c : ℤ × ℤ, ((c.1 : ℝ), (c.2 : ℝ))) cofinite (cocompact _),
  { convert int.tendsto_coe_cofinite.prod_map_coprod int.tendsto_coe_cofinite;
    simp [coprod_cocompact, coprod_cofinite] },
  have h₃ : tendsto (λ c : ℤ × ℤ, ((c.1 : ℂ) * z + (c.2 : ℂ)).norm_sq) cofinite at_top,
  { convert tendsto_at_top_norm_sq.comp (h₁.comp h₂),
    ext,
    simp },
  exact (h₃.comp (tendsto_embedding_cofinite (function.embedding.subtype _))),
end

end finite_pairs

---- delete later
lemma gcd_cast (a b : ℤ) : gcd a b = a.gcd b := (int.coe_gcd a b).symm

lemma gcd_eq_one_iff_coprime' (a b : ℤ) : gcd a b = 1 ↔ is_coprime a b :=
begin
  rw [←int.coe_gcd, ←int.coe_nat_one, int.coe_nat_inj', int.gcd_eq_one_iff_coprime],
end

lemma gcd_eq_one_iff_coprime'' (a b : ℤ) : (∃ c d , a*d-b*c=1) ↔ is_coprime a b :=
begin
  split,
  { rintros ⟨c, d, h⟩,
    rw is_coprime,
    use d,
    use (-c),
    convert h using 1,
    ring },
  { rintros ⟨c, d, h⟩,
    use (-d),
    use c,
    convert h using 1,
    ring },
end

lemma gcd_eq_one_iff_coprime''' (a b : ℤ) : (∃ c d , a*d-b*c=1) ↔ gcd a b = 1 :=
 iff.trans (gcd_eq_one_iff_coprime'' a b) (iff.symm (gcd_eq_one_iff_coprime' a b))


lemma bottom_row_coprime (g : SL(2, ℤ)) : int.gcd (g 1 0) (g 1 1) = 1 :=
begin
--- ALEX HOMEWORK
  have := @det2 _ _ g,
  have detIs := g.2,
  have e1 :  (∃ (c d : ℤ), (g 1 0) * d - (g 1 1) * c = 1),
  {
    use -(g 0 0),
    use -(g 0 1),
    symmetry,
    convert this using 1,
    symmetry,
    convert detIs,
    ring,
  },
  have := (gcd_eq_one_iff_coprime''' (g 1 0) (g 1 1)).mp e1,
  rw ←int.coe_gcd at this,
  norm_cast at this,
  exact this,
end

def bottom_row : SL(2, ℤ) → coprime_ints := λ g, ⟨(g.1 1 0, g.1 1 1), bottom_row_coprime g⟩

lemma bottom_row_surj : function.surjective bottom_row :=
begin
  intros cd,
  have cop : int.gcd (cd:ℤ×ℤ).1 (cd:ℤ×ℤ).2  = 1 := cd.2,
  let a := int.gcd_b (cd:ℤ×ℤ).1 (cd:ℤ×ℤ).2,
  let b := - int.gcd_a (cd:ℤ×ℤ).1 (cd:ℤ×ℤ).2,
  let A := ![![a ,b ], ![(cd:ℤ×ℤ).1, (cd:ℤ×ℤ).2]],
  have det_A_1 : det A = 1,
  { rw det2,
    simp [a, b, A],
    have := int.gcd_eq_gcd_ab (cd:ℤ×ℤ).1 (cd:ℤ×ℤ).2,
    rw cop at this,
    symmetry,
    convert this using 1,
    ring },
  use ⟨A, det_A_1⟩,
  rw bottom_row,
  simp [A],
end

lemma exists_g_with_min_bottom (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (bottom g z).norm_sq ≤ (bottom g' z).norm_sq  :=
begin
  haveI : nonempty coprime_ints := sorry,
  obtain ⟨cd, hcd⟩  := filter.tendsto.exists_forall_le (finite_pairs z),
  obtain ⟨g, hg⟩  := bottom_row_surj cd,
  use g,
  intros g',
  convert hcd (bottom_row g'),
  { simp [bottom_row] at hg,
    simp [bottom, ← hg], },
  simp [bottom_row],
end

lemma exists_g_with_max_Im (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ),  (g' • z).val.im ≤ (g • z).val.im :=
begin
  obtain ⟨g, hg⟩  := exists_g_with_min_bottom z,
  use g,
  intros g',
  have hgg := hg g',
  rw [im_smul_SL'', im_smul_SL''],
  rwa div_le_div_left,
  { exact im_pos_of_in_H' },
  { exact norm_sq_pos.mpr (@bottom_nonzero g' z z.2) },
  { exact norm_sq_pos.mpr (@bottom_nonzero g z z.2) },
end

section
/-! This is an attempt to do the maximin argument using more abstract existence theory. -/

open filter

--instance {α : Type*} [ring α] [topological_space α] {n m : Type*} [fintype n] [fintype m] :
 -- topological_space (matrix n m α) :=
--Pi.topological_space

instance {α : Type*} [ring α] [metric_space α] {n m : Type*} [fintype n] [fintype m] :
  metric_space (matrix n m α) :=
metric_space_pi


/- This needs to be added to mathlib!!! There is `preimage_subset_preimage_iff` but it
    requires `(hs : s ⊆ range f)`, which is only needed in the other direction! -/
lemma preimage_subset_preimage {α β : Type*} {s t : set α} {f : β → α} :
  s ⊆ t → f ⁻¹' s ⊆ f ⁻¹' t :=
begin
  intros h x, apply h
end

-- for `order.filter.basic`
lemma filter.tendsto.of_tendsto_comp {β A B : Type*} {lβ : filter β} {lA : filter A}
  {lB : filter B} {g : A → B} {mB : B → β}
  (hAβ : tendsto (mB ∘ g) lA lβ) (hBβ : comap mB lβ ≤ lB) :
  tendsto g lA lB :=
begin
  rw tendsto_iff_comap at hAβ ⊢,
  calc lA ≤ comap (mB ∘ g) lβ : hAβ
  ... ≤ comap g lB : by simpa [comap_comap] using comap_mono hBβ
end

-- for `order.filter.cofinite`
lemma function.injective.tendsto_cofinite {α A : Type*} {mA : A → α} (hmA : function.injective mA) :
  tendsto mA cofinite cofinite :=
λ s h, h.preimage (hmA.inj_on _)

-- ugly, clean up somehow?
-- for `topology.subset_properties`
lemma comap_cocompact {β B : Type*} [topological_space β] [topological_space B] {mB : B → β}
  (hmB : continuous mB) : comap mB (cocompact β) ≤ cocompact B :=
begin
  intros s,
  simp only [mem_comap_sets, mem_cocompact],
  rintros ⟨t, ht, hts⟩,
  use (mB '' t)ᶜ,
  simp only [mem_cocompact],
  split,
  refine ⟨mB '' t, ht.image hmB, set.subset.refl _⟩,
  rw set.compl_subset_comm at hts,
  rw ← set.compl_subset_compl,
  refine set.subset.trans hts _,
  tidy,
end

/- Is this non-crap? (More elegant phrasing?...) We know that $ℤ$ matrices are discrete in $ℝ$; so intersection of $Z$ matrices is discrete in line -/
lemma tendsto_inverse_image_fun {α β A B : Type*} [topological_space β] [topological_space B]
  {f : α → β} {g : A → B} {mA : A → α} {mB : B → β}
  (hmA : function.injective mA) (hmB : continuous mB) (h : f ∘ mA = mB ∘ g)
  --(h : ∀ x, f (mA x) = mB (g x))
  (hf : tendsto f cofinite (cocompact _)) :
  tendsto g cofinite (cocompact _) :=
begin
  refine filter.tendsto.of_tendsto_comp _ (comap_cocompact hmB),
  simpa [h] using hf.comp hmA.tendsto_cofinite,
  -- rintros s hK,
  -- rw mem_cocompact' at hK,
  -- obtain ⟨K, hK1, hK2⟩ := hK,
  -- have diag_chase : mA '' (g ⁻¹' K) ⊆ f ⁻¹' (mB '' K) := by tidy,
  -- have : (mB '' K)ᶜ ∈ cocompact β ,
  -- { rw mem_cocompact',
  --   refine ⟨mB '' K, is_compact.image hK1 hmB, _⟩,
  --   rw compl_compl },
  -- have : (f ⁻¹' (mB '' K)).finite,
  -- { convert (filter.mem_cofinite.mp (hf this)),
  --   simp only [set.preimage_compl, compl_compl] },
  -- have : (mA '' (g ⁻¹' K)).finite := set.finite.subset this diag_chase,
  -- have : (g ⁻¹' K).finite,
  -- { convert set.finite.preimage _ this,
  --   exact (function.injective.preimage_image hmA (g ⁻¹' K)).symm,
  --   exact set.inj_on_of_injective hmA _ },
  -- exact set.finite.subset this (preimage_subset_preimage hK2),
end



/- Is this non-crap? (More elegant phrasing?...) We know that $ℤ$ matrices are discrete in $ℝ$; so intersection of $Z$ matrices is discrete in line -/
lemma tendsto_inverse_image_fun' {α β : Type*} [topological_space β] (A : set α) (B : set β)
  {f : α → β} (hf₁ : ∀ x ∈ A, f x ∈ B ) (hf₂ : tendsto f cofinite (cocompact _)) :
  tendsto (subtype.map f (λ x h, set.mem_def.mp (hf₁ x h))) cofinite (cocompact _) :=
begin
  refine tendsto_inverse_image_fun subtype.coe_injective continuous_subtype_coe _ hf₂,
  intros y,
  simp,
end

/- Non-crap lemma but put it elsewhere ?  Maybe cocompact in discrete is cofinite -/
lemma cocompact_ℝ_to_cofinite_ℤ (ι : Type*) [fintype ι] :
  tendsto ((λ (p : ι → ℤ), (coe : ℤ → ℝ) ∘ p)) cofinite (cocompact (ι → ℝ)) :=
by simpa [←Coprod_cofinite,←Coprod_cocompact]
  using tendsto.prod_map_Coprod (λ i, int.tendsto_coe_cofinite)



/- Non-crap lemma: ℤ -matrices are cofinite inside comcompact ℝ matrices -/
lemma cocompact_ℝ_to_cofinite_ℤ_matrix {ι ι' : Type*} [fintype ι] [fintype ι']  :
  tendsto (λ m, matrix.map m (coe : ℤ → ℝ)) cofinite (cocompact (matrix ι ι' ℝ)) :=
begin
--  convert tendsto.pi_map_Coprod (λ i, cocompact_ℝ_to_cofinite_ℤ ι'),
  convert tendsto.prod_map_Coprod (λ i, cocompact_ℝ_to_cofinite_ℤ ι'),
  { exact Coprod_cofinite.symm },
  { exact Coprod_cocompact.symm }
end


/-- method 1 -/
def line (cd : coprime_ints) : set (matrix (fin 2) (fin 2) ℝ) :=
  {g | g 1 0 = (cd : ℤ × ℤ).1 ∧ g 1 1 = (cd : ℤ × ℤ).2 ∧ det g = 1}

/- Do we need this? Maybe delete
lemma line_proper (cd : coprime_ints) :
  map coe (cocompact (line cd)) = cocompact (matrix (fin 2) (fin 2) ℝ) :=
begin

  sorry
end
-/


-- make `line` an affine subspace of 2x2 matrices, using the following lemma
lemma line_det (cd : coprime_ints) {g : matrix _ _ ℝ} (hg : g ∈ line cd) :
  g 0 0 * cd.1.2 - g 0 1 * cd.1.1 = 1 :=
begin
  convert hg.2.2,
  rw [det2, hg.1, hg.2.1],
  ring,
end

lemma in_line (cd : coprime_ints) {g : SL(2, ℤ)} (hg : bottom_row g = cd) :
  ↑(g : SL(2, ℝ)) ∈ line cd :=
begin
  rw line,
  rw set.mem_set_of_eq,
  rw bottom_row at hg,
  simp only [subtype.val_eq_coe] at hg,
  split,
  simp [hg],
  sorry,
  split,
  simp [hg],
  sorry,
  exact (g: SL(2,ℝ)).2,
end

def to_line (cd : coprime_ints) (g : bottom_row ⁻¹' {cd}) : line cd :=
⟨↑(g : SL(2, ℝ)), in_line cd g.2⟩

/- Can be deduced from ...
lemma tendsto_line (cd : coprime_ints) : tendsto (to_line cd) cofinite (cocompact _) :=
begin

  sorry
end
-/

/-
def lattice_intersect (A : set (matrix (fin 2) (fin 2) ℝ)) :
  set (matrix (fin 2) (fin 2) ℤ) :=
(int.cast_ring_hom ℝ).map_matrix ⁻¹' (A : set (matrix (fin 2) (fin 2) ℝ))


example (cd : coprime_ints) : bottom_row ⁻¹' {cd} → (lattice_intersect (line cd)) :=
set.cod_restrict (coe : bottom_row ⁻¹' {cd} → (matrix (fin 2) (fin 2) ℤ)) (lattice_intersect (line cd))
begin
  rintros ⟨⟨g, hg'⟩, hg⟩,
  simp [lattice_intersect, line] at *,
  sorry
end

def lattice_intersect_fun (A : set (matrix (fin 2) (fin 2) ℝ)) :
  lattice_intersect A → A :=
inverse_image_fun A (int.cast_ring_hom ℝ).map_matrix

/-- lemma about intersection of affine subspaces with integer lattice -/
lemma tendsto_lattice_intersect_fun (A : set (matrix (fin 2) (fin 2) ℝ)) :
  tendsto (lattice_intersect_fun A) cofinite (cocompact _) :=
begin
  apply tendsto_inverse_image_fun,
  { sorry },
  { exact  pi_prod_cofinite (λ i, (pi_prod_cofinite (λ j, int.tendsto_coe_cofinite))) }
end

-/



def smul_aux' : (matrix (fin 2) (fin 2) ℝ) → ℂ → ℂ := sorry

def acbd : (matrix (fin 2) (fin 2) ℝ) → ℝ := λ g, (g 0 0) * (g 1 0) + (g 0 1)*(g 1 1)


lemma something1 (cd : coprime_ints) (z : H) (g : line cd) :
∃ w , (smul_aux' ↑g z).re = (acbd g)/(real.sqrt ((cd.1.1)^2+(cd.1.2)^2)) + w :=
begin
  sorry,
end


/- Needed: Conditions on a linear transformation for a given linear functional to be tendsto cocompact cocopmact
on the kernel of the linear transformation  -/


lemma tendsto_acbd (cd : coprime_ints):
  tendsto (λ g, acbd (↑g)) (cocompact (line cd)) (cocompact ℝ) :=
begin
  let cabs := _root_.abs cd.1.1,
  let dabs := _root_.abs cd.1.2,
  let maxCD := max cabs dabs,
  intros K hK ,
  rw mem_cocompact at hK,

  obtain ⟨ K1, hK1, hK2⟩  := hK,

  obtain ⟨ t, ht⟩  := (metric.bounded_iff_subset_ball 0).mp (is_compact.bounded hK1),
  rw mem_map,
  rw mem_cocompact,
  refine ⟨
  ((coe : line cd → (matrix (fin 2) (fin 2) ℝ)) ⁻¹'
   (metric.closed_ball (0: matrix (fin 2) (fin 2) ℝ) (max (2*(_root_.abs t)+1) maxCD) )),
   sorry, _⟩ ,
   --simp,
  rw set.compl_subset_comm,
  rw set.compl_subset_comm at hK2,
  intros g hg,
  simp [dist_eq_norm] at hg,
  simp only [set.mem_preimage, metric.mem_closed_ball,  int_cast_abs, subtype.val_eq_coe],
  have : acbd ↑g ∈ metric.closed_ball (0:ℝ) t,
  {
    apply ht,
    apply hK2,
    exact hg,
  },
  rw dist_pi_def,
  let a : nnreal := nnreal.of_real (max (2 * |t| + 1) ↑maxCD),
  rw ← nnreal.coe_of_real (max (2 * |t| + 1) ↑maxCD),
  norm_cast,
  have : (∀ (b : fin 2), b ∈ finset.univ → (λ (b : fin 2), nndist ((↑g: matrix _ _ ℝ) b) 0) b ≤ a) := sorry,
  refine @finset.sup_le nnreal (fin 2) _ (finset.univ) ((λ (b : fin 2), nndist ((↑g: matrix _ _ ℝ) b) (0))) a _,

  sorry
end

/- Non-crap lemma: given the line of cd, the real part of the action of g on z is cocompact -/
lemma tendsto_action (cd : coprime_ints) (z : H) :
  tendsto (λ g, (smul_aux' ↑g z).re) (cocompact (line cd)) (cocompact ℝ) :=
begin
  -- let g : ℝ → matrix (fin 2) (fin 2) ℝ :=

  have := something1 cd z,
  sorry
end

/- Non-crap lemma: Absolute value function is cocompact -/
lemma tendsto_at_top_abs :
  tendsto _root_.abs (cocompact ℝ) at_top :=
begin
  rw has_basis_cocompact.tendsto_iff at_top_basis_Ioi,
  { refine λ b _, ⟨set.Icc (-b) b, compact_Icc, λ x hx, _⟩,
    simpa [lt_abs, or_comm, lt_neg, not_and_distrib] using hx },
  { apply_instance },
  { apply_instance }
end

lemma sddsf (cd : coprime_ints) (z : ℂ) :
  tendsto (λ g : lattice_intersect (line cd), _root_.abs (smul_aux' ↑(lattice_intersect_fun _ g) z).re)
    cofinite at_top :=
(tendsto_at_top_abs.comp (tendsto_action cd z)).comp (tendsto_lattice_intersect_fun (line cd))

/-- method 2 -/
def line' (cd : coprime_ints) : set (ℝ × ℝ) :=
  {ab | ab.1 * (cd : ℤ × ℤ).2 - ab.2 * (cd : ℤ × ℤ).1 = 1}

def in_line' (cd : coprime_ints) {g : SL(2, ℤ)} (hg : bottom_row g = cd) :
  (↑(g 0 0), ↑(g 0 1)) ∈ line' cd :=
sorry

def to_line' (cd : coprime_ints) (g : bottom_row ⁻¹' {cd}) : line' cd :=
⟨(g 0 0, g 0 1), in_line' cd g.2⟩

lemma tendsto_line' (cd : coprime_ints) : tendsto (to_line' cd) cofinite (cocompact _) := sorry

lemma inv_image_eq_line (cd : coprime_ints) :
  bottom_row ⁻¹' {cd} = (prod.map coe coe : ℤ × ℤ → ℝ × ℝ) ⁻¹' line cd :=
sorry

end

/- Non-crap lemma but content-free; should be combination of building blocks -/
lemma something' (z:H) (cd : coprime_ints) :
  tendsto (λ g : bottom_row ⁻¹' {cd}, _root_.abs (((g : SL(2, ℤ)) • z).val.re)) cofinite at_top :=
begin

end

lemma something (z:H) (cd : coprime_ints) :
  ∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ), bottom_row g = bottom_row g' →
  _root_.abs ((g • z).val.re) ≤ _root_.abs ((g' • z).val.re)) :=
begin

  sorry,
end

variables {g : SL(2,ℤ)} {z : H}

lemma im_S_z {z : H} : (S • z).val.im = z.val.im / z.val.norm_sq :=
begin
  rw im_smul_SL'',
  rw bottom,
  simp,
  rw S,
  simp,
end

lemma im_lt_im_S {z : H} (h: norm_sq z.val < 1) : z.val.im < (S • z).val.im :=
begin
  rw im_S_z,
  have imz : 0 < z.val.im := im_pos_of_in_H',
  have hnz : 0 < norm_sq z.val,
  {
    rw norm_sq_pos,
    intro h,
    rw h at imz,
    rw zero_im at imz,
    linarith,
  },
  set N := norm_sq z.val with hN,
  set zim := z.val.im with hzim,
  have : zim * N < zim, by nlinarith,
  exact (lt_div_iff hnz).mpr this,
end

/- TODO : prove directly instead of by contradiction
-/
lemma norm_sq_ge_one_of_act_S {z : H} (h : (S • z).val.im ≤ z.val.im) : 1 ≤ norm_sq z.val :=
begin
  by_contradiction hcontra,
  push_neg at hcontra,
  have := im_lt_im_S hcontra,
  linarith,
end

lemma T_inv_action {z : H} : (T⁻¹ • z).1 = z - 1 :=
begin
  convert @smul_sound (T⁻¹) z,
  rw smul_aux,
  rw T_inv,
  simp,
  ring,
end

lemma half_ge_x_T_inv (x : ℝ) (h : 1/2 < x) : |x - 1| < x :=
begin
  have : -(x) < x-1 ∧ x-1 < x := by split; linarith,
  exact abs_lt.mpr this,
end

lemma half_le_neg_x_T (x : ℝ) (h : 1/2 < -x) : |x + 1| < |x| :=
begin
  have : -|x| < x+1 ∧ x+1 < |x|,
  { have : |x| = -x,
    { refine _root_.abs_of_neg _,
      linarith },
    rw this,
    split; linarith },
  exact abs_lt.mpr this,
end

lemma re_ge_half_of_act_T {z : H}
(h: 1/2 < _root_.abs (z:ℂ).re)
:
((_root_.abs (T • z).val.re) < _root_.abs z.val.re) ∨
((_root_.abs (T⁻¹ • z).val.re) < _root_.abs z.val.re)
:=
begin
  rw T_action,
  rw T_inv_action,
  let x := z.val.re,
  simp,
  rw lt_abs at h,
  cases h,
  { right,
    convert (half_ge_x_T_inv ((z:ℂ).re) h),
    exact _root_.abs_of_nonneg (by linarith) },
  { left,
    exact half_le_neg_x_T (z:ℂ).re h },
end

lemma bot_row_eq_diff_by_unipotent (g g' : SL(2,ℝ)) (h : bottom_row g = bottom_row g') :
∃ (x:ℝ), g = (![![1,x],![0,1]],_) * g' :=
begin
  -- human proof: g= a,b,c,d, g' = a' b' c d (same c d!)
  -- then g*g⁻¹ = (a b c d)(d -b' -c a') = (1 * 0 1)

--  let ![![a,b],![c,d]] := g.1,
  let Tn := g * g'⁻¹,
  sorry,

end

lemma find_g_with_min_re (z:H) (cd : coprime_ints) :
∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ),  bottom_row g = bottom_row g' →
_root_.abs ((g • z).val.re) ≤ _root_.abs ((g' • z).val.re)) :=
begin
/-  -- Argh this is all wrong;
-- Need to look somehow at the set of all preimages of cd
-- among those, choose g with minimal real part
-- the rest is tautological
  obtain ⟨g, hg⟩ := bottom_row_surj cd,
  use g,
  split,
  exact hg,
  intros g' hg',
  by_contradiction hcontra,
  push_neg at hcontra,
  obtain ⟨n, hn⟩ := bot_row_eq_diff_by_T_n g g' hg',
  rw hn at hcontra,
  -/
  sorry,
end



lemma is_fundom {z : H} : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  obtain ⟨g, hg2⟩ := exists_g_with_max_Im z,
  obtain ⟨n, hn⟩ := find_appropriate_T ((g : SL(2,ℤ)) • z),
  use (T^n * g),
  have hS : S ∈ G' := by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' := by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' := by {apply subgroup.gpow_mem G' hT},
--  have hTng : T^n * g ∈ G' := G'.mul_mem hTn hg1,
--  have hSTg : S * T^n * g ∈ G' := G'.mul_mem (G'.mul_mem hS hTn) hg1,
  replace hg2 := hg2 (S * T^n * g), -- hSTg,
  set z' := (T^n * g) • z with z'df,
  have imz' : z'.val.im = ((g : SL(2,ℤ)) • z).val.im,
  { rw [z'df, ← smul_smul, im_Tn_z] },
  rw smul_smul at hn,
  change |z'.val.re| ≤ 1 / 2 at hn,
  suffices : 1 ≤ z'.1.norm_sq,
  -- by exact ⟨hTn,⟨this, hn⟩⟩,
  {
    exact ⟨this, hn⟩,
  },

  set w := (S * T^n * g) • z with hw,
  apply norm_sq_ge_one_of_act_S,
  replace hw : w = S•z',
  {rw [hw, z'df, smul_smul, mul_assoc]},
  rw [imz', ← hw],
  exact hg2,
end

@[simp]
lemma fundom_aux_1 {z : H} (hz : z ∈ 𝒟) (h' : T • z ∈ 𝒟) : z.val.re = -1/2 := sorry

@[simp]
lemma fundom_aux_2 {z : H} (hz : z ∈ 𝒟) (h' : T⁻¹ • z ∈ 𝒟) : z.val.re = 1/2 := sorry

@[simp]
lemma fundom_aux_3 {z : H} (hz : z ∈ 𝒟) (h' : S • z ∈ 𝒟) : z.val.abs = 1 := sorry

/- Why is this not doable by linarith directly? -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ a / b) : b ≤ 1 :=
begin
  suffices: a * b ≤ a, nlinarith,
  rw le_div_iff hb at h,
  exact h,
end

lemma namedIs (c :ℕ ) (h: c≤ 1) :  c=0 ∨ c=1 :=
begin
  cases nat.of_le_succ h,
  {
    left,
    exact le_zero_iff.mp h_1,
  },
  right,
  exact h_1,
end

lemma namedIsZ (c :ℤ  ) (h: c≤ 1) (h2: 0≤ c) :  c=0 ∨ c=1 :=
begin
  --lift n to ℕ using hn
  lift c to ℕ using h2,
  norm_cast,
  refine namedIs _ _ ,
  exact_mod_cast h,
end

-- Describe closure of D as union of boundary segments and interior.
-- Then the lemma goes by cases on where z and z'

lemma fundom_no_repeats' (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟') (hz' : z' ∈ 𝒟') :
  (z = z') :=
begin
  sorry,
end

lemma is_fundom'' {z : H} : ∃ g : SL(2,ℤ), g • z ∈ closure fundamental_domain' :=
begin
  sorry,
end


lemma fundom_no_repeats (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟) (hz' : z' ∈ 𝒟) :
  (z = z') ∨
  (z.val.re = -1/2 ∧ z' = T • z) ∨
  (z'.val.re = -1/2 ∧ z = T • z') ∨
  (z.val.abs = 1 ∧ z'.val.abs = 1 ∧ z' = S • z ∧ z = S • z') :=
begin
  wlog hwlog : z.val.im ≤ z'.val.im,
  {
    by_cases hne : z = z', tauto,
    right,
    replace h := sign_coef h,
    obtain ⟨g, hcpos, hac, hg⟩ := h,
    set a := g.1 0 0,
    set b := g.1 0 1,
    set c := g.1 1 0 with ←cdf,
    set d := g.1 1 1 with ←ddf,
    have hcd : complex.norm_sq (c * z + d) ≤ 1,
    {
      have himzpos : 0 < z.val.im := im_pos_of_in_H',
      have hnz : 0 < complex.norm_sq (c * z + d),
      {
        rw norm_sq_pos,
        intro hcontra,
        rw [← cdf, ← ddf, ← bottom_def] at hcontra,
        exact czPd_nonZ_CP (ne.symm (ne_of_lt himzpos)) hcontra,
      },
      suffices: z.val.im * complex.norm_sq (c * z + d) ≤ z.val.im, nlinarith,
      rw [hg, im_smul_SL',cdf,ddf, le_div_iff hnz] at hwlog,
      exact hwlog,
    },
    have hc : _root_.abs c ≤ 1,
    {
      sorry
    },
    replace hc : c = 0 ∨ c = 1,
    {

      rw abs_le at hc,
      exact namedIsZ c hc.2 hcpos,
    },
    rcases hc with  hc | hc ,
    { -- case c = 0
      have ha : a = 1 := (hac hc).2,
      have hd : d = 1 := (hac hc).1,
      have hgT : g = T^b,
      {
        rw T_pow,
        apply subtype.eq,
        simp,
        tauto,
      },
      have hb : _root_.abs c ≤ 1,
      {
        sorry
      },
      replace hb : b = -1 ∨ b = 0 ∨ b = 1,
      {
        sorry
      },
      rcases hb with hb | hb | hb,
      all_goals {rw hb at hgT, rw hgT at hg, clear hb, clear hgT, simp at hg},
      {
        right, left,
        rw ←inv_smul_eq_iff at hg,
        rw ←hg at hz,
        rw fundom_aux_1 hz' hz,
        tauto,
      },
      { tauto },
      {
        left,
        rw hg at hz',
        rw fundom_aux_1 hz hz',
        tauto,
      }
    },
    { -- case c = 1
      sorry
    }
  },
  obtain ⟨g, hg⟩ := h,
  have hh : ∃ g : SL(2,ℤ), z = g • z' := ⟨g⁻¹, by {simp [eq_inv_smul_iff, hg]}⟩,
  specialize this hh hz' hz,
  tauto,
end


-- define fundamental domain
-- open region, g.z=w -> g=1
-- all z in H, exists g in G such that g.z in closure F

-- define std domain {|z|>1, |z.re| <1/2}

-- proof std domain is a fund dom for G

-- define modular form1

-- define Eisenstein series

-- prove E-sereis are modular

-- E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}} 1/(cz+d)^k

/-
  human:
  d/ dz E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}}  d/ dz 1/(cz+d)^k

  OR

  E(z,k) - E(w,k)
  =
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)
=
(z-w)   *
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)

-/

/- define Ramanujan delta

-/


-- @[simp]
-- lemma coeff_coe {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)).val i j = ((g.val i j) : ℝ) := by refl

-- @[simp]
-- lemma coeff_coe' {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)) i j = ((g i j) : ℝ) := by refl

-- lemma div_eq_mul_conj_div_norm_sq {z w : ℂ} : z / w = (z * (w.conj)) / complex.norm_sq w :=
-- begin
--   rw [div_eq_mul_inv, inv_def, div_eq_mul_inv, mul_assoc],
--   norm_num,
-- end


-- @[simp]
-- lemma mul_congr { x y : SL(2,ℤ)} : x * y = 1 ↔ x.1 * y.1 = 1 := by simp




-- lemma e14 : at_top ≤ cocompact ℝ :=
-- begin
--   intros s hs,
--   simp only [mem_at_top_sets],
--   simp only [mem_cocompact] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ := e7 ht.bounded,
--   use r + 1,
--   intros b hb,
--   apply hts,
--   intros hb',
--   have := hr _ hb',
--   simp only [real.norm_eq_abs, abs_le] at this,
--   linarith
-- end

-- lemma e16 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (s : set ℝ) :
--   norm ⁻¹' s ∈ cocompact E ↔ s ∈ (at_top : filter ℝ) :=
-- begin
--   rw [mem_at_top_sets, mem_cocompact],
--   split,
--   { rintros ⟨t, ht, hts⟩,
--     obtain ⟨r, hr⟩ := e7 ht.bounded,
--     use r + 1,
--     intros b hb,
--     obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
--     have h_norm : ∥b • (∥x∥)⁻¹ • x∥ = b := sorry,
--     have : b • (∥x∥)⁻¹ • x ∈ tᶜ,
--     { have := mt (hr (b • (∥x∥)⁻¹ • x)),
--       apply this,
--       linarith },
--     simpa [h_norm] using hts this },
--   { rintros ⟨r, hr⟩,
--     refine ⟨metric.closed_ball 0 r, proper_space.compact_ball 0 r, _⟩,
--     intros x hx,
--     simp at hx,
--     exact hr (∥x∥) hx.le },
-- end

-- lemma e17 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] :
--   map norm (cocompact E) = (at_top : filter ℝ) :=
-- begin
--   ext s,
--   exact e16 s
-- end

-- lemma e15 {α : Type*} {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (l : filter α) {f : α → E} :
--   tendsto f l (cocompact E) ↔ tendsto (norm ∘ f) l at_top :=
-- begin
--   split,
--   { exact tendsto_norm_cocompact_at_top.comp },
--   sorry
-- end


-- lemma finite_integers {M : ℝ} :
--   set.finite {c : ℤ | |(c : ℝ)| ≤ M } :=
-- begin
--     let s:= finset.Ico_ℤ (⌊-M⌋) (⌊M⌋+1),
--     suffices : {c : ℤ | |↑c| ≤ M} ⊆  s,
--     {
--       refine set.finite.subset s.finite_to_set this,
--     },
--     intros c,
--     simp [s],
--     intros h,
--     rw abs_le at h,
--     have h1 := h.1,
--     have h2 := h.2,
--     split,
--     {
--       have : (⌊-M⌋ :ℝ ) ≤ -M :=  floor_le (-M),
--       have := le_trans this h1,
--       exact_mod_cast this,
--     },
--     {
--       have : (c:ℝ ) < (⌊M⌋:ℝ) + 1,
--       {
--         calc
--         (c:ℝ) ≤ M           : h2
--         ...   < (⌊M⌋:ℝ) + 1 : M_lt_Mp1 M,
--       },

--       norm_cast at this,
--       exact this,
--     },
-- end

-- -- for `normed_space.basic`
-- lemma metric.bounded.exists_norm_le {α : Type*} [normed_group α] {s : set α} (hs : metric.bounded s) :
--   ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
-- begin
--   rcases s.eq_empty_or_nonempty with (rfl | hs'),
--   { simp },
--   obtain ⟨R₁, hR₁⟩ := hs,
--   obtain ⟨x, hx⟩ := hs',
--   use ∥x∥ + R₁,
--   intros y hy,
--   have : ∥x - y∥ ≤ R₁ := by simpa [dist_eq_norm] using hR₁ x y hx hy,
--   have := norm_le_insert x y,
--   linarith
-- end

-- -- for `order.filter.basic`
-- lemma e9 {α : Type*} (l : filter α) {s t : set α} (hst : s ∪ tᶜ ∈ l) (ht : t ∈ l) : s ∈ l :=
-- begin
--   refine mem_sets_of_superset _ (s.inter_subset_left t),
--   convert inter_mem_sets hst ht using 1,
--   ext,
--   simp only [set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq],
--   finish
-- end


-- lemma e10 {α : Type*} {l : filter α} {E F : Type*} [normed_group E] [normed_group F] [proper_space E]
--   {f : α → E} {g : α → F} (h : asymptotics.is_O f g l) (hf : tendsto f l (cocompact E)) :
--   tendsto g l (cocompact F) :=
-- begin
--   rw tendsto_def at ⊢ hf,
--   intros s hs,
--   simp [filter.mem_cocompact'] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ : ∃ r, ∀ p ∈ sᶜ, ∥p∥ ≤ r := (ht.bounded.subset hts).exists_norm_le,
--   rw asymptotics.is_O_iff at h,
--   obtain ⟨c, hc⟩ := h,
--   rw eventually_iff_exists_mem at hc,
--   obtain ⟨v, hv, hvfg⟩ := hc,
--   have : ∀ x ∈ v ∩ g ⁻¹' sᶜ, x ∈ f ⁻¹' metric.closed_ball (0:E) (c * r),
--   { rintros x ⟨hxv, hxgs⟩,
--     have := hr (g x) hxgs,
--     have := hvfg x hxv,
--     simp,
--     sorry },
--   have h₂ : f ⁻¹' (metric.closed_ball (0:E) (c * r))ᶜ ⊆ g ⁻¹' s ∪ vᶜ,
--   { intros x,
--     have := this x,
--     simp only [set.mem_preimage, set.mem_inter_eq, set.mem_compl_eq] at this,
--     simp only [set.mem_preimage, set.mem_union_eq, set.mem_compl_eq],
--     contrapose!,
--     finish },
--   have h₃ : f ⁻¹' (metric.closed_ball 0 (c * r))ᶜ ∈ l,
--   { apply hf (metric.closed_ball (0:E) (c * r))ᶜ,
--     simp only [mem_cocompact'],
--     refine ⟨metric.closed_ball (0:E) (c * r), proper_space.compact_ball 0 (c * r), _⟩,
--     simp },
--   have : g ⁻¹' s ∪ vᶜ ∈ l := mem_sets_of_superset h₃ h₂,
--   refine e9 l this hv
-- end


-- lemma tendsto_cocompact_of_antilipschitz {α β : Type*} [metric_space α] [proper_space α]
--   [metric_space β] {c : nnreal} {f : α → β} (hf : antilipschitz_with c f) :
--   tendsto f (cocompact α) (cocompact β) :=
-- begin
--   rw tendsto_iff_eventually,
--   simp only [mem_cocompact, eventually_iff_exists_mem],
--   rintros p ⟨v, hv, hvp⟩,
--   rw mem_cocompact' at hv,
--   obtain ⟨t, ht, htv⟩ := hv,
--   obtain ⟨r, hr⟩ := ht.bounded,
--   -- have := hf.bounded_preimage ht.bounded,
--   by_cases h : ∃ x, ¬ p (f x),
--   { obtain ⟨x, hx⟩ := h,
--     have hxt : f x ∈ t := htv (mt (hvp (f x)) hx),
--     refine ⟨(metric.closed_ball x (c * r))ᶜ, _, _⟩,
--     { rw mem_cocompact,
--       refine ⟨metric.closed_ball x (c * r), proper_space.compact_ball x (↑c * r), rfl.subset⟩ },
--     intros x' hx',
--     have hxx'r : r < dist (f x) (f x'),
--     { simp at hx',
--       rw dist_comm at hx',
--       rw antilipschitz_with_iff_le_mul_dist at hf,
--       have : dist x x' ≤ c * dist (f x) (f x') := hf x x',
--       have := lt_of_lt_of_le hx' this,
--       sorry }, -- this follows from the previous line except with a special case for `c = 0`
--     have := mt (hr (f x) (f x') hxt),
--     push_neg at this,
--     have := (mt (@htv (f x'))) (this hxx'r),
--     apply hvp,
--     simpa using this },
--   { push_neg at h,
--     refine ⟨set.univ, univ_mem_sets, _⟩,
--     intros x hx,
--     exact h x },
-- end

-- lemma tendsto_at_top_sum_sq :
--   tendsto (λ x : ℝ × ℝ, x.1 ^ 2 + x.2 ^ 2) (cocompact (ℝ × ℝ)) at_top :=
-- begin
--   refine tendsto_at_top_mono _
--     (tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top),
--   rintros ⟨x₁, x₂⟩,
--   simp only [prod.norm_def, real.norm_eq_abs],
--   cases max_choice (|x₁|) (|x₂|) with h h;
--   { rw [h, abs_mul_abs_self],
--     nlinarith },
-- end

-- @[simp] lemma expand_sum_01 {R : Type*} [ring R] (f : fin 2 → R ) :
-- (∑ (x : fin 2), f x) = f 0 + f 1 :=
-- by simp [fin.sum_univ_succ]
