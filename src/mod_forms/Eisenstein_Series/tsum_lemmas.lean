import data.complex.exponential
import analysis.calculus.series
import analysis.calculus.parametric_interval_integral
import data.complex.basic

noncomputable theory

open topological_space set  metric filter function complex measure_theory

open_locale interval real nnreal ennreal topology big_operators nat classical



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

lemma has_sum_pnat' (f : ℕ → ℂ) (hf2: summable f) : has_sum (λ n:ℕ, f(n + 1)) (∑' (n : ℕ+), f n) :=
begin
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
  simp,
end

lemma nat_pos_tsum2' {α : Type*}[topological_space α] [add_comm_monoid α] (f : ℕ → α) :
summable (λ (x : ℕ+), f x) ↔ summable (λ x : ℕ, (f (x + 1))):=
begin
rw ←equiv.summable_iff (_root_.equiv.pnat_equiv_nat),
split,
intro hf,
apply summable.congr hf,
intro b,
simp,
intro hf,
apply summable.congr hf,
intro b,
simp,
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

lemma tsum_pnat' (f : ℕ → ℂ) : ∑' (n : ℕ+), f n = ∑' n, f (n + 1) :=
begin
by_cases hf2: summable (λ (n : ℕ+), f n),
have hpos : has_sum (λ n:ℕ, f(n + 1)) (∑' (n : ℕ+), f n), by {
  have:= (_root_.equiv.pnat_equiv_nat).has_sum_iff,
  simp_rw equiv.pnat_equiv_nat at *,
  simp at *,
  rw ←this,
  have hf3 : summable ((λ (n : ℕ), f (n + 1)) ∘ pnat.nat_pred), by {
    apply summable.congr hf2,
    intro b, simp,},
  rw (summable.has_sum_iff hf3),
  congr,
  funext,
  simp,},
apply symm,
apply hpos.tsum_eq,
have h1 := tsum_eq_zero_of_not_summable hf2,
rw nat_pos_tsum2' at hf2,
have h2:= tsum_eq_zero_of_not_summable hf2,
simp [h1,h2],
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

lemma sumaux (f : ℕ × ℕ → ℂ) (e : ℕ+) : ∑ (x : nat.divisors_antidiagonal e), f x =
  ∑ (x : ℕ × ℕ) in nat.divisors_antidiagonal e, f x :=
begin
simp only [finset.univ_eq_attach],
apply finset.sum_finset_coe,
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


lemma has_deriv_at_tsum_fun {α : Type*} [ne_bot (at_top : filter (finset α))] (f : α → ℂ → ℂ)
  {s : set ℂ} (hs : is_open s) (x : ℂ) (hx  : x ∈ s)
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
