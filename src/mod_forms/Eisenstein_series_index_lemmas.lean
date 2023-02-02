import tactic.pi_instances
import mod_forms.mod_group
import linear_algebra.matrix.general_linear_group
import for_mathlib.mod_forms2
import data.matrix.notation
import data.setoid.partition
import topology.instances.ennreal
import topology.instances.nnreal
import mod_forms.Riemann_zeta_fin
import mod_forms.holomorphic_functions
import order.filter.archimedean
import mod_forms.Weierstrass_M_test
import analysis.complex.upper_half_plane.basic
import analysis.complex.upper_half_plane.topology
import topology.compact_open
import analysis.calculus.deriv
import number_theory.modular
import mod_forms.mat_m

universes u v w

open complex
open modular_group
open integral_matrices_with_determinant
open_locale big_operators nnreal classical filter matrix upper_half_plane

local attribute [-instance] matrix.special_linear_group.has_coe_to_fun
local notation `SL2Z`:=matrix.special_linear_group (fin 2) ℤ
local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _
noncomputable theory

namespace Eisenstein_series

lemma ridic (a b c d : ℤ): a*d-b*c=1 → a*d-c*b=1:=
begin
intro h, linarith,
end


lemma ridic2 (a b c d z : ℤ) (h: a*d-b*c=1):  z*d*a-z*c*b=z:=
begin
ring_nf, rw h, rw one_mul,
end

/- This is the permutation of the summation index coming from the moebius action-/
def Ind_perm (A : SL2Z ): ℤ × ℤ → ℤ × ℤ:=
λ z, (z.1 * (A.1 0 0) + z.2 * (A.1 1 0), z.1 * (A.1 0 1) + z.2 * (A.1 1 1))

lemma det_sl_one  (M : SL2Z) : (M.1 0 0 * M.1 1 1 + -(M.1 0 1 * M.1 1 0)) = 1 :=
begin
apply det_m,
end

def Ind_equiv (A : SL2Z): ℤ × ℤ ≃ ℤ × ℤ  :=
{ to_fun:=Ind_perm A,
  inv_fun:=Ind_perm A⁻¹,
  left_inv:= λ z,
  by {simp_rw Ind_perm,
    ring_nf,
    have hdet := det_sl_one A,
    simp only [subtype.val_eq_coe,SL2Z_inv_a, SL2Z_inv_c, neg_mul, SL2Z_inv_b, SL2Z_inv_d] at *,
    nth_rewrite 1 mul_comm,
    nth_rewrite 2 mul_comm,
    ext,
    simp only,
    simp_rw hdet,
    ring,
    simp only,
    nth_rewrite 2 add_comm,
    simp_rw [hdet],
    ring,},
  right_inv :=  λ z, by
  { simp_rw Ind_perm,
    ring_nf,
    have hdet := det_sl_one A,
    simp only [subtype.val_eq_coe,SL2Z_inv_a, SL2Z_inv_c, neg_mul, SL2Z_inv_b, SL2Z_inv_d] at *,
    ext,
    simp only [mul_neg],
    nth_rewrite 2 mul_comm,
    simp_rw hdet,
    ring,
    simp only [mul_neg],
    nth_rewrite 2 add_comm,
    nth_rewrite 4 mul_comm,
    simp_rw [hdet],
    ring,}}


@[simp]lemma ind_simp (A: SL2Z) (z : ℤ × ℤ):
  Ind_equiv A z = (z.1* (A.1 0 0) +z.2* (A.1 1 0), z.1*(A.1 0 1)+z.2* (A.1 1 1)) :=
begin
refl,
end

lemma max_aux' (a b : ℕ): max a b = a ∨ max a b =b:=
begin
apply max_choice,
end

lemma max_aux (a b : ℕ):a= max a b  ∨  b=max a b :=
begin
have:= (max_aux' a b),  cases this, simp [this], simp [this],
end

lemma max_aux'' (a b n : ℕ) (h: max a b =n): a=n ∨ b =n :=
begin
rw ← h,
apply max_aux,
end


lemma max_aux3 (a b n : ℕ) (h: max a b =n): a ≤ n ∧ b ≤ n :=
begin
rw ← h, split, exact le_max_left a b, exact le_max_right a b,
end

/--For `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that the maximum of the
absolute values of the pair is `m` -/
def Square (m: ℕ): finset (ℤ × ℤ):=
((finset.Ico (-m : ℤ) (m+1)).product (finset.Ico (-m : ℤ) (m+1))).filter
(λ x, max (x.1).nat_abs (x.2).nat_abs = m)

/--For `m : ℤ` this is the finset of `ℤ × ℤ` of elements such that..-/
def Square2 (m: ℕ) : finset (ℤ × ℤ):=
  (finset.Ico (-m : ℤ) (m+1)).product {m } ∪ (finset.Ico (-m : ℤ) (m+1)).product {-(m: ℤ)} ∪
  ({m} : finset (ℤ)).product (finset.Ico (-m+1) (m)) ∪
  ({-m} : finset (ℤ)).product (finset.Ico (-m+1) (m))


lemma square2_card (n : ℕ) (h: 1 ≤ n) : (finset.card (Square2 n) : ℤ) = 8 * n  :=
begin
    rw [Square2,finset.card_union_eq, finset.card_union_eq, finset.card_union_eq,finset.card_product,
    finset.card_product, finset.card_product, finset.card_product],
    { simp only [finset.card_singleton, mul_one, one_mul],
      have hn : -(n : ℤ) ≤ n+1, by {linarith,},
      have hn2 : -(n : ℤ) +1 ≤ n, by {linarith,},
      have r1 := int.card_Ico_of_le (-(n : ℤ)) (n+1) hn,
      have r2 := int.card_Ico_of_le (-(n : ℤ)+1) (n) hn2,
      simp only [int.coe_nat_add, int.card_Ico, sub_neg_eq_add, neg_add_le_iff_le_add] at *,
      rw [r1,r2],
      ring_nf },
    { rw finset.disjoint_iff_ne,
      intros a ha b hb,
      simp only [ne.def, finset.mem_singleton, finset.mem_product, finset.mem_Ico] at *,
      by_contra H,
      have haa := ha.2,
      have hbb := hb.2,
      rw H at haa,
      rw hbb at haa,
      have hv:=eq_zero_of_neg_eq haa,
      simp only [int.coe_nat_eq_zero] at hv,
      rw hv at h,
      simp only [nat.one_ne_zero,
      le_zero_iff] at h,
      exact h },
    { rw finset.disjoint_iff_ne,
      intros a ha b hb,
      simp only [ne.def, finset.mem_union, finset.mem_singleton, neg_add_le_iff_le_add,
      finset.mem_product, finset.mem_Ico] at *,
      cases ha,
      have hbb:=hb.2,
      have haa:=ha.2,
      by_contra H,
      rw ← H at hbb,
      rw haa at hbb,
      simp only [lt_self_iff_false, and_false] at hbb,
      exact hbb,
      have hbb:=hb.2,
      have haa:=ha.2,
      by_contra H,
      rw ← H at hbb,
      rw haa at hbb,
      simp at hbb,
      have hk:=hbb.1,
      linarith },
    { rw finset.disjoint_iff_ne,
    intros a ha b hb,
    simp only [ne.def, finset.mem_union, finset.union_assoc, finset.mem_singleton, neg_add_le_iff_le_add,
    finset.mem_product, finset.mem_Ico] at *,
    by_contra H,
    cases ha,
      { have hbb := hb.2,
       have haa:=ha.2,
       rw ← H at hbb,
       rw ←haa at hbb,
       simp [lt_self_iff_false, and_false] at hbb,
       exact hbb },
    cases ha,
    { have hbb:=hb.2,
      have haa:=ha.2,
      rw ← H at hbb,
      rw haa at hbb,
      simp only [int.coe_nat_pos, neg_lt_self_iff, add_right_neg] at hbb,
      linarith },
    { have hbb:=hb.1,
      have haa:=ha.1,
     rw H at haa,
     rw hbb at haa,
      have hv:=eq_zero_of_neg_eq haa,
      simp only [int.coe_nat_eq_zero] at hv,
      rw hv at h,
      simp only [nat.one_ne_zero, le_zero_iff] at h,
      exact h } }
end

lemma nat_abs_inter (a: ℤ) (n: ℕ) (h: a.nat_abs < n): a < (n: ℤ) ∧  0 <(n: ℤ)+ a:=
begin
  have:= int.nat_abs_eq  a,
  cases this,
  rw this,
  split,
  norm_cast,
  exact h,
  norm_cast,
  simp only [add_pos_iff],
  left,
  have h1 : 0 ≤ a.nat_abs, by {exact zero_le (int.nat_abs a),},
  linarith,
  rw this,
  split,
  rw neg_lt_iff_pos_add,
  norm_cast,
  simp,
  have h1 : 0 ≤ a.nat_abs, by {exact zero_le (int.nat_abs a),},
  left,
  linarith,
  rw ←int.coe_nat_lt at h,
  rw ← sub_pos at h,
  convert h,
end

lemma nat_abs_inter2 (a: ℤ) (n: ℕ) (h: a.nat_abs ≤ n): a ≤ (n: ℤ) ∧  0 ≤ (n: ℤ)+ a:=
begin
have := lt_or_eq_of_le h, cases this,
have H:= nat_abs_inter a n this, have H1:= le_of_lt H.1, have H2:=le_of_lt H.2, simp [H1,H2], rw ← this,
split, exact int.le_nat_abs, rw add_comm, rw ← neg_le_iff_add_nonneg', rw ← int.abs_eq_nat_abs,
simp_rw neg_le_abs_self ,
end


@[simp]lemma square_mem (n : ℕ) (x : ℤ × ℤ ) : x ∈ (Square n) ↔ max (x.1).nat_abs (x.2).nat_abs=n:=
begin
split,
intro x,
rw Square at x,
simp at x,
simp_rw x,
intro hx,
rw Square,
simp,
simp [hx],
have h2:=max_aux3 _ _ _ hx,
have h21:= nat_abs_inter2 _ _ h2.1,
have h22:= nat_abs_inter2 _ _ h2.2,
split,
split,
rw  neg_le_iff_add_nonneg',
exact h21.2,
have:= h21.1,
linarith,
split,
rw  neg_le_iff_add_nonneg',
exact h22.2,
have:= h22.1,linarith,
end

lemma square_mem' (n : ℕ) (x : ℤ × ℤ ) : x ∈ (Square n) ↔
((x.1).nat_abs=n ∧ (x.2).nat_abs <  n) ∨ ((x.2).nat_abs=n ∧ (x.1).nat_abs < n) ∨ ((x.1).nat_abs=n ∧
 (x.2).nat_abs=n) :=
begin
simp,
split,
intro c1,
have:= max_aux3 _ _ _ c1,
have H:= max_aux'' _ _ _ c1,
have h1:= this.1,
have h2:=this.2,
rw le_iff_lt_or_eq at h2,
rw le_iff_lt_or_eq at h1,
cases H,
simp_rw H,
simp,
exact h2,
simp_rw H,
simp,
exact h1,
intro c2,
cases c2,
rw c2.1,
simp,
have :=c2.2,
linarith,
cases c2,
rw c2.1,
simp,
have:=c2.2,
linarith,
rw [c2.1,c2.2],
simp,
end

lemma auxin (a: ℤ) (n: ℕ)(h: 0 < (n: ℤ)+a):  1 ≤  (n: ℤ)+a:=
begin
assumption,
end


lemma auxin2 (a: ℤ) (n: ℕ)(h: 0 < (n: ℤ)+a):   -(n: ℤ) ≤ a:=
begin
linarith,
end

lemma cat (a b : ℤ) (n: ℕ)  (h1: b=(n:ℤ)) (h2: -(n:ℤ) ≤ a ∧ a < (n:ℤ)+1 ):
 b.nat_abs= n ∧ (a.nat_abs < n ∨ a.nat_abs=n) :=
begin
  rw h1,
  simp,
  have:=int.nat_abs_eq a,
  cases this,
  rw this at h2,
  norm_cast at h2,
  have h22:=h2.2,
  exact nat.lt_succ_iff_lt_or_eq.mp h22,
  rw this at h2,
  have h22:=h2.1,
  have H:= lt_or_eq_of_le h22,
  simp only [neg_lt_neg_iff, neg_inj] at H,
  norm_cast at H,
  have h234: n = a.nat_abs ↔ a.nat_abs =n, by {exact comm, },
  rw ←h234,
  exact H,
end

lemma cat1 (a b : ℤ) (n: ℕ)  (h1: b=-(n:ℤ)) (h2: -(n:ℤ) ≤ a ∧ a < (n:ℤ)+1 ):
b.nat_abs= n ∧ (a.nat_abs < n ∨ a.nat_abs=n) :=
begin
 rw h1,
 simp,
 have:=int.nat_abs_eq a,
 cases this,
 rw this at h2,
 norm_cast at h2,
 have h22:=h2.2,
 exact nat.lt_succ_iff_lt_or_eq.mp h22,
 rw this at h2,
 have h22:=h2.1,
 have H:= lt_or_eq_of_le h22,
  simp only [neg_lt_neg_iff, neg_inj] at H,
  norm_cast at H,
  have h234: n = a.nat_abs ↔ a.nat_abs =n, by {exact comm, },
  rw ←h234,
  exact H,
end


lemma dog (a b : ℤ) (n: ℕ)  (h1: a=(n:ℤ)) (h2: 1 ≤ (n: ℤ)+ b ∧ b < (n:ℤ) ):
  a.nat_abs= n ∧ b.nat_abs < n :=
begin
 rw h1, simp,  have:=int.nat_abs_eq b, cases this, rw this at h2, norm_cast at h2,exact h2.2,
 rw this at h2, have h22:= h2.1, norm_cast at *, linarith,
end

lemma dog1 (a b : ℤ) (n: ℕ)  (h1: a=-(n:ℤ)) (h2: 1 ≤ (n: ℤ)+ b ∧ b < (n:ℤ) ): a.nat_abs= n ∧ b.nat_abs < n :=
begin
 rw h1, simp,  have:=int.nat_abs_eq b, cases this, rw this at h2, norm_cast at h2,exact h2.2,
 rw this at h2, have h22:= h2.1,  norm_cast at *, linarith,
end

lemma sqr_eq_sqr2 (n: ℕ): (Square n)=(Square2 n):=
begin
  ext1,
  split,
  rw square_mem',
  intro ha,
  rw Square2,
  simp_rw int.nat_abs_eq_iff at ha,
  simp only [finset.mem_union, finset.union_assoc, finset.mem_product,  finset.mem_Ico,
  neg_add_le_iff_le_add, finset.mem_singleton],
  cases ha,
  cases ha.1,
  have h1:= nat_abs_inter _ _ ha.2,
  have h2:= auxin _ _ h1.2,
  simp_rw [h,h1,h2],
  simp,
  have h1:= nat_abs_inter _ _ ha.2,
  have h2:= auxin _ _ h1.2,
  simp_rw [h,h1,h2],
  simp,
  cases ha,
  cases ha.1,
  have h1:= nat_abs_inter _ _ ha.2,
  have h2:= auxin2 _ _ h1.2,
  simp_rw [h,h2],
  simp,
  have h3:=h1.1,
  have Hk: a.1 < (n: ℤ)+1, by {linarith, },
  simp only [Hk, true_or],
  have h1:= nat_abs_inter _ _ ha.2,
  have h2:= auxin2 _ _ h1.2,
  simp_rw [h,h2],
  simp,
  have h3:=h1.1,
  have Hk: a.1 < (n: ℤ)+1, by {linarith, },
  simp only [Hk, true_or, or_true],
  cases  ha.1,
  cases  ha.2,
  simp_rw [h,h_1],
  have n1: -(n: ℤ) ≤ (n: ℤ), by {linarith,},
  simp_rw [n1],
  simp only [lt_add_iff_pos_right, true_or, eq_self_iff_true, and_self, zero_lt_one],
  simp_rw [h,h_1],
  have n1: -(n: ℤ) ≤ (n: ℤ), by {linarith,},
  simp_rw [n1],
  simp only [lt_add_iff_pos_right, true_or, eq_self_iff_true, or_true, and_self, zero_lt_one],
  cases ha.2,
  simp_rw [h,h_1],
  simp only [true_and, lt_self_iff_false, le_refl, and_true, eq_self_iff_true, or_false, and_false] at *,
  have n1: -(n: ℤ) < (n: ℤ)+1, by {linarith,} ,
  simp_rw [n1],
  simp only [true_or],
  have hg: -(n: ℤ) < n+1, by {linarith,},
  simp_rw [h,h_1, hg],
  simp,
  intro ha,
  rw Square2 at ha,
  simp only [finset.mem_union, finset.union_assoc, finset.mem_product,  finset.mem_Ico,
  neg_add_le_iff_le_add, finset.mem_singleton] at ha,
  rw square_mem',
  cases ha,
  have:= cat _ _ _ ha.2 ha.1,
  simp_rw this,
  simp only [true_and, lt_self_iff_false, and_true, false_or, eq_self_iff_true, and_false],
  exact this.2,
  cases ha,
  have:= cat1 _ _ _ ha.2 ha.1,
  simp_rw this,
  simp,
  exact this.2,
  cases ha,
  have:= dog _ _ _ ha.1 ha.2,
  simp_rw this,
  simp only [true_or, eq_self_iff_true, and_self],
  have:= dog1 _ _ _ ha.1 ha.2,
  simp_rw this,
  simp only [true_or, eq_self_iff_true, and_self],
  end


lemma Square_size (n : ℕ) (h: 1 ≤ n) : finset.card (Square (n)) = 8 * n :=
begin
  rw sqr_eq_sqr2,
  have := square2_card n h,
  norm_cast at this,
  apply this,
end


lemma Squares_are_disjoint: ∀ (i j : ℕ), i ≠ j → disjoint (Square i) (Square j):=
begin
  intros i j hij,
  rw finset.disjoint_iff_ne,
  intros a ha,
  simp at ha,
  intros b hb,
  simp at hb,
  by_contradiction,
  rw h at ha,
  rw hb at ha,
  induction ha,
  induction h,
  cases a,
  induction hb,
  cases b,
  dsimp at *,
  simp at *,
  assumption,
end

lemma Squares_cover_all :  ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ Square (i) :=
begin
intro y,
use max y.1.nat_abs y.2.nat_abs,
simp only [square_mem, and_self, forall_eq'],
end

lemma Square_zero : Square (0: ℕ)={(0,0)}:=
begin
refl,
end

lemma Square_zero_card: finset.card (Square 0)=1:=
begin
rw Square_zero,
refl,
end

/- Some summable lemmas-/

variables {α : Type u} {β : Type v} {γ : Type w} {i : α → set β}

instance  (a: α): has_lift_t (i a) (set.Union i):=
begin
  fsplit,
  intros H,
  cases H,
  fsplit,
  apply H_val,
  simp at *, fsplit, work_on_goal 2 { assumption },
  end

instance: has_coe_t  (finset (ℤ × ℤ))  (set (ℤ × ℤ)):=infer_instance

def coef (s : finset (ℤ × ℤ)): set (ℤ × ℤ):=
(s: set (ℤ × ℤ ))

def fn (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) (x : ℤ × ℤ):
  x ∈  (⋃ (s: ℕ), coef (In s)):=
begin
  have h1:=HI x,
  rw set.mem_Union,
  cases h1,
  cases x,
  cases h1_h,
  dsimp at *,
  simp at *,
  fsplit, work_on_goal 2 { assumption },
end

def fnn  (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) (x:  ℤ × ℤ)  :
(⋃ (s: ℕ), coef (In s)):= ⟨x, fn In HI x⟩


def union_equiv (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) :
  (⋃ (s: ℕ), coef (In s)) ≃ ℤ × ℤ:={
to_fun:=λ x, x.1 ,
inv_fun:=λ x,   fnn In HI x,
left_inv:= by {simp, intros x, cases x, refl},
right_inv:=by {simp, intros x, refl}}


lemma unionmem (i: α → set β) (x : α) (y : i x): (coe y)  ∈ (⋃ x, i x):=
begin
  simp,
  use x,
  cases y,
  assumption,
end

lemma summable_disjoint_union_of_nonneg {i : α →  set β} {f : (⋃ x, i x) → ℝ}
  (h: ∀ a b, a ≠ b →  disjoint (i a) (i b)) (hf : ∀ x, 0 ≤ f x) :
  summable f ↔ (∀ x, summable (λ (y : i x), f ⟨y, unionmem i x y⟩ )) ∧
  summable (λ x, ∑' (y : i x), f ⟨y , unionmem i x y⟩) :=
 begin
  let h0:=(set.Union_eq_sigma_of_disjoint h).symm,
  have h01: summable f ↔ summable ( f ∘ h0 ),
    by {have:= equiv.summable_iff h0 , rw this, },
  have h22 : ∀ y : (Σ (s: α ), i s), 0 ≤ (f ∘ h0) y:= by {simp_rw h0,
  rw set.Union_eq_sigma_of_disjoint,
  simp only [equiv.symm_symm, function.comp_app, sigma.forall, equiv.of_bijective_apply],
  simp_rw set.sigma_to_Union,
  simp_rw hf,
  simp only [forall_2_true_iff],},
  have h1:=summable_sigma_of_nonneg h22 ,
  rw h01, rw h1,
  have H1: ∀ (x : α), summable (λ (y : (λ (s : α), ↥(i s)) x), f (h0 ⟨x, y⟩)) ↔
  summable (λ (y : ↥(i x)), f ⟨y,  unionmem i x y⟩),
  by { intro x,
     dsimp,
    simp_rw h0,
    rw set.Union_eq_sigma_of_disjoint,
    simp only [equiv.symm_symm, equiv.of_bijective_apply],
    simp_rw set.sigma_to_Union, },
  simp_rw H1,
  simp only [ and.congr_right_iff],
  intro hfin,
  have H2: ∀  (x : α), ∑' (y : (λ (s : α), ↥(i s)) x),
  (f ∘ ⇑h0) ⟨x, y⟩=∑' (y : ↥(i x)), f ⟨↑y, unionmem i x y⟩,
   by { intro x,
   simp only [function.comp_app],
   simp_rw h0,
   rw set.Union_eq_sigma_of_disjoint,
   simp only [equiv.symm_symm, equiv.of_bijective_apply],
   simp_rw set.sigma_to_Union,},
  simp_rw H2,
 end


lemma tsum_disjoint_union_of_nonneg' {i : α →  set β} {f : (⋃ x, i x) → ℝ}
  (h: ∀ a b, a ≠ b →  disjoint (i a) (i b)) (h1: summable f):
  ∑' x, f x= ∑' x , ∑' (y : i x), f ⟨y , unionmem i x y⟩   :=
 begin
  let h0:=(set.Union_eq_sigma_of_disjoint h).symm,
  have h01: ∑' x, f x = ∑' y , ( f  (h0 y)) , by {have:= equiv.tsum_eq h0 f,rw ← this,   },
  rw h01,
  rw tsum_sigma,
  simp_rw h0,
  rw set.Union_eq_sigma_of_disjoint,
  simp,
  simp_rw set.sigma_to_Union,
  have h01: summable f ↔ summable ( f ∘ h0 ), by {have:= equiv.summable_iff h0 , rw this, },
  rw ← h01,
  exact h1,
 end

lemma tsum_disjoint_union_of_nonneg'' {i : α →  set β} {f : (⋃ x, i x) → ℂ}
  (h: ∀ a b, a ≠ b →  disjoint (i a) (i b)) (h1: summable f) :
  ∑' x, f x= ∑' x , ∑' (y : i x), f ⟨y , unionmem i x y⟩   :=
 begin
  let h0:=(set.Union_eq_sigma_of_disjoint h).symm,
  have h01: ∑' x, f x = ∑' y , ( f  (h0 y)) , by {have:= equiv.tsum_eq h0 f,rw ← this,   },
  rw h01,
  rw tsum_sigma,
  simp_rw h0,
  rw set.Union_eq_sigma_of_disjoint,
  simp,
  simp_rw set.sigma_to_Union,
  have h01: summable f ↔ summable ( f ∘ h0 ), by {have:= equiv.summable_iff h0 , rw this, },
  rw ← h01,
  exact h1,
 end


lemma disjoint_aux (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) :
  ∀ (i j : ℕ), i ≠ j → disjoint (In i) (In j):=
begin
 intros i j h,
 intros x h1 h2 a h3,
 cases a,
 dsimp at *,
 simp at *,
 have HI0:=HI a_fst a_snd,
  have:= exists_unique.unique HI0 (h1 h3) (h2 h3),
  rw this at h,
  simp at *,
  exact h,
end



lemma sum_lemma (f: ℤ × ℤ → ℝ) (h: ∀ y : ℤ × ℤ, 0 ≤ f y) (In: ℕ → finset (ℤ × ℤ))
  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) )  :
  summable f ↔ summable (λ ( n : ℕ), ∑ x in In (n), f x)  :=
begin
  let h2:= union_equiv In HI,
  have h22: ∀ y : (⋃ (s: ℕ), coef (In s)), 0 ≤ (f ∘ h2) y:= by {simp_rw h2, simp_rw union_equiv, simp,
  simp_rw coef, simp_rw h, simp only [forall_const, implies_true_iff],},
  have hdis':=disjoint_aux In HI,
  have h5: ∀ (x : ℕ), finset ((coef (In x))), by {intro x, rw coef, exact finset.univ,},
  have hg:∀ (x : ℕ), (coef (In x))={y : ℤ × ℤ | y ∈ In x}, by {intros x, refl,},
  have hdis:∀ (a b : ℕ) , a ≠ b →  disjoint (coef (In a)) (coef (In b)), by {intros a b hab, simp_rw coef,
  rw finset.disjoint_coe, apply hdis', exact hab,},
  have h3:=summable_disjoint_union_of_nonneg  hdis h22 ,
  have h4: summable f ↔ summable (f ∘ h2), by {have:= equiv.summable_iff h2 , rw this, },
  rw h4,
  rw h3,
  simp only [function.comp_app],
  dsimp,
  have h6: ∀ (x : ℕ), ∑' (y : ↥(coef (In x))), f (h2 ⟨y,_⟩) = ∑ y in  (In x), f y, by {
    simp only, intro x, apply finset.tsum_subtype', },
  simp_rw h6,
  simp only [and_iff_right_iff_imp],
  simp_rw h2,
  rw union_equiv,
  simp only [equiv.coe_fn_mk, subtype.coe_mk],
  intros H x,
  rw hg,
  apply finset.summable,
  apply unionmem,
  end


lemma tsum_lemma (f: ℤ × ℤ → ℝ) (In: ℕ → finset (ℤ × ℤ))
  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) ) (hs :summable f):
  ∑' x, f x =  ∑' ( n : ℕ), (∑ x in In (n), f x)  :=
begin
  let h2:= union_equiv In HI,
  have hdis':=disjoint_aux In HI,
  have h5: ∀ (x : ℕ), finset ((coef (In x))), by {intro x, rw coef, exact finset.univ,},
  have hg:∀ (x : ℕ), (coef (In x))={y : ℤ × ℤ | y ∈ In x}, by {intros x, refl,},
  have hdis:∀ (a b : ℕ) , a ≠ b →  disjoint (coef (In a)) (coef (In b)),
    by {intros a b hab, simp_rw coef,
    rw finset.disjoint_coe, apply hdis', exact hab,},
  have h6: ∀ (x : ℕ), ∑' (y : ↥(coef (In x))), f (h2 ⟨y,_⟩) = ∑ y in  (In x), f y,
   by {  simp only, intro x, apply finset.tsum_subtype', },
  simp_rw h6,
  have HS:summable (f ∘ h2), by {rw equiv.summable_iff  h2, exact hs,},
  have HH:= tsum_disjoint_union_of_nonneg'  hdis HS,
  simp at HH,
  have:= equiv.tsum_eq h2 f,
  rw ← this,
  rw HH,
  simp_rw h6,
  apply unionmem,
end

lemma tsum_lemma' (f: ℤ × ℤ → ℂ) (In: ℕ → finset (ℤ × ℤ))  (HI: ∀ (y : ℤ × ℤ), ∃! (i : ℕ), y ∈ In (i) )
(hs :summable f): ∑' x, f x =  ∑'  ( n : ℕ), (∑ x in In (n), f x)  :=
begin
  let h2:= union_equiv In HI,
  have hdis':=disjoint_aux In HI,
  have h5: ∀ (x : ℕ), finset ((coef (In x))), by {intro x, rw coef, exact finset.univ,},
  have hg:∀ (x : ℕ), (coef (In x))={y : ℤ × ℤ | y ∈ In x}, by {intros x, refl,},
  have hdis:∀ (a b : ℕ) , a ≠ b →  disjoint (coef (In a)) (coef (In b)),
    by {intros a b hab,
    simp_rw coef,
    rw finset.disjoint_coe,
    apply hdis',
    exact hab,},
  have h6: ∀ (x : ℕ), ∑' (y : ↥(coef (In x))), f (h2 ⟨y,_⟩) = ∑ y in  (In x), f y,
  by {simp only,
  intro x,
  apply finset.tsum_subtype', },
  simp_rw h6,
  have HS:summable (f ∘ h2), by {rw equiv.summable_iff  h2, exact hs,},
  have HH:= tsum_disjoint_union_of_nonneg''  hdis HS,
  simp at HH,
  have:= equiv.tsum_eq h2 f,
  rw ← this,
  rw HH,
  simp_rw h6,
  apply unionmem,
end

lemma realpow (n : ℕ ) (k : ℤ): (n: ℝ)^((k : ℝ)-1)= n^(k-1):=
begin
  have:=real.rpow_int_cast (n: ℝ) (k-1),
  rw ← this,
  simp only [int.cast_one, int.cast_sub],
end

lemma summable_if_complex_abs_summable {f : α → ℂ} :
  summable (λ x, complex.abs (f x)) →  summable f :=
begin
intro h,
apply summable_of_norm_bounded  (λ x, complex.abs (f x))  h,
intro i,
unfold norm,
exact complete_of_proper,
end

lemma complex_abs_sum_le {ι : Type*} (s : finset ι) (f : ι → ℂ) :
complex.abs(∑ i in s, f i) ≤ ∑ i in s, complex.abs(f i) :=
begin
 exact abv_sum_le_sum_abv (λ (k : ι), f k) s,
end

lemma upper_gt_zero (z: ℍ) : 0<(z: ℂ ).im:=
begin
 have H:= z.property,
 simp at H,
 apply H,
end
/--Auxilary function use for bounding Eisentein series-/
def lb (z: ℍ): ℝ:=((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2

lemma lb_pos (z : ℍ): 0 < lb z :=
begin
  rw lb,
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re],
  have H1: 0 < ((z.1.2)^4 + (z.1.1*z.1.2)^2),
  by {rw add_comm,
  apply add_pos_of_nonneg_of_pos,
  nlinarith,
  have h1: z.1.2^4=z.1.2^2*z.1.2^2,
  ring_nf,
  rw h1,
  apply mul_pos,
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe],
  have:=upper_gt_zero z,
  rw pow_two,
  apply mul_pos,
  exact this,
  exact this,
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe],
  have:=upper_gt_zero z,
  rw pow_two,
  apply mul_pos,
  exact this,
  exact this, },
  have H2: 0 < (z.1.1^2+z.1.2^2)^2, by {nlinarith,},
  have H3: ((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2=
    ((z.1.2)^4 + (z.1.1*z.1.2)^2)*((z.1.1^2+z.1.2^2)^2)⁻¹ , by {ring,},
  simp at H3,
  rw H3,
  have H4: 0 < ((z.1.1^2+z.1.2^2)^2)⁻¹,
  by {rw inv_pos, exact H2,},
  apply mul_pos H1 H4,
end

/--This function is used to give an upper bound on Eisenstein series-/
def rfunct (z: ℍ): ℝ:=
min (real.sqrt((z.1.2)^2)) (real.sqrt(lb z))

lemma rfunct_pos (z : ℍ): 0 < (rfunct z):=
begin
  have H:= z.property, simp at H,
  rw rfunct,
  simp only [lt_min_iff, real.sqrt_pos, upper_half_plane.coe_im, subtype.val_eq_coe],
  split,
  rw pow_two,
  apply mul_pos,
  exact H,
  exact H,
  apply lb_pos,
end


lemma alem (a b c : ℝ): (a-b) ≤ a+c ↔ -b ≤ c:=
begin
  have: a-b= a+(-b), by {ring,},
  split,
  rw this,
  simp_rw add_le_add_iff_left,
  simp,
  rw this,
  simp_rw add_le_add_iff_left,
  simp,
end

lemma ineq1 (x y d: ℝ  ): 0 ≤ d^2*(x^2+y^2)^2+2*d*x*(x^2+y^2)+x^2:=
begin
  have h1: d^2*(x^2+y^2)^2+2*d*x*(x^2+y^2)+x^2 =(d*(x^2+y^2)+x)^2, by {ring,},
  rw h1,
  nlinarith,
end

lemma lowbound (z : ℍ) (δ : ℝ): ((z.1.2)^4 + (z.1.1*z.1.2)^2)/(z.1.1^2+z.1.2^2)^2 ≤
  (δ*z.1.1+1)^2+(δ*z.1.2)^2:=
begin
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re],
  have H1: (δ*z.1.1+1)^2+(δ*z.1.2)^2=δ^2*(z.1.1^2+z.1.2^2)+2*δ*z.1.1+1, by {ring,},
  simp only [upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re] at H1,
  rw H1,
  rw div_le_iff,
  simp only,
  have H2: (δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) + 2 * δ *  (z: ℂ).re + 1) *
  ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2=δ ^ 2 * ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2)^3 + 2 * δ *
  (z: ℂ).re* ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2+   ( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2,
  by {ring,},
  simp only [upper_half_plane.coe_im, upper_half_plane.coe_re] at H2,
  rw H2,
  rw ← sub_nonneg,
  have H3:( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2) ^ 2-((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=
  ((z: ℂ).re)^2*( (z: ℂ).re ^ 2 +  (z: ℂ).im ^ 2), by {ring,},
  have H4: δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 3 + 2 * δ *
  (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 + ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) ^ 2 -
  ((z: ℂ).im ^ 4 + ((z: ℂ).re * (z: ℂ).im) ^ 2)=
  (((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2))*(δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 + 2 * δ *
  (z: ℂ).re * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {ring,},
  simp only [upper_half_plane.coe_im, upper_half_plane.coe_re] at H4,
  rw H4,
  have H5: 0 ≤ (δ ^ 2 * ((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)^2 + 2 * δ * (z: ℂ).re * ((z: ℂ).re ^ 2 +
  (z: ℂ).im ^ 2) +(z: ℂ).re ^ 2), by {apply ineq1,},
  have H6: 0 ≤ (((z: ℂ).re ^ 2 + (z: ℂ).im ^ 2)), by {nlinarith,},
  apply mul_nonneg H6 H5,
  have H7:= z.property, simp at H7,
  have H8:0 < (z: ℂ).im ^ 2, by {simp only [H7, pow_pos, upper_half_plane.coe_im], },
  have H9: 0 <((z: ℂ).im ^ 2+(z: ℂ).re ^ 2), by {nlinarith,},
  apply pow_two_pos_of_ne_zero,
  nlinarith,
end

lemma auxlem (z : ℍ) (δ : ℝ) :
  (rfunct z) ≤ complex.abs ( (z: ℂ)+δ ) ∧ (rfunct z) ≤ complex.abs ( δ*(z: ℂ) +1):=
begin
  split,
  {rw rfunct,
  rw complex.abs,
  simp,
  have H1: real.sqrt (((z: ℂ).im)^2) ≤
  real.sqrt (((z: ℂ).re + δ) * ((z: ℂ).re + δ) + (z: ℂ).im * (z: ℂ).im),
  by {rw real.sqrt_le_sqrt_iff,
  nlinarith,nlinarith,},
  simp at *,
  left,
  rw norm_sq_apply,
  simp,
  simp_rw H1,},
  {rw rfunct,
  rw complex.abs,
  simp,
  have H1:  real.sqrt (lb z) ≤
  real.sqrt ((δ*(z: ℂ).re  + 1) * (δ*(z: ℂ).re  + 1) + δ*(z: ℂ).im *  (δ*(z: ℂ).im )),
  by { rw lb,
  rw real.sqrt_le_sqrt_iff,
  have:= lowbound z δ,
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

lemma le_of_pow' (a b : ℝ) (k: ℕ)(h : 0 ≤ a) (h2: 0 ≤ b) (h3: a ≤ b): a^k ≤ b^k:=
begin
exact pow_le_pow_of_le_left h h3 k,
end

lemma baux (a : ℝ) (k : ℕ) (b : ℂ) (h: 0 ≤ a) (h2: a ≤ complex.abs b): a^k ≤ complex.abs (b^k):=
begin
  rw complex.abs_pow,
  apply pow_le_pow_of_le_left,
  exact h,
  exact h2,
end


lemma baux2 (z : ℍ) (k: ℕ): complex.abs ((rfunct z)^k)=(rfunct z)^k:=
begin
  norm_cast,
  let a:=rfunct z,
  simp,
  have ha: 0 ≤ a, by {simp_rw a, have:= rfunct_pos z , apply le_of_lt this, },
  have:= complex.abs_of_nonneg ha,
  norm_cast at this,
  simp_rw a at this,
  rw this,
end

lemma auxlem2 (z : ℍ) (n : ℕ)  (x: ℤ × ℤ) (h2: x ∈ Square n) (k : ℕ)  :
  complex.abs (((rfunct z): ℂ)^k) ≤ complex.abs (( (z: ℂ)+(x.2: ℂ)/(x.1 : ℂ) )^k):=
begin
  norm_cast,
  have H1: complex.abs ((rfunct z)^k)=(rfunct z)^k, by {apply baux2,},
  norm_cast at H1,
  rw H1,
  apply baux,
  have:= rfunct_pos z,
  apply le_of_lt this,
  have:= auxlem z ((x.2/x.1): ℝ),
  norm_cast at this,
  apply this.1,
end


lemma auxlem3 (z : ℍ) (n : ℕ)  (x: ℤ × ℤ) (h2: x ∈ Square n) (k : ℕ)  :
 complex.abs (((rfunct z): ℂ)^k) ≤  complex.abs (( ((x.1: ℂ)/(x.2 : ℂ))*(z: ℂ) +1)^k):=
begin
  norm_cast,
  have H1:= (baux2 z k),
  norm_cast at H1,
  rw H1,
  apply baux,
  have:= rfunct_pos z,
  apply le_of_lt this,
  have:= auxlem z ((x.1/x.2): ℝ),
  norm_cast at *,
  apply this.2,
end


end Eisenstein_series
