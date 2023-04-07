import mod_forms.Eisenstein_Series.Eisen_is_holo
import data.complex.exponential
import analysis.complex.upper_half_plane.basic
import mod_forms.Riemann_zeta_fin
import analysis.calculus.iterated_deriv
import analysis.calculus.series


noncomputable theory

open modular_form Eisenstein_series upper_half_plane topological_space set measure_theory
interval_integral metric filter function complex
open_locale interval real nnreal ennreal topology big_operators nat classical

local notation `ℍ'`:=(⟨upper_half_plane.upper_half_space, upper_half_plane_is_open⟩: open_subs)

local notation `ℍ` := upper_half_plane


lemma map_to_ball (x : ℍ') : ∃ (ε : ℝ) (Ba : set ℍ'), metric.ball x ε ⊆ Ba  ∧ 0 < ε ∧ ∃ (A B : ℝ),
  Ba ⊆ (upper_half_space_slice A B) ∧ 0 < B :=
begin
  have h1:= closed_ball_in_slice x,
  obtain ⟨A, B, ε, hε, hB, hball, hA, hεB⟩ := h1,
  refine ⟨ ε,  metric.closed_ball x ε ,_,hε, A, B, _, hB ⟩,
  apply ball_subset_closed_ball,
  apply hball,
end

def bolas (x : ℍ') : set ℍ' :=
begin
have := map_to_ball x,
let e := this.some,
use metric.ball x e,
end

lemma ABbolas (x : ℍ') : ∃ (A B : ℝ), bolas x  ⊆ (upper_half_space_slice A B) :=
begin
simp_rw bolas,
have H1 := map_to_ball x,
obtain ⟨ε, Ba, h1, h2, A, B, hab, hb⟩ := H1,
refine ⟨A,B,_⟩,
intros z hz,
have h3 : z ∈ metric.ball x ε, by {convert hz, sorry,},
sorry,
end

lemma mem_uhs (x : ℂ) : x ∈ ℍ'.1 ↔ 0 < x.im :=
begin
refl,
end

--lemma aux_cb (x : ℍ') (r : ℝ) (hr : 0 < r) (hx : closed_ball (x : ℂ) r ⊆ ℍ')

lemma closed_ball_in_some_slice (x : ℍ') (r : ℝ) (hr : 0 < r) (hx : closed_ball (x : ℂ) r ⊆ ℍ') :
  ∃ (A B : ℝ), 0 < B ∧ closed_ball x r ⊆ (upper_half_space_slice A B) :=
begin
refine ⟨r + complex.abs x, (x : ℂ).2-r, _⟩,
split,
have hh : (⟨(x : ℂ).1, (x : ℂ).2 -r⟩  : ℂ)∈ closed_ball (x : ℂ) r, by {simp, rw complex.dist_eq,
  have : (⟨upper_half_plane.re x, (upper_half_plane.im x) -r⟩ : ℂ) - x = -r*I , by {ext, simp, simp,},
  rw this,
  simp,
 sorry},
simp at hx,
have hxx := hx hh,
simp at hxx,
rw mem_uhs at hxx,
simp at hxx,
sorry,
intros z hz,
have h1 : dist z x = complex.abs ((z : ℂ) - (x : ℂ)), by {refl, },
simp at *,
have I1:= complex.abs.sub_le (z : ℂ) (x : ℂ) 0,
have ineq1:= _root_.abs_sub_le x.1.2 z.1.2 0,
rw h1 at hz,
split,
sorry,
sorry,
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
refine ⟨2*r, b.im,_ ⟩,
split,
have hbim := hs hb,
simp only [subtype.coe_mk] at hbim,
rw mem_uhs b at hbim,
exact hbim,

intros z hz,
simp at *,
split,
have hr3 := hr2 hz,
simp at hr3,
apply le_trans (abs_re_le_abs z),
  have:= complex.abs.sub_le (z : ℂ) (t : ℂ) 0,
end

lemma compact_in_slice (S : set  ℂ) (hs : S ⊆ ℍ') (hs2 : is_compact S) : ∃ (A B : ℝ), 0 < B ∧
   (image (inclusion hs) ⊤)  ⊆ (upper_half_space_slice A B) :=
begin
have hh : is_compact (image (inclusion hs) ⊤), by {apply is_compact.image_of_continuous_on,
 simp, exact is_compact_iff_is_compact_univ.mp hs2, apply (continuous_inclusion hs).continuous_on, },

have hb:=hh.bounded,
let  t := (⟨complex.I, by {simp,} ⟩ : ℍ),
have hb2:=  bounded.subset_ball_lt  hb 0 t,
obtain ⟨r, hr, hr2⟩ := hb2,

have ht :  closed_ball (t : ℂ) r ⊆ ℍ', by { simp, sorry},
have HH := closed_ball_in_some_slice t r hr ht,

refine ⟨2*r, r, _⟩,
split,
apply hr,
intros x hx,
simp at hx,
simp at hr2,
have hr3 := hr2 hx,
simp at hr3,
simp,
have hg : complex.abs ((x : ℂ) - (t : ℂ)) ≤ r, by {sorry},
sorry,
--apply le_trans (abs_re_le_abs x),
--apply le_trans hr3,
--linarith,
end
