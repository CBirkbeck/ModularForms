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
