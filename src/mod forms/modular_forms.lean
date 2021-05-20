import tactic.ring
import group_theory.group_action
import algebra.module
import tactic.pi_instances
import algebra.module.submodule
import .holomorphic_functions
import linear_algebra.determinant
import .modular_group
import .GLnR
import ring_theory.coprime
import ring_theory.int.basic
import .upper_half_space

universes u v

open complex


noncomputable theory

instance: metric_space upper_half_space:=infer_instance

lemma upper_half_plane_is_open: is_open upper_half_space:= 
begin
rw metric.is_open_iff, 
sorry, 
end

lemma upper_half_plane_open_subs: upper_half_space ∈ open_subs:=

begin
simp, exact upper_half_plane_is_open,
end  

local notation `ℍ`:=(⟨upper_half_space, upper_half_plane_open_subs⟩: open_subs)


/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/





def is_Petersson_weight_ (k : ℤ) := { f : ℍ → ℂ | ∀ M : SL2Z, ∀ z : ℍ, f (moeb M z) = ((M 1 0 )*z + M 1 1)^k * f z}



lemma ext2 (k : ℤ) (f g :  is_Petersson_weight_ k): f = g ↔ ∀ (x : ℍ ), f.1 x = g.1 x:=

begin
cases g, cases f, dsimp at *, simp at *, fsplit, 
work_on_goal 0 { intros ᾰ x h, induction ᾰ, refl }, intros ᾰ, ext1, cases x, 
tactic.ext1 [] {new_goals := tactic.new_goals.all}, work_on_goal 0 { solve_by_elim }, solve_by_elim,
end  


@[simp] lemma mem_pet (k : ℤ) (f: ℍ → ℂ) :
  f  ∈ is_Petersson_weight_ k  ↔  ∀ M : SL2Z, ∀ z : ℍ, f (moeb M z) = ((M 1 0 )*z + M 1 1)^k * f z := iff.rfl



def mod_form_sum (k: ℤ) (f g : is_Petersson_weight_ k): ℍ → ℂ :=
λ z, f.1 z + g.1 z

def zero_form (k :ℤ): ℍ → ℂ:=
λ z , (0: ℂ) 

def neg_form (k : ℤ) (f : is_Petersson_weight_ k) : ℍ → ℂ:=
λ z, - f.1 z 

lemma mod_sum_is_mod (k: ℤ) (f g : is_Petersson_weight_ k): ( mod_form_sum k f g ∈  is_Petersson_weight_ k):=
begin
simp only [mem_pet], intros M z, rw mod_form_sum, simp only [subtype.val_eq_coe], have h1:=f.property, 
simp only [mem_pet, subtype.val_eq_coe] at h1, have h2:=g.property, simp only [mem_pet, subtype.val_eq_coe] at h2,
 rw [h1, h2], ring,
end  

lemma zero_form_is_form (k: ℤ) : (zero_form k ∈ is_Petersson_weight_ k):=

begin
simp only [mem_pet], intros M z, rw zero_form, simp only [mul_zero], 
end  

@[simp] lemma zero_simp (k: ℤ): ∀ (x: ℍ), (⟨zero_form k,  zero_form_is_form k⟩ : is_Petersson_weight_ k).val x = (0: ℂ) := 

begin
intro x, simp [zero_form], 
end  

lemma neg_form_is_form (k: ℤ) (f : is_Petersson_weight_ k): (neg_form k f ∈ is_Petersson_weight_ k ):=

begin
simp only [mem_pet], rw neg_form, intros M z, have h1:=f.property, simp only [mem_pet, subtype.val_eq_coe] at h1, ring_nf, 
rw subtype.val_eq_coe, rw h1, ring,
end  

lemma add_l_neg (k: ℤ) (f : is_Petersson_weight_ k ) : mod_form_sum k ⟨ neg_form k f, neg_form_is_form k f ⟩  f = zero_form k:=

begin
simp only [mod_form_sum, zero_form, neg_form, add_left_neg],  
end  

lemma sum_com (k: ℤ) (f g : is_Petersson_weight_ k ): mod_form_sum k f g = mod_form_sum k g f:=

begin
simp only [mod_form_sum, subtype.val_eq_coe],  ext, simp only [add_re], ring, simp only [add_im], ring,
end  

instance (k : ℤ): add_comm_group (is_Petersson_weight_ k):=
{add:= λ f g, ⟨ mod_form_sum k f g,  mod_sum_is_mod k f g⟩, 
add_comm:= by {intros f g, have:=sum_com k f g, cases g, cases f, dsimp at *, apply subtype.ext, assumption,},
add_assoc:= by {intros f g h, simp only [subtype.mk_eq_mk], rw mod_form_sum, simp only [subtype.val_eq_coe], rw mod_form_sum, 
simp only [subtype.val_eq_coe], rw mod_form_sum, 
simp only [subtype.val_eq_coe], rw mod_form_sum, 
simp, ext, simp, ring, ring_nf, },
zero:=⟨zero_form k , zero_form_is_form k⟩, 
add_zero:=by {intro f, simp only, ext, simp only [zero_form, subtype.coe_mk], rw mod_form_sum, 
simp only [add_zero, subtype.val_eq_coe], 
simp only [mod_form_sum, zero_form, add_zero, subtype.coe_eta, subtype.val_eq_coe],},
zero_add:=by {intro f, simp only, ext, simp only [zero_form, subtype.coe_mk], rw mod_form_sum, 
simp only [add_zero, subtype.val_eq_coe], 
simp, simp [zero_form, mod_form_sum],  },
neg:= λ f, ⟨neg_form k f, neg_form_is_form k f ⟩, 
add_left_neg:=by {simp, intros f h, have:=add_l_neg k ⟨f,h⟩, dsimp at *, apply subtype.ext, assumption,}  ,
}

def sca_mul_def' (k: ℤ):  ℂ →   (is_Petersson_weight_ k) →  (ℍ → ℂ):=
λ z f , λ x , z * (f.1 x)

lemma sca_is_mod (k: ℤ ) (f: is_Petersson_weight_ k) (z : ℂ) : (sca_mul_def' k  z f) ∈ is_Petersson_weight_ k:=

begin
simp only [sca_mul_def', mem_pet, subtype.val_eq_coe], intros M x, have h1:=f.property, 
simp only [mem_pet, subtype.val_eq_coe] at h1, rw h1, ring,
end  

def sca_mul_def (k : ℤ): ℂ → (is_Petersson_weight_ k) → (is_Petersson_weight_ k) :=
λ z f, ⟨ sca_mul_def' k z f, sca_is_mod k f z⟩

@[simp]lemma ze_si (k : ℤ ): ∀ (x : ℍ), (0 : is_Petersson_weight_ k ).1 x = (0 : ℂ):=
begin
simp only [set_coe.forall, subtype.val_eq_coe], intros x , refl,
end  

@[simp]lemma mod_sum_val (k: ℤ) (f g : is_Petersson_weight_ k): (f+g).1=f.1+g.1:=
begin
simp only [subtype.val_eq_coe], refl,
end

lemma ad_sum (k: ℤ) (r s : ℂ ) (f : is_Petersson_weight_ k): sca_mul_def k (r+s) f = sca_mul_def k r f +sca_mul_def k s f:=

begin
have:=ext2 k (sca_mul_def k (r+s) f)  (sca_mul_def k r f +sca_mul_def k s f), rw this, simp only [sca_mul_def,sca_mul_def'], 
intro x, simp only [subtype.val_eq_coe], ring_nf,
end  

instance  (k : ℤ) : module ℂ (is_Petersson_weight_ k) :=


{ smul:=sca_mul_def k ,
  smul_zero:= by {simp [sca_mul_def, sca_mul_def'], intro r, ext, simp only [zero_re, subtype.coe_mk],
   rw ← subtype.val_eq_coe, simp only [zero_re, ze_si], simp only [zero_im, subtype.coe_mk], refl,},
  zero_smul:= by {simp only [zero_re, zero_im, ze_si, mem_pet, set_coe.forall, subtype.coe_mk, mul_zero, subtype.val_eq_coe], 
  intro x, intro h, 
  simp only [sca_mul_def, sca_mul_def', zero_mul], refl,},
  add_smul:= by {simp [sca_mul_def,sca_mul_def'], intros r s h, have:= ad_sum k r s h, assumption,},
  smul_add:= by {simp [sca_mul_def, sca_mul_def'], simp [ext2], intros r f g x , ring,},
  one_smul:=by {simp [sca_mul_def, sca_mul_def'],},
  mul_smul:=by {simp [sca_mul_def, sca_mul_def'], intros x y f, ring_nf,},
  
}
  


def is_bound_at_infinity := { f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M }

def is_zero_at_infinity := { f : ℍ → ℂ | ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε }

@[simp]lemma bound_mem (f: ℍ → ℂ): (f ∈  is_bound_at_infinity ) ↔ ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M:=iff.rfl

@[simp]lemma zero_at_inf_mem (f: ℍ → ℂ): (f ∈  is_zero_at_infinity  ) ↔ ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε:=iff.rfl


lemma zero_form_is_bound (k : ℤ): (zero_form k) ∈  is_bound_at_infinity:=

begin
simp only [H_mem, bound_mem, ge_iff_le, set_coe.forall, subtype.coe_mk], 
use (0: ℝ ), use (0:ℝ), intros x h1, rw zero_form, simp only [complex.abs_zero],
end  

lemma zero_form_is_zero_at_inf (k : ℤ): (zero_form k) ∈  is_zero_at_infinity:=

begin
simp only [H_mem, zero_at_inf_mem, gt_iff_lt, ge_iff_le, 
set_coe.forall, subtype.coe_mk], intros ε he, use (0:ℝ), 
intros x  h1, rw zero_form, simp only [complex.abs_zero], rw le_iff_lt_or_eq, simp only [he, true_or],
end  

lemma is_zero_at_inf_is_bound (f: ℍ → ℂ): (f ∈ is_zero_at_infinity) → (f ∈ is_bound_at_infinity):=
begin
simp only [H_mem, zero_at_inf_mem, gt_iff_lt, bound_mem, ge_iff_le, set_coe.forall, 
subtype.coe_mk],intro H, use (1: ℝ), apply H, norm_cast, exact dec_trivial,
end  





lemma abs_ew (a b : ℂ) (h : a = b): abs a = abs b:=
begin
rw h, 
end  



@[simp]lemma smul_sim (f: ℍ → ℂ) (z : ℂ) (x : ℍ): (z • f) x= z* (f x):=

begin
simp only [algebra.id.smul_eq_mul, pi.smul_apply],
end  


def bounded_at_infty: submodule (ℂ) (ℍ  → ℂ):={ 
  carrier :={ f : ℍ → ℂ | ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M },
  zero_mem' :=by {simp, use (1: ℝ ), use (0: ℝ ), intros x  h1, norm_cast, exact dec_trivial},
  add_mem' := by  {intros f g hf hg, begin
    cases hf with Mf hMf,
    cases hg with Mg hMg,
    cases hMf with Af hAMf,
    cases hMg with Ag hAMg,
    existsi (Mf + Mg),
    existsi (max Af Ag),
    intros z hz,
    simp,
    apply le_trans (complex.abs_add _ _),
    apply add_le_add,
    { refine hAMf z _,
      exact le_trans (le_max_left _ _) hz },
    { refine hAMg z _,
      exact le_trans (le_max_right _ _) hz }
  end},
  

  smul_mem' := by {intros c f hyp,  begin
    cases hyp with M hM,
    cases hM with A hAM,
    existsi (complex.abs c * M),
    existsi A,
    intros z hz,
    have h2:=smul_sim  f c z, have h3:=abs_ew ((c• f) z ) (c* f z) h2, rw [complex.abs_mul] at h3,
    have h4:= mul_le_mul_of_nonneg_left (hAM z hz) (complex.abs_nonneg c), rw ← h3 at h4, convert h4,
  end  }, }

 
 
def zero_at_infty: submodule (ℂ) (ℍ  → ℂ):={ 
  carrier :={ f : ℍ → ℂ | ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε },
  zero_mem' :=by {simp, intros ε he, use (-1: ℝ ), intros x  h1, linarith},
  add_mem' := by  {intros f g hf hg ε hε, begin
    cases hf (ε/2) (half_pos hε) with Af hAf,
    cases hg (ε/2) (half_pos hε) with Ag hAg,
    existsi (max Af Ag),
    intros z hz,
    simp,
    apply le_trans (complex.abs_add _ _),
    rw show ε = ε / 2 + ε / 2, by simp,
    apply add_le_add,
    { refine hAf z (le_trans (le_max_left _ _) hz) },
    { refine hAg z (le_trans (le_max_right _ _) hz) }
  end,},
  

  smul_mem' := by {intros c f hyp ε hε, begin
    by_cases hc : (c = 0),
    { existsi (0 : ℝ ), intros, simp only [hc, pi.zero_apply, complex.abs_zero, zero_smul], exact le_of_lt hε },
    have habsinv: (complex.abs c)⁻¹>0:= by {simp only [gt_iff_lt, complex.abs_pos, ne.def, inv_pos], exact hc,}, 
    have hcc:  (ε / complex.abs c) > 0 := by {simp, rw div_eq_mul_inv, apply mul_pos hε habsinv,}, 
    {cases hyp (ε / complex.abs c) (hcc) with A hA,
     existsi A,
      intros z hz, 
      simp,
      rw show ε = complex.abs c * (ε / complex.abs c),
      begin
        rw [mul_comm],
        refine (div_mul_cancel _ _).symm,
        simp [hc]
      end,
      apply mul_le_mul_of_nonneg_left (hA z hz) (complex.abs_nonneg c), }

  end }, }
 


@[simp]lemma bound_mem' (f: ℍ → ℂ): (f ∈  bounded_at_infty ) ↔ ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M:=iff.rfl


@[simp]lemma zero_at_inf_mem' (f: ℍ → ℂ): (f ∈  zero_at_infty  ) ↔ ∀ ε : ℝ, ε > 0 → ∃ A : ℝ, ∀ z : ℍ, im z ≥ A → abs (f z) ≤ ε:=iff.rfl




lemma is_zero_at_inf_is_bound' (f: ℍ → ℂ): (f ∈ zero_at_infty) → (f ∈ bounded_at_infty):=
begin
simp only [zero_at_inf_mem', bound_mem', gt_iff_lt, ge_iff_le, set_coe.forall, subtype.coe_mk],
 intro H, use (1: ℝ), apply H, norm_cast, exact dec_trivial,
end  


-- structure is_modular_form (k : ℕ) (f : ℍ → ℂ) : Prop :=
-- (hol      : is_holomorphic f)
-- (transf   : ∀ M : SL2Z, ∀ z : ℍ, f (SL2Z_H M z) = (M.c*z + M.d)^k * f z)
-- (infinity : ∃ (M A : ℝ), ∀ z : ℍ, im z ≥ A → abs (f z) ≤ M)




def is_modular_form (k : ℕ) := {f : ℍ → ℂ | is_holomorphic f} ∩ (is_Petersson_weight_ k) ∩ bounded_at_infty

def is_cusp_form (k : ℕ) := {f : ℍ → ℂ | is_holomorphic f} ∩ (is_Petersson_weight_ k) ∩ zero_at_infty

lemma is_modular_form_of_is_cusp_form {k : ℕ} (f : ℍ → ℂ) (h : is_cusp_form k f) : is_modular_form k f :=
⟨h.1, is_zero_at_inf_is_bound' f h.2⟩



/-! ### Eisenstein series -/

namespace Eisenstein_series

def Ind:={x : ℤ × ℤ | x ≠ (0,0)}

@[simp]lemma Ind_mem (x: ℤ × ℤ): x ∈ Ind ↔ x ≠ (0,0):=iff.rfl 

--gcd_eq_zero_iff






--intro h2, have h2: gcd z1 z2 =0, by {have hh:= int.gcd_eq_gcd_ab z1 z2, convert hh,  sorry,},  rw gcd_eq_zero_iff at h2, exact h2,



lemma SL2z_entries_coprime (A: SL2Z): is_coprime (A.1 0 0) (A.1 1 0):=
begin
rw is_coprime, have h1:= det_onne A,  simp only [vale] at h1, use (A.1 1 1), use (-A.1 0 1), simp, simp at h1, ring_nf,
cases A, dsimp at *, simp at *, ring_nf, assumption,  
end

lemma r0 (a b z1 z2 x : ℤ) (h: z1*a+z2*b=0): z1*a*x+z2*b*x=0:=

begin
have h1: z1*a*x+z2*b*x=(z1*a+z2*b)*x, by {ring,}, rw h1, rw h, simp only [zero_mul],
end  

lemma r1 (a b c d z1 z2 : ℤ) (h1: a*d-c*b=1) (h2:z1*a*d+z2*c*d=0) (h3: z1*b*c+z2*d*c=0 ): z1=0:=
begin
rw ← h2 at h3, have h0: z2*d*c=z2*c*d, by {sorry,}, rw h0 at h3, simp at h3,  sorry,
end


def Ind_perm (A : SL2Z ): Ind →  Ind:=
λ z, ⟨(z.1.1* (A.1 0 0) +z.1.2* (A.1 1 0), z.1.1*(A.1 0 1)+z.1.2* (A.1 1 1)), by {simp only [Ind_mem, not_and, prod.mk.inj_iff, ne.def, subtype.val_eq_coe],
have h1:=z.property, simp at *, have h2:= det_onne A, simp [vale] at *, intros H1 H2, rw ← subtype.val_eq_coe at h2, 
have ha: z.val.fst * A.val 0 0 * A.val 1 1+ z.val.snd * A.val 1 0 * A.val 1 1 = 0:= by {apply r0, simp only [subtype.val_eq_coe], exact H1,},
have hb: z.val.fst * A.val 0 1 * A.val 1 0+ z.val.snd * A.val 1 1 * A.val 1 0 = 0:= by {apply r0, simp, exact H2,},
have hab: z.val.fst =0:= by {apply r1 (A.val 0 0) (A.val 0 1) (A.val 1 0) (A.val 1 1) z.val.fst z.val.snd  h2  ha hb,},
have ha': z.val.fst * A.val 0 0 * A.val 0 1+ z.val.snd * A.val 1 0 * A.val 0 1 = 0:= by {apply r0, simp, exact H1,},
have hb': z.val.fst * A.val 0 1 * A.val 0 0+ z.val.snd * A.val 1 1 * A.val 0 0 = 0:= by {apply r0, simp, exact H2,},
have hab: z.val.snd =0:= by {sorry,},
cases z, cases A, cases z_val, dsimp at *, simp at *, solve_by_elim,
},⟩

lemma ridic (a b c d : ℤ): a*d-b*c=1 → a*d-c*b=1:=
begin
intro h, linarith,
end

lemma ridic2 (a b c d z : ℤ) (h: a*d-b*c=1):  z*d*a-z*c*b=z:=
begin
ring_nf, rw h, rw one_mul,
end

lemma Ind_equiv (A : SL2Z): Ind ≃ Ind:={
to_fun:=Ind_perm A,
inv_fun:=Ind_perm A⁻¹,
left_inv:=λ z, by {rw Ind_perm, rw Ind_perm, 
have ha:= SL2Z_inv_a A, simp only [vale] at ha, 
have hb:= SL2Z_inv_b A, simp only [vale] at hb, 
have hc:= SL2Z_inv_c A, simp only [vale] at hc, 
have hd:= SL2Z_inv_d A, simp only [vale] at hd, 
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf, rw mul_comm at hdet, simp only [hdet], 
have ht: A.val 1 1 * A.val 1 0 - A.val 1 0 * A.val 1 1=0, by {ring, }, simp only [ht], 
have ht2: -(A.val 0 1 * A.val 0 0) + A.val 0 0 * A.val 0 1=0, by {ring,}, simp only [ht2],
have ht3: -(A.val 0 1 * A.val 1 0) + A.val 0 0 * A.val 1 1 =1, by {rw add_comm,  rw mul_comm at hdet, simp, 
simp at *, ring_nf, rw ridic, exact hdet, }, simp only [ht3], ring_nf,
 cases z, cases A, cases z_val, dsimp at *, simp at *,},
right_inv:= λ z, by { rw Ind_perm, rw Ind_perm, 
have ha:= SL2Z_inv_a A, simp only [vale] at ha, 
have hb:= SL2Z_inv_b A, simp only [vale] at hb, 
have hc:= SL2Z_inv_c A, simp only [vale] at hc, 
have hd:= SL2Z_inv_d A, simp only [vale] at hd, 
have hdet:=det_onne A, simp only [vale] at hdet,
simp only, ring_nf, simp only [ha, hb, hc, hd], ring_nf, 
have hz1:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.val.fst hdet, simp only [hz1], 
have hz2:= ridic2 (A.val 0 0) (A.val 1 0) (A.val 0 1) (A.val 1 1) z.val.snd hdet, simp only [hz2], 
cases z, cases A, cases z_val, dsimp at *, simp at *, } ,
}




def Eis' (k: ℤ) (z : ℍ) : Ind →  ℂ:=
λ x, 1/(x.1.1*z+x.1.2)^k  

lemma Eis'_moeb (k: ℤ) (z : ℍ) (A : SL2Z) (i : Ind): Eis' k (moeb A z) i=  ((A.1 1 0*z+A.1 1 1)^k)*(Eis' k z (Ind_equiv A i ) ):=

begin
rw Eis', rw Eis', rw moeb, simp, rw mat2_complex, simp, dsimp,  sorry,
end  

def Eisenstein_series_weight_ (k: ℤ) : ℍ → ℂ:=
 λ z, ∑' (x : Ind), (Eis' k z x) 



lemma Eis_is_summable (A: SL2Z) (k : ℤ) (z : ℍ) : summable (Eis' k z) :=

begin
rw summable, use (0: ℂ), rw has_sum, rw Eis', simp, sorry, 
end  

lemma Eis_is_summable' (A: SL2Z) (k : ℤ) (z : ℍ) : summable (Eis' k z ∘⇑(Ind_equiv A)) :=
begin
rw equiv.summable_iff (Ind_equiv A), exact Eis_is_summable A k z,

end

lemma Eis_is_Pet (k: ℤ):  (Eisenstein_series_weight_ k) ∈ is_Petersson_weight_ k :=

begin
rw is_Petersson_weight_, rw Eisenstein_series_weight_, simp only [set.mem_set_of_eq], 
intros A z, have h1:= Eis'_moeb k z A,  have h2:=tsum_congr h1, convert h2, simp only [subtype.val_eq_coe], 
have h3:=equiv.tsum_eq (Ind_equiv A) (Eis' k z), 
have h5:= summable.tsum_mul_left ((((A.1 1 0): ℂ) * z + ((A.1 1 1): ℂ)) ^ k) (Eis_is_summable' A k z),
 simp only [prod.forall, function.comp_app, set_coe.forall, subtype.val_eq_coe] at *,  
 rw ← h3, simp only [vale, subtype.val_eq_coe], convert h5, rw h5,
end

end Eisenstein_series



/-
instance (k : ℕ) : is_submodule (is_modular_form k) := is_submodule.inter_submodule

instance (k : ℕ) : is_submodule (is_cusp_form k) := is_submodule.inter_submodule

/- def Hecke_operator {k : ℕ} (m : ℤ) : modular_forms k → modular_forms k :=
λ f,
(m^k.pred : ℂ) • (sorry : modular_forms k) -- why is this • failing?
 -/
 -/