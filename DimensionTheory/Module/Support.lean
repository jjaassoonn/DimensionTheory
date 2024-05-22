import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Algebra.Exact

import DimensionTheory.missing_lemmas.Ideal

open PrimeSpectrum
open BigOperators

universe u v
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

notation module " _p " primeIdeal:40 =>
  LocalizedModule (Ideal.primeCompl primeIdeal.1) module

/--
Support of an `R`-module
-/
def Module.Supp : Set (PrimeSpectrum R) :=
{ 𝔭 : PrimeSpectrum R | Nontrivial <| M _p 𝔭 }

notation "Supp(" R "," M ")" => Module.Supp R M

namespace Module.Supp

variable {R}

lemma mem_iff {𝔭 : PrimeSpectrum R} : 𝔭 ∈ Supp(R, M) ↔ Nontrivial (M _p 𝔭) := Iff.rfl

lemma mem_iff_of_finite [fin : Module.Finite R M] {𝔭 : PrimeSpectrum R} :
    𝔭 ∈ Supp(R, M) ↔ 𝔭 ∈ zeroLocus (Module.annihilator R M) := by
  classical
  constructor
  · rintro (⟨x, y, hxy⟩ : Nontrivial _) r hr₀
    by_contra! hr₁
    suffices Subsingleton (M _p 𝔭) from hxy (Subsingleton.elim _ _)
    have eq : ∀ (x : M _p 𝔭), x = 0 := by
      intro x
      induction x using LocalizedModule.induction_on with
      | h a b =>
        show _ = LocalizedModule.mk 0 1
        rw [LocalizedModule.mk_eq]
        refine ⟨⟨r, hr₁⟩, ?_⟩
        simp only [SetLike.mem_coe, Module.mem_annihilator] at hr₀
        simpa only [one_smul, smul_zero] using hr₀ a
    exact ⟨fun a b ↦ eq a |>.trans <| eq b |>.symm⟩
  · intro H
    by_contra! h
    replace h := subsingleton_or_nontrivial (M _p 𝔭) |>.resolve_right h
    obtain ⟨S, hS⟩ := fin.1
    if hS' : S = ⊥
    then
      subst hS'
      simp only [Finset.bot_eq_empty, Finset.coe_empty, Submodule.span_empty] at hS
      have eq0 : annihilator R M = ⊤ := by
        ext x
        simp only [mem_annihilator, Submodule.mem_top, iff_true]
        intro m
        have mem : x • m ∈ (⊤ : Submodule R M) := ⟨⟩
        rwa [← hS] at mem
      simp [eq0] at H
    else
      have (ω : S) : LocalizedModule.mk ω.1 1 = .mk 0 1 := h.elim _ _
      simp_rw [LocalizedModule.mk_eq, one_smul, smul_zero] at this
      choose x hx using this
      have mem : (∏ (ω : S), x ω : R) ∈ annihilator R M := by
        rw [mem_annihilator]
        intro m
        have mem_m : m ∈ (⊤ : Submodule R M) := ⟨⟩
        rw [← hS, mem_span_finset] at mem_m
        obtain ⟨f, rfl⟩ := mem_m
        rw [Finset.smul_sum]
        apply Finset.sum_eq_zero
        intro z hz

        let e : Option (S.erase z) ≃ S :=
          Finset.subtypeInsertEquivOption (t := S.erase z) (x := z) (h := by simp) |>.symm.trans
          ⟨fun x ↦ ⟨x.1, by simpa [Finset.insert_erase hz] using x.2⟩,
            fun x ↦ ⟨x.1, by simp [Finset.insert_erase hz, x.2]⟩,
            by intro; ext; rfl, by intro; ext; rfl⟩
        rw [calc (∏ (ω : S), x ω : R)
          _ = ∏ ω : Option (S.erase z), (x ⟨_, (e ω).2⟩ : R) :=
              Fintype.prod_bijective e e.bijective _ _ (fun _ ↦ rfl) |>.symm,
          Fintype.prod_option]
        simp only [Finset.subtypeInsertEquivOption, ne_eq, Option.elim, Equiv.trans_apply,
          Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, Finset.univ_eq_attach, e]
        rw [mul_comm, mul_smul, ← mul_smul _ (f z), mul_comm, mul_smul]
        erw [hx ⟨_, hz⟩]
        rw [smul_zero, smul_zero]
      specialize H mem
      erw [SetLike.mem_coe] at H
      rw [𝔭.2.prod_mem_iff_exists_mem'] at H
      simp only [Finset.univ_eq_attach, Finset.mem_attach, true_and, Subtype.exists] at H
      obtain ⟨_, _, h⟩ := H
      exact (x _).2 h

lemma eq_union_of_exact
    {M' M M'' : Type*}
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module R M'] [Module R M] [Module R M'']
    [Module.Finite R M'] [Module.Finite R M] [Module.Finite R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (inj : Function.Injective f)
    (ex : Function.Exact f g)
    (surj : Function.Surjective g) :
    Supp(R, M) = Supp(R, M') ∪ Supp(R, M'') := by
  sorry

end Module.Supp
