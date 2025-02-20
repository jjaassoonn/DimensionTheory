/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Additive Functions from an abelian Category

If `G` is an commutative additive group and `𝒞` an abelian category, then an additive function with
value in `G` is a function `μ : 𝒞 → G` such that whenever `0 → A → B → C → 0` is short exact,
we have `μ(B) = μ(A) + μ(C)`.

## Main results

- `μ(0) = 0`
- `μ(A) = μ(B)` if `A ≅ B`
- if `f : A ⟶ B`, then `μ (kernel f) + μ (image f) = μ A` and `μ (image f) + μ (cokernel f) = μ B`
- if `A₀ → A₁ → A₂ → A₃ → A₄ → A₅` is exact, then
  `μ(A₀) - μ(A₁) + μ(A₂) - μ(A₃) + μ(A₄) - μ(A₅) = μ (ker f₀) - μ (coker f₄)`.

-/

open CategoryTheory CategoryTheory.Limits

universe u u' v v' w

variable (𝒞 : Type u) [Category.{v} 𝒞] (𝒟 : Type u') [Category.{v'} 𝒟]
variable (G : Type w) [AddCommGroup G]
variable [Abelian 𝒞] [Abelian 𝒟]

open ZeroObject

/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
structure AdditiveFunction :=
/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
toFun : 𝒞 → G
/--
A function `λ : 𝒞 → ℤ` is additive precisely when `λ B = λ A + λ C` for every short exact sequence
`s := 0 --> A --> B --> C --> 0`.
-/
additive (s : ShortComplex 𝒞) (hs : s.ShortExact) : toFun s.X₁ + toFun s.X₃ = toFun s.X₂

@[inherit_doc]
notation 𝒞 "⟹+" G => AdditiveFunction 𝒞 G


-- @[inherit_doc]
-- notation C "==>+ ℤ" => AdditiveFunction C

namespace AdditiveFunction

variable {𝒞 G}
variable (μ : 𝒞 ⟹+ G)

private lemma ext' {α β : 𝒞 ⟹+ G} (h : α.toFun = β.toFun) : α = β := by
  cases α; cases β; rwa [mk.injEq]

instance : DFunLike (AdditiveFunction 𝒞 G) 𝒞 (fun _ ↦ G) where
  coe μ := μ.toFun
  coe_injective' _ _ h := AdditiveFunction.ext' h

@[ext] lemma ext {α β : 𝒞 ⟹+ G} (h : ∀ x, α x = β x) : α = β := by
  apply ext'; ext; apply h

lemma map_zero : μ 0 = 0 := by
  let s : ShortComplex 𝒞 :=
  { X₁ := 0
    X₂ := 0
    X₃ := 0
    f := 0
    g := 0
    zero := by aesop_cat }
  have hs : s.Exact := by
    rw [ShortComplex.exact_iff_mono]
    simp only [s]
    · infer_instance
    · rfl
  replace hs : s.ShortExact := ⟨hs⟩
  have : μ 0 + μ 0 = μ 0 := μ.additive s hs
  aesop

lemma eq_of_iso {x y : 𝒞} (e : x ≅ y) : μ x = μ y := by
  let s : ShortComplex 𝒞 :=
  { X₁ := x
    X₂ := y
    X₃ := 0
    f := e.hom
    g := 0
    zero := by aesop_cat }
  have hs : s.Exact := by
    rw [ShortComplex.exact_iff_epi]
    simp only
    · infer_instance
    · rfl
  replace hs : s.ShortExact := ⟨hs⟩
  have : μ x + μ 0 = μ y := μ.additive s hs
  rwa [map_zero, add_zero] at this

section

variable {A B : 𝒞} (f : A ⟶ B)

private noncomputable abbrev sc1 : ShortComplex 𝒞 where
  X₁ := kernel f
  X₂ := A
  X₃ := image f
  f := kernel.ι _
  g := factorThruImage f
  zero := zero_of_comp_mono (image.ι f) <| by
    rw [Category.assoc, image.fac, kernel.condition]

private lemma sc1_exact : sc1 f |>.Exact := by
  simp only [sc1]
  apply ShortComplex.exact_of_f_is_kernel

  fapply KernelFork.IsLimit.ofι
  · intro x g h
    refine kernel.lift _ g ?_
    rw [← image.fac f, ← Category.assoc, h]
    simp only [zero_comp]
  · intro x g h
    simp only [kernel.lift_ι]
  · intro x g h g' h'
    ext
    simpa

private lemma sc1_shortExact : sc1 f |>.ShortExact := ⟨sc1_exact _⟩

private noncomputable abbrev sc2 : ShortComplex 𝒞 where
  X₁ := image f
  X₂ := B
  X₃ := cokernel f
  f := image.ι _
  g := cokernel.π _
  zero := by aesop_cat

private lemma sc2_exact : sc2 f |>.Exact := by
  apply ShortComplex.exact_of_g_is_cokernel
  simp only
  fapply CokernelCofork.IsColimit.ofπ
  · intro x g h
    refine cokernel.desc _ g ?_
    rw [← image.fac f, Category.assoc, h]
    simp
  · aesop_cat
  · intros x g h g' h'
    aesop_cat

private lemma sc2_shortExact : sc2 f |>.ShortExact := ⟨sc2_exact _⟩

lemma eq_apply_kernel_add_apply_image : μ (kernel f) + μ (image f) = μ A :=
  μ.additive _ <| sc1_shortExact f

lemma eq_apply_image_add_apply_cokernel : μ (image f) + μ (cokernel f) = μ B :=
  μ.additive _ <| sc2_shortExact f

lemma apply_kernel_sub_apply_cokernel_eq_apply_src_sub_apply_tgt :
    μ (kernel f) - μ (cokernel f) = μ A - μ B := by
  have eq1 := congr_arg₂ (· - ·) (μ.eq_apply_kernel_add_apply_image f)
    (μ.eq_apply_image_add_apply_cokernel f)
  simp only at eq1
  rw [← eq1]
  abel

end

section ShortComplex

variable (s : ShortComplex 𝒞) (hs : s.Exact)

private noncomputable def imageIsoKernel : image s.f ≅ kernel s.g :=
  calc image s.f
    _ ≅ imageSubobject s.f := imageSubobjectIso _ |>.symm
    _ ≅ kernelSubobject s.g :=
      letI : IsIso (imageToKernel s.f s.g s.zero) := by
        rwa [← ShortComplex.exact_iff_isIso_imageToKernel]
      asIso (imageToKernel s.f s.g _)
    _ ≅ kernel s.g := kernelSubobjectIso _

include hs in
lemma apply_shortComplex_of_exact : μ (kernel s.f) - μ (image s.g) = μ s.X₁ - μ s.X₂ := by
  have eq1 : μ (kernel s.f) + μ (image s.f) - (μ (kernel s.g) + μ (image s.g)) = μ s.X₁ - μ s.X₂ :=
    congr_arg₂ (· - ·)
      (μ.eq_apply_kernel_add_apply_image s.f)
      (μ.eq_apply_kernel_add_apply_image s.g)
  rw [μ.eq_of_iso (imageIsoKernel s hs)] at eq1
  rwa [add_comm (μ (kernel s.g)), add_sub_add_right_eq_sub] at eq1

lemma apply_shortComplex_of_exact' : μ (kernel s.g) - μ (cokernel s.g) = μ s.X₂ - μ s.X₃ :=
  μ.apply_kernel_sub_apply_cokernel_eq_apply_src_sub_apply_tgt s.g

end ShortComplex

section ComposableArrows

section arbitrary_length

variable {N : ℕ} (S : ComposableArrows 𝒞 N) (hS : S.Exact)

local notation "ker_" m => kernel (S.map' m (m + 1))
local notation "im_" m => image (S.map' m (m + 1))

@[simps!]
private noncomputable def im_eq_ker_succ (n : ℕ) (hn : n + 2 ≤ N := by omega) :
    (image (S.map' n (n + 1))) ≅ kernel (S.map' (n + 1) (n + 2)) :=
  (imageSubobjectIso (S.map' n (n + 1))).symm ≪≫
    @asIso (f := imageToKernel (S.map' n (n + 1)) (S.map' (n + 1) (n + 2)) <|
        hS.toIsComplex.zero n) _ (by
        let S' : ShortComplex 𝒞 := S.sc hS.toIsComplex n
        change IsIso (imageToKernel S'.f S'.g S'.zero)
        rw [← ShortComplex.exact_iff_isIso_imageToKernel]
        exact hS.exact _) ≪≫
  kernelSubobjectIso (S.map' (n + 1) (n + 2))

include hS in
lemma apply_image_eq_apply_ker_succ (n : ℕ) (hn : n + 2 ≤ N) : μ (im_ n) = μ (ker_ (n + 1)) :=
  μ.eq_of_iso (im_eq_ker_succ S hS n hn)

include hS in
lemma apply_sub_apply_succ (n : ℕ) (hn : n + 3 ≤ N) :
    μ (S.obj' n) - μ (S.obj' (n + 1)) =
    μ (ker_ n) - μ (ker_ (n + 2)) := by
  have eq0 : μ (S.obj' n) - μ (S.obj' (n + 1)) = μ (ker_ n) - μ (im_ (n + 1)) :=
    μ.apply_shortComplex_of_exact (S.sc hS.toIsComplex n) (hS.exact _) |>.symm
  rw [apply_image_eq_apply_ker_succ (hS := hS)] at eq0
  exact eq0

include hS in
lemma apply_eq_apply_image_add_apply_image
    (n : ℕ) (hn1 : 1 ≤ n := by omega) (hn2 : n + 1 ≤ N := by omega) :
    μ (S.obj' n) = μ (image (S.map' (n - 1) n)) + μ (image (S.map' n (n + 1))) := by
  let sc : ShortComplex 𝒞 :=
  { X₁ := image (S.map' (n - 1) n)
    X₂ := S.obj' n
    X₃ := image (S.map' n (n + 1))
    f := image.ι _
    g := factorThruImage (S.map' _ _)
    zero := by
      refine zero_of_comp_mono (image.ι _) ?_
      rw [Category.assoc, image.fac]
      refine image.ext _ ?_
      rw [image.fac_assoc, comp_zero]

      have eq1 :
          S.map' (n - 1) (n - 1 + 1) ≫ S.map' (n - 1 + 1) (n - 1 + 2) ≫
          S.map' (n - 1 + 2) (n + 1) = 0 := by
        rw [← Category.assoc, hS.toIsComplex.zero (n - 1), zero_comp]
      simp only [← S.map_comp, homOfLE_comp, ← eq1] }

  have sc_exact : sc.Exact := by
    have e1 := hS.exact' (n - 1) n (n + 1)
    rw [ShortComplex.exact_iff_image_eq_kernel] at e1 ⊢
    simp only [ComposableArrows.obj', Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int,
      ComposableArrows.map', homOfLE_leOfHom] at e1 ⊢
    convert e1 using 1
    · exact imageSubobject_mono _
    · generalize_proofs _ _ h
      simp_rw [← image.fac (S.map <| homOfLE h)]
      rw [kernelSubobject_comp_mono]

  have sc_shortExact : sc.ShortExact := ⟨sc_exact⟩
  exact μ.additive _ sc_shortExact |>.symm

include hS in
lemma apply_eq_apply_kernel_add_apply_kernel
    (n : ℕ) (hn : n + 2 ≤ N) :
    μ (S.obj' n) = μ (kernel (S.map' n (n + 1))) + μ (kernel (S.map' (n + 1) (n + 2))) := by
  let sc : ShortComplex 𝒞 :=
  { X₁ := kernel (S.map' n (n + 1))
    X₂ := S.obj' n
    X₃ := kernel (S.map' (n + 1) (n + 2))
    f := kernel.ι _
    g := kernel.lift _ (S.map' _ _) <| hS.toIsComplex.zero n
    zero := zero_of_comp_mono (kernel.ι _) <| by simp }

  have sc_exact : sc.Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    simp only [ComposableArrows.obj', Int.reduceNeg, id_eq, Nat.cast_ofNat, Int.Nat.cast_ofNat_Int,
      ComposableArrows.map', homOfLE_leOfHom]
    fapply KernelFork.IsLimit.ofι
    · intro x g h
      exact kernel.lift _ g <| by simpa using h =≫ kernel.ι _
    · intro x g h
      simp
    · intro x g h g' h'
      ext
      simpa

  have sc_shortExact : sc.ShortExact := by
    refine .mk' sc_exact equalizer.ι_mono ?_
    change Epi (kernel.lift _ _ _)

    suffices eq0 :
      (kernel.lift _ (S.map' n (n + 1)) <| hS.toIsComplex.zero n) =
      factorThruImage _ ≫ (im_eq_ker_succ S hS n).hom by rw [eq0]; exact epi_comp _ _

    ext
    rw [im_eq_ker_succ_hom (n := n), kernel.lift_ι, Category.assoc, Category.assoc, Category.assoc,
      kernelSubobject_arrow, imageToKernel_arrow, imageSubobject_arrow', image.fac]

  exact μ.additive _ sc_shortExact |>.symm

end arbitrary_length

section length6

variable (S : ComposableArrows 𝒞 5) (hS : S.Exact)

local notation "μ_" n => μ (S.obj' n)

include hS in
lemma alternating_apply_aux_of_length6 :
    (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) =
    (μ (kernel (S.map' 0 1)) - μ (kernel (S.map' 4 5))) + (μ_ 4) - (μ_ 5) := by
  rw [show (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) =
    ((μ_ 0) - (μ_ 1)) + ((μ_ 2) - (μ_ 3)) + ((μ_ 4) - (μ_ 5)) by abel]

  rw [apply_sub_apply_succ (hS := hS) (n := 0), apply_sub_apply_succ (hS := hS) (n := 2)]
  abel

include hS in
lemma alternating_sum_apply_of_length6 :
    (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) =
    μ (kernel (S.map' 0 1)) - μ (cokernel (S.map' 4 5)) := by
  rw [μ.alternating_apply_aux_of_length6 (hS := hS)]
  have eq0 : _ = μ (S.obj' 4) - μ (S.obj' 5) :=
    μ.apply_shortComplex_of_exact' (S.sc hS.toIsComplex 3)
  rw [add_sub_assoc, ← eq0]
  simp only [Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, id_eq, Nat.cast_ofNat, Fin.zero_eta,
    Fin.mk_one, ComposableArrows.map', sub_add_sub_cancel]

include hS in
lemma alternating_sum_apply_eq_zero_of_zero_zero_of_length6_aux
    (left_zero : IsZero S.left) (right_zero : IsZero S.right) :
    (μ_ 0) - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) - (μ_ 5) = 0 := by
  rw [alternating_sum_apply_of_length6 (hS := hS)]
  rw [show μ (kernel (S.map' 0 1)) = 0 from ?_, show μ (cokernel (S.map' 4 5)) = 0 from ?_,
    sub_zero]
  · rw [μ.eq_of_iso, μ.map_zero]
    rw [show ComposableArrows.map' S 4 5 = 0 from IsZero.eq_zero_of_tgt right_zero _]
    exact cokernelZeroIsoTarget ≪≫ right_zero.isoZero
  · rw [μ.eq_of_iso, μ.map_zero]
    rw [show ComposableArrows.map' S 0 1 = 0 from IsZero.eq_zero_of_src left_zero _]
    exact kernelZeroIsoSource ≪≫ left_zero.isoZero

include hS in
lemma alternating_sum_apply_eq_zero_of_zero_zero_of_length6
    (left_zero : IsZero S.left) (right_zero : IsZero S.right) :
    - (μ_ 1) + (μ_ 2) - (μ_ 3) + (μ_ 4) = 0 := by
  refine Eq.trans ?_ <|
    μ.alternating_sum_apply_eq_zero_of_zero_zero_of_length6_aux (hS := hS)
      left_zero right_zero
  rw [show (μ_ 0) = 0 from (μ.eq_of_iso <| IsZero.iso left_zero <| isZero_zero _).trans μ.map_zero]
  rw [show (μ_ 5) = 0 from (μ.eq_of_iso <| IsZero.iso right_zero <| isZero_zero _).trans μ.map_zero]
  rw [zero_sub, sub_zero]

include hS in
lemma alternating_sum_apply_eq_zero_of_zero_zero_of_length6'
    (left_zero : IsZero S.left) (right_zero : IsZero S.right) :
    (μ_ 1) - (μ_ 2) + (μ_ 3) - (μ_ 4) = 0 := by
  have eq0 := congr_arg (-·) <|
    μ.alternating_sum_apply_eq_zero_of_zero_zero_of_length6 (hS := hS) left_zero right_zero
  dsimp only [id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceAdd,
    Int.reduceSub, ComposableArrows.obj', Nat.reduceAdd, Fin.mk_one, Fin.reduceFinMk] at eq0
  rw [neg_zero] at eq0
  rw [← eq0]
  abel

end length6

end ComposableArrows

section AddCommGroup

instance add : Add (𝒞 ⟹+ G) where
  add α β :=
  { toFun := α + β
    additive := fun s hs ↦ by
      have eq0 : α _ + α _ + (β _ + β _) = α _ + β _ :=
        congr_arg₂ (· + ·) (α.additive _ hs) (β.additive _ hs)
      simp only [Pi.add_apply] at eq0 ⊢
      rw [← eq0]
      abel }

@[simp] lemma add_apply (α β : 𝒞 ⟹+ G) (x) : (α + β) x = α x + β x := rfl

instance neg : Neg (𝒞 ⟹+ G) where
  neg μ :=
  { toFun := - μ
    additive := fun s hs ↦ by
      have eq0 : - (μ _ + μ _) = - μ _ := congr_arg (- ·) (μ.additive _ hs)
      simp only [Pi.neg_apply] at eq0 ⊢
      rw [← eq0]
      abel }

@[simp] lemma neg_apply (μ : 𝒞 ⟹+ G) (x) : (-μ) x = - (μ x) := rfl

instance zero : Zero (𝒞 ⟹+ G) where
  zero :=
  { toFun := 0
    additive := fun _ _ ↦ show 0 + 0 = 0 by simp }

@[simp] lemma zero_apply (x) : (0 : 𝒞 ⟹+ G) x = 0 := rfl

instance addSemigroup : AddSemigroup (𝒞 ⟹+ G) where
  add_assoc α β γ := ext fun x ↦ by simp [add_assoc]

instance addZeroClass : AddZeroClass (𝒞 ⟹+ G) where
  zero_add _ := ext fun _ ↦ by simp
  add_zero _ := ext fun _ ↦ by simp

instance addMonoid : AddMonoid (𝒞 ⟹+ G) where
  __ := addSemigroup
  __ := addZeroClass
  nsmul := nsmulRec
  nsmul_zero _ := by simp only [nsmulRec]
  nsmul_succ _ _ := by simp only [nsmulRec]


instance addCommMonoid : AddCommMonoid (𝒞 ⟹+ G) where
  __ := addMonoid
  add_comm _ _ := ext fun _ ↦ by simp [add_comm]

instance : AddCommGroup (𝒞 ⟹+ G) where
  __ := addCommMonoid
  neg_add_cancel _ := ext fun _ ↦ by simp
  zsmul := zsmulRec

end AddCommGroup

section equivalence

variable {𝒟}
variable (e : 𝒞 ≌ 𝒟)

/--
pushforward of an additive function along a category equivalence
-/
@[simps]
def pushforward : 𝒟 ⟹+ G where
  toFun x := μ (e.inverse.obj x)
  additive _ h := μ.additive _ (h.map_of_exact e.inverse)

end equivalence

end AdditiveFunction
