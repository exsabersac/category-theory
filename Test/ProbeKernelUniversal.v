(*
   本文件为测试：ProbeKernelUniversal。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Kernel.Universal.
Require Import Category.Structure.Kernel.Universal.Examples.

Local Open Scope category_scope.

Section KillProbes.

Context {C : Category}.
Context {ZM : ZeroMorphisms C}.
Context {x y k : C}.
Context (f : x ~> y).
Context (i : k ~> x).
Context (K : IsKernelOf f i).
Context (U : AUniversalElement (KillPresheaf f) k).

(*
   本节说明 ProbeKernelUniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (kernel_aue_morphism f K).
Check (aue_kernel_morphism f U).
Check (fun (d : C) (h : d ~{C}~> x) (Hh : f ∘ h ≈ zmor) =>
         kernel_aue_mediator f K d h Hh).
Check (fun (d : C) (h : d ~{C}~> x) (Hh : f ∘ h ≈ zmor ∘ h) =>
         kernel_round_mediator f K h Hh).
Check (fun (d : C) (p : Kills f d) => aue_kernel_round_mediator f U d p).

(** 本节：Negative: whole record does not come back kernel side.
 (Stripped: cannot unify [aue_kernel f (kernel_aue f K)] [K].) （已译） *)
Fail Check (eq_refl : aue_kernel f (kernel_aue f K) = K).

(** Negative: not even [fork_eq] field alone -- [kill_fork] and
 [fork_kill] opaque, so 复合 not 恒等 term.
 (Stripped: cannot unify two [fork_eq] terms.) （已译） *)
Fail Check (eq_refl : fork_eq (aue_kernel f (kernel_aue f K)) = fork_eq K).

(** 本节：Negative: nor universal-element side. (Stripped: cannot unify
 [kernel_aue f (aue_kernel f U)] [U].) （已译） *)
Fail Check (eq_refl : kernel_aue f (aue_kernel f U) = U).

(*
   本节说明 ProbeKernelUniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun (d : C) (p : Kills f d) =>
              eq_refl
                : unique_obj (@aue_universal (C^op) (KillPresheaf f) k
                                (kernel_aue f (aue_kernel f U)) d p)
                  = unique_obj (@aue_universal (C^op) (KillPresheaf f) k U d p)).

End KillProbes.

Section ForkProbes.

Context {C : Category}.
Context {x y k : C}.
Context (f g : x ~> y).
Context (i : k ~> x).
Context (E : IsEqualizer f g k i).
Context (V : AUniversalElement (ForkPresheaf f g) k).

(*
   本节说明 ProbeKernelUniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (aue_equalizer_round f g E).
Check (aue_equalizer_round_universal f g V).
Check (aue_equalizer_round_elem f g V).
Check (fun (d : C) (p : Forks f g d) => aue_equalizer_round_mediator f g V d p).

(** 本节：Negative: other whole round trip not [eq_refl]. (Stripped:
 cannot unify [equalizer_aue f g (aue_equalizer f g V)] [V].) （已译） *)
Fail Check (eq_refl : equalizer_aue f g (aue_equalizer f g V) = V).

(* 相关说明。 （已译） *)

Check (fun (ZM : ZeroMorphisms C) => kill_fork_iso f).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun ZM : ZeroMorphisms C =>
              eq_refl : KillPresheaf f = ForkPresheaf f zmor).

(* * Negative: nor are their element types the same type.  Stripped, again
    without a "cannot unify" line: the term [eq_refl] 'has type
    "Kills f k = Kills f k" while it is expected to have type
    "Kills f k = Forks f zmor k"'.（标题）（已译） *)
Fail Check (fun ZM : ZeroMorphisms C =>
              eq_refl : Kills f k = Forks f zmor k).

End ForkProbes.

(*
   本节说明hom、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun (C : Category) (ZM : ZeroMorphisms C) (x y : C) (f : x ~> y)
           (k : C) => @kernel_universal_element_iso C ZM x y f k).

Check (fun (C : Category) (x y : C) (f g : x ~> y) (k : C) =>
         @equalizer_universal_element_iso C x y f g k).

(*
   本节说明 ProbeKernelUniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (fun (A B : AbObject) (f : A ~{Ab}~> B) (k : Ab) =>
              @kernel_universal_element_iso Ab
                (ZeroMorphisms_of_ZeroObject Ab_Zero) A B f k).

Fail Check (fun (R S : Rng) (u v : R ~{Rng}~> S) (k : Rng) =>
              @equalizer_universal_element_iso Rng R S u v k).

(*
   本节说明 ProbeKernelUniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_aue f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_representation f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_Representable f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) => ab_kernel_repr_obj f).
Check (fun (A B : AbObject) (f : A ~{Ab}~> B) (z : AbObject)
           (h : z ~{Ab}~> A) => ab_kernel_round f h).

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun (C : Category) (Z : @ZeroObject C) (x y : C) =>
         @zmor_is_zero_mor C Z x y).

Check (fun (C : Category) (Z : @ZeroObject C) (x y k : C) (f : x ~> y)
           (i : k ~> x) => @IsKernel_is_IsKernelOf C Z x y f k i).

Check (ab_parity_med_computes).
Check (ab_parity_kernel_has_two).
Check (ab_parity_kernel_proper).

(*
   本节说明 ProbeKernelUniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (Rng_no_zero_morphisms : ZeroMorphisms Rng → False).
Check (Rng_no_zero_object : @ZeroObject Rng → False).

(** 本节：... fork presheaf nevertheless formable there. （已译） *)
Check (fun (R S : Rng) (u v : R ~{Rng}~> S) => Rng_fork_presheaf u v).
