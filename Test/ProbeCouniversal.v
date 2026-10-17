(*
   本文件为测试：ProbeCouniversal。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Arrow.Dual.Examples.

Local Open Scope category_scope.

Section Probes.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {c : C}.
Context (U : CouniversalArrow c F).

(* 相关说明。 （已译） *)

Check (coarrow U : F (coarrow_obj U) ~{C}~> c).

Check (eq_refl : coarrow U = @arrow (C^op) (D^op) c (Opposite_Functor F) U).

Check (eq_refl : coarrow_obj U
                   = @arrow_obj (C^op) (D^op) c (Opposite_Functor F) U).

(** The couniversal 映射 property likewise: statement mentions no
 [op], it primal statement's own term. （已译） *)

Check (fun (d : D) (h : F d ~{C}~> c) =>
         eq_refl : @ump_couniversal_arrows C D c F U d h
                     = @ump_universal_arrows (C^op) (D^op) c
                         (Opposite_Functor F) U d h).

(* * ** (2) The terminal-对象 reading 定理

 Positive control: construction, fact it chooses the
 couniversal 对象 nose. （已译） *)

Check (couniversal_arrow_terminal U : @Terminal (F ↓ =(c))).
Check (couniversal_arrow_terminal_obj U).
Check (couniversal_arrow_of_terminal (couniversal_arrow_terminal U)
         : CouniversalArrow c F).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (@arrow_initial (C^op) (D^op) c (Opposite_Functor F) U
              : @Terminal (F ↓ =(c))).

(** Nor two comma 范畴 themselves Leibniz-equal — the
 reason mismatch, isolated. (Stripped: cannot unify.) （已译） *)
Fail Check (eq_refl
              : @Comma _1 (D^op) (C^op) (@Diagonal (C^op) _1 c)
                       (Opposite_Functor F)
                  = @Comma D _1 C F (@Diagonal C _1 c)).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (fun T : @Terminal (F ↓ =(c)) => terminal_is_initial_op T).
Check (fun T : @Terminal (F ↓ =(c)) => (T : @Initial ((F ↓ =(c))^op))).

(** ...and it not closed Construction/Comma.v's [Cocomma] either,
 issue proposed route. Positive control first: the
 cocomma same two 函子 exists. （已译） *)
Check (@Cocomma D _1 C F (@Diagonal C _1 c) : Category).

(** 本节：Negative: it not comma op-side [arrow_initial] inhabits.
 (Stripped: cannot unify [@Initial (=(c) ↓ F^op)] with
 [@Initial (F ↑ =(c))].) （已译） *)
Fail Check (@arrow_initial (C^op) (D^op) c (Opposite_Functor F) U
              : @Initial (@Cocomma D _1 C F (@Diagonal C _1 c))).

(** 本节：Negative: nor it opposite F ↓ =(c) nose.
 (Stripped: cannot unify [F ↑ =(c)] [(F ↓ =(c))^op].) （已译） *)
Fail Check (eq_refl : @Cocomma D _1 C F (@Diagonal C _1 c)
                        = (@Comma D _1 C F (@Diagonal C _1 c))^op).

(* 相关说明。 （已译） *)
Check (CouniversalArrow c F : Type).
Check (UniversalArrow c F : Type).

(** 本节：Negative: they different. (Stripped: cannot unify
 [CouniversalArrow c F] [UniversalArrow c F].) （已译） *)
Fail Check (eq_refl : CouniversalArrow c F = UniversalArrow c F).

End Probes.

(* * ** (4) The counit agrees up [≈]

 Measured at worked example, so probe about real
 伴随 not variable. （已译） *)

Section CounitProbe.

Context `{C : Category}.
Context `{@Cartesian C}.
Context (p : C ∏ C).

(** Positive controls: 对象 action assembled 右伴随
 reduces product nose, counit IS projection
 pair up [≈]. （已译） *)
Check (eq_refl : fobj[@product_via_couniversal_functor C _] p
                   = (fst p × snd p)).
Check (@product_via_couniversal_counit C _ p).

(** 本节：Negative: agreement not [eq_refl]. (Stripped: cannot
 unify [counit] [proj_pair p].) （已译） *)
Fail Check (eq_refl
              : @counit (C ∏ C) C (Diagonal_Product C)
                        (@product_via_couniversal_functor C _)
                        (@product_via_couniversal C _) p
                  = @proj_pair C _ p).

End CounitProbe.

(*
   本节说明 ProbeCouniversal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
