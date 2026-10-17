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

(** ** (1) The covariant reading is definitional

    Positive controls.  [coarrow] has the covariant type, and IS the
    op-side [arrow] — the same term, not a transported one. *)

Check (coarrow U : F (coarrow_obj U) ~{C}~> c).

Check (eq_refl : coarrow U = @arrow (C^op) (D^op) c (Opposite_Functor F) U).

Check (eq_refl : coarrow_obj U
                   = @arrow_obj (C^op) (D^op) c (Opposite_Functor F) U).

(** The couniversal mapping property likewise: its statement mentions no
    [op], and it is the primal statement's own term. *)

Check (fun (d : D) (h : F d ~{C}~> c) =>
         eq_refl : @ump_couniversal_arrows C D c F U d h
                     = @ump_universal_arrows (C^op) (D^op) c
                         (Opposite_Functor F) U d h).

(** ** (2) The terminal-object reading is a theorem

    Positive control: the construction, and the fact that it chooses the
    couniversal object on the nose. *)

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

(** Nor are the two comma categories themselves Leibniz-equal — the
    reason for the mismatch, isolated.  (Stripped: cannot unify.) *)
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

(** ...and it is not closed by Construction/Comma.v's [Cocomma] either,
    which the issue proposed as the route.  Positive control first: the
    cocomma of the same two functors exists. *)
Check (@Cocomma D _1 C F (@Diagonal C _1 c) : Category).

(** Negative: it is not the comma the op-side [arrow_initial] inhabits.
    (Stripped: cannot unify [@Initial (=(c) ↓ F^op)] with
    [@Initial (F ↑ =(c))].) *)
Fail Check (@arrow_initial (C^op) (D^op) c (Opposite_Functor F) U
              : @Initial (@Cocomma D _1 C F (@Diagonal C _1 c))).

(** Negative: nor is it the opposite of F ↓ =(c) on the nose.
    (Stripped: cannot unify [F ↑ =(c)] with [(F ↓ =(c))^op].) *)
Fail Check (eq_refl : @Cocomma D _1 C F (@Diagonal C _1 c)
                        = (@Comma D _1 C F (@Diagonal C _1 c))^op).

(** ** (3) The dual is not the primal

    Positive control: both types exist, at the same arguments. *)
Check (CouniversalArrow c F : Type).
Check (UniversalArrow c F : Type).

(** Negative: and they are different.  (Stripped: cannot unify
    [CouniversalArrow c F] with [UniversalArrow c F].) *)
Fail Check (eq_refl : CouniversalArrow c F = UniversalArrow c F).

End Probes.

(** ** (4) The counit agrees only up to [≈]

    Measured at the worked example, so the probe is about a real
    adjunction and not a variable. *)

Section CounitProbe.

Context `{C : Category}.
Context `{@Cartesian C}.
Context (p : C ∏ C).

(** Positive controls: the object action of the assembled right adjoint
    reduces to the product on the nose, and the counit IS the projection
    pair up to [≈]. *)
Check (eq_refl : fobj[@product_via_couniversal_functor C _] p
                   = (fst p × snd p)).
Check (@product_via_couniversal_counit C _ p).

(** Negative: that agreement is not an [eq_refl].  (Stripped: cannot
    unify the [counit] with [proj_pair p].) *)
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
