Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/well-pointed+category

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The singleton separates *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition sets_elem@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> X := {| morphism := fun _ => x |}.

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Sets_unit_separates@{o so+} :
  @IsSeparator Sets@{o so} unit_setoid_object@{o o}.
Proof.
  intros X Y f g H x.
  exact (H (sets_elem x) ttt).
Qed.

(* Mac Lane's first example, as the one-object generating family. *)
Definition Sets_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so} unit_setoid_object@{o o}
    Sets_unit_separates.

(** ** The terminal object separates *)

(* The same 常值 map, but out [Sets_Terminal]'s 对象 rather than
 out [unit_setoid_object]. It has built separately: two
 对象 do not convert, header measures. （已译） *)
Program Definition sets_elem_term@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  @terminal_obj Sets@{o so} Sets_Terminal@{so o} ~{Sets@{o so}}~> X :=
  {| morphism := fun _ => x |}.

(* Route 1, delivered 常值: direct 证明. This issue
 #447's pinned name. （已译） *)
Lemma Sets_terminal_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  intros X Y f g H x.
  exact (H (sets_elem_term x) ttt).
Qed.

Definition Sets_terminal_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    Sets_terminal_separates.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_terminal_unit_iso@{o so+} :
  @Isomorphism Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    unit_setoid_object@{o o}.
Proof.
  unshelve refine {| to := _; from := _ |}.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - intro u; now destruct u.
  - intro u; now destruct u.
Defined.

(* Route 2: transport along 同构, direction
 [unit_setoid_object ≅ terminal_obj], through Structure/Generator.v's
 [separator_iso]. （已译） *)
Definition Sets_terminal_separates_by_transport@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  separator_iso Sets_unit_separates (iso_sym Sets_terminal_unit_iso).

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_terminal_separates_from_Concrete@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  IsSeparator_of_Separator
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) Sets_Separator@{o so}.

(* * ** The 始对象 does not separate （已译） *)

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Sets_empty_not_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj (Sets@{o so}^op) Sets_Initial@{so o}) → False.
Proof.
  intro Hsep.
  apply Sets_two_arrows@{o so}.
  apply Hsep.
  intros k u; destruct u.
Qed.

(* The same 定理 route issue #447 named, pinned at 对象
 universe [Set] donors, header attributes. （已译） *)
Lemma Sets_empty_not_separates_pick@{so+} :
  @IsSeparator Sets@{Set so}
    (@terminal_obj (Sets@{Set so}^op) Sets_Initial@{so Set}) → False.
Proof.
  intro Hsep.
  apply Bool.diff_true_false.
  refine (Hsep unit_setoid_object@{Set Set} _ pick_true pick_false _ ttt).
  intros k u; destruct u.
Qed.
