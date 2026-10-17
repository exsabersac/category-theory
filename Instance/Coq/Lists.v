Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Coq.
Require Import List.

Generalizable All Variables.

(* * * Lists initial algebra list 自函子 over COQ （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   本文件给出 Coq 类型相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(* The list endofunctor [ListF A X = option (A * X) = 1 + A × X]. *)
Program Definition ListF (A : Type) : Coq ⟶ Coq := {|
  fobj := fun X => option (A * X)%type;
  fmap := fun X Y (f : X -> Y) o =>
            match o with
            | None => None
            | Some (a, x) => Some (a, f x)
            end
|}.
Next Obligation.
  (* fmap respects pointwise equality *)
  intros A X Y f g Hfg o.
  destruct o as [[a x]|].
  - simpl; rewrite (Hfg x); reflexivity.
  - reflexivity.
Qed.
Next Obligation.
  (* fmap preserves identities *)
  intros A X o.
  destruct o as [[a x]|]; reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition *)
  intros A X Y Z f g o.
  destruct o as [[a x]|]; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition alg (A : Type) : ListF A (list A) ~{Coq}~> list A :=
  fun o => match o with
           | None => @nil A
           | Some (a, l) => cons a l
           end.

(* 相关说明。 （已译） *)
Fixpoint fold {A Y : Type} (beta : option (A * Y)%type -> Y)
              (l : list A) : Y :=
  match l with
  | nil => beta None
  | cons a l' => beta (Some (a, fold beta l'))
  end.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_is_fold {A Y : Type} (beta : option (A * Y)%type -> Y)
      (h : list A -> Y)
      (Hh : forall o, h (alg A o) = beta (fmap[ListF A] h o))
      (l : list A) : h l = fold beta l.
Proof.
  induction l as [|a l' IH].
  - apply (Hh None).
  - simpl.
    rewrite <- IH.
    apply (Hh (Some (a, l'))).
Qed.

(* The unique algebra map [(list A, alg A)] arbitrary algebra [y],
 packaging fold together 交换方块. （已译） *)
Program Definition list_alg_hom (A : Type) (y : FAlg (ListF A))
  : (list A; alg A) ~{FAlg (ListF A)}~> y :=
  {| falg_hom := fold (`2 y) |}.
Next Obligation.
  (* fold ∘ alg ≈ β ∘ fmap fold, checked shape by shape *)
  intros A y o.
  destruct o as [[a l]|]; reflexivity.
Qed.

(* [list A] together [alg A] initial [ListF A]-algebra: it the
 终对象 opposite algebra 范畴. （已译） *)
Program Definition list_initial (A : Type) : @Initial (FAlg (ListF A)) := {|
  terminal_obj := (list A; alg A);
  one := fun y => list_alg_hom A y
|}.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros A x f g.
  destruct f as [hf Hf], g as [hg Hg].
  intro l; simpl.
  rewrite (hom_is_fold (`2 x) hf Hf l).
  rewrite (hom_is_fold (`2 x) hg Hg l).
  reflexivity.
Qed.
