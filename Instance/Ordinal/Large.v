Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem

   本文件给出序数相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The type of small ordinals *)

(* 相关说明。 （已译） *)
Inductive SmallOrd@{u} : Type@{u+1} :=
  osup : forall (Ix : Type@{u}), (Ix -> SmallOrd) -> SmallOrd.

(* 相关说明。 （已译） *)
Definition oidx@{u} (x : SmallOrd@{u}) : Type@{u} :=
  match x return Type@{u} with osup A _ => A end.

Definition oelt@{u} (x : SmallOrd@{u}) : oidx@{u} x -> SmallOrd@{u} :=
  match x as x0 return (oidx@{u} x0 -> SmallOrd@{u}) with osup _ f => f end.

(* Both destructors compute on a constructor application. *)
Example oidx_osup@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  oidx (osup A f) = A := eq_refl.

Example oelt_osup@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  oelt (osup A f) = f := eq_refl.

(** ** The extensional order *)

(*
   本节说明 Large 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint ole@{u} (x : SmallOrd@{u}) : SmallOrd@{u} -> Prop :=
  match x with
  | osup A f =>
      fun y => match y with
               | osup B g => forall a : A, exists b : B, ole (f a) (g b)
               end
  end.

(* The destructor-shaped reading [ole]. Every 证明 below goes through
 rather than destructing ordinal, what keeps the
 induction hypotheses usable. （已译） *)
Lemma ole_unfold@{u} (x y : SmallOrd@{u}) :
  ole x y <-> (forall a : oidx x, exists b : oidx y, ole (oelt x a) (oelt y b)).
Proof. destruct x, y; simpl; split; exact (fun h => h). Qed.

Lemma ole_refl@{u} (x : SmallOrd@{u}) : ole x x.
Proof. induction x as [A f IH]; simpl; intro a; exists a; exact (IH a). Qed.

(* Each element of an ordinal precedes it; equivalently, [osup A f] is an
   upper bound of its own family [f].  It is discharged by the induction
   hypothesis alone, with no case analysis on [f a].（标题）（已译） *)
Lemma ole_elem@{u} (x : SmallOrd@{u}) (a : oidx x) : ole (oelt x a) x.
Proof.
  revert a; induction x as [A f IH]; intro a.
  apply ole_unfold; intro a0; exists a; exact (IH a a0).
Qed.

Lemma ole_trans@{u} (x y z : SmallOrd@{u}) : ole x y -> ole y z -> ole x z.
Proof.
  revert y z; induction x as [A f IH]; intros y z Hxy Hyz.
  apply ole_unfold; intro a.
  destruct (proj1 (ole_unfold _ _) Hxy a) as [b Hb].
  destruct (proj1 (ole_unfold _ _) Hyz b) as [c Hc].
  exists c; exact (IH a _ _ Hb Hc).
Qed.

(* A preorder, deliberately no more: [ole] not antisymmetric, a
 thin 范畴 needs reflexivity transitivity. （已译） *)
Definition ole_preorder@{u} : PreOrder ole@{u} :=
  {| PreOrder_Reflexive  := ole_refl@{u}
   ; PreOrder_Transitive := ole_trans@{u} |}.

(* The strict order: [x] precedes some element of [y]. *)
Definition olt@{u} (x y : SmallOrd@{u}) : Prop :=
  exists b : oidx y, ole x (oelt y b).

Lemma olt_ole@{u} (x y : SmallOrd@{u}) : olt x y -> ole x y.
Proof. intros [b Hb]; exact (ole_trans _ _ _ Hb (ole_elem y b)). Qed.

(* 相关说明。 （已译） *)
Lemma olt_irrefl@{u} (x : SmallOrd@{u}) : olt x x -> False.
Proof.
  induction x as [A f IH]; intros [a Ha].
  exact (IH a (proj1 (ole_unfold _ _) Ha a)).
Qed.

(* * ** The thin 范畴, opposite （已译） *)

(* The 对象 small ordinals -- [Type@{u+1}] -- hom-set is
 PROPOSITION [ole x y]. （已译） *)
Definition SmallOrd_Proset : Category := @Proset SmallOrd ole ole_preorder.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SmallOrd_op_Proset : Category :=
  @Proset SmallOrd (op_rel ole) (op_PreOrder ole_preorder).

(* Hom-sets subsingletons nose: hom-setoid proset
 relates any two parallel 态射 [True], holds by
 reduction. （已译） *)
Example smallord_equiv_is_True (x y : SmallOrd)
  (f g : x ~{SmallOrd_Proset}~> y) : (f ≈ g) = True := eq_refl.

Definition SmallOrd_Thin : Thin SmallOrd_Proset :=
  fun _ _ _ _ => Logic.I.

Definition SmallOrd_op_Thin : Thin SmallOrd_op_Proset :=
  fun _ _ _ _ => Logic.I.

(** ** Small suprema *)

(*
   本节说明 Large 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive osum@{u} (A : Type@{u}) (B : A -> Type@{u}) : Type@{u} :=
  opair : forall a : A, B a -> osum.

Arguments opair {A B} a b.

(*
   本节说明 Large 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ojoin@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) : SmallOrd@{u} :=
  osup (osum A (fun a => oidx (f a)))
       (fun p => match p with opair a k => oelt (f a) k end).

Lemma ojoin_ub@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) (a : A) :
  ole (f a) (ojoin A f).
Proof. apply ole_unfold; intro k; exists (opair a k); exact (ole_refl _). Qed.

Lemma ojoin_least@{u} (A : Type@{u}) (f : A -> SmallOrd@{u}) (y : SmallOrd@{u})
  (H : forall a, ole (f a) y) : ole (ojoin A f) y.
Proof.
  apply ole_unfold; intros [a k].
  exact (proj1 (ole_unfold _ _) (H a) k).
Qed.

(* The two clauses packaged as Instance/Proset/Limit.v's predicate. *)
Definition ojoin_IsLUB@{u +} (A : Type@{u}) (f : A -> SmallOrd@{u}) :
  IsLUB ole f (ojoin A f) :=
  (ojoin_ub A f, fun n Hn => ojoin_least A f n Hn).

(* 相关说明。 （已译） *)
Definition ozero@{u} : SmallOrd@{u} := osup False (fun e => match e with end).

Lemma ozero_least@{u} (x : SmallOrd@{u}) : ole ozero x.
Proof. apply ole_unfold; intros []. Qed.

(* 相关说明。 （已译） *)
Definition osucc@{u} (x : SmallOrd@{u}) : SmallOrd@{u} :=
  osup poly_unit@{u} (fun _ => x).

Lemma ole_osucc@{u} (x : SmallOrd@{u}) : ole x (osucc x).
Proof. exact (ole_elem (osucc x) ttt). Qed.

Lemma olt_osucc@{u} (x : SmallOrd@{u}) : olt x (osucc x).
Proof. exists ttt; exact (ole_refl x). Qed.

(* The successor STRICTLY above: 这是 [olt_irrefl] read at [x]. （已译） *)
Lemma osucc_not_ole@{u} (x : SmallOrd@{u}) : ole (osucc x) x -> False.
Proof. intro H; exact (olt_irrefl x (proj1 (ole_unfold _ _) H ttt)). Qed.

(* * ** Small-completeness opposite 范畴 （已译） *)

(*
   本节说明 Large 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SmallOrd_HasAllJoins : HasAllJoins ole :=
  fun A f => existT _ (ojoin A f) (ojoin_IsLUB A f).

(* Mac Lane's "Ord^op is small-完备". Every diagram whose shape
 范畴 has 对象 at ordinals' own universe -- one level BELOW
 对象 type [SmallOrd_op_Proset] -- has 极限.（已译） *)
Definition SmallOrd_op_Complete : @Complete SmallOrd_op_Proset :=
  Proset_op_Complete_of_all_joins ole_preorder SmallOrd_HasAllJoins.

(* The indexed-product reading one family, through
 Instance/Proset/Limit.v's [Proset_LUB_Limit]: limit in
 [SmallOrd^op] discrete diagram join 对象. （已译） *)
Definition SmallOrd_op_indexed_limit@{u +}
  (A : Type@{u}) (d : A -> SmallOrd@{u}) :
  Limit (DiscreteCat_Functor (C:=SmallOrd_op_Proset) d) :=
  Proset_LUB_Limit ole_preorder d (ojoin A d) (ojoin_IsLUB A d).

(* The nullary case: 终对象 [SmallOrd^op] least
 ordinal. (The INITIAL 对象 [SmallOrd^op] would greatest
 ordinal, refuted below.) （已译） *)
Definition SmallOrd_op_Terminal : @Terminal SmallOrd_op_Proset :=
  Proset_Terminal (op_PreOrder ole_preorder) ozero ozero_least.

(* 相关说明。 （已译） *)
Lemma smallord_lub_not_zero@{u +} :
  IsLUB ole@{u} (pair_family ozero@{u} (osucc@{u} ozero@{u})) ozero@{u}
  -> False.
Proof. intros [Hub _]; exact (osucc_not_ole ozero (Hub false)). Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Theorem SmallOrd_no_greatest@{u} (m : SmallOrd@{u})
  (H : forall x : SmallOrd@{u}, ole x m) : False.
Proof. exact (osucc_not_ole m (H (osucc m))). Qed.

(*
   本节说明 Large 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem SmallOrd_no_small_cofinal_family@{u}
  (A : Type@{u}) (e : A -> SmallOrd@{u})
  (H : forall x : SmallOrd@{u}, exists a : A, ole x (e a)) : False.
Proof.
  apply (SmallOrd_no_greatest (ojoin A e)); intro x.
  destruct (H x) as [a Ha].
  exact (ole_trans _ _ _ Ha (ojoin_ub A e a)).
Qed.

(* The order facts read categorically. *)
Theorem SmallOrd_no_Terminal (T : @Terminal SmallOrd_Proset) : False.
Proof.
  exact (SmallOrd_no_greatest _ (terminal_is_greatest ole_preorder T)).
Qed.

Theorem SmallOrd_op_no_Initial (Iobj : @Initial SmallOrd_op_Proset) : False.
Proof.
  exact (SmallOrd_no_greatest _
           (initial_is_least (op_PreOrder ole_preorder) Iobj)).
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem SmallOrd_op_no_self_limit
  (L : Limit (Id[SmallOrd_op_Proset])) : False.
Proof.
  destruct L as [[v legs] _].
  apply (SmallOrd_no_greatest v); intro x.
  exact (@vertex_map _ _ _ _ legs x).
Qed.

(*
   本节说明 Large 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem SmallOrd_op_not_large_complete
  (HC : @Complete SmallOrd_op_Proset) : False.
Proof. exact (SmallOrd_op_no_self_limit (HC SmallOrd_op_Proset Id)). Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SmallOrd_self_limit : Limit (Id[SmallOrd_Proset]) :=
  Proset_Limit_general ole_preorder (Id[SmallOrd_Proset]) ozero
    (ozero_least, fun n Hn => Hn ozero).
