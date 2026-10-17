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

(** * The large thin preorder of small ordinals *)

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+functor+theorem

   本文件给出序数相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The type of small ordinals *)

(* An ordinal is a [Type@{u}]-indexed family of ordinals.  The result lives
   at [Type@{u+1}], one level above the types that may index it: that gap
   is the whole subject of this file. *)
Inductive SmallOrd@{u} : Type@{u+1} :=
  osup : forall (Ix : Type@{u}), (Ix -> SmallOrd) -> SmallOrd.

(* The index type of an ordinal, and its indexed family of elements.  The
   index binder is written [A] and never [I]: see the trap recorded in the
   header. *)
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

(* [x <= y] when every element of [x] is dominated by some element of [y].
   The recursion is structural in the FIRST argument alone -- the inner
   [match] on [y] is a case analysis, not a recursive call -- which is what
   keeps the definition inside Coq's guard condition without a mutual
   fixpoint. *)
Fixpoint ole@{u} (x : SmallOrd@{u}) : SmallOrd@{u} -> Prop :=
  match x with
  | osup A f =>
      fun y => match y with
               | osup B g => forall a : A, exists b : B, ole (f a) (g b)
               end
  end.

(* The destructor-shaped reading of [ole].  Every proof below goes through
   this rather than destructing an ordinal, which is what keeps the
   induction hypotheses usable. *)
Lemma ole_unfold@{u} (x y : SmallOrd@{u}) :
  ole x y <-> (forall a : oidx x, exists b : oidx y, ole (oelt x a) (oelt y b)).
Proof. destruct x, y; simpl; split; exact (fun h => h). Qed.

Lemma ole_refl@{u} (x : SmallOrd@{u}) : ole x x.
Proof. induction x as [A f IH]; simpl; intro a; exists a; exact (IH a). Qed.

(* Each element of an ordinal precedes it; equivalently, [osup A f] is an
   upper bound of its own family [f].  It is discharged by the induction
   hypothesis alone, with no case analysis on [f a]. *)
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

(* A preorder, and deliberately no more: [ole] is not antisymmetric, and a
   thin category needs only reflexivity and transitivity. *)
Definition ole_preorder@{u} : PreOrder ole@{u} :=
  {| PreOrder_Reflexive  := ole_refl@{u}
   ; PreOrder_Transitive := ole_trans@{u} |}.

(* The strict order: [x] precedes some element of [y]. *)
Definition olt@{u} (x y : SmallOrd@{u}) : Prop :=
  exists b : oidx y, ole x (oelt y b).

Lemma olt_ole@{u} (x y : SmallOrd@{u}) : olt x y -> ole x y.
Proof. intros [b Hb]; exact (ole_trans _ _ _ Hb (ole_elem y b)). Qed.

(* No ordinal precedes one of its own elements.  This is the only genuinely
   inductive negative fact in the file, and everything that says "there is
   no top" reduces to it. *)
Lemma olt_irrefl@{u} (x : SmallOrd@{u}) : olt x x -> False.
Proof.
  induction x as [A f IH]; intros [a Ha].
  exact (IH a (proj1 (ole_unfold _ _) Ha a)).
Qed.

(** ** The thin category, and its opposite *)

(* The objects are the small ordinals -- a [Type@{u+1}] -- and a hom-set is
   the PROPOSITION [ole x y]. *)
Definition SmallOrd_Proset : Category := @Proset SmallOrd ole ole_preorder.

(* Mac Lane's [Ord^op], built as the proset of the reversed preorder rather
   than as [SmallOrd_Proset^op].  The two are not convertible: they agree at
   [obj], [hom], [id], [compose] and the hom-setoid's [equiv], and diverge at
   [setoid_equiv], which is a [Qed]-opaque [Program] obligation of
   Instance/Proset.v applied to two different preorders (located, not
   guessed; the measurement is in the header).  Every theorem of
   Instance/Proset/Limit.v is stated over an arbitrary [PreOrder], so
   nothing is lost by building the reversed one directly. *)
Definition SmallOrd_op_Proset : Category :=
  @Proset SmallOrd (op_rel ole) (op_PreOrder ole_preorder).

(* Hom-sets are subsingletons on the nose: the hom-setoid of a proset
   relates any two parallel morphisms by [True], and that holds by
   reduction. *)
Example smallord_equiv_is_True (x y : SmallOrd)
  (f g : x ~{SmallOrd_Proset}~> y) : (f ≈ g) = True := eq_refl.

Definition SmallOrd_Thin : Thin SmallOrd_Proset :=
  fun _ _ _ _ => Logic.I.

Definition SmallOrd_op_Thin : Thin SmallOrd_op_Proset :=
  fun _ _ _ _ => Logic.I.

(** ** Small suprema *)

(* The index type of a join: the disjoint union, over [a : A], of the index
   types of the [f a].  It is declared here rather than taken from [sigT]
   so that both components are held at [Type@{u}] by DECLARATION; that is
   what keeps [ojoin] a small ordinal rather than making its smallness
   depend on how [sigT]'s levels happen to be inferred. *)
Inductive osum@{u} (A : Type@{u}) (B : A -> Type@{u}) : Type@{u} :=
  opair : forall a : A, B a -> osum.

Arguments opair {A B} a b.

(* The supremum of a SMALL family of ordinals.  Note that [osup A f] is not
   itself that supremum -- it is the supremum of the successors of the
   [f a] -- so the construction flattens one level. *)
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

(* The least ordinal: the empty family.  [False] serves as the empty index
   type at every level, by cumulativity, so no [Set]-level empty type is
   pinned here. *)
Definition ozero@{u} : SmallOrd@{u} := osup False (fun e => match e with end).

Lemma ozero_least@{u} (x : SmallOrd@{u}) : ole ozero x.
Proof. apply ole_unfold; intros []. Qed.

(* The successor: a one-element family.  [poly_unit] is the library's
   universe-polymorphic unit (Lib/Setoid.v); [unit] would pin the index
   type to [Set]. *)
Definition osucc@{u} (x : SmallOrd@{u}) : SmallOrd@{u} :=
  osup poly_unit@{u} (fun _ => x).

Lemma ole_osucc@{u} (x : SmallOrd@{u}) : ole x (osucc x).
Proof. exact (ole_elem (osucc x) ttt). Qed.

Lemma olt_osucc@{u} (x : SmallOrd@{u}) : olt x (osucc x).
Proof. exists ttt; exact (ole_refl x). Qed.

(* The successor is STRICTLY above: this is [olt_irrefl] read at [x]. *)
Lemma osucc_not_ole@{u} (x : SmallOrd@{u}) : ole (osucc x) x -> False.
Proof. intro H; exact (olt_irrefl x (proj1 (ole_unfold _ _) H ttt)). Qed.

(** ** Small-completeness of the opposite category *)

(* Every [Type@{u}]-indexed family of ordinals has a join.  The index
   universe of [HasAllJoins] is the ordinals' OWN universe here, which is
   what turns the next definition into a small-completeness statement; the
   measured instance is quoted in the header. *)
Definition SmallOrd_HasAllJoins : HasAllJoins ole :=
  fun A f => existT _ (ojoin A f) (ojoin_IsLUB A f).

(* Mac Lane's "Ord^op is small-complete".  Every diagram whose shape
   category has objects at the ordinals' own universe -- one level BELOW
   the object type of [SmallOrd_op_Proset] -- has a limit. *)
Definition SmallOrd_op_Complete : @Complete SmallOrd_op_Proset :=
  Proset_op_Complete_of_all_joins ole_preorder SmallOrd_HasAllJoins.

(* The indexed-product reading of one family, through
   Instance/Proset/Limit.v's [Proset_LUB_Limit]: the limit in
   [SmallOrd^op] of a discrete diagram is the join of its objects. *)
Definition SmallOrd_op_indexed_limit@{u +}
  (A : Type@{u}) (d : A -> SmallOrd@{u}) :
  Limit (DiscreteCat_Functor (C:=SmallOrd_op_Proset) d) :=
  Proset_LUB_Limit ole_preorder d (ojoin A d) (ojoin_IsLUB A d).

(* The nullary case: the terminal object of [SmallOrd^op] is the least
   ordinal.  (The INITIAL object of [SmallOrd^op] would be a greatest
   ordinal, and is refuted below.) *)
Definition SmallOrd_op_Terminal : @Terminal SmallOrd_op_Proset :=
  Proset_Terminal (op_PreOrder ole_preorder) ozero ozero_least.

(* Non-vacuity, in the sense of Instance/Proset/Limit.v's
   [nat_glb_not_4]: [IsLUB] is refutable here, so the positive statements
   above are not statements about a uniformly inhabited type.  Zero is not
   a join of {zero, zero+1}. *)
Lemma smallord_lub_not_zero@{u +} :
  IsLUB ole@{u} (pair_family ozero@{u} (osucc@{u} ozero@{u})) ozero@{u}
  -> False.
Proof. intros [Hub _]; exact (osucc_not_ole ozero (Hub false)). Qed.

(** ** No greatest ordinal, and where the universe gap does the work *)

(* There is no greatest small ordinal: the successor of a candidate would
   have to precede it, and [olt_irrefl] refutes that. *)
Theorem SmallOrd_no_greatest@{u} (m : SmallOrd@{u})
  (H : forall x : SmallOrd@{u}, ole x m) : False.
Proof. exact (osucc_not_ole m (H (osucc m))). Qed.

(* THE UNIVERSE ARGUMENT, STATED.  [SmallOrd@{u}] has no cofinal family
   indexed by a [Type@{u}]: if it had one, [ojoin] would turn it into a
   greatest element.  So the supremum construction of the previous section,
   which accepts every [Type@{u}]-indexed family, cannot be applied to the
   class of ALL ordinals -- not because the construction is partial, but
   because [SmallOrd@{u} : Type@{u+1}] is not a [Type@{u}] and no
   [Type@{u}] is cofinal in it.  This is the precise sense in which
   small-completeness and the absence of a top are compatible. *)
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

(* The identity diagram on [SmallOrd^op] has no limit: a cone over it has a
   leg to every object, and in the reversed order that leg family IS the
   statement that the apex is a greatest ordinal.  Only the CONE is used,
   not the universal property. *)
Theorem SmallOrd_op_no_self_limit
  (L : Limit (Id[SmallOrd_op_Proset])) : False.
Proof.
  destruct L as [[v legs] _].
  apply (SmallOrd_no_greatest v); intro x.
  exact (@vertex_map _ _ _ _ legs x).
Qed.

(* Hence [Complete] is refuted when its DIAGRAM shape is allowed to range
   over the category's own object universe -- while
   [SmallOrd_op_Complete] inhabits [Complete] with the diagram shape one
   universe below.  Same constant, two instances; the printed instances are
   quoted in the header's UNIVERSES paragraph, and they are the sharp form
   of Mac Lane's remark that the size discipline is doing real work. *)
Theorem SmallOrd_op_not_large_complete
  (HC : @Complete SmallOrd_op_Proset) : False.
Proof. exact (SmallOrd_op_no_self_limit (HC SmallOrd_op_Proset Id)). Qed.

(** ** The control that keeps the previous theorem from being a triviality

    [SmallOrd_op_not_large_complete] refutes [Complete] at the diagonal
    instance, and a reader is entitled to ask whether that instance is
    uninhabitable for every category, in which case the refutation would say
    nothing about the ordinals.  It is not.  The SAME diagonal shape is
    inhabited in the UNREVERSED order, where [ozero] is a greatest lower
    bound of the identity diagram because it is least:

      About SmallOrd_self_limit  ->  Limit@{u u1 u0 u1} Id[SmallOrd_Proset]

    slots 2 and 4 both [u1], which is the pairing
    [SmallOrd_op_no_self_limit] refutes on the other side.  So the
    refutation is about the absence of a GREATEST ordinal, not about the
    universe pairing being unusable, and that is exactly the content
    Mac Lane's remark needs. *)

Definition SmallOrd_self_limit : Limit (Id[SmallOrd_Proset]) :=
  Proset_Limit_general ole_preorder (Id[SmallOrd_Proset]) ozero
    (ozero_least, fun n Hn => Hn ozero).
