(** * Preorders are closed under products and functor categories *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Product.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Coq.Lists.List.
Require Import Category.Instance.Two.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Fong–Spivak, "Seven Sketches in Compositionality", §1.2.2
 nLab:      https://ncatlab.org/nlab/show/thin+category

   本文件给出预序集相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Products: Mac Lane II.3 Ex. 2 *)

(*
   本节说明 Closure 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition prod_rel {A B : Type} (R : relation A) (S : relation B) :
  relation (A * B) :=
  fun p q => R (fst p) (fst q) ∧ S (snd p) (snd q).

#[export] Instance PreOrder_prod {A B : Type}
  {R : relation A} {S : relation B}
  (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) : RelationClasses.PreOrder (prod_rel R S).
Proof.
  constructor.
  - intro p; split.
    + exact (@RelationClasses.PreOrder_Reflexive _ _ P (fst p)).
    + exact (@RelationClasses.PreOrder_Reflexive _ _ Q (snd p)).
  - intros p q r [Hpq1 Hpq2] [Hqr1 Hqr2]; split.
    + exact (@RelationClasses.PreOrder_Transitive _ _ P _ _ _ Hpq1 Hqr1).
    + exact (@RelationClasses.PreOrder_Transitive _ _ Q _ _ _ Hpq2 Hqr2).
Qed.

Program Definition Proset_prod_to {A B : Type}
  {R : relation A} {S : relation B} (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) :
  Proset (PreOrder_prod P Q) ⟶ Proset P ∏ Proset Q := {|
  fobj := fun p => p;
  fmap := fun x y (h : R (fst x) (fst y) ∧ S (snd x) (snd y)) =>
    (fst h, snd h)
|}.
Next Obligation.
  intros A B R S P Q x y h h' Hh; split; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x; split; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x y z h h'; split; exact I.
Qed.

Program Definition Proset_prod_from {A B : Type}
  {R : relation A} {S : relation B} (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) :
  Proset P ∏ Proset Q ⟶ Proset (PreOrder_prod P Q) := {|
  fobj := fun p => p;
  fmap := fun x y h =>
    ((fst h, snd h)
      : R (fst x) (fst y) ∧ S (snd x) (snd y))
|}.
Next Obligation.
  intros A B R S P Q x y h h' Hh; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x y z h h'; exact I.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Proset_prod_iso {A B : Type}
  {R : relation A} {S : relation B} (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) :
  Proset (PreOrder_prod P Q) ≅[Cat] Proset P ∏ Proset Q := {|
  to   := Proset_prod_to P Q;
  from := Proset_prod_from P Q
|}.
Next Obligation.
  intros A B R S P Q; exists (fun p => iso_id).
  intros x y f; split; exact I.
Qed.
Next Obligation.
  intros A B R S P Q; exists (fun p => iso_id).
  intros x y f; exact I.
Qed.

(** ** Functor categories: Mac Lane II.4 Ex. 4, structural half *)

(* A functor category into a thin target is thin: natural
   transformations are compared pointwise, and their components are
   parallel in the target. *)
Lemma Thin_Fun {C D : Category} (TD : Thin D) : Thin (@Fun C D).
Proof.
  intros F G σ τ x.
  exact (TD _ _ _ _).
Qed.

(** ** The functor category between preorders, concretely *)

Section MonotoneOrder.

Context {A : Type} {R : relation A} (P : RelationClasses.PreOrder R).
Context {B : Type} {S : relation B} (Q : RelationClasses.PreOrder S).

(* The pointwise order on monotone maps. *)
Definition mm_le (f g : @MonotoneFun A R B S) : Prop :=
  ∀ x : A, S (mono_map f x) (mono_map g x).

#[export] Instance mm_le_PreOrder : RelationClasses.PreOrder mm_le.
Proof using Q.
  constructor.
  - intros f x.
    exact (@RelationClasses.PreOrder_Reflexive _ _ Q (mono_map f x)).
  - intros f g h Hfg Hgh x.
    exact (@RelationClasses.PreOrder_Transitive _ _ Q _ _ _ (Hfg x) (Hgh x)).
Qed.

(* The preorder of monotone maps, as a thin category. *)
Definition MonotoneProset : Category := Proset mm_le_PreOrder.

(* The dictionary, functorially: on objects it is
   Instance/Proset/Monotone.v's [monotone_of_Functor]/
   [Functor_of_monotone] pair; on morphisms, a natural transformation
   between functors of prosets is exactly a pointwise-order proof, and
   conversely (Theory/Thin.v's [thin_natural] at the thin target). *)
Program Definition Fun_Proset_to :
  @Fun (Proset P) (Proset Q) ⟶ MonotoneProset := {|
  fobj := monotone_of_Functor P Q;
  fmap := fun F G σ => fun x => transform σ x
|}.
Next Obligation.
  intros F G σ τ Hστ; exact I.
Qed.
Next Obligation.
  intros F; exact I.
Qed.
Next Obligation.
  intros F G H σ τ; exact I.
Qed.

Program Definition Fun_Proset_from :
  MonotoneProset ⟶ @Fun (Proset P) (Proset Q) := {|
  fobj := Functor_of_monotone P Q;
  fmap := fun f g h =>
    thin_natural (proset_thin Q)
      (Functor_of_monotone P Q f) (Functor_of_monotone P Q g)
      (fun x => h x)
|}.
Next Obligation.
  intros f g h h' Hh x; exact I.
Qed.
Next Obligation.
  intros f x; exact I.
Qed.
Next Obligation.
  intros f g h p q x; exact I.
Qed.

(*
   本节说明函子、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Fun_Proset_iso :
  @Fun (Proset P) (Proset Q) ≅[Cat] MonotoneProset := {|
  to   := Fun_Proset_to;
  from := Fun_Proset_from
|}.
Next Obligation.
  simpl; exists (fun f => iso_id).
  intros; exact I.
Qed.
Next Obligation.
  simpl; unshelve eexists.
  - intro F.
    unshelve refine
      (@Build_Isomorphism (@Fun (Proset P) (Proset Q))
         (Functor_of_monotone P Q (monotone_of_Functor P Q F)) F
         (thin_natural (proset_thin Q)
            (Functor_of_monotone P Q (monotone_of_Functor P Q F)) F
            (fun x => fmap[F] (@RelationClasses.PreOrder_Reflexive _ _ P x)))
         (thin_natural (proset_thin Q) F
            (Functor_of_monotone P Q (monotone_of_Functor P Q F))
            (fun x => fmap[F] (@RelationClasses.PreOrder_Reflexive _ _ P x)))
         _ _).
    + simpl; intros; exact I.
    + simpl; intros; exact I.
  - simpl; intros; exact I.
Qed.

End MonotoneOrder.

(** ** Seven Sketches §1.2.2: the worked product Roof ∏ 2 *)

(*
   本节说明 Closure 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition roof_two_hom_dec :
  ∀ x y : Roof ∏ _2, (x ~> y) + ((x ~> y) → False).
Proof.
  intros [r1 t1] [r2 t2].
  destruct r1, r2, t1, t2;
  first
    [ solve [ left; split; constructor ]
    | solve [ right; intros [f g]; inversion f ]
    | solve [ right; intros [f g]; inversion g ] ].
Defined.

(* Sanity: the decider is exercised at one related and one unrelated
   pair — the apex reaches the right foot, and nothing climbs back up
   the V. *)
Example roof_two_related :
  ((RZero, TwoX) : Roof ∏ _2) ~> (RPos, TwoY).
Proof.
  exact (ZeroPos, TwoXY).
Qed.

Example roof_two_unrelated :
  (((RPos, TwoX) : Roof ∏ _2) ~> (RNeg, TwoX)) → False.
Proof.
  intros [f g]; inversion f.
Qed.

(* The counts, made load-bearing: the decider is transparent, so the
   fifteen/twenty-one split computes. *)
Definition roof_two_objs : list (Roof ∏ _2) :=
  ((RNeg, TwoX) :: (RNeg, TwoY) :: (RZero, TwoX) :: (RZero, TwoY)
     :: (RPos, TwoX) :: (RPos, TwoY) :: nil)%list.

Definition roof_two_related_count : nat :=
  length
    (filter
       (fun p =>
          match roof_two_hom_dec (fst p) (snd p) with
          | inl _ => true
          | inr _ => false
          end)
       (list_prod roof_two_objs roof_two_objs)).

Example roof_two_fifteen : roof_two_related_count = 15%nat := eq_refl.

Example roof_two_twenty_one :
  (length (list_prod roof_two_objs roof_two_objs)
     - roof_two_related_count)%nat = 21%nat := eq_refl.
