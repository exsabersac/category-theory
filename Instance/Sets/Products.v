Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

Import EqNotations.

(** * Small products and coproducts in [Sets] *)

(*
 nLab:      https://ncatlab.org/nlab/show/coproduct
 nLab:      https://ncatlab.org/nlab/show/complete+category
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The default obligation tactic is switched off for this file, as
   Instance/Sets/End.v does: where [Program] raises an obligation it is
   discharged by an explicit script below rather than by the library's [cat] /
   [cat_simpl] automation, and no script below invokes a proof-search tactic:
   none of them calls [auto], [eauto], [intuition], [firstorder] or [tauto].
   A few scripts do use the tacticals [now] (at the obligations of
   [Sets_iprod_tuple], [Sets_icoprod_obj] and [Sets_icoprod_case]) and
   [first [...]] (in the two singleton pigeonhole lemmas), which sequence and
   choose among explicit steps rather than search.  Note also that some
   [proper_morphism] fields never become obligations at all -- instance
   resolution closes them during elaboration -- which is why several tactic
   scripts further down use an [all:] selector, a no-op when no goal is
   left. *)
#[local] Obligation Tactic := idtac.

(** ** Indexed products: the dependent-function setoid *)

Definition Sets_iprod_equiv {A : Type} (F : A → SetoidObject) :
  crelation (∀ i : A, F i) :=
  fun g h => ∀ i : A, g i ≈ h i.

Program Definition Sets_iprod_obj {A : Type}
  (F : A → SetoidObject) : SetoidObject := {|
  carrier   := ∀ i : A, F i;
  is_setoid := {| equiv := Sets_iprod_equiv F |}
|}.
Next Obligation.
  intros A F.
  constructor.
  - intros g i; reflexivity.
  - intros g h Hgh i; symmetry; exact (Hgh i).
  - intros g h k Hgh Hhk i; transitivity (h i); [exact (Hgh i)|exact (Hhk i)].
Qed.

Program Definition Sets_iprod_proj {A : Type}
  (F : A → SetoidObject) (i : A) : Sets_iprod_obj F ~{Sets}~> F i := {|
  morphism := fun g => g i
|}.
Next Obligation. intros A F i g h Hgh; exact (Hgh i). Qed.

Program Definition Sets_iprod_tuple {A : Type}
  (F : A → SetoidObject) (c : SetoidObject)
  (pi : ∀ i : A, c ~{Sets}~> F i) : c ~{Sets}~> Sets_iprod_obj F := {|
  morphism := fun x i => pi i x
|}.
Next Obligation. intros A F c pi x y Hxy i; now rewrite Hxy. Qed.

Program Definition Sets_iprod_ump {A : Type} (F : A → SetoidObject)
  (c : SetoidObject) (pi : ∀ i : A, c ~{Sets}~> F i) :
  ∃! u : c ~{Sets}~> Sets_iprod_obj F,
    ∀ i : A, Sets_iprod_proj F i ∘ u ≈ pi i := {|
  unique_obj := Sets_iprod_tuple F c pi
|}.
Next Obligation. intros A F c pi i x; reflexivity. Qed.
Next Obligation. intros A F c pi v Hv x i; symmetry; exact (Hv i x). Qed.

Definition Sets_IsIndexedProduct {A : Type}
  (F : A → obj[Sets]) :
  IsIndexedProduct F (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  @Build_IsIndexedProduct Sets A F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (fun c pi => Sets_iprod_ump F c pi).

#[export]
Instance Sets_HasIndexedProducts : @HasIndexedProducts Sets :=
  @Build_HasIndexedProducts Sets
    (@Sets_iprod_obj) (@Sets_iprod_proj) (@Sets_IsIndexedProduct).

(** ** The endomorphism-indexed product

    The index that Theory/WeaklyInitial.v declines to draw from a class,
    because for a general category it need not sit where the class puts the
    index: the endomorphisms of an object.  At [Sets] it does sit there.  The
    two constants below are the whole of the observation -- their existence,
    and the universe context they elaborate at, ARE the content, so both are
    stated as instances of what [Sets_HasIndexedProducts] already supplies
    rather than reproved.  See the header for what this does and does not say
    about the general note. *)

Definition Sets_endo_iprod (P : obj[Sets]) : obj[Sets] :=
  indexed_product (fun _ : P ~{Sets}~> P => P).

Definition Sets_endo_iprod_ump (P : obj[Sets]) :
  IsIndexedProduct (fun _ : P ~{Sets}~> P => P) (Sets_endo_iprod P)
                   (indexed_product_proj (fun _ : P ~{Sets}~> P => P)) :=
  indexed_product_ump (fun _ : P ~{Sets}~> P => P).

(** ** Indexed coproducts: the sigma setoid *)

Definition Sets_icoprod_carrier {A : Type}
  (F : A → SetoidObject) : Type := { i : A & F i }.

Definition Sets_icoprod_equiv {A : Type} (F : A → SetoidObject) :
  crelation (Sets_icoprod_carrier F) :=
  fun p q =>
    { e : projT1 p = projT1 q
    & rew [fun i : A => carrier (F i)] e in projT2 p ≈ projT2 q }.

Program Definition Sets_icoprod_obj {A : Type}
  (F : A → SetoidObject) : SetoidObject := {|
  carrier   := Sets_icoprod_carrier F;
  is_setoid := {| equiv := Sets_icoprod_equiv F |}
|}.
Next Obligation.
  intros A F.
  constructor.
  - intros [i x]; exists eq_refl; reflexivity.
  - intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
    exists eq_refl; simpl; now symmetry.
  - intros [i x] [j y] [k z] [e Hxy] [e' Hyz]; simpl in *.
    destruct e; destruct e'; simpl in *.
    exists eq_refl; simpl; now transitivity y.
Qed.

Program Definition Sets_icoprod_inj {A : Type}
  (F : A → SetoidObject) (i : A) : F i ~{Sets}~> Sets_icoprod_obj F := {|
  morphism := fun x => existT _ i x
|}.
Next Obligation. intros A F i x y Hxy; exists eq_refl; exact Hxy. Qed.

Program Definition Sets_icoprod_case {A : Type}
  (F : A → SetoidObject) (c : SetoidObject)
  (iota : ∀ i : A, F i ~{Sets}~> c) : Sets_icoprod_obj F ~{Sets}~> c := {|
  morphism := fun p => iota (projT1 p) (projT2 p)
|}.
Next Obligation.
  intros A F c iota [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
  now rewrite Hxy.
Qed.

Program Definition Sets_icoprod_ump {A : Type} (F : A → SetoidObject)
  (c : SetoidObject) (iota : ∀ i : A, F i ~{Sets}~> c) :
  ∃! u : Sets_icoprod_obj F ~{Sets}~> c,
    ∀ i : A, u ∘ Sets_icoprod_inj F i ≈ iota i := {|
  unique_obj := Sets_icoprod_case F c iota
|}.
Next Obligation. intros A F c iota i x; reflexivity. Qed.
Next Obligation.
  intros A F c iota v Hv [i x]; simpl; symmetry; exact (Hv i x).
Qed.

Definition Sets_IsIndexedCoproduct {A : Type}
  (F : A → obj[Sets]) :
  IsIndexedCoproduct F (Sets_icoprod_obj F) (Sets_icoprod_inj F) :=
  @Build_IsIndexedCoproduct Sets A F
    (Sets_icoprod_obj F) (Sets_icoprod_inj F)
    (fun c iota => Sets_icoprod_ump F c iota).

#[export]
Instance Sets_HasIndexedCoproducts : @HasIndexedCoproducts Sets :=
  @Build_HasIndexedCoproducts Sets
    (@Sets_icoprod_obj) (@Sets_icoprod_inj)
    (@Sets_IsIndexedCoproduct).

(** ** Awodey 2.9 Exercise 7(b): the function set as a constant-family product *)

Definition Sets_discrete (I : Type) : obj[Sets] :=
  {| carrier := I; is_setoid := eq_Setoid I |}.

(* The exponential X^I of Instance/Sets/Cartesian/Closed.v, taken at the
   discrete setoid on the index type I.  Written as a definition rather than
   inline so that the ambient category is pinned to [Sets] for elaboration. *)
Definition Sets_pow (I : Type) (X : obj[Sets]) : obj[Sets] :=
  (X ^ Sets_discrete I)%object.

Program Definition Sets_exponent_eval (I : Type) (X : obj[Sets]) (i : I) :
  Sets_pow I X ~{Sets}~> X := {|
  morphism := fun f => f i
|}.
Next Obligation. intros I X i f g Hfg; exact (Hfg i). Qed.

(* The element of X^I named by a family [pi] at a point [x].  Built with
   [unshelve refine] rather than [Program] so that the [proper_morphism]
   certificate is supplied by hand.  This is not a matter of taste: with the
   [Program] form, instance resolution closes that field during elaboration
   -- the definition raises no obligation at all -- and the constant comes out
   pinned to [Set]:

     ∀ (I : Type@{u}) (X c : obj[Sets@{Set u0}]), ...
       (* with  Set < u0  and  Set = u *)

   The index universe [u] is [Set] by a universe EQUALITY, not merely bounded
   by it, and the ambient [Sets] is pinned along with it.  The [unshelve
   refine] form below instead prints
   [∀ (I : Type@{u}) (X c : obj[Sets@{u u0}])] with only [u < u0].  (Observed
   while writing this file; the mechanism behind the pinning was not
   investigated.) *)
Definition Sets_exponent_elt (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) (x : c) : Sets_discrete I ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun i => pi i x |}.
  intros i j Hij; destruct Hij; reflexivity.
Defined.

Program Definition Sets_exponent_tuple (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) : c ~{Sets}~> Sets_pow I X := {|
  morphism := Sets_exponent_elt I X c pi
|}.
Next Obligation.
  intros I X c pi x y Hxy i; exact (proper_morphism (pi i) x y Hxy).
Qed.

Program Definition Sets_exponent_ump (I : Type) (X c : obj[Sets])
  (pi : ∀ i : I, c ~{Sets}~> X) :
  ∃! u : c ~{Sets}~> Sets_pow I X,
    ∀ i : I, Sets_exponent_eval I X i ∘ u ≈ pi i := {|
  unique_obj := Sets_exponent_tuple I X c pi
|}.
Next Obligation. intros I X c pi i x; reflexivity. Qed.
Next Obligation. intros I X c pi v Hv x i; symmetry; exact (Hv i x). Qed.

Definition Sets_exponent_IsIndexedProduct (I : Type) (X : obj[Sets]) :
  IsIndexedProduct (fun _ : I => X) (Sets_pow I X)
                   (Sets_exponent_eval I X) :=
  @Build_IsIndexedProduct Sets I (fun _ : I => X) (Sets_pow I X)
    (Sets_exponent_eval I X) (fun c pi => Sets_exponent_ump I X c pi).

(* Each isomorphism below is assembled from two named setoid maps rather than
   through [Program] at the isomorphism itself: the isomorphism is a [refine]
   over two concrete morphisms, leaving exactly the two inverse laws.

   The maps themselves are built two ways.  Most are [unshelve refine], with
   the [proper_morphism] certificate discharged under an [all:] selector: for
   some of them instance resolution already closes that goal during
   elaboration, and [all:] is a no-op when no goal remains, so the script does
   not depend on which of the two happens.  The exception is the pair making
   up [Sets_constant_iprod_exponent] -- [Sets_exponent_tuple] above and
   [Sets_exponent_untuple] just below -- both of which are [Program].  For
   [Sets_exponent_untuple], whose SOURCE is the exponential [Sets_pow I X],
   this was measured: refining a record literal against a goal whose type has
   to be unfolded through [Sets_Closed] did not return within sixty seconds,
   where the [Program] form elaborates in well under a second.
   [Sets_exponent_tuple] was written as [Program] from the start and no such
   measurement was taken for it. *)
Program Definition Sets_exponent_untuple (I : Type) (X : obj[Sets]) :
  Sets_pow I X ~{Sets}~> indexed_product (fun _ : I => X) := {|
  morphism := fun f => fun i => f i
|}.
Next Obligation. intros I X f g Hfg i; exact (Hfg i). Qed.

Definition Sets_constant_iprod_exponent (I : Type) (X : obj[Sets]) :
  indexed_product (fun _ : I => X) ≅[Sets] Sets_pow I X.
Proof.
  refine {| to := Sets_exponent_tuple I X (indexed_product (fun _ : I => X))
                    (fun i => Sets_iprod_proj (fun _ : I => X) i)
          ; from := Sets_exponent_untuple I X |}.
  - intros f i; reflexivity.
  - intros g i; reflexivity.
Defined.

(** ** Degenerate indices

    An indexed product over an empty index is the terminal object, and one
    over a singleton index is the family's only member; dually for
    coproducts.  Neither exercises the construction.  They are recorded here
    so that the contrast drawn with the non-degenerate cases of the next
    section is proved rather than asserted. *)

Definition Sets_iprod_empty_to (F : False → obj[Sets]) :
  indexed_product F ~{Sets}~> 1%object.
Proof.
  unshelve refine {| morphism := fun _ => ttt |}.
  all: intros g h Hgh; reflexivity.
Defined.

Definition Sets_iprod_empty_from (F : False → obj[Sets]) :
  1%object ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun _ => fun i : False => match i with end |}.
  all: intros x y Hxy i; destruct i.
Defined.

Definition Sets_iprod_empty (F : False → obj[Sets]) :
  indexed_product F ≅[Sets] 1%object.
Proof.
  refine {| to := Sets_iprod_empty_to F; from := Sets_iprod_empty_from F |}.
  - intros u; destruct u; reflexivity.
  - intros g i; destruct i.
Defined.

Definition Sets_iprod_unit_to (F : poly_unit → obj[Sets]) :
  indexed_product F ~{Sets}~> F ttt.
Proof.
  unshelve refine {| morphism := fun g => g ttt |}.
  all: intros g h Hgh; exact (Hgh ttt).
Defined.

Definition Sets_iprod_unit_from (F : poly_unit → obj[Sets]) :
  F ttt ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun x =>
      fun i => match i return carrier (F i) with ttt => x end |}.
  all: intros x y Hxy i; destruct i; exact Hxy.
Defined.

Definition Sets_iprod_unit (F : poly_unit → obj[Sets]) :
  indexed_product F ≅[Sets] F ttt.
Proof.
  refine {| to := Sets_iprod_unit_to F; from := Sets_iprod_unit_from F |}.
  - intros x; reflexivity.
  - intros g i; destruct i; reflexivity.
Defined.

Definition Sets_icoprod_empty_to (F : False → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> 0%object.
Proof.
  unshelve refine {| morphism := fun p => projT1 p |}.
  all: intros [i x]; destruct i.
Defined.

Definition Sets_icoprod_empty_from (F : False → obj[Sets]) :
  0%object ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun x : False => match x with end |}.
  all: intros x; destruct x.
Defined.

Definition Sets_icoprod_empty (F : False → obj[Sets]) :
  indexed_coproduct F ≅[Sets] 0%object.
Proof.
  refine {| to := Sets_icoprod_empty_to F; from := Sets_icoprod_empty_from F |}.
  - intros x; destruct x.
  - intros [i x]; destruct i.
Defined.

Definition Sets_icoprod_unit_to (F : poly_unit → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> F ttt.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ i x =>
          match i return carrier (F i) → carrier (F ttt) with
          | ttt => fun x => x
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i; exact Hxy.
Defined.

Definition Sets_icoprod_unit_from (F : poly_unit → obj[Sets]) :
  F ttt ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun x => existT _ ttt x |}.
  all: intros x y Hxy; exists eq_refl; exact Hxy.
Defined.

Definition Sets_icoprod_unit (F : poly_unit → obj[Sets]) :
  indexed_coproduct F ≅[Sets] F ttt.
Proof.
  refine {| to := Sets_icoprod_unit_to F; from := Sets_icoprod_unit_from F |}.
  - intros x; reflexivity.
  - intros [i x]; destruct i; exists eq_refl; reflexivity.
Defined.

(** ** Non-degenerate indices: two distinct indices, and an infinite index *)

(* [bool] is the smallest non-degenerate index.  The product over it is the
   binary product of Instance/Sets/Cartesian.v -- a statement whose right-hand
   side names two distinct members of the family, which the empty and
   singleton statements cannot do.  ([Sets_iprod_empty] and [Sets_iprod_unit]
   above are their counterparts, and neither mentions two members.) *)

Definition Sets_iprod_bool_to (F : bool → obj[Sets]) :
  indexed_product F ~{Sets}~> (F true × F false)%object.
Proof.
  unshelve refine {| morphism := fun g => (g true, g false) |}.
  all: intros g h Hgh; split; [exact (Hgh true)|exact (Hgh false)].
Defined.

Definition Sets_iprod_bool_from (F : bool → obj[Sets]) :
  (F true × F false)%object ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun p =>
      fun b => match b return carrier (F b) with
               | true  => fst p
               | false => snd p
               end |}.
  all: intros p q [Hl Hr] b; destruct b; assumption.
Defined.

Definition Sets_iprod_bool (F : bool → obj[Sets]) :
  indexed_product F ≅[Sets] (F true × F false)%object.
Proof.
  refine {| to := Sets_iprod_bool_to F; from := Sets_iprod_bool_from F |}.
  - intros p; split; reflexivity.
  - intros g b; destruct b; reflexivity.
Defined.

(* [nat] is an infinite index.  The product over it satisfies the stream
   equation P ≅ F 0 × P': peel one factor off and a product of the same shape
   is underneath.  This exhibits the infinite case; it is not by itself a
   separation from the degenerate ones, which is what
   [Sets_iprod_unit_pigeonhole] and [Sets_iprod_nat_no_pigeonhole] at the end
   of this file are for. *)

Definition Sets_iprod_nat_to (F : nat → obj[Sets]) :
  indexed_product F
    ~{Sets}~> (F 0%nat × indexed_product (fun n => F (S n)))%object.
Proof.
  unshelve refine {| morphism := fun g => (g 0%nat, fun m => g (S m)) |}.
  all: intros g h Hgh; split; [exact (Hgh 0%nat)|intros m; exact (Hgh (S m))].
Defined.

Definition Sets_iprod_nat_from (F : nat → obj[Sets]) :
  (F 0%nat × indexed_product (fun n => F (S n)))%object
    ~{Sets}~> indexed_product F.
Proof.
  unshelve refine {| morphism := fun p =>
      fun n => match n return carrier (F n) with
               | O   => fst p
               | S m => snd p m
               end |}.
  all: intros p q [Hl Hr] n; destruct n; [exact Hl|exact (Hr n)].
Defined.

Definition Sets_iprod_nat (F : nat → obj[Sets]) :
  indexed_product F
    ≅[Sets] (F 0%nat × indexed_product (fun n => F (S n)))%object.
Proof.
  refine {| to := Sets_iprod_nat_to F; from := Sets_iprod_nat_from F |}.
  - intros p; split; [reflexivity|intros m; reflexivity].
  - intros g n; destruct n; reflexivity.
Defined.

(* The coproduct counterpart of [Sets_iprod_bool]: the sigma setoid over
   [bool] is the binary coproduct of Instance/Sets/Cocartesian.v. *)

Definition Sets_icoprod_bool_to (F : bool → obj[Sets]) :
  indexed_coproduct F ~{Sets}~> (F true + F false)%object.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ b x =>
          match b return carrier (F b) →
                         carrier (F true) + carrier (F false) with
          | true  => fun x => Datatypes.inl x
          | false => fun x => Datatypes.inr x
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i; exact Hxy.
Defined.

Definition Sets_icoprod_bool_from (F : bool → obj[Sets]) :
  (F true + F false)%object ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun s =>
      match s with
      | Datatypes.inl x => existT _ true x
      | Datatypes.inr y => existT _ false y
      end |}.
  all: intros s t Hst; destruct s, t; try contradiction;
       exists eq_refl; exact Hst.
Defined.

Definition Sets_icoprod_bool (F : bool → obj[Sets]) :
  indexed_coproduct F ≅[Sets] (F true + F false)%object.
Proof.
  refine {| to := Sets_icoprod_bool_to F; from := Sets_icoprod_bool_from F |}.
  - intros s; destruct s; reflexivity.
  - intros [i x]; destruct i; exists eq_refl; reflexivity.
Defined.

(* The coproduct counterpart of [Sets_iprod_nat]: the sigma setoid over [nat]
   splits off its zeroth summand and reproduces itself underneath. *)

Definition Sets_icoprod_nat_to (F : nat → obj[Sets]) :
  indexed_coproduct F
    ~{Sets}~> (F 0%nat + indexed_coproduct (fun n => F (S n)))%object.
Proof.
  unshelve refine {| morphism := fun p =>
      match p with
      | existT _ n x =>
          match n return carrier (F n) →
                         carrier (F 0%nat)
                         + Sets_icoprod_carrier (fun m => F (S m)) with
          | O   => fun x => Datatypes.inl x
          | S m => fun x => Datatypes.inr (existT _ m x)
          end x
      end |}.
  all: intros [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *;
       destruct i;
       [ exact Hxy | exists eq_refl; exact Hxy ].
Defined.

Definition Sets_icoprod_nat_from (F : nat → obj[Sets]) :
  (F 0%nat + indexed_coproduct (fun n => F (S n)))%object
    ~{Sets}~> indexed_coproduct F.
Proof.
  unshelve refine {| morphism := fun s =>
      match s with
      | Datatypes.inl x => existT (fun i : nat => carrier (F i)) 0%nat x
      | Datatypes.inr q =>
          match q with
          | existT _ m x => existT (fun i : nat => carrier (F i)) (S m) x
          end
      end |}.
  all: intros s t Hst; destruct s as [x|[m x]], t as [y|[n y]];
       try contradiction; simpl in *;
       [ exists eq_refl; exact Hst
       | destruct Hst as [e Hxy]; simpl in *; destruct e; simpl in *;
         exists eq_refl; exact Hxy ].
Defined.

Definition Sets_icoprod_nat (F : nat → obj[Sets]) :
  indexed_coproduct F
    ≅[Sets] (F 0%nat + indexed_coproduct (fun n => F (S n)))%object.
Proof.
  refine {| to := Sets_icoprod_nat_to F; from := Sets_icoprod_nat_from F |}.
  - intros s; destruct s as [x|[m x]]; reflexivity.
  - intros [i x]; destruct i; simpl; exists eq_refl; reflexivity.
Defined.

(** ** A separating property: pigeonhole at a singleton index, refuted at [nat]

    The isomorphisms above exhibit the construction at non-degenerate
    indices, but none of them is by itself a separation: none exhibits a
    property that holds at a degenerate index and is lost at a genuine one.
    The four results here do.  What is proved is the implication

      ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z,

    read over the product -- and, separately, over the coproduct -- of
    two-element setoids: no three elements are pairwise apart.  It holds over
    a SINGLETON index and is refutable over [nat].  A property of the
    construction at a degenerate index is therefore provably lost at a
    genuine one.

    Two cautions on reading that implication.  It is NOT the disjunctive
    pigeonhole "of any three elements, two coincide"; no disjunction is
    proved anywhere below.  The two forms are interderivable for these
    particular objects only because [Sets_bool] carries decidable equality,
    and that decidability is used inside the proofs (the [destruct ... eqn:]
    on [bool]) rather than stated as a hypothesis.  Separately, the informal
    reason the singleton case holds -- the object there has only two elements
    up to [≈] -- is not itself proved; the implication is. *)

(* The two-element setoid, [bool] under Coq's equality. *)
Definition Sets_bool : obj[Sets] :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Lemma Sets_iprod_unit_pigeonhole
  (x y z : carrier (indexed_product (fun _ : poly_unit => Sets_bool))) :
  ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z.
Proof.
  intros Hxy Hyz.
  assert (Hb : ∀ a b : carrier (indexed_product (fun _ : poly_unit => Sets_bool)),
                 a ttt = b ttt → a ≈ b)
    by (intros a b H i; destruct i; exact H).
  destruct (x ttt) eqn:Hx, (y ttt) eqn:Hy, (z ttt) eqn:Hz;
  first [ apply Hb; rewrite Hx, Hz; reflexivity
        | exfalso; apply Hxy; apply Hb; rewrite Hx, Hy; reflexivity
        | exfalso; apply Hyz; apply Hb; rewrite Hy, Hz; reflexivity ].
Qed.

(* Three elements of the [nat]-indexed product of two-element setoids: the
   constantly-[false] tuple, and the tuples true at index 0 and at index 1. *)
Definition Sets_iprod_pt0 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) := fun _ => false.

Definition Sets_iprod_pt1 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) :=
  fun n => match n with O => true | S _ => false end.

Definition Sets_iprod_pt2 :
  carrier (indexed_product (fun _ : nat => Sets_bool)) :=
  fun n => match n with S O => true | _ => false end.

Lemma Sets_iprod_nat_no_pigeonhole :
  (∀ x y z : carrier (indexed_product (fun _ : nat => Sets_bool)),
     ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z) → False.
Proof.
  intros H.
  assert (H01 : (Sets_iprod_pt0 ≈ Sets_iprod_pt1) → False)
    by (intros Heq; specialize (Heq 0%nat); simpl in Heq; discriminate).
  assert (H12 : (Sets_iprod_pt1 ≈ Sets_iprod_pt2) → False)
    by (intros Heq; specialize (Heq 0%nat); simpl in Heq; discriminate).
  specialize (H _ _ _ H01 H12 1%nat); simpl in H; discriminate.
Qed.

Lemma Sets_icoprod_unit_pigeonhole
  (x y z : carrier (indexed_coproduct (fun _ : poly_unit => Sets_bool))) :
  ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z.
Proof.
  intros Hxy Hyz.
  assert (Hb : ∀ a b : carrier (indexed_coproduct (fun _ : poly_unit => Sets_bool)),
                 projT2 a = projT2 b → a ≈ b)
    by (intros [i a] [j b] Hab; simpl in *; destruct i, j;
        exists eq_refl; exact Hab).
  destruct (projT2 x) eqn:Hx, (projT2 y) eqn:Hy, (projT2 z) eqn:Hz;
  first [ apply Hb; rewrite Hx, Hz; reflexivity
        | exfalso; apply Hxy; apply Hb; rewrite Hx, Hy; reflexivity
        | exfalso; apply Hyz; apply Hb; rewrite Hy, Hz; reflexivity ].
Qed.

(* The [k]-th summand's [true].  Identifying two of these calls for an
   equality of the two indices, which is what the refutation below turns
   on. *)
Definition Sets_icoprod_pt (k : nat) :
  carrier (indexed_coproduct (fun _ : nat => Sets_bool)) :=
  existT (fun _ : nat => carrier Sets_bool) k true.

Lemma Sets_icoprod_nat_no_pigeonhole :
  (∀ x y z : carrier (indexed_coproduct (fun _ : nat => Sets_bool)),
     ((x ≈ y) → False) → ((y ≈ z) → False) → x ≈ z) → False.
Proof.
  intros H.
  assert (H01 : (Sets_icoprod_pt 0 ≈ Sets_icoprod_pt 1) → False)
    by (intros [e _]; simpl in e; discriminate).
  assert (H12 : (Sets_icoprod_pt 1 ≈ Sets_icoprod_pt 2) → False)
    by (intros [e _]; simpl in e; discriminate).
  destruct (H _ _ _ H01 H12) as [e _]; simpl in e; discriminate.
Qed.
