Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.

Generalizable All Variables.

(** * The full subcategory of propositional setoids, reflective in [Sets] *)

(*
 nLab:    https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:    https://ncatlab.org/nlab/show/Bishop+set
 nLab:    https://ncatlab.org/nlab/show/propositional+truncation
 Book:    The Univalent Foundations Program, "Homotopy Type Theory", IAS
 Book:    Awodey, "Category Theory", Carnegie Mellon pre-print of the 1st

   本文件给出全嵌入相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The subcategory *)

Definition PropSets_sub@{o so | o < so +} :
  Subcategory@{so o so o} Sets@{o so} :=
  @Build_Subcategory Sets@{o so} PropEquivObj@{so o o}
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition PropSets@{o so | o < so +} : Category@{so o o} :=
  Sub@{so o so o so o so} Sets@{o so} PropSets_sub@{o so}.

Definition PropSets_Incl@{o so | o < so +} :
  PropSets@{o so} ⟶ Sets@{o so} :=
  Incl@{so o so o so so} Sets@{o so} PropSets_sub@{o so}.

Example PropSets_Incl_fobj@{o so | o < so +} (X : PropSets@{o so}) :
  fobj[PropSets_Incl@{o so}] X = projT1 X := eq_refl.

Example PropSets_Incl_fmap@{o so | o < so +} (X Y : PropSets@{o so})
  (f : X ~{PropSets@{o so}}~> Y) :
  fmap[PropSets_Incl@{o so}] f = projT1 f := eq_refl.

(** ** Full and faithful *)

Definition PropSets_Full@{o so | o < so +} :
  Full Sets@{o so} PropSets_sub@{o so} :=
  fun _ _ _ _ _ => I.

(* Built directly rather than by [Full_Implies_Full_Functor], which is
   [Qed]: the chosen preimage of g is (g; I), and it computes, for later
   files; nothing in the tree reads through it yet. *)
Definition PropSets_Incl_Full@{o so | o < so +} :
  Functor.Full PropSets_Incl@{o so}.
Proof.
  unshelve refine {| prefmap := fun X Y g => _ |}.
  - exists g. exact I.
  - intros X Y g x. simpl. reflexivity.
Defined.

Definition PropSets_Incl_Faithful@{o so | o < so +} :
  Functor.Faithful PropSets_Incl@{o so} :=
  Incl_Faithful Sets@{o so} PropSets_sub@{o so}.

(** ** Locally propositional *)

(* Two arrows are ≈ when their functions agree pointwise up to the
   target's `≈`, so the target's [pequiv] mirrors it pointwise: the
   relation of Instance/Sets/Propositional.v's [hom_PropEquiv], read on
   first projections, since a hom-setoid of [PropSets] is a [sigT] over
   [Sets]'s and not [Sets]'s own. *)
#[export] Instance PropSets_LocallyPropositional@{o so | o < so +} :
  LocallyPropositional PropSets@{o so} :=
  LocallyPropositional_of_relation PropSets@{o so}
    (fun X Y (f g : X ~{PropSets@{o so}}~> Y) =>
       ∀ a : carrier (projT1 X),
         @pequiv _ _ (projT2 Y) (projT1 f a) (projT1 g a))
    (fun X Y f g H a => pequiv_to _ _ (H a))
    (fun X Y f g H a => pequiv_from _ _ (H a)).

(** ** Functors into [Sets] with propositional values *)

Definition PropSets_lift@{co ch o so | o < so, ch <= o +}
  {C : Category@{co ch ch}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) : C ⟶ PropSets@{o so}.
Proof.
  unshelve refine (@Build_Functor C PropSets@{o so}
                     (fun c => existT _ (F c) (P c)) (fun x y f => _)
                     _ _ _).
  - exists (fmap[F] f). exact I.
  - intros x y f g H. simpl. exact (@fmap_respects _ _ F x y f g H).
  - intros x. simpl. exact (@fmap_id _ _ F x).
  - intros x y z f g. simpl. exact (@fmap_comp _ _ F x y z f g).
Defined.

Example PropSets_lift_obj@{co o so s | o < so, o < s +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (c : C) :
  fobj[PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P] c
    = fobj[F] c := eq_refl.

Example PropSets_lift_map@{co o so s | o < so, o < s +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (x y : C) (f : x ~> y) :
  fmap[PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P] f
    = fmap[F] f := eq_refl.

Definition PropSets_lift_Incl@{co o so s a b |
  o < so, o < s, o < b, co <= a, co <= b, o <= a, so <= a +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) :
  @equiv _ (@Functor_Setoid@{a b co s so o} C Sets@{o so})
    (PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P) F.
Proof.
  exists (fun c => iso_id). intros x y f a. simpl. reflexivity.
Defined.

(** ** The truncation *)

Definition trunc_equivalence@{o | +} (S : SetoidObject@{o o}) :
  @Equivalence@{o o} (carrier S)
    (fun x y : carrier S => inhabited (x ≈ y)).
Proof.
  constructor.
  - intros x. exact (inhabits (reflexivity x)).
  - intros x y [H]. exact (inhabits (symmetry H)).
  - intros x y z [H] [K]. exact (inhabits (transitivity H K)).
Defined.

Definition trunc_setoid@{o | +} (S : SetoidObject@{o o}) :
  SetoidObject@{o o} :=
  {| carrier := carrier S;
     is_setoid := {| equiv := fun x y : carrier S => inhabited (x ≈ y);
                     setoid_equiv := trunc_equivalence@{o} S |} |}.

Definition trunc_PropEquiv@{o so | o < so +} (S : SetoidObject@{o o}) :
  PropEquivObj@{so o o} (trunc_setoid@{o} S) :=
  @PropEquiv_of_relation (carrier S) (is_setoid (trunc_setoid@{o} S))
    (fun x y : carrier S => inhabited (x ≈ y))
    (fun x y H => H) (fun x y H => H).

Definition PropSets_trunc_obj@{o so | o < so +} (S : Sets@{o so}) :
  PropSets@{o so} :=
  existT _ (trunc_setoid@{o} S) (trunc_PropEquiv@{o so} S).

Definition PropSets_trunc@{o so | o < so +} :
  Sets@{o so} ⟶ PropSets@{o so}.
Proof.
  unshelve refine (@Build_Functor Sets@{o so} PropSets@{o so}
                     PropSets_trunc_obj@{o so} (fun S T f => _) _ _ _).
  - unshelve eexists; [ | exact I ].
    unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => f x) _).
    intros x y H. simpl in *. destruct H as [H].
    exact (inhabits (proper_morphism f x y H)).
  - intros S T f g H x. simpl. exact (inhabits (H x)).
  - intros S x. simpl. exact (inhabits (reflexivity x)).
  - intros S T U f g x. simpl. exact (inhabits (reflexivity _)).
Defined.

(** ** The reflection *)

Definition trunc_transpose@{o so | o < so +}
  {S : Sets@{o so}} {X : PropSets@{o so}}
  (k : PropSets_trunc@{o so} S ~{PropSets@{o so}}~> X) :
  S ~{Sets@{o so}}~> PropSets_Incl@{o so} X.
Proof.
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => projT1 k x) _).
  intros x y H. exact (proper_morphism (projT1 k) x y (inhabits H)).
Defined.

Definition trunc_extend@{o so | o < so +}
  {S : Sets@{o so}} {X : PropSets@{o so}}
  (g : S ~{Sets@{o so}}~> PropSets_Incl@{o so} X) :
  PropSets_trunc@{o so} S ~{PropSets@{o so}}~> X.
Proof.
  unshelve eexists; [ | exact I ].
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => g x) _).
  intros x y H. apply (@pequiv_elim_inhabited _ _ (projT2 X)).
  simpl in H. destruct H as [H]. exact (inhabits (proper_morphism g x y H)).
Defined.

#[local] Obligation Tactic := idtac.

Program Definition PropSets_trunc_iso@{o so | o < so +}
  (S : Sets@{o so}) (X : PropSets@{o so}) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom PropSets@{o so} (PropSets_trunc@{o so} S) X ;
       is_setoid := @homset PropSets@{o so} (PropSets_trunc@{o so} S) X |}
    {| carrier := @hom Sets@{o so} S (PropSets_Incl@{o so} X) ;
       is_setoid := @homset Sets@{o so} S (PropSets_Incl@{o so} X) |} := {|
  to   := {| morphism := fun k => trunc_transpose@{o so} k |};
  from := {| morphism := fun g => trunc_extend@{o so} g |}
|}.
Next Obligation. intros S X k k' H x; exact (H x). Qed.
Next Obligation. intros S X g g' H x; exact (H x). Qed.
Next Obligation. intros S X g x; reflexivity. Qed.
Next Obligation. intros S X k x; reflexivity. Qed.

Definition PropSets_trunc_Incl@{o so a | o < so +} :
  @Adjunction@{so o o so o o o o so o a} PropSets@{o so} Sets@{o so}
    PropSets_trunc@{o so} PropSets_Incl@{o so}.
Proof.
  unshelve refine (@Build_Adjunction'@{so o o so o o a so} _ _
                     PropSets_trunc@{o so} PropSets_Incl@{o so}
                     PropSets_trunc_iso@{o so} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

Example PropSets_trunc_unit@{o so a | o < so +} (S : Sets@{o so}) :
  @Sets.morphism _ _ _ _
    (@Category.Theory.Adjunction.unit _ _ _ _
       PropSets_trunc_Incl@{o so a} S) = (fun x : carrier S => x)
  := eq_refl.

Example PropSets_trunc_counit@{o so a | o < so +} (X : PropSets@{o so}) :
  @Sets.morphism _ _ _ _
    (projT1 (@Category.Theory.Adjunction.counit _ _ _ _
               PropSets_trunc_Incl@{o so a} X))
    = (fun x : carrier (projT1 X) => x)
  := eq_refl.

Definition PropSets_Reflective@{o so a | o < so +} :
  Reflective PropSets_sub@{o so} :=
  {| reflective_full := PropSets_Full@{o so};
     reflector := PropSets_trunc@{o so};
     reflective_adj := PropSets_trunc_Incl@{o so a} |}.

(** ** The choice principle, written out (moved here by #1349) *)

(* The principle ∀ A, inhabited A → A under Instance/Sets/Classifier/
   OneLevel.v's name for it, written unfolded so that this file needs no
   further [Require]: the hypothesis of [choice_of_untr] is OneLevel.v's
   [Untruncate@{c}], by [eq_refl] (control C53 of
   Test/ProbeMonadicity469.v).  Moved here from Instance/Pos/Monadicity.v
   by #1349; Instance/Top/Components.v derives its [unsquash_Untruncate]
   and [Untruncate_unsquash] from these two. *)
Definition untr_of_choice@{c | +} (G : ∀ A : Type@{c}, inhabited A → A) :
  ∀ P : Type@{c}, (∀ Q : Prop, (P → Q) → Q) → P :=
  fun P h => G P (h (inhabited P) (fun p => inhabits p)).

Definition choice_of_untr@{c | +}
  (U : ∀ P : Type@{c}, (∀ Q : Prop, (P → Q) → Q) → P) :
  ∀ A : Type@{c}, inhabited A → A :=
  fun A h => U A (fun Q k => match h with inhabits a => k a end).

(** ** The squash setoid (moved here by #1349) *)

(* The setoid on [bool] whose [true ≈ false] is a given type [Q].  Moved
   here from Instance/Top/Components.v by #1349. *)
Definition squash_rel@{o} (Q : Type@{o}) (x y : bool) : Type@{o} :=
  ((x = y) + Q)%type.

Lemma squash_sym@{o} (Q : Type@{o}) (x y : bool) :
  squash_rel Q x y -> squash_rel Q y x.
Proof. intros [e|q]; [left; symmetry; exact e|right; exact q]. Qed.

Lemma squash_trans@{o} (Q : Type@{o}) (x y z : bool) :
  squash_rel Q x y -> squash_rel Q y z -> squash_rel Q x z.
Proof.
  intros [e1|q] [e2|q']; [left; exact (eq_trans e1 e2)|right; exact q'
                            |right; exact q|right; exact q].
Qed.

Definition SquashSetoid@{o} (Q : Type@{o}) : SetoidObject@{o o}.
Proof.
  refine {| carrier := bool; is_setoid := {| equiv := squash_rel Q |} |}.
  constructor.
  - intro x; left; reflexivity.
  - exact (squash_sym Q).
  - exact (squash_trans Q).
Defined.
