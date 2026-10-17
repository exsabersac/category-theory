Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Rel.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(** * The concrete-category roster: Coq, CMon, and Rel *)

(*
   nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
   Paper:     Freyd, "Homotopy is not concrete", Lecture Notes in Mathematics

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Coq: types and functions *)

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Coq_Underlying@{u u0 +} :
  Coq@{u u0 u0 u0} ⟶ Sets@{u0 u} := {|
  fobj := fun A => {| carrier   := A
                    ; is_setoid := {| equiv        := @eq A
                                    ; setoid_equiv := eq_equivalence |} |};
  fmap := fun _ _ f => {| morphism := f |}
|}.
Next Obligation. intros A B f a b Hab; simpl in *; subst; exact eq_refl. Qed.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; reflexivity. Qed.
Next Obligation. intros A B C f g a; reflexivity. Qed.

(* Faithfulness is the identity implication: both `≈`s unfold to pointwise
   Leibniz equality of the same function. *)
#[export] Instance Coq_Underlying_Faithful@{u u0 +} :
  Faithful Coq_Underlying@{u u0} .
Proof.
  constructor; intros A B f g Hfg.
  exact Hfg.
Qed.

#[export] Instance Coq_Concrete@{u u0 +} : Concrete Coq@{u u0 u0 u0} := {|
  underlying          := Coq_Underlying@{u u0};
  underlying_faithful := Coq_Underlying_Faithful@{u u0}
|}.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Coq_two_arrows : @id Coq bool ≈ negb → False.
Proof.
  intro Heq.
  specialize (Heq true).
  simpl in Heq.
  discriminate.
Qed.

(** ** CMon: commutative monoids *)

(* The proof Instance/CMon.v itself only asserts.  Equivalence of
   homomorphisms in `CMon` (`CMonHom_Setoid`) is by definition pointwise
   equivalence of the underlying setoid maps, which is what `CMon_Forget`
   records, so injectivity of its hom-map is the identity implication. *)
#[export] Instance CMon_Forget_Faithful : Faithful CMon_Forget.
Proof.
  constructor; simpl; intros M N f g Hfg a.
  exact (Hfg a).
Qed.

#[export] Instance CMon_Concrete : Concrete CMon := {|
  underlying          := CMon_Forget;
  underlying_faithful := CMon_Forget_Faithful
|}.

(* The natural numbers under Leibniz equality, as a setoid. *)
Definition nat_setoid_object : SetoidObject :=
  {| carrier   := nat
   ; is_setoid := {| equiv := @eq nat ; setoid_equiv := eq_equivalence |} |}.

(* The additive monoid of natural numbers, used only to show that `CMon` has
   parallel morphisms that differ. *)
Definition nat_CMon : CMonObject.
Proof.
  unshelve refine {| cmon_setoid := nat_setoid_object
                   ; cmon_zero   := 0%nat
                   ; cmon_plus   := Nat.add |}.
  - intros a b c; simpl; symmetry; apply PeanoNat.Nat.add_assoc.
  - intros a b; simpl; apply PeanoNat.Nat.add_comm.
  - intros a; simpl; reflexivity.
  (*
   本节说明 Concrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Defined.

(* The constant-zero endomorphism of `nat_CMon`; it preserves the unit and the
   operation, so it is a genuine homomorphism. *)
Definition nat_CMon_zero_hom : CMonHom nat_CMon nat_CMon.
Proof.
  unshelve refine (Build_CMonHom nat_CMon nat_CMon _ _ _).
  - refine {| morphism := fun _ => 0%nat |}.
  - simpl; reflexivity.
  - intros a b; simpl; reflexivity.
Defined.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma CMon_two_arrows : @id CMon nat_CMon ≈ nat_CMon_zero_hom → False.
Proof.
  intro Heq.
  specialize (Heq 1%nat).
  simpl in Heq.
  discriminate.
Qed.

(** ** Rel: sets and relations, the negative half *)

(* An auxiliary arithmetic fact, proved here to keep the file's dependencies
   to the ones already present in Instance/Rel.v. *)
Lemma nat_neq_succ (n : nat) : n = S n → False.
Proof.
  induction n as [|n IH]; intro Hn.
  - discriminate.
  - apply IH.
    now injection Hn.
Qed.

(*
   本节说明 Concrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Rel_hom_is_not_a_function (f : nat → nat) :
  (∀ x y : nat, some_number x y ↔ f x = y) → False.
Proof.
  intro Hgraph.
  (* `f 0` is above 0, since `f 0 = f 0`. *)
  assert (H0 : some_number 0%nat (f 0%nat)) by now apply Hgraph.
  (* `S (f 0)` is also above 0, so the graph reading forces `f 0 = S (f 0)`. *)
  assert (HS : some_number 0%nat (S (f 0%nat))).
  { unfold some_number in *.
    apply PeanoNat.Nat.lt_lt_succ_r, H0. }
  apply (nat_neq_succ (f 0%nat)).
  now apply Hgraph.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Rel_empty : (unit : Rel) ~{Rel}~> (unit : Rel) :=
  fun _ _ => False.

Lemma Rel_two_arrows : @id Rel unit ≈ Rel_empty → False.
Proof.
  intro Heq.
  apply (Heq tt tt).
  (* `id` in Rel is `Singleton`, so the point is related to itself. *)
  constructor.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Rel_subsingleton_not_Faithful (U : Rel ⟶ Sets)
        (Hsub : ∀ a b : carrier (U (unit : Rel)), a ≈ b) :
  Faithful U → False.
Proof.
  intro HF.
  apply Rel_two_arrows.
  apply (fmap_inj (F:=U)).
  simpl; intro a.
  apply Hsub.
Qed.

(** ** Rel: sets and relations, the positive half *)

(*
   本节说明函子、单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rel_Powerset : Rel ⟶ Sets := {|
  fobj := fun X => {| carrier   := X → Prop
                    ; is_setoid := {| equiv := fun S T => ∀ x, S x ↔ T x |} |};
  fmap := fun X Y R =>
            {| morphism := fun S y => (exists x : X, S x ∧ R x y)%type |}
|}.
Next Obligation.
  (* the powerset setoid: pointwise `↔` is an equivalence *)
  (* `↔` here is Category.Lib's `iffT`, a pair of maps, so the two directions
     are reached with [fst] and [snd] rather than [proj1]/[proj2]. *)
  intros X; constructor.
  - intros S a; split; intro Ha; exact Ha.
  - intros S T HST a; split; [ exact (snd (HST a)) | exact (fst (HST a)) ].
  - intros S T U HST HTU a; split; intro Ha.
    + exact (fst (HTU a) (fst (HST a) Ha)).
    + exact (snd (HST a) (snd (HTU a) Ha)).
Qed.
Next Obligation.
  (* the direct image of a fixed relation respects `≈` of subsets *)
  intros X Y R S T HST b.
  split; intros [a [Ha HR]]; exists a; split.
  - exact (fst (HST a) Ha).
  - exact HR.
  - exact (snd (HST a) Ha).
  - exact HR.
Qed.
Next Obligation.
  (* equivalent relations have equal direct images *)
  intros X Y R R' HRR' S b.
  split; intros [a [Ha HR]]; exists a; split.
  - exact Ha.
  - exact (fst (HRR' a b) HR).
  - exact Ha.
  - exact (snd (HRR' a b) HR).
Qed.
Next Obligation.
  (* the direct image along the diagonal is the identity on subsets *)
  intros X S a; split; intro Hin.
  - destruct Hin as [b [HSb Hdiag]].
    now destruct Hdiag.
  - exists a.
    split; [ exact Hin | constructor ].
Qed.
Next Obligation.
  (* direct image takes relational composites to composites of maps *)
  intros X Y Z R R' S c; split.
  - intros [a [Ha [b [HR' HR]]]].
    exists b; split; [ exists a; split; assumption | exact HR ].
  - intros [b [[a [Ha HR']] HR]].
    exists a; split; [ exact Ha | exists b; split; assumption ].
Qed.

(* Faithfulness: probe the direct-image map with the singleton subsets.  If
   `R` and `R'` have the same direct images then they agree on every
   `{x}`, hence everywhere. *)
#[export] Instance Rel_Powerset_Faithful : Faithful Rel_Powerset.
Proof.
  constructor; simpl; intros X Y R R' Himg x y.
  specialize (Himg (fun a => a = x) y).
  split; intro Hxy.
  - destruct Himg as [Hfwd _].
    destruct Hfwd as [a [Ha HR]]; [ now exists x | ].
    now subst.
  - destruct Himg as [_ Hbwd].
    destruct Hbwd as [a [Ha HR]]; [ now exists x | ].
    now subst.
Qed.

#[export] Instance Rel_Concrete : Concrete Rel := {|
  underlying          := Rel_Powerset;
  underlying_faithful := Rel_Powerset_Faithful
|}.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Rel_Powerset_unit_not_subsingleton :
  (∀ a b : carrier (Rel_Powerset (unit : Rel)), a ≈ b) → False.
Proof.
  intro Hsub.
  apply (Hsub (fun _ => False) (fun _ => True) tt).
  exact I.
Qed.
