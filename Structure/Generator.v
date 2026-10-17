Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   nLab:  https://ncatlab.org/nlab/show/separator
   nLab:  https://ncatlab.org/nlab/show/generator

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Generating (separating) families and objects *)

(* Mac Lane §V.7 p. 127 / Riehl 4.7.7 / Awodey §7.2: a family of objects
   SEPARATES (generates) C when parallel arrows agreeing after every arrow
   OUT of a member are equal.  Stated positively as a cancellation law,
   the constructively correct reading, exactly as [Cogenerator] states its
   dual. *)
Record Generator {C : Category} := {
  gen_index : Type;
  gen_obj : gen_index -> C;
  gen_separates : forall (x y : C) (f g : x ~> y),
    (forall (j : gen_index) (k : gen_obj j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g
}.

Arguments Generator : clear implicits.
Arguments gen_index {C} _.
Arguments gen_obj {C} _ _.
Arguments gen_separates {C} _ {x y} f g _.

(* Awodey's single-object form: one object whose generalized elements
   distinguish parallel arrows. *)
Definition IsSeparator {C : Category} (c : C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition Generator_of_separator {C : Category} (c : C) (H : IsSeparator c) :
  Generator C := {|
  gen_index := unit;
  gen_obj := fun _ => c;
  gen_separates := fun x y f g Hk => H x y f g (fun k => Hk tt k)
|}.

(* Joint faithfulness of a family of functors: the arrows are told apart
   by SOME member.  For the representables [Hom (gen_obj j), ─] this is
   the separation condition read through [fmap]. *)
Definition JointlyFaithful {C D : Category} {J : Type}
  (F : J -> C ⟶ D) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall j : J, fmap[F j] f ≈ fmap[F j] g) -> f ≈ g.

(** ** Awodey §7.2: separation IS faithfulness of the representable *)

Section Characterizations.

Context {C : Category}.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition separator_faithful (c : C) (H : IsSeparator c) :
  Faithful [Hom c,─] :=
  @Build_Faithful C Sets [Hom c,─] (fun x y f g E => H x y f g (fun k => E k)).

(* Backward, by the same unfolding read the other way: [fmap_inj] is the
   field of [Faithful], and its hypothesis is already the separation
   hypothesis. *)
Definition faithful_separator (c : C) (F : Faithful [Hom c,─]) :
  IsSeparator c :=
  fun x y f g H => @fmap_inj _ _ [Hom c,─] F x y f g (fun k => H k).

(** ** Mac Lane §V.7 / Riehl §E.4: the family form is joint faithfulness *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition generator_jointly_faithful (G : Generator C) :
  JointlyFaithful (fun j : gen_index G => [Hom gen_obj G j,─]) :=
  fun x y f g H => gen_separates G f g (fun j k => H j k).

Definition jointly_faithful_generator {J : Type} (F : J -> C)
  (H : JointlyFaithful (fun j : J => [Hom F j,─])) : Generator C :=
  @Build_Generator C J F (fun x y f g Hk => H x y f g (fun j k => Hk j k)).

(** ** The single-object / family bridge *)

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition separator_of_generator (G : Generator C) (j0 : gen_index G)
  (Hsing : forall j : gen_index G, j = j0) : IsSeparator (gen_obj G j0).
Proof.
  intros x y f g H.
  apply (gen_separates G f g); intros j k.
  revert k; rewrite (Hsing j); intros k; apply H.
Defined.

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example separator_generator_roundtrip (c : C) (H : IsSeparator c) :
  separator_of_generator (Generator_of_separator c H) tt
    (fun j => match j with tt => eq_refl end) = H := eq_refl.

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Separates {J : Type} (F : J -> C) : Type :=
  forall (x y : C) (f g : x ~> y),
    (forall (j : J) (k : F j ~> x), f ∘ k ≈ g ∘ k) -> f ≈ g.

Definition generator_iff_jointly_faithful {J : Type} (F : J -> C) :
  (Separates F -> JointlyFaithful (fun j : J => [Hom F j,─])) *
  (JointlyFaithful (fun j : J => [Hom F j,─]) -> Separates F) :=
  (fun H x y f g E => H x y f g (fun j k => E j k),
   fun H x y f g E => H x y f g (fun j k => E j k)).

(* The same bridge one level up, between the two faithfulness notions:
   [JointlyFaithful] over a [unit] index is [Faithful]. *)
Definition jointly_faithful_faithful {D : Category} (F : C ⟶ D)
  (H : Faithful F) : JointlyFaithful (fun _ : unit => F) :=
  fun x y f g E => @fmap_inj _ _ F H x y f g (E tt).

Definition faithful_jointly_faithful {D : Category} (F : C ⟶ D)
  (H : JointlyFaithful (fun _ : unit => F)) : Faithful F :=
  @Build_Faithful C D F (fun x y f g E => H x y f g (fun _ => E)).

End Characterizations.

(** ** Transport along isomorphisms and along maps of index types *)

Section Transport.

Context {C : Category}.

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_test_iso {x y : C} (f g : x ~> y) {c d : C} (i : c ≅ d)
  (H : forall k : d ~> x, f ∘ k ≈ g ∘ k) (k : c ~> x) : f ∘ k ≈ g ∘ k.
Proof.
  specialize (H (k ∘ from i)).
  rewrite !comp_assoc in H.
  rewrite <- (id_right (f ∘ k)), <- (id_right (g ∘ k)).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite H.
Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition separator_iso {c d : C} (H : IsSeparator c) (i : c ≅ d) :
  IsSeparator d :=
  fun x y f g Hk => H x y f g (hom_test_iso f g i Hk).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition gen_family_mono (G : Generator C) {K : Type} (ob : K -> C)
  (u : gen_index G -> K) (i : forall j, gen_obj G j ≅ ob (u j)) :
  Generator C :=
  @Build_Generator C K ob
    (fun x y f g H =>
       gen_separates G f g (fun j => hom_test_iso f g (i j) (H (u j)))).

(* Replacing each member by an isomorphic object, the index kept. *)
Definition gen_iso (G : Generator C) (d : gen_index G -> C)
  (i : forall j, gen_obj G j ≅ d j) : Generator C :=
  gen_family_mono G d (fun j => j) i.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition gen_extend (G : Generator C) {K : Type} (ob : K -> C) :
  Generator C :=
  gen_family_mono G (fun jk => match jk with
                               | inl j => gen_obj G j
                               | inr k => ob k
                               end) inl (fun _ => iso_id).

End Transport.

(** ** Riehl's contrapositive reading, as far as it is free *)

Section Contrapositive.

Context {C : Category}.

(*
   本节说明 Generator 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition gen_separates_contra (G : Generator C) {x y : C} (f g : x ~> y)
  (Hne : f ≈ g -> False) :
  (forall (j : gen_index G) (k : gen_obj G j ~> x), f ∘ k ≈ g ∘ k) -> False :=
  fun H => Hne (gen_separates G f g H).

Definition separator_contra {c : C} (H : IsSeparator c) {x y : C}
  (f g : x ~> y) (Hne : f ≈ g -> False) :
  (forall k : c ~> x, f ∘ k ≈ g ∘ k) -> False :=
  fun Hk => Hne (H x y f g Hk).

End Contrapositive.
