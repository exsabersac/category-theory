Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The arrows-only presentation of natural transformations *)

(*
 nLab: https://ncatlab.org/nlab/show/natural+transformation
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出箭头形式的自然变换。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ArrowTransform.

Context {C : Category}.
Context {D : Category}.
Context {S : C ⟶ D}.
Context {T : C ⟶ D}.

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record ArrowTransform := {
  τ_arr {c c' : C} (f : c ~> c') : S c ~> T c';

  (* post-composition splices in through T *)
  τ_arr_left {c c' c'' : C} (g : c' ~> c'') (f : c ~> c') :
    fmap[T] g ∘ τ_arr f ≈ τ_arr (g ∘ f);

  (* pre-composition splices in through S *)
  τ_arr_right {c c' c'' : C} (g : c' ~> c'') (f : c ~> c') :
    τ_arr (g ∘ f) ≈ τ_arr g ∘ fmap[S] f
}.

(* The two fields chained, i.e. the exercise's displayed equation with its
   middle term elided. *)

Lemma τ_arr_splice (A : ArrowTransform) {c c' c'' : C}
      (g : c' ~> c'') (f : c ~> c') :
  fmap[T] g ∘ τ_arr A f ≈ τ_arr A g ∘ fmap[S] f.
Proof.
  rewrite τ_arr_left.
  apply τ_arr_right.
Qed.

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma τ_arr_from_left (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  τ_arr A f ≈ fmap[T] f ∘ τ_arr A (id[c]).
Proof.
  rewrite (τ_arr_left A f (id[c])).       (* fmap[T] f ∘ τ id ≈ τ (f ∘ id) *)
  rewrite (τ_arr_right A f (id[c])).      (* τ (f ∘ id) ≈ τ f ∘ fmap[S] id *)
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Lemma τ_arr_from_right (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  τ_arr A f ≈ τ_arr A (id[c']) ∘ fmap[S] f.
Proof.
  rewrite <- (τ_arr_right A (id[c']) f).  (* τ id ∘ fmap[S] f ≈ τ (id ∘ f) *)
  rewrite <- (τ_arr_left A (id[c']) f).   (* τ (id ∘ f) ≈ fmap[T] id ∘ τ f *)
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* Respectfulness is a consequence of the two laws, not a further field. *)

#[export]
Instance τ_arr_respects (A : ArrowTransform) {c c'} :
  Proper (equiv ==> equiv) (@τ_arr A c c').
Proof.
  intros f f' Hf.
  rewrite (τ_arr_from_left A f).
  rewrite (τ_arr_from_left A f').
  now rewrite Hf.
Qed.

(* The naturality square of the diagonal family c ↦ τ (id[c]), obtained by
   reading the previous two lemmas in opposite directions. *)

Lemma τ_arr_diagonal_naturality (A : ArrowTransform) {c c' : C} (f : c ~> c') :
  fmap[T] f ∘ τ_arr A (id[c]) ≈ τ_arr A (id[c']) ∘ fmap[S] f.
Proof.
  rewrite <- τ_arr_from_left.
  apply τ_arr_from_right.
Qed.

(* Arrow families form a setoid under pointwise ≈ at every arrow, exactly
   as transformations form one under pointwise ≈ at every object
   ([Transform_Setoid]).  The correspondence below is an equivalence of
   these two setoids, not merely a bijection of their carriers. *)

#[export]
Program Instance ArrowTransform_Setoid : Setoid ArrowTransform := {|
  equiv := fun A B => ∀ (c c' : C) (f : c ~> c'), τ_arr A f ≈ τ_arr B f
|}.
Next Obligation.
  constructor.
  - intros A c c' f.
    reflexivity.
  - intros A B H c c' f.
    symmetry.
    apply H.
  - intros A B E H1 H2 c c' f.
    transitivity (τ_arr B f).
    + apply H1.
    + apply H2.
Qed.

(* From a transformation to its arrow family: transport along S, then
   transform.  Both laws are then instances of naturality and
   functoriality. *)

Program Definition Transform_to_Arrows (N : S ⟹ T) : ArrowTransform := {|
  τ_arr := fun c c' f => transform[N] c' ∘ fmap[S] f
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  now rewrite <- fmap_comp.
Qed.
Next Obligation.
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Transform_to_Arrows_alt (N : S ⟹ T) {c c' : C} (f : c ~> c') :
  τ_arr (Transform_to_Arrows N) f ≈ fmap[T] f ∘ transform[N] c.
Proof.
  simpl.
  symmetry.
  apply naturality.
Qed.

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Arrows_to_Transform (A : ArrowTransform) : S ⟹ T :=
  Build_Transform' (fun c => τ_arr A (id[c]))
                   (fun c c' f => τ_arr_diagonal_naturality A f).

(* Both composites are the identity up to ≈. *)

Theorem Transform_to_Arrows_to_Transform (N : S ⟹ T) :
  Arrows_to_Transform (Transform_to_Arrows N) ≈ N.
Proof.
  intros c.
  simpl.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Theorem Arrows_to_Transform_to_Arrows (A : ArrowTransform) :
  Transform_to_Arrows (Arrows_to_Transform A) ≈ A.
Proof.
  intros c c' f.
  simpl.
  now rewrite <- τ_arr_from_right.
Qed.

(* Both directions respect the two setoids. *)

#[export]
Instance Transform_to_Arrows_respects :
  Proper (equiv ==> equiv) Transform_to_Arrows.
Proof.
  intros N M H c c' f.
  simpl.
  now rewrite (H c').
Qed.

#[export]
Instance Arrows_to_Transform_respects :
  Proper (equiv ==> equiv) Arrows_to_Transform.
Proof.
  intros A B H c.
  simpl.
  apply H.
Qed.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Transform_determined_by_arrows (N M : S ⟹ T) :
  Transform_to_Arrows N ≈ Transform_to_Arrows M → N ≈ M.
Proof.
  intros H c.
  pose proof (H c c (id[c])) as Hc.
  simpl in Hc.
  rewrite !fmap_id in Hc.
  now rewrite !id_right in Hc.
Qed.

Theorem Arrows_determined_by_transform (A B : ArrowTransform) :
  Arrows_to_Transform A ≈ Arrows_to_Transform B → A ≈ B.
Proof.
  intros H c c' f.
  simpl in H.
  rewrite (τ_arr_from_left A f).
  rewrite (τ_arr_from_left B f).
  now rewrite (H c).
Qed.

Theorem Arrows_unique_transform (A : ArrowTransform) (N : S ⟹ T) :
  Transform_to_Arrows N ≈ A → N ≈ Arrows_to_Transform A.
Proof.
  intros H c.
  simpl.
  rewrite <- (H c c (id[c])).
  simpl.
  rewrite fmap_id.
  now rewrite id_right.
Qed.

Theorem Transform_unique_arrows (N : S ⟹ T) (A : ArrowTransform) :
  Arrows_to_Transform A ≈ N → A ≈ Transform_to_Arrows N.
Proof.
  intros H c c' f.
  simpl.
  rewrite (τ_arr_from_right A f).
  now rewrite (H c').
Qed.

(*
   本节说明同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Transform_Arrows_iso :
  @Isomorphism Sets {| carrier := S ⟹ T |} {| carrier := ArrowTransform |}.
Proof.
  unshelve econstructor.
  - (* to: a transformation to its arrow family; the setoid-map obligation
       is discharged by [Transform_to_Arrows_respects] *)
    simpl.
    unshelve refine {| morphism := Transform_to_Arrows |}.
  - (* from: an arrow family to the transformation on the identities *)
    simpl.
    unshelve refine {| morphism := Arrows_to_Transform |}.
  - (* to ∘ from ≈ id, pointwise *)
    intros A.
    apply Arrows_to_Transform_to_Arrows.
  - (* from ∘ to ≈ id, pointwise *)
    intros N.
    apply Transform_to_Arrows_to_Transform.
Defined.

End ArrowTransform.

Arguments ArrowTransform {C D} S T.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Transform_to_Arrows_nat_id `(F : C ⟶ D) {c c' : C} (f : c ~> c') :
  τ_arr (Transform_to_Arrows (@nat_id C D F)) f ≈ fmap[F] f.
Proof.
  simpl.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* Non-triviality in general: distinct transformations have distinct arrow
   families.  This is [Transform_determined_by_arrows] contraposed, and a
   concrete pair of witnesses appears below. *)

Corollary distinct_Transforms_distinct_Arrows {C D : Category}
      {S T : C ⟶ D} (N M : S ⟹ T) :
  ¬ (N ≈ M) → ¬ (Transform_to_Arrows N ≈ Transform_to_Arrows M).
Proof.
  intros H HA.
  apply H.
  now apply Transform_determined_by_arrows.
Qed.

(* The remaining sections need two concrete small categories and the
   constant functors between them; the requires are placed here to keep
   the development above free of them. *)

Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Parallel.

(* The functorial action of a constant functor is an identity; every
   computation in the two sections below reduces through this lemma. *)

Lemma diagonal_fmap {C J : Category} (x : C) {c c' : J} (f : c ~> c') :
  fmap[Δ[J](x)] f ≈ id[x].
Proof. reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition parX : Parallel := ParX.
Definition parY : Parallel := ParY.

Definition par_one : parX ~> parY := (true; ParOne).
Definition par_two : parX ~> parY := (false; ParTwo).

Lemma par_one_par_two_distinct : ¬ (par_one ≈ par_two).
Proof.
  intros H.
  unfold par_one, par_two in H.
  simpl in H.
  discriminate.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Local Notation ConstX := (Δ[_2](parX)).
Local Notation ConstY := (Δ[_2](parY)).

Section ConcreteArrows.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition const_arrows (h : parX ~> parY) : ArrowTransform ConstX ConstY.
Proof.
  unshelve refine
    (@Build_ArrowTransform _2 Parallel ConstX ConstY (fun c c' f => h) _ _).
  - intros c c' c'' g f.
    now rewrite diagonal_fmap, id_left.
  - intros c c' c'' g f.
    now rewrite diagonal_fmap, id_right.
Defined.

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma const_arrows_transform (h : parX ~> parY) (c : _2) :
  transform[Arrows_to_Transform (const_arrows h)] c ≈ h.
Proof. reflexivity. Qed.

Lemma const_arrows_roundtrip (h : parX ~> parY) {c c' : _2} (f : c ~> c') :
  τ_arr (Transform_to_Arrows (Arrows_to_Transform (const_arrows h))) f ≈ h.
Proof.
  rewrite (Arrows_to_Transform_to_Arrows (const_arrows h) c c' f).
  reflexivity.
Qed.

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma const_arrows_distinct :
  ¬ (const_arrows par_one ≈ const_arrows par_two).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  exact (H TwoX TwoY TwoXY).
Qed.

Lemma const_transforms_distinct :
  ¬ (Arrows_to_Transform (const_arrows par_one)
       ≈ Arrows_to_Transform (const_arrows par_two)).
Proof.
  intros H.
  apply const_arrows_distinct.
  now apply Arrows_determined_by_transform.
Qed.

End ConcreteArrows.

Section Independence.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dom_family {c c' : _2} (f : c ~> c') : ConstX c ~> ConstY c' :=
  match c with
  | TwoX => par_one
  | TwoY => par_two
  end.

Definition cod_family {c c' : _2} (f : c ~> c') : ConstX c ~> ConstY c' :=
  match c' with
  | TwoX => par_one
  | TwoY => par_two
  end.

(* Both families respect ≈, ignoring their argument outright. *)

Lemma dom_family_respects {c c' : _2} :
  Proper (equiv ==> equiv) (@dom_family c c').
Proof. intros f g Hf; reflexivity. Qed.

Lemma cod_family_respects {c c' : _2} :
  Proper (equiv ==> equiv) (@cod_family c c').
Proof. intros f g Hf; reflexivity. Qed.

(* Reading the domain satisfies the left law and refutes the right one. *)

Lemma dom_family_left {c c' c'' : _2} (g : c' ~> c'') (f : c ~> c') :
  fmap[ConstY] g ∘ dom_family f ≈ dom_family (g ∘ f).
Proof. now rewrite diagonal_fmap, id_left. Qed.

Lemma dom_family_not_right :
  ¬ (∀ (c c' c'' : _2) (g : c' ~> c'') (f : c ~> c'),
       dom_family (g ∘ f) ≈ dom_family g ∘ fmap[ConstX] f).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  rewrite <- (id_right par_two).
  exact (H TwoX TwoY TwoY (@id _2 TwoY) TwoXY).
Qed.

(* Reading the codomain satisfies the right law and refutes the left one. *)

Lemma cod_family_right {c c' c'' : _2} (g : c' ~> c'') (f : c ~> c') :
  cod_family (g ∘ f) ≈ cod_family g ∘ fmap[ConstX] f.
Proof. now rewrite diagonal_fmap, id_right. Qed.

Lemma cod_family_not_left :
  ¬ (∀ (c c' c'' : _2) (g : c' ~> c'') (f : c ~> c'),
       fmap[ConstY] g ∘ cod_family f ≈ cod_family (g ∘ f)).
Proof.
  intros H.
  apply par_one_par_two_distinct.
  rewrite <- (id_left par_one).
  exact (H TwoX TwoX TwoY TwoXY (@id _2 TwoX)).
Qed.

End Independence.

(* ------------------------------------------------------------------------ *)
(** ** Neither law alone implies respectfulness *)

(*
   本节说明 Arrows 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition BlurRight : Category := {|
  obj     := unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => true;
  compose := fun _ _ _ g f => f          (* right-zero: the composite is f *)
|}.

Program Definition BlurLeft : Category := {|
  obj     := unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun _ => true;
  compose := fun _ _ _ g f => g          (* left-zero: the composite is g *)
|}.

(* The separating pair is the same one the independence countermodels use:
   the two distinct arrows ParX ~> ParY of the parallel-pair category. *)
Lemma par_one_two_distinct : ¬ (par_one ≈ par_two).
Proof. intros H; unfold par_one, par_two in H; simpl in H; discriminate. Qed.

Section LeftLawAlone.

Notation SR := (Δ[BlurRight](parX)).
Notation TR := (Δ[BlurRight](parY)).

Definition blur_right_family {c c' : BlurRight} (f : c ~> c') : SR c ~> TR c' :=
  if f then par_one else par_two.

(* It satisfies the LEFT splice law in full generality: with right-zero
   composition the law reads τ f ≈ τ f. *)
Lemma blur_right_left {c c' c'' : BlurRight} (g : c' ~> c'') (f : c ~> c') :
  fmap[TR] g ∘ blur_right_family f ≈ blur_right_family (g ∘ f).
Proof. apply id_left. Qed.

(* Yet it is not respectful: the two arrows are `≈` and their images are
   not.  So the LEFT law alone does not imply respectfulness. *)
Theorem left_law_alone_gives_no_respect :
  ¬ (∀ c c' : BlurRight, Proper (equiv ==> equiv) (@blur_right_family c c')).
Proof.
  intros H.
  apply par_one_two_distinct.
  exact (H tt tt true false I).
Qed.

End LeftLawAlone.

Section RightLawAlone.

Notation SL := (Δ[BlurLeft](parX)).
Notation TL := (Δ[BlurLeft](parY)).

Definition blur_left_family {c c' : BlurLeft} (f : c ~> c') : SL c ~> TL c' :=
  if f then par_one else par_two.

(* The mirror image: with left-zero composition the RIGHT law reads
   τ g ≈ τ g. *)
Lemma blur_left_right {c c' c'' : BlurLeft} (g : c' ~> c'') (f : c ~> c') :
  blur_left_family (g ∘ f) ≈ blur_left_family g ∘ fmap[SL] f.
Proof. symmetry; apply id_right. Qed.

Theorem right_law_alone_gives_no_respect :
  ¬ (∀ c c' : BlurLeft, Proper (equiv ==> equiv) (@blur_left_family c c')).
Proof.
  intros H.
  apply par_one_two_distinct.
  exact (H tt tt true false I).
Qed.

End RightLawAlone.

(* The countermodels are non-degenerate in the way that matters: the two
   arrows really are identified by the setoid, and really are distinguished
   by the family. *)
Example blur_arrows_equivalent :
  (true : @hom BlurRight tt tt) ≈ (false : @hom BlurRight tt tt).
Proof. exact I. Qed.

Example blur_family_separates :
  blur_right_family (c:=tt) (c':=tt) true
    <> blur_right_family (c:=tt) (c':=tt) false.
Proof. simpl; unfold par_one, par_two; discriminate. Qed.
