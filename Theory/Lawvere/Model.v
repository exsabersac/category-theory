Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.

Generalizable All Variables.

(** * Models of a Lawvere theory *)

(*
 nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   本文件给出 Lawvere 理论的模型。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Model.

Context (T : LawvereTheory).
Context (C : Category).
Context `{@Cartesian C}.
Context `{@Terminal C}.

Record Model := {
  model_fun : @law_cat T ⟶ C;

  model_cartesian :
    @CartesianFunctor (@law_cat T) C model_fun (@law_cartesian T) _;

  model_terminal :
    @TerminalFunctor (@law_cat T) C model_fun (@law_terminal T) _
}.

(*
   * ** The 范畴 of models

   本节说明相关定义、性质与动机。 The full subcategory 函子 范畴 [law_cat T, C] whose 对象 carry both preservation witnesses.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Models_sub : Subcategory (@Fun (@law_cat T) C) :=
  @Build_Subcategory (@Fun (@law_cat T) C)
    (fun F : @law_cat T ⟶ C =>
       (@CartesianFunctor (@law_cat T) C F (@law_cartesian T) _ *
        @TerminalFunctor (@law_cat T) C F (@law_terminal T) _)%type)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Models : Category := Sub (@Fun (@law_cat T) C) Models_sub.

(*
   本节说明相关定义、性质与动机。 * ** Bridges between record subcategory presentations. A [Model] packs into 对象 [Models], every 对象 [Models] unpacks [Model];

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Model_pack (M : Model) : Models :=
  (model_fun M; (model_cartesian M, model_terminal M)).

Definition Model_unpack (x : Models) : Model :=
  {| model_fun       := `1 x
   ; model_cartesian := fst `2 x
   ; model_terminal  := snd `2 x |}.

(*
   本节说明相关定义、性质与动机。 * The two presentations are mutually inverse nose: each round. trip is eta-expansion, discharged case analysis. (Propositional [=] packed OBJECT data — sanctioned case;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Model_unpack_pack (M : Model) : Model_unpack (Model_pack M) = M.
Proof. destruct M; reflexivity. Qed.

Lemma Model_pack_unpack (x : Models) : Model_pack (Model_unpack x) = x.
Proof. destruct x as [F [HC HT]]; reflexivity. Qed.

(** ** Morphisms of models are all natural transformations

    [Models_sub] is a full subcategory: every natural transformation
    between the underlying functors of two models is a morphism of
    models (the [shom] witness is [I]). *)

Definition Models_Full :
  Construction.Subcategory.Full (@Fun (@law_cat T) C) Models_sub :=
  fun _ _ _ _ _ => I.

(** Concretely: any natural transformation between the underlying
    functors of two models lifts to a morphism in [Models], and it is
    sent back to itself by the (faithful) inclusion. *)

Definition Model_hom_of_transform (x y : Models) (f : `1 x ⟹ `1 y) :
  x ~{ Models }~> y := (f; I).

Lemma Model_hom_of_transform_incl (x y : Models) (f : `1 x ⟹ `1 y) :
  fmap[Incl _ Models_sub] (Model_hom_of_transform x y f)
    ≈ (f : `1 x ~{ @Fun (@law_cat T) C }~> `1 y).
Proof. simpl; intros; reflexivity. Qed.

End Model.
