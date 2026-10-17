Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

(** The 范畴 elements Sets-valued 函子, projection. （已译） *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_elements

   本文件给出泛元素相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Elements.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* The 函子 laws K, read at element. A Sets hom equation a
 pointwise family, so it must instantiated at element before it
 can used ordinary 等价. （已译） *)

Lemma elements_id_cond {d : D} (x : K d) : fmap[K] id x ≈ x.
Proof. exact (@fmap_id _ _ K _ x). Qed.

Lemma elements_comp_cond {c d e : D} {x : K c} {y : K d} {z : K e}
      (u : d ~> e) (v : c ~> d) :
  fmap[K] v x ≈ y → fmap[K] u y ≈ z → fmap[K] (u ∘ v) x ≈ z.
Proof.
  intros Hv Hu.
  transitivity (fmap[K] u (fmap[K] v x)).
  - exact (@fmap_comp _ _ K _ _ _ u v x).
  - now rewrite Hv.
Qed.

Lemma elements_respects_cond {c d : D} {x : K c} (f g : c ~> d) :
  f ≈ g → fmap[K] f x ≈ fmap[K] g x.
Proof. intro Hfg; exact (@fmap_respects _ _ K _ _ f g Hfg x). Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Elements : Category := {|
  obj := ∃ d : D, K d;
  hom := fun x y => ∃ f : `1 x ~{D}~> `1 y, fmap[K] f (`2 x) ≈ `2 y;
  homset := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id := fun x => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. apply elements_id_cond. Qed.
Next Obligation. eapply elements_comp_cond; eassumption. Qed.

(* The projection, taking (d, x) d 态射 first
 component. （已译） *)

Program Definition Elements_proj : Elements ⟶ D := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Instance Elements_proj_Faithful : Faithful Elements_proj.

(* Faithfulness definitional under hom-setoid chosen above: the
 injectivity statement 恒等 implication, witness
 records fact readers instance. （已译） *)

Definition Elements_proj_faithful_definitional
  {x y : Elements} (f g : x ~{Elements}~> y) :
  fmap[Elements_proj] f ≈ fmap[Elements_proj] g → f ≈ g :=
  fun H => H.

(* The chosen lift base 态射 at element, definitional
 check projection returns base 态射. （已译） *)

Program Definition Elements_lift {d d' : D} (x : K d) (f : d ~> d') :
  ((d; x) : Elements) ~{Elements}~> (d'; fmap[K] f x) := (f; _).

Lemma Elements_lift_over {d d' : D} (x : K d) (f : d ~> d') :
  fmap[Elements_proj] (Elements_lift x f) ≈ f.
Proof. reflexivity. Qed.

(* The comma presentation. [SetsOne] singleton Sets_Terminal,
 [=(SetsOne)] 常值 函子 1 ⟶ Sets at it. （已译） *)

Definition SetsOne : Sets := @terminal_obj Sets Sets_Terminal.

Definition ElementsComma : Category := =(SetsOne) ↓ K.

Program Definition Elements_to_Comma : Elements ⟶ ElementsComma := {|
  fobj := fun x => ((ttt, `1 x); {| morphism := fun _ => `2 x |});
  fmap := fun _ _ f => ((ttt, `1 f); _)
|}.

Program Definition Elements_from_Comma : ElementsComma ⟶ Elements := {|
  fobj := fun x => (snd `1 x; `2 x ttt);
  fmap := fun _ _ f => (snd `1 f; _)
|}.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Elements_Comma : Elements ≅[Cat] ElementsComma.
Proof.
  isomorphism; simpl; intros.
  - apply Elements_to_Comma.
  - apply Elements_from_Comma.
  - constructive.
    + exists (ttt, id); abstract (intros u; destruct u; symmetry;
                                  apply elements_id_cond).
    + exists (ttt, id); abstract (intros u; destruct u; symmetry;
                                  apply elements_id_cond).
    + abstract (split; [reflexivity | cat]).
    + abstract (split; [reflexivity | cat]).
    + abstract (split; [reflexivity |
                        simpl; rewrite id_right, id_left; reflexivity]).
  - constructive.
    + exists id; abstract (apply elements_id_cond).
    + exists id; abstract (apply elements_id_cond).
    + abstract cat.
    + abstract cat.
    + abstract (simpl; rewrite id_right, id_left; reflexivity).
Qed.

End Elements.

(* 相关说明。 （已译） *)
#[export] Existing Instance Elements_proj_Faithful.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.

Section Elements_Comma_Projection.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Elements_proj_comma_iso :
  comma_proj2 ◯ Elements_to_Comma K ≅[[Elements K, D]] Elements_proj K := {|
  to   := {| transform := fun _ => id |};
  from := {| transform := fun _ => id |}
|}.

End Elements_Comma_Projection.

Section Presheaf_Elements.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* 相关说明。 （已译） *)

Definition PElements : Category := (Elements P)^op.

(* 相关说明。 （已译） *)

Lemma PElements_hom (x y : PElements) :
  (x ~{PElements}~> y) = (∃ f : `1 x ~{C}~> `1 y, fmap[P] f (`2 y) ≈ `2 x).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

Program Definition PElements_proj : PElements ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

End Presheaf_Elements.
