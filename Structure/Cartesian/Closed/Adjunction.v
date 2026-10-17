Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The currying adjunction (- × S) ⊣ (-)^S, and evaluation as its counit *)

(*
   nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/representable+functor
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book: Riehl, "Category Theory in Context", Dover 2016; §2.1

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/exponential+object
   nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book: Riehl, "Category Theory in Context", Dover 2016
   Paper: Lawvere, "Adjointness in Foundations", Dialectica 23(3/4), 1969;

   本节说明伴随、自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CurryAdjunction.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

Context (S : C).

(* The left adjoint (- × S) : C ⟶ C. On arrows it is [first f] = f × id[S],
   so the functor laws are [first_id] and [first_comp]. *)
Program Definition Prod_Functor : C ⟶ C := {|
  fobj := fun x => x × S;
  fmap := fun _ _ f => first f
|}.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Exp_Functor : C ⟶ C := {|
  fobj := fun x => x ^ S;
  fmap := fun _ _ f => curry (f ∘ eval)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite <- comp_assoc; apply curry_comp. Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eval_natural {x y : C} (f : x ~> y) :
  f ∘ eval ≈ eval ∘ fmap[Prod_Functor] (fmap[Exp_Functor] f).
Proof. simpl; now rewrite ump_exponents. Qed.

(*
   本节说明伴随、自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition eval_Transform : Prod_Functor ◯ Exp_Functor ⟹ Id[C] := {|
  transform := fun _ => eval
|}.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Curry_Adjunction : Prod_Functor ⊣ Exp_Functor := {|
  adj := fun _ _ =>
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
|}.
(* to_adj_nat_l: curry (f ∘ first g) ≈ curry f ∘ g *)
Next Obligation. symmetry; apply curry_comp_l. Qed.
(* to_adj_nat_r: curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g *)
Next Obligation. apply curry_comp. Qed.
(* from_adj_nat_l: uncurry (f ∘ g) ≈ uncurry f ∘ first g *)
Next Obligation. apply uncurry_comp. Qed.
(* from_adj_nat_r: uncurry (curry (f ∘ eval) ∘ g) ≈ f ∘ uncurry g *)
Next Obligation. symmetry; apply uncurry_comp_r. Qed.

(*
   本节说明伴随、笛卡尔、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary curry_adj_counit {x : C} :
  @counit _ _ _ _ Curry_Adjunction x ≈ eval.
Proof. reflexivity. Qed.

(* Dually the unit is [curry id] : x ~> (x × S)^S, again convertible, not
   merely ≈-equal. *)
Corollary curry_adj_unit {x : C} :
  @unit _ _ _ _ Curry_Adjunction x ≈ curry id.
Proof. reflexivity. Qed.

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary curry_adj_to {x y : C} (f : x × S ~> y) :
  to (@adj _ _ _ _ Curry_Adjunction x y) f ≈ curry f.
Proof. reflexivity. Qed.

Corollary curry_adj_from {x y : C} (g : x ~> y ^ S) :
  from (@adj _ _ _ _ Curry_Adjunction x y) g ≈ uncurry g.
Proof. reflexivity. Qed.

(* The two triangle identities, obtained from the general theory of
   Theory/Adjunction.v rather than re-proved. The first, ε ∘ F η ≈ id, reads
   eval ∘ (curry id × id[S]) ≈ id on x × S. *)
Corollary curry_adj_triangle_left {x : C} :
  eval ∘ first (curry (id[x × S])) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ Curry_Adjunction x). Qed.

(* The second, U ε ∘ η ≈ id, on x^S; here [curry (eval ∘ eval)] is
   [fmap[Exp_Functor]] applied to the counit [eval]. *)
Corollary curry_adj_triangle_right {x : C} :
  curry (eval ∘ eval) ∘ curry (id[x^S × S]) ≈ id.
Proof. exact (@fmap_counit_unit _ _ _ _ Curry_Adjunction x). Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Exp_Functor_InternalHom {x y : C} (f : x ~> y) :
  fmap[Exp_Functor] f
    ≈ @fmap _ _ (InternalHomFunctor C) (S, x) (S, y) (id[S], f).
Proof. simpl; rewrite second_id, id_right; reflexivity. Qed.

End CurryAdjunction.

Arguments Prod_Functor {C _} S.
Arguments Exp_Functor {C _ _} S.

Section CurryRepresentable.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

Context (S B : C).

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Curry_Presheaf : C^op ⟶ Sets := [Hom ─, B] ◯ (Prod_Functor S)^op.

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Curry_Representation : [Hom ─, B^S] ≅ Curry_Presheaf := {|
  to   := {| transform := fun _ => {| morphism := uncurry |} |};
  from := {| transform := fun _ => {| morphism := curry |} |}
|}.
Next Obligation. symmetry; apply uncurry_comp. Qed.
Next Obligation. apply uncurry_comp. Qed.
Next Obligation. apply curry_comp_l. Qed.
Next Obligation. symmetry; apply curry_comp_l. Qed.
Next Obligation. rewrite first_id, id_right; apply uncurry_curry. Qed.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Curry_Representable : Representable Curry_Presheaf := {|
  repr_obj := B ^ S;
  represented := Curry_Representation
|}.

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Curry_repr_universal :
  to Curry_Representation (B ^ S) id ≈ eval.
Proof. reflexivity. Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Curry_Presheaf_fmap {x y : C} (f : y ~> x) (g : x × S ~> B) :
  fmap[Curry_Presheaf] f g ≈ g ∘ first f.
Proof. reflexivity. Qed.

End CurryRepresentable.

Arguments Curry_Presheaf {C _} S B.
Arguments Curry_Representation {C _ _} S B.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Curry_Representable_resolves
  {C : Category} `{@Cartesian C} `{@Closed C _} (S B : C) :
  Representable (Curry_Presheaf S B) := _.

Example Curry_repr_obj
  {C : Category} `{@Cartesian C} `{@Closed C _} (S B : C) :
  Representable_to_obj _ (Curry_Representable S B) = (B ^ S)%object.
Proof. reflexivity. Qed.
