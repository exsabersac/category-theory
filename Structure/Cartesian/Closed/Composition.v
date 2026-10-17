Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.Coend.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.

Generalizable All Variables.

(** * Internal composition in a cartesian closed category *)

(*
   nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
   nLab: https://ncatlab.org/nlab/show/dinatural+transformation
   nLab: https://ncatlab.org/nlab/show/enriched+category

   本文件给出闭结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Composition.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(** ** The composition and identity morphisms *)

(* Mac Lane's c^b × b^a ~> c^a: transpose the double evaluation. *)
Definition internal_compose {a b c : C} : c^b × b^a ~> c^a :=
  curry (eval ∘ second eval ∘ to prod_assoc).

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Arguments internal_compose : simpl never.

(* The three exponentials, pinned in their [exponent_obj] spelling, so that
   the argument order of the header's notation note is machine-checked. *)
Example internal_compose_obj (a b c : C) :
  (c^b × b^a ~{C}~> c^a)
    = (exponent_obj b c × exponent_obj a b ~{C}~> exponent_obj a c)
  := eq_refl.

(** ** The beta laws *)

Lemma uncurry_internal_compose_raw {a b c : C} :
  uncurry (@internal_compose a b c)
    ≈ eval ∘ second eval ∘ to prod_assoc.
Proof. apply uncurry_curry. Qed.

Lemma eval_internal_compose {a b c : C} :
  eval ∘ first (@internal_compose a b c)
    ≈ eval ∘ second eval ∘ to prod_assoc.
Proof. rewrite eval_first; apply uncurry_internal_compose_raw. Qed.

(*
   本节说明 Composition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma uncurry_internal_compose {w a b c : C}
      (h : w ~> c^b) (k : w ~> b^a) :
  uncurry (internal_compose ∘ (h △ k))
    ≈ uncurry h ∘ (exl △ uncurry k).
Proof.
  rewrite uncurry_comp.
  rewrite uncurry_internal_compose_raw.
  rewrite <- !eval_first.
  unfork.
Qed.

(*
   本节说明 Composition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma eval_internal_compose_fork {w a b c : C}
      (g : w ~> c^b × b^a) (k : w ~> a) :
  eval ∘ ((internal_compose ∘ g) △ k)
    ≈ eval ∘ ((exl ∘ g) △ (eval ∘ ((exr ∘ g) △ k))).
Proof.
  unfold internal_compose.
  rewrite eval_curry.
  rewrite <- !comp_assoc.
  unfork.
Qed.

Context `{@Terminal C}.

(* Mac Lane's identity arrow of the internal category: 1 ~> x^x. *)
Definition internal_id {x : C} : 1 ~> x^x := curry exr.

Arguments internal_id : simpl never.

Lemma uncurry_internal_id {x : C} :
  uncurry (@internal_id x) ≈ exr.
Proof. apply uncurry_curry. Qed.

Lemma eval_internal_id_fork {w x : C} (g : w ~> 1) (k : w ~> x) :
  eval ∘ ((internal_id ∘ g) △ k) ≈ k.
Proof.
  unfold internal_id.
  rewrite eval_curry.
  now rewrite exr_fork.
Qed.

(** ** The unit laws *)

(* [1 × y^x ~> y^x]: composing with the internal identity on the left is
   the projection, which is [to unit_left] over [CC_Monoidal]. *)
Theorem internal_compose_id_left {x y : C} :
  @internal_compose x y y ∘ split internal_id id ≈ exr.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite uncurry_internal_compose.
  rewrite (uncurry_comp (@internal_id y) exl).
  rewrite uncurry_internal_id.
  rewrite <- !eval_first.
  unfork.
  rewrite !exr_fork.
  now rewrite id_left.
Qed.

(* [y^x × 1 ~> y^x]: composing with the internal identity on the right is
   the other projection, which is [to unit_right] over [CC_Monoidal]. *)
Theorem internal_compose_id_right {x y : C} :
  @internal_compose x x y ∘ split id internal_id ≈ exl.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite uncurry_internal_compose.
  rewrite (uncurry_comp (@internal_id x) exr).
  rewrite uncurry_internal_id.
  rewrite <- !eval_first.
  unfork.
  rewrite !exr_fork.
  cat.
Qed.

(** ** Associativity *)

(* The two projections of the associator, in the composed shape the fork
   algebra below actually meets. *)
Lemma exl_prod_assoc_r {v a b c : C} (h : v ~> (a × b) × c) :
  exl ∘ (to (@prod_assoc C _ a b c) ∘ h) ≈ exl ∘ (exl ∘ h).
Proof. rewrite !comp_assoc; simpl; now rewrite exl_fork. Qed.

Lemma exr_prod_assoc_r {v a b c : C} (h : v ~> (a × b) × c) :
  exr ∘ (to (@prod_assoc C _ a b c) ∘ h)
    ≈ (exr ∘ (exl ∘ h)) △ (exr ∘ h).
Proof.
  rewrite comp_assoc; simpl; rewrite exr_fork.
  rewrite <- fork_comp.
  now rewrite !comp_assoc.
Qed.

(* Mac Lane's "prove it (like composition) associative", in exactly the
   shape [ecompose_assoc] demands: the associator on the right. *)
Theorem internal_compose_assoc {x y z w : C} :
  @internal_compose x y w ∘ split internal_compose id
    ≈ @internal_compose x z w ∘ split id internal_compose
        ∘ to prod_assoc.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite <- !eval_first.
  unfold first.
  rewrite <- !comp_assoc.
  rewrite !eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !id_left.
  rewrite !exl_prod_assoc_r, !exr_prod_assoc_r.
  rewrite !eval_internal_compose_fork.
  rewrite !exl_fork, !exr_fork.
  reflexivity.
Qed.

(** ** Naturality in [a] and in [c] *)

(* The companion of [eval_internal_compose_fork] for the internal hom's own
   action: it strips one [ihom] from inside an evaluation. *)
Lemma eval_ihom_fork {v a b c d : C} (f : b ~> a) (h : c ~> d)
      (g : v ~> c^a) (m : v ~> b) :
  eval ∘ ((ihom f h ∘ g) △ m) ≈ h ∘ (eval ∘ (g △ (f ∘ m))).
Proof.
  unfold ihom.
  rewrite eval_curry.
  rewrite <- !comp_assoc.
  unfork.
Qed.

(* Naturality in the base [c], at fixed [a] and [b]: both sides are
   morphisms [c^b × b^a ~> c'^a]. *)
Theorem internal_compose_natural_c {a b c c' : C} (g : c ~> c') :
  ihom id g ∘ @internal_compose a b c
    ≈ @internal_compose a b c' ∘ first (ihom id g).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite eval_internal_compose_fork.
  rewrite eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(* Naturality in the exponent [a], at fixed [b] and [c]: the variable is
   CONTRAVARIANT, so the square runs against an arrow [f : a' ~> a] and
   both sides are morphisms [c^b × b^a ~> c^a']. *)
Theorem internal_compose_natural_a {a a' b c : C} (f : a' ~> a) :
  ihom f id ∘ @internal_compose a b c
    ≈ @internal_compose a' b c ∘ second (ihom f id).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first, second.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite eval_internal_compose_fork.
  rewrite eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition expBase_obj (a c : C) : C := c^a.

Definition expBase_map (a : C) {c c' : C} (g : c ~> c') :
  expBase_obj a c ~> expBase_obj a c' := ihom id g.

Program Definition ExpBase (a : C) : C ⟶ C := {|
  fobj := expBase_obj a;
  fmap := fun _ _ g => expBase_map a g
|}.
Next Obligation.
  proper; unfold expBase_map, expBase_obj; now rewrites.
Qed.
Next Obligation. unfold expBase_map, expBase_obj; apply ihom_id. Qed.
Next Obligation.
  unfold expBase_map, expBase_obj.
  rewrite ihom_comp; now rewrite id_left.
Qed.

Definition composeSrcC_obj (a b c : C) : C := c^b × b^a.

Definition composeSrcC_map (a b : C) {c c' : C} (g : c ~> c') :
  composeSrcC_obj a b c ~> composeSrcC_obj a b c' :=
  first (ihom id g).

Program Definition ComposeSrcC (a b : C) : C ⟶ C := {|
  fobj := composeSrcC_obj a b;
  fmap := fun _ _ g => composeSrcC_map a b g
|}.
Next Obligation.
  proper; unfold composeSrcC_map, composeSrcC_obj; now rewrites.
Qed.
Next Obligation.
  unfold composeSrcC_map, composeSrcC_obj.
  rewrite ihom_id; apply first_id.
Qed.
Next Obligation.
  unfold composeSrcC_map, composeSrcC_obj.
  rewrite <- first_comp, ihom_comp; now rewrite id_left.
Qed.

Definition expExp_obj (c : C) (a : C^op) : C := c^(opobj a).

Definition expExp_map (c : C) {a a' : C^op} (f : a ~> a') :
  expExp_obj c a ~> expExp_obj c a' := ihom (oparr f) id.

Program Definition ExpExp (c : C) : C^op ⟶ C := {|
  fobj := expExp_obj c;
  fmap := fun _ _ f => expExp_map c f
|}.
Next Obligation.
  proper; unfold expExp_map, expExp_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold expExp_map, expExp_obj, oparr; apply ihom_id.
Qed.
Next Obligation.
  unfold expExp_map, expExp_obj, oparr.
  rewrite ihom_comp; now rewrite id_left.
Qed.

Definition composeSrcA_obj (b c : C) (a : C^op) : C :=
  c^b × b^(opobj a).

Definition composeSrcA_map (b c : C) {a a' : C^op} (f : a ~> a') :
  composeSrcA_obj b c a ~> composeSrcA_obj b c a' :=
  second (ihom (oparr f) id).

Program Definition ComposeSrcA (b c : C) : C^op ⟶ C := {|
  fobj := composeSrcA_obj b c;
  fmap := fun _ _ f => composeSrcA_map b c f
|}.
Next Obligation.
  proper; unfold composeSrcA_map, composeSrcA_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold composeSrcA_map, composeSrcA_obj, oparr.
  rewrite ihom_id; apply second_id.
Qed.
Next Obligation.
  unfold composeSrcA_map, composeSrcA_obj, oparr.
  rewrite <- second_comp, ihom_comp; now rewrite id_left.
Qed.

(* The four object actions read back on the nose, which is what makes the
   two transformations typecheck with no transport -- and what the hazard
   above would have destroyed. *)
Example expBase_fobj (a c : C) : fobj[ExpBase a] c = c^a := eq_refl.

Example composeSrcC_fobj (a b c : C) :
  fobj[ComposeSrcC a b] c = c^b × b^a := eq_refl.

Example expExp_fobj (c : C) (a : C^op) :
  fobj[ExpExp c] a = c^(opobj a) := eq_refl.

Example composeSrcA_fobj (b c : C) (a : C^op) :
  fobj[ComposeSrcA b c] a = c^b × b^(opobj a) := eq_refl.

(* Mac Lane's "natural transformation", in [c]. *)
Definition compose_Transform_c (a b : C) :
  ComposeSrcC a b ⟹ ExpBase a :=
  @Build_Transform' C C (ComposeSrcC a b) (ExpBase a)
    (fun c => @internal_compose a b c)
    (fun c c' g => @internal_compose_natural_c a b c c' g).

(* And in [a], where the variable is contravariant. *)
Definition compose_Transform_a (b c : C) :
  ComposeSrcA b c ⟹ ExpExp c :=
  @Build_Transform' (C^op) C (ComposeSrcA b c) (ExpExp c)
    (fun a => @internal_compose a b c)
    (fun a a' f => @internal_compose_natural_a a a' b c f).

(* The components ARE [internal_compose], on the nose. *)
Example compose_Transform_c_component (a b c : C) :
  transform (compose_Transform_c a b) c = @internal_compose a b c
  := eq_refl.

Example compose_Transform_a_component (a b c : C) :
  transform (compose_Transform_a b c) a = @internal_compose a b c
  := eq_refl.

(** ** Dinaturality in [b] *)

(*
   本节说明自然变换、函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem internal_compose_dinatural {a c b1 b2 : C} (f : b1 ~> b2) :
  @internal_compose a b1 c ∘ split (ihom f id) id
    ≈ @internal_compose a b2 c ∘ split id (ihom id f).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first, split.
  rewrite <- !comp_assoc.
  rewrite !eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !id_left.
  rewrite !eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(*
   本节说明 Composition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition composeB_obj (a c : C) (p : C^op ∏ C) : C :=
  c^(opobj (fst p)) × (snd p)^a.

Definition composeB_map (a c : C) {x y : C^op ∏ C} (m : x ~> y) :
  composeB_obj a c x ~> composeB_obj a c y :=
  split (ihom (oparr (fst m)) id) (ihom id (snd m)).

Program Definition ComposeB (a c : C) : C^op ∏ C ⟶ C := {|
  fobj := composeB_obj a c;
  fmap := fun _ _ m => composeB_map a c m
|}.
Next Obligation.
  proper; unfold composeB_map, composeB_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold composeB_map, composeB_obj, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold composeB_map, composeB_obj, oparr; simpl.
  now rewrite split_comp, !ihom_comp, !id_left.
Qed.

(* The constant family [internal_compose] satisfies the tree's own covariant
   cowedge condition (Structure/Coend.v) at that bifunctor, with apex
   [c^a]. *)
Definition internal_compose_Cowedge_cond (a c : C) :
  @Cowedge_cond C C (ComposeB a c) (c^a)
    (fun x => @internal_compose a x c).
Proof.
  intros x y f.
  simpl; unfold composeB_map, composeB_obj, oparr, op; simpl.
  rewrite !ihom_id.
  apply internal_compose_dinatural.
Defined.

(* ... and therefore assembles into an inhabitant of [Wedge]. *)
Definition internal_compose_Wedge (a c : C) :=
  @covariant_cowedge C C (ComposeB a c) (c^a)
    (fun x => @internal_compose a x c)
    (internal_compose_Cowedge_cond a c).

(** ** A cartesian closed category is enriched over itself *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example assoc_bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example assoc_tensor_is_prod {x y z : C} :
  to (@tensor_assoc C CC_Monoidal x y z) = to (@prod_assoc C _ x y z)
  := eq_refl.

Example assoc_unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Example assoc_unit_right_is_exl {x : C} :
  to (@unit_right C CC_Monoidal x) = exl := eq_refl.

(* The payoff: [C] enriched over itself, with hom-objects the
   exponentials. *)
Program Definition CCC_Enriched : @Enriched C CC_Monoidal := {|
  eobj := obj[C];
  ehom := fun x y => y^x;
  eid := fun x => internal_id;
  ecompose := fun x y z => internal_compose
|}.
Next Obligation. exact internal_compose_id_left. Qed.
Next Obligation. exact internal_compose_id_right. Qed.
Next Obligation. exact internal_compose_assoc. Qed.

End Composition.

(** * Agreement with composition of functions in [Set] *)

(*
   本节说明 Composition 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example sets_internal_compose (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) (t : a) :
  @internal_compose Sets _ _ a b c (g, f) t = g (f t) := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example sets_internal_compose_underlying (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (fun t : a => @internal_compose Sets _ _ a b c (g, f) t)
    = (fun t : a => (g ∘[Sets] f) t) := eq_refl.

Example sets_internal_compose_morphism (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  @internal_compose Sets _ _ a b c (g, f) ≈[Sets] g ∘ f.
Proof. intro t; reflexivity. Qed.

(* And the identity: [internal_id] is the identity function of [Sets]. *)
Example sets_internal_id (x : Sets)
        (u : @terminal_obj Sets Sets_Terminal) (t : x) :
  @internal_id Sets _ _ Sets_Terminal x u t = t := eq_refl.

(* [Sets] is therefore enriched over itself, with hom-objects the function
   setoids. *)
Definition Sets_Enriched : @Enriched Sets CC_Monoidal := CCC_Enriched.
