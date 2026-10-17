Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
   本文件给出 topos 结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

(*
   nLab:      https://ncatlab.org/nlab/show/power+object
   nLab:      https://ncatlab.org/nlab/show/topos
   Wikipedia: https://en.wikipedia.org/wiki/Topos

   本节说明伴随、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ToposPower.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

(** ** (A) The power-object functor *)

(* P := Ω^(−), partial application internal hom at Ω. Its
 contravariance [InternalHomFunctor]'s first 论元. （已译） *)
Definition PowF : C^op ⟶ C := Partial_l (InternalHomFunctor C) Ω.

(* Three readbacks, all on the nose. *)
Example powf_obj (a : C) : fobj[PowF] a = Pow a := eq_refl.

Example powf_obj_exponent (a : C) : fobj[PowF] a = exponent_obj a Ω := eq_refl.

Example powf_map {a b : C} (f : b ~{C}~> a) :
  fmap[PowF] f = curry (id ∘ eval ∘ second f) := eq_refl.

(* * ** (B) [flip] involution, two 复合 laws （已译） *)

(* NEW: no involution 引理 cartesian-closed [flip] existed. （已译） *)
Lemma flip_flip {a b : C} (f : a ~> Ω^b) : flip (flip f) ≈ f.
Proof.
  unfold flip.
  rewrite uncurry_curry, <- comp_assoc, swap_invol, id_right.
  apply curry_uncurry.
Qed.

#[local] Program Instance flip_respects {a b : C} :
  Proper (equiv ==> equiv) (@flip C _ _ a Ω b).
Next Obligation. proper. unfold flip. now rewrites. Qed.

(* Naturality in the SOURCE: precomposition downstairs is P-image
   postcomposition upstairs. *)
Lemma flip_comp {a a' b : C} (f : a ~> Ω^b) (g : a' ~> a) :
  flip (f ∘ g) ≈ fmap[PowF] g ∘ flip f.
Proof.
  unfold flip; simpl.
  rewrite uncurry_comp, curry_comp_l, id_left, <- !comp_assoc,
          <- first_second, !comp_assoc, eval_first, uncurry_curry,
          <- !comp_assoc, swap_second.
  reflexivity.
Qed.

(* Naturality in the EXPONENT: P-image precomposition downstairs is
   postcomposition upstairs. *)
Lemma flip_pow_comp {a x x' : C} (p : a ~> Ω^x') (k : x ~> x') :
  flip (fmap[PowF] k ∘ p) ≈ flip p ∘ k.
Proof.
  apply uncurry_inj.
  unfold flip; simpl.
  rewrite uncurry_curry, uncurry_comp, uncurry_curry, uncurry_comp,
          uncurry_curry, id_left, <- (eval_first p), <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  unfork.
Qed.

(* 相关说明。 （已译） *)

(* [flip] 态射 [Sets], used BOTH legs 同构. （已译） *)
Program Definition flip_mor (a b : C) :
  {| carrier := a ~{C}~> Ω^b ; is_setoid := @homset C a (Ω^b) |}
    ~{Sets}~>
  {| carrier := b ~{C}~> Ω^a ; is_setoid := @homset C b (Ω^a) |} :=
  {| morphism := fun f => flip f |}.
Next Obligation. proper. unfold flip. now rewrites. Qed.

Program Definition pow_aor (a x : C) :
  @Isomorphism Sets
    {| carrier := @hom C a (PowF x); is_setoid := @homset C a (PowF x) |}
    {| carrier := @hom C x (PowF a); is_setoid := @homset C x (PowF a) |} :=
  {| to := flip_mor a x ; from := flip_mor x a |}.
Next Obligation. simpl; apply flip_flip. Qed.
Next Obligation. simpl; apply flip_flip. Qed.

(* Mac Lane §IV.2 定义 2's vocabulary (Adjunction/Right.v): four
 自然性 fields [flip_comp], [flip_pow_comp], [flip_pow_comp],
 [flip_comp], order. （已译） *)
Program Definition pow_self_adjoint : AdjointOnTheRight PowF PowF :=
  {| aor := pow_aor |}.
Next Obligation. apply flip_comp. Qed.
Next Obligation. apply flip_pow_comp. Qed.
Next Obligation. apply flip_pow_comp. Qed.
Next Obligation. apply flip_comp. Qed.

(*
   本节说明伴随、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pow_adjunction :
  @Adjunction (C^op) C (Opposite_Functor PowF) PowF :=
  Adjunction_of_AdjointOnTheRight pow_self_adjoint.

(* 相关说明。 （已译） *)
Example pow_to_adj_is_flip {a x : C} (f : a ~> PowF x) :
  to (@adj (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x a) f
    = flip f := eq_refl.

Example pow_from_adj_is_flip {a x : C} (f : x ~> PowF a) :
  from (@adj (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x a) f
    = flip f := eq_refl.

(* The unit counit self-伴随 right one and
 same map, [flip id] -- classically "singleton singleton"
 Ω^(Ω^x) map. Both readbacks nose. （已译） *)
Example pow_unit_is_flip_id {x : C} :
  @unit (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x
    = flip (@id C (Pow x)) := eq_refl.

Example pow_counit_is_flip_id {x : C} :
  @counit (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x
    = flip (@id C (Pow x)) := eq_refl.

(* * ** (D) The reduction 引理 precomposition （已译） *)

(* 相关说明。 （已译） *)
Lemma pow_precompose {z u x : C} (m : u ~> x) (h : z × x ~> Ω) :
  fmap[PowF] m ∘ curry h ≈ curry (h ∘ second m).
Proof.
  simpl.
  rewrite curry_comp_l, id_left, <- !comp_assoc, <- first_second,
          !comp_assoc, eval_first, uncurry_curry.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Power 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example relations_iso_to_is_curry_char {a b : C} (s : SubObj (a × b)) :
  to (relations_iso a b) s = curry (char_sub s) := eq_refl.

Example relations_iso_from_is_reindex {a b : C} (f : a ~> Pow b) :
  from (relations_iso a b) f = sub_reindex (uncurry f) truth_subobject
  := eq_refl.

(* The issue's transposition: read f : ~> Pow b subobject × b,
 turn 关系 round [swap], read it back b ~> Pow a. （已译） *)
Definition pow_relations {a b : C} (f : a ~> Pow b) : b ~> Pow a :=
  to (relations_iso b a) (sub_reindex swap (from (relations_iso a b) f)).

(*
   本节说明拉回/推出、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pow_aor_is_relations {a b : C} (f : a ~> Pow b) :
  to (pow_aor a b) f ≈ pow_relations f.
Proof.
  assert (Hl : to (pow_aor a b) f ≈ curry (uncurry f ∘ swap))
    by reflexivity.
  assert (Hr : pow_relations f
                 ≈ curry (char_sub (sub_reindex swap
                     (sub_reindex (uncurry f) truth_subobject))))
    by reflexivity.
  rewrite Hl, Hr.
  apply curry_respects.
  symmetry.
  transitivity (char_sub (sub_reindex (uncurry f) truth_subobject) ∘ swap).
  - apply char_reindex.
  - apply compose_respects; [| reflexivity].
    apply (classifier_char_roundtrip (uncurry f)).
Qed.

End ToposPower.

Arguments PowF {C H}.
