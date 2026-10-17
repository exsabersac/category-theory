Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.

Generalizable All Variables.

(* * * The 范畴 commutative monoids （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/commutative+monoid
 Wikipedia: https://en.wikipedia.org/wiki/Monoid#Commutative_monoid

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record CMonObject := {
  cmon_setoid :> SetoidObject;

  cmon_zero : carrier cmon_setoid;
  cmon_plus : carrier cmon_setoid → carrier cmon_setoid → carrier cmon_setoid;

  cmon_plus_respects : Proper (equiv ==> equiv ==> equiv) cmon_plus;

  cmon_plus_assoc : ∀ a b c,
    cmon_plus (cmon_plus a b) c ≈ cmon_plus a (cmon_plus b c);
  cmon_plus_comm : ∀ a b, cmon_plus a b ≈ cmon_plus b a;
  cmon_plus_zero_l : ∀ a, cmon_plus cmon_zero a ≈ a;

  (* The carrier is a SET: its `≈` is logically equivalent to a [Prop]-valued
     relation.  See Lib/Setoid/Propositional.v. *)
  cmon_prop : PropEquiv (is_setoid cmon_setoid)
}.

#[export] Existing Instance cmon_plus_respects.
#[export] Existing Instance cmon_prop.

(* 相关说明。 （已译） *)
Corollary cmon_plus_zero_r (M : CMonObject) (a : carrier (cmon_setoid M)) :
  cmon_plus M a (cmon_zero M) ≈ a.
Proof.
  rewrite cmon_plus_comm.
  apply cmon_plus_zero_l.
Qed.

(* 相关说明。 （已译） *)
Record CMonHom (M N : CMonObject) := {
  cmon_map :> SetoidMorphism (cmon_setoid M) (cmon_setoid N);

  cmon_map_zero : cmon_map (cmon_zero M) ≈ cmon_zero N;
  cmon_map_plus : ∀ a b,
    cmon_map (cmon_plus M a b) ≈ cmon_plus N (cmon_map a) (cmon_map b)
}.

Arguments cmon_map {M N} _.
Arguments cmon_map_zero {M N} _.
Arguments cmon_map_plus {M N} _ _ _.

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)
#[export]
Program Instance CMonHom_Setoid {M N : CMonObject} : Setoid (CMonHom M N) := {|
  equiv := fun f g => ∀ a, cmon_map f a ≈ cmon_map g a
|}.
Next Obligation.
  intros M N.
  constructor.
  - intros f a.
    reflexivity.
  - intros f g Hfg a.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (cmon_map g a).
    + apply Hfg.
    + apply Hgh.
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance CMonHom_PropEquiv {M N : CMonObject} :
  PropEquiv (@CMonHom_Setoid M N).
Proof.
  unshelve refine
    {| pequiv := fun f g : CMonHom M N =>
                   forall a : carrier (cmon_setoid M),
                     @pequiv _ _ (cmon_prop N) (cmon_map f a) (cmon_map g a) |}.
  - intros f g H a; exact (pequiv_to _ _ (H a)).
  - intros f g H a; exact (pequiv_from _ _ (H a)).
Defined.

(* The 恒等 homomorphism: 恒等 setoid map, preserves the
 unit operation nose. （已译） *)
Program Definition cmon_hom_id {M : CMonObject} : CMonHom M M := {|
  cmon_map := setoid_morphism_id
|}.
Next Obligation.
  intros M; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros M a b; simpl.
  reflexivity.
Qed.

(* Composition homomorphisms: 复合 underlying setoid maps;
 preservation unit operation composes. （已译） *)
Program Definition cmon_hom_compose {M N P : CMonObject}
        (f : CMonHom N P) (g : CMonHom M N) : CMonHom M P := {|
  cmon_map := setoid_morphism_compose (cmon_map f) (cmon_map g)
|}.
Next Obligation.
  intros M N P f g; simpl.
  unfold Basics.compose.
  rewrite (cmon_map_zero g).
  apply (cmon_map_zero f).
Qed.
Next Obligation.
  intros M N P f g a b; simpl.
  unfold Basics.compose.
  rewrite (cmon_map_plus g).
  apply (cmon_map_plus f).
Qed.

Lemma cmon_hom_compose_respects {M N P : CMonObject} :
  Proper (equiv ==> equiv ==> equiv) (@cmon_hom_compose M N P).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(* The 范畴 commutative monoids.

 对象: commutative monoids over setoids
 arrows: 单位- operation-preserving setoid maps
 恒等: 恒等 setoid map
 复合: 复合 setoid maps（已译） *)
(*
   本节说明 CMon 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition CMon@{u p} : Category@{u p p} := {|
  obj     := CMonObject@{p p p};
  hom     := CMonHom@{p};
  homset  := @CMonHom_Setoid@{p};
  id      := @cmon_hom_id@{p};
  compose := @cmon_hom_compose@{u p};

  compose_respects := @cmon_hom_compose_respects@{u p}
|}.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance CMon_LocallyPropositional : LocallyPropositional CMon.
Proof.
  constructor.
  intros M N.
  exact (@CMonHom_PropEquiv M N).
Defined.

(* The forgetful 函子 [Sets], dropping 幺半群 structure. It is
 faithful construction, since 等价 homomorphisms [CMon] is
 等价 underlying setoid maps. （已译） *)
Program Definition CMon_Forget : CMon ⟶ Sets := {|
  fobj := fun M => cmon_setoid M;
  fmap := fun _ _ f => cmon_map f
|}.
Next Obligation.
  intros M N f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros M a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros M N P f g a; simpl.
  reflexivity.
Qed.
