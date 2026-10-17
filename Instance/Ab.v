(*
   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** ** Objects *)

(** An abelian group: commutative 幺半群 negation a
 left inverse. The right inverse law follows commutativity
 ([ab_neg_right] below), so it not field. （已译） *)
Record AbObject := {
  ab_cmon :> CMonObject;

  ab_neg : carrier (cmon_setoid ab_cmon) → carrier (cmon_setoid ab_cmon);
  ab_neg_respects : Proper (equiv ==> equiv) ab_neg;

  ab_neg_left : ∀ a, cmon_plus ab_cmon (ab_neg a) a ≈ cmon_zero ab_cmon
}.

#[export] Existing Instance ab_neg_respects.

Corollary ab_neg_right (A : AbObject) (a : carrier (cmon_setoid A)) :
  cmon_plus A a (ab_neg A a) ≈ cmon_zero A.
Proof.
  rewrite cmon_plus_comm.
  apply ab_neg_left.
Qed.

(** Cancellation, used repeatedly below. This one property that
 genuinely separates group 幺半群. （已译） *)
Lemma ab_cancel_l (A : AbObject) (a b c : carrier (cmon_setoid A)) :
  cmon_plus A a b ≈ cmon_plus A a c → b ≈ c.
Proof.
  intro H.
  rewrite <- (cmon_plus_zero_l A b), <- (cmon_plus_zero_l A c).
  rewrite <- (ab_neg_left A a).
  rewrite !cmon_plus_assoc.
  now rewrite H.
Qed.

(** Negation is determined: anything acting as a left inverse IS the
    negation.  Needed to show homomorphisms preserve it. *)
Lemma ab_neg_unique (A : AbObject) (a b : carrier (cmon_setoid A)) :
  cmon_plus A b a ≈ cmon_zero A → b ≈ ab_neg A a.
Proof.
  intro H.
  apply (ab_cancel_l A a).
  rewrite (cmon_plus_comm A a b), H.
  now symmetry; apply ab_neg_right.
Qed.

Lemma ab_neg_zero (A : AbObject) : ab_neg A (cmon_zero A) ≈ cmon_zero A.
Proof.
  symmetry; apply ab_neg_unique.
  apply cmon_plus_zero_l.
Qed.

(** 本节：Negation distributes over addition. This needs commutativity, so it an
 abelian-group fact rather than group fact, it what makes the
 quotient below respect negation. （已译） *)
Lemma ab_neg_plus (A : AbObject) (a b : carrier (cmon_setoid A)) :
  ab_neg A (cmon_plus A a b)
    ≈ cmon_plus A (ab_neg A a) (ab_neg A b).
Proof.
  symmetry; apply ab_neg_unique.
  rewrite cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A b) a b).
  rewrite (cmon_plus_comm A (ab_neg A b) a).
  rewrite (cmon_plus_assoc A a (ab_neg A b) b).
  rewrite ab_neg_left, cmon_plus_zero_r.
  apply ab_neg_left.
Qed.

(** ** Morphisms *)

(* * A 同态 阿贝尔 groups is exactly 同态 the
 underlying commutative monoids. Preservation negation is derived, not
 demanded -- standard fact that monoid map between groups is group
 map.（已译） *)
Definition AbHom (A B : AbObject) := CMonHom A B.

Lemma ab_map_neg {A B : AbObject} (f : AbHom A B) (a : carrier (cmon_setoid A)) :
  cmon_map f (ab_neg A a) ≈ ab_neg B (cmon_map f a).
Proof.
  apply ab_neg_unique.
  rewrite <- cmon_map_plus.
  rewrite ab_neg_left.
  apply cmon_map_zero.
Qed.

(** ** The category *)

(* * [Ab] is full subcategory [CMon] 对象 carrying negation:
 same homs, same identities, same 复合, same hom-setoid. Stating it
 this way is what makes [ab_map_neg] 定理 rather than 融贯性
 obligation.（已译） *)
(*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Ab@{u p} : Category@{u p p} := {|
  obj     := AbObject@{p p p};
  hom     := AbHom@{p};
  homset  := fun A B => @CMonHom_Setoid@{p} A B;
  id      := fun A => @cmon_hom_id@{p} A;
  compose := fun A B C f g => @cmon_hom_compose@{u p} A B C f g;

  (*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  compose_respects := fun A B C => @cmon_hom_compose_respects@{u p} A B C
|}.

(** The forgetful 函子 [Sets], through underlying setoid. （已译） *)
Program Definition Ab_Forget : Ab ⟶ Sets := {|
  fobj := fun A => cmon_setoid (ab_cmon A);
  fmap := fun _ _ f => cmon_map f
|}.

(* * ** The zero group zero 对象 （已译） *)

(** The one-element abelian group. Its negation forced: there one
 element, so [ab_neg] 常值 map inverse law is
 [reflexivity]. （已译） *)
Definition Ab_trivial : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := CMon_trivial;
    ab_neg  := fun _ => ttt
  |}.
  - intros x y Hxy; reflexivity.
  - intros a; reflexivity.
Defined.

(** 本节：Everything maps point, one map does. （已译） *)
Definition Ab_one (A : AbObject) : A ~{Ab}~> Ab_trivial := CMon_one A.

Lemma Ab_one_unique (A : AbObject) (f : A ~{Ab}~> Ab_trivial) :
  f ≈ Ab_one A.
Proof. intro a; destruct (cmon_map f a); reflexivity. Qed.

Program Definition Ab_Terminal : @Terminal Ab := {|
  terminal_obj := Ab_trivial;
  one          := Ab_one
|}.
Next Obligation. now rewrite (Ab_one_unique _ f), (Ab_one_unique _ g). Qed.

(** 本节：Dually: unique map OUT point sends point zero. This is
 where group being trivial does work -- there nothing choose. （已译） *)
Definition Ab_zero_hom (A : AbObject) : Ab_trivial ~{Ab}~> A :=
  CMon_zero_hom A.

Lemma Ab_zero_hom_unique (A : AbObject) (f : Ab_trivial ~{Ab}~> A) :
  f ≈ Ab_zero_hom A.
Proof.
  intro a; destruct a; simpl.
  now rewrite (cmon_map_zero f).
Qed.

Program Definition Ab_Initial : @Initial Ab := {|
  terminal_obj := Ab_trivial : obj[Ab^op];
  one          := Ab_zero_hom
|}.
Next Obligation.
  (* Routed through transitivity at the hom-setoid level rather than by
     [rewrite]: rewriting puts both sides under [cmon_map], where it leaves
     undetermined evars. *)
  etransitivity;
    [ apply Ab_zero_hom_unique | symmetry; apply Ab_zero_hom_unique ].
Qed.

(** The same 对象 both, so coincidence iso 恒等 -- exactly
 at Instance/CMon/Biproduct.v. （已译） *)
#[export] Instance Ab_Zero : ZeroObject Ab :=
  @Build_ZeroObject Ab Ab_Terminal Ab_Initial iso_id.

(* * ** Mac Lane's §I.7 命题: monic = injective, epic = surjective （已译） *)

Definition AbInjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ x y : carrier (cmon_setoid A), cmon_map f x ≈ cmon_map f y → x ≈ y.

Definition AbSurjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ b : carrier (cmon_setoid B), { a & cmon_map f a ≈ b }.

(*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AbPropSurjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ b : carrier (cmon_setoid B),
    (exists a : carrier (cmon_setoid A),
       @pequiv _ _ (cmon_prop B) (cmon_map f a) b)%type.

Lemma ab_surjective_prop {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → AbPropSurjective f.
Proof.
  intros Hs b.
  destruct (Hs b) as [a Ha].
  exists a.
  now apply pequiv_from.
Qed.

(* * *** The kernel, used probe 对象 monic half （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Kernel.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_ker_carrier : Type :=
  { a : carrier (cmon_setoid A) & cmon_map f a ≈ cmon_zero B }.

Program Definition ab_ker_setoid : Setoid ab_ker_carrier := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.

Lemma ab_ker_zero_pf : cmon_map f (cmon_zero A) ≈ cmon_zero B.
Proof. apply cmon_map_zero. Qed.

Lemma ab_ker_plus_pf (p q : ab_ker_carrier) :
  cmon_map f (cmon_plus A (projT1 p) (projT1 q)) ≈ cmon_zero B.
Proof.
  rewrite cmon_map_plus, (projT2 p), (projT2 q).
  apply cmon_plus_zero_l.
Qed.

Lemma ab_ker_neg_pf (p : ab_ker_carrier) :
  cmon_map f (ab_neg A (projT1 p)) ≈ cmon_zero B.
Proof.
  rewrite ab_map_neg, (projT2 p).
  apply ab_neg_zero.
Qed.

Definition AbKernel : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := ab_ker_carrier ; is_setoid := ab_ker_setoid |}
       ; cmon_zero := existT _ (cmon_zero A) ab_ker_zero_pf
       ; cmon_plus := fun p q =>
           existT _ (cmon_plus A (projT1 p) (projT1 q)) (ab_ker_plus_pf p q)
       ; cmon_prop :=
           sigma_first_PropEquiv ab_ker_setoid
             (fun _ _ h => h) (fun _ _ h => h) (cmon_prop A) |};
    ab_neg := fun p => existT _ (ab_neg A (projT1 p)) (ab_ker_neg_pf p)
  |}.
  - (* cmon_plus_respects *)
    intros p p' Hp q q' Hq; simpl in *.
    now rewrite Hp, Hq.
  - (* cmon_plus_assoc *)
    intros a b c; simpl; apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros a b; simpl; apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros a; simpl; apply cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros p q Hpq; simpl in *; now rewrite Hpq.
  - (* ab_neg_left *)
    intros a; simpl; apply ab_neg_left.
Defined.

(** The 含入 kernel, zero map alongside it. [f] equalizes
 them, whole point. （已译） *)
Program Definition ab_kernel_incl : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun p : ab_ker_carrier => projT1 p |} |}.

Program Definition ab_kernel_zero : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun _ : ab_ker_carrier => cmon_zero A |} |}.
Next Obligation. symmetry; apply cmon_plus_zero_l. Qed.

End Kernel.

Arguments AbKernel {A B} f.
Arguments ab_kernel_incl {A B} f.
Arguments ab_kernel_zero {A B} f.

(** *** Monic *)

(*
   本节说明幺半群、核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ab_monic_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f → AbInjective f.
Proof.
  intros Hm x y Hxy.
  (* 相关说明。 （已译） *)
  assert (Hk : ∀ p : carrier (cmon_setoid (AbKernel f)),
                 projT1 p ≈ cmon_zero A).
  { apply (@monic _ _ _ f Hm (AbKernel f)
             (ab_kernel_incl f) (ab_kernel_zero f)).
    intro p; simpl.
    rewrite (projT2 p).
    symmetry; apply cmon_map_zero. }
  (* Step 2: x - y lies in the kernel. *)
  assert (Hd : cmon_map f (cmon_plus A x (ab_neg A y)) ≈ cmon_zero B).
  { rewrite cmon_map_plus, ab_map_neg, Hxy.
    apply ab_neg_right. }
  (* Step 3: so x - y is zero, hence x ≈ y. *)
  pose proof (Hk (existT _ (cmon_plus A x (ab_neg A y)) Hd)) as Hz.
  simpl in Hz.
  apply (ab_cancel_l A (ab_neg A y)).
  rewrite (cmon_plus_comm A (ab_neg A y) x) in *.
  rewrite Hz.
  now rewrite (cmon_plus_comm A (ab_neg A y) y), ab_neg_right.
Qed.

Lemma ab_injective_monic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbInjective f → Monic f.
Proof.
  intros Hi.
  constructor; intros Z g h Hgh z.
  apply Hi.
  exact (Hgh z).
Qed.

Theorem ab_monic_iff_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f ↔ AbInjective f.
Proof.
  split; [ apply ab_monic_injective | apply ab_injective_monic ].
Qed.

(* * *** The quotient B/fA, used probe 对象 epic half （已译） *)

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Quotient.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_coset_eq (x y : carrier (cmon_setoid B)) : Prop :=
  (exists a : carrier (cmon_setoid A),
     @pequiv _ _ (cmon_prop B) x (cmon_plus B y (cmon_map f a)))%type.

Lemma ab_coset_refl (x : carrier (cmon_setoid B)) : ab_coset_eq x x.
Proof.
  exists (cmon_zero A).
  apply pequiv_from.
  rewrite cmon_map_zero.
  symmetry; apply cmon_plus_zero_r.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ab_coset_sym (x y : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y x.
Proof.
  intros [a Ha].
  apply pequiv_to in Ha.
  exists (ab_neg A a).
  apply pequiv_from.
  rewrite ab_map_neg, Ha.
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  symmetry; apply cmon_plus_zero_r.
Qed.

Lemma ab_coset_trans (x y z : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y z → ab_coset_eq x z.
Proof.
  intros [a Ha] [b Hb].
  apply pequiv_to in Ha.
  apply pequiv_to in Hb.
  exists (cmon_plus A b a).
  apply pequiv_from.
  rewrite cmon_map_plus.
  rewrite Ha, Hb.
  now rewrite cmon_plus_assoc.
Qed.

Program Definition ab_coset_setoid : Setoid (carrier (cmon_setoid B)) := {|
  equiv := ab_coset_eq
|}.
Next Obligation.
  constructor.
  - exact ab_coset_refl.
  - exact ab_coset_sym.
  - exact ab_coset_trans.
Qed.

Definition AbQuotient : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := carrier (cmon_setoid B)
                         ; is_setoid := ab_coset_setoid |}
       ; cmon_zero := cmon_zero B
       ; cmon_plus := cmon_plus B
       ; cmon_prop :=
           @PropEquiv_of_relation _ ab_coset_setoid ab_coset_eq
             (fun _ _ h => h) (fun _ _ h => h) |};
    ab_neg := ab_neg B
  |}.
  - (*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    intros x x' Hx y y' Hy; simpl in Hx, Hy |- *.
    destruct Hx as [a Ha], Hy as [b Hb].
    apply pequiv_to in Ha.
    apply pequiv_to in Hb.
    exists (cmon_plus A a b).
    apply pequiv_from.
    rewrite cmon_map_plus, Ha, Hb.
    (* (x' + f a) + (y' + f b) ≈ (x' + y') + (f a + f b) *)
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [ | reflexivity ].
    apply cmon_plus_comm.
  - (* cmon_plus_assoc *)
    intros x y z; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros x y; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros x; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros x y Hxy; simpl in Hxy |- *.
    destruct Hxy as [a Ha].
    apply pequiv_to in Ha.
    exists (ab_neg A a).
    apply pequiv_from.
    rewrite ab_map_neg.
    change (ab_neg B x ≈ cmon_plus B (ab_neg B y) (ab_neg B (cmon_map f a))).
    rewrite <- ab_neg_plus.
    now rewrite Ha.
  - (* ab_neg_left *)
    intros x; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply ab_neg_left.
Defined.

(** The projection (恒等 carriers, coarser equality) zero map.
 [f] equalizes them -- exactly statement [f a] is
 congruent zero modulo image. （已译） *)
Program Definition ab_quot_proj : B ~{Ab}~> AbQuotient :=
  {| cmon_map := {| morphism := fun b : carrier (cmon_setoid B) => b |} |}.
Next Obligation. intros x y Hxy; simpl; exists (cmon_zero A); apply pequiv_from;
  rewrite cmon_map_zero, cmon_plus_zero_r; exact Hxy. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.

Program Definition ab_quot_zero : B ~{Ab}~> AbQuotient :=
  {| cmon_map :=
       {| morphism := fun _ : carrier (cmon_setoid B) => cmon_zero B |} |}.
Next Obligation. intros x y Hxy; apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation.
  simpl.
  exists (cmon_zero A).
  apply pequiv_from.
  rewrite cmon_map_zero, cmon_plus_zero_r.
  symmetry; apply cmon_plus_zero_l.
Qed.

End Quotient.

Arguments AbQuotient {A B} f.
Arguments ab_quot_proj {A B} f.
Arguments ab_quot_zero {A B} f.

(** *** Epic *)

(*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ab_epic_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f → AbPropSurjective f.
Proof.
  intros He b.
  assert (Hpq : ab_quot_proj f ≈ ab_quot_zero f).
  { apply (@epic _ _ _ f He (AbQuotient f)
             (ab_quot_proj f) (ab_quot_zero f)).
    intro a; simpl.
    exists a.
    apply pequiv_from.
    rewrite cmon_plus_zero_l.
    reflexivity. }
  specialize (Hpq b); simpl in Hpq.
  destruct Hpq as [a Ha].
  apply pequiv_to in Ha.
  exists a.
  apply pequiv_from.
  rewrite cmon_plus_zero_l in Ha.
  now symmetry.
Qed.

Lemma ab_surjective_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  destruct (Hs b) as [a Ha].
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ab_prop_surjective_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbPropSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  apply (@pequiv_to _ _ (cmon_prop Z)).
  destruct (Hs b) as [a Ha].
  apply pequiv_from.
  apply pequiv_to in Ha.
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(*
   本节说明 Ab 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem ab_epic_iff_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f ↔ AbPropSurjective f.
Proof.
  split; [ apply ab_epic_surjective | apply ab_prop_surjective_epic ].
Qed.

(* 相关说明。 （已译） *)

(* * L8: [Ab]'s hom-setoid IS [CMonHom_Setoid] (see [Ab] above), so
 Instance/CMon.v's [CMonHom_PropEquiv] supplies whole family at once.
 This is what lets 构造 that turns 对象 ambient
 范畴 into 阿贝尔 group -- [hom_ab] Adjunction/Additive.v,
 [ehom_ab] Construction/Enriched/Ab.v -- be instantiated at [Ab] itself
 without hand-written hypothesis.（已译） *)
#[export] Instance Ab_LocallyPropositional : LocallyPropositional Ab.
Proof.
  constructor.
  intros A B.
  exact (@CMonHom_PropEquiv A B).
Defined.
