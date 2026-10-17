(** * The functor-of-points criterion for monoid and group objects *)

(*
   nLab:      https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Group_object
   Book:      Mac Lane, CWM 2nd ed., Section III.6 ("Groups in
   Paper:     Eckmann, Hilton, "Group-Like Structures in General

   本文件给出可表性相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Grp.

Generalizable All Variables.

Section HomData.

Context {C : Category}.

Record HomMonoidData (e : C) := {
  hmd_mul  : ∀ {x : C}, (x ~> e) → (x ~> e) → (x ~> e);
  hmd_unit : ∀ {x : C}, x ~> e;

  hmd_mul_respects : ∀ {x : C},
    Proper (equiv ==> equiv ==> equiv) (@hmd_mul x);

  hmd_assoc : ∀ {x : C} (f g h : x ~> e),
    hmd_mul (hmd_mul f g) h ≈ hmd_mul f (hmd_mul g h);
  hmd_unit_l : ∀ {x : C} (f : x ~> e), hmd_mul hmd_unit f ≈ f;
  hmd_unit_r : ∀ {x : C} (f : x ~> e), hmd_mul f hmd_unit ≈ f;

  hmd_mul_natural : ∀ {x y : C} (f g : x ~> e) (h : y ~> x),
    hmd_mul f g ∘ h ≈ hmd_mul (f ∘ h) (g ∘ h);
  hmd_unit_natural : ∀ {x y : C} (h : y ~> x),
    hmd_unit ∘ h ≈ @hmd_unit y
}.



Record HomGroupData (e : C) := {
  hgd_monoid :> HomMonoidData e;
  hgd_inv : ∀ {x : C}, (x ~> e) → (x ~> e);

  hgd_inv_respects : ∀ {x : C}, Proper (equiv ==> equiv) (@hgd_inv x);

  hgd_inv_l : ∀ {x : C} (f : x ~> e),
    hmd_mul e hgd_monoid (hgd_inv f) f ≈ hmd_unit e hgd_monoid;
  hgd_inv_r : ∀ {x : C} (f : x ~> e),
    hmd_mul e hgd_monoid f (hgd_inv f) ≈ hmd_unit e hgd_monoid;

  hgd_inv_natural : ∀ {x y : C} (f : x ~> e) (h : y ~> x),
    hgd_inv f ∘ h ≈ hgd_inv (f ∘ h)
}.



End HomData.

Arguments HomMonoidData {C} _.
Arguments HomGroupData {C} _.

Arguments hmd_mul {C e} _ {x} _ _.
Arguments hmd_unit {C e} _ {x}.
Arguments hmd_mul_respects {C e} _ {x}.
Arguments hmd_assoc {C e} _ {x} _ _ _.
Arguments hmd_unit_l {C e} _ {x} _.
Arguments hmd_unit_r {C e} _ {x} _.
Arguments hmd_mul_natural {C e} _ {x y} _ _ _.
Arguments hmd_unit_natural {C e} _ {x y} _.

Arguments hgd_monoid {C e} _.
Arguments hgd_inv {C e} _ {x} _.
Arguments hgd_inv_respects {C e} _ {x}.
Arguments hgd_inv_l {C e} _ {x} _.
Arguments hgd_inv_r {C e} _ {x} _.
Arguments hgd_inv_natural {C e} _ {x y} _ _.

#[export] Existing Instance hmd_mul_respects.
#[export] Existing Instance hgd_inv_respects.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomMonoidEngine.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (M : @MonoidObject C CC_Monoidal c).

Definition rg_mul : c × c ~> c := @mappend C CC_Monoidal c M.
Definition rg_unit : 1 ~> c := @mempty C CC_Monoidal c M.

Lemma rg_assoc_law :
  rg_mul ∘ Cartesian.split rg_mul id
    ≈ rg_mul ∘ Cartesian.split id rg_mul
        ∘ ((exl ∘ exl) △ ((exr ∘ exl) △ exr)).
Proof. exact (@mappend_assoc C CC_Monoidal c M). Qed.

Lemma rg_unit_left_law : rg_mul ∘ Cartesian.split rg_unit id ≈ exr.
Proof. exact (@mempty_left C CC_Monoidal c M). Qed.

Lemma rg_unit_right_law : rg_mul ∘ Cartesian.split id rg_unit ≈ exl.
Proof. exact (@mempty_right C CC_Monoidal c M). Qed.

Definition hmul {x : C} (f g : x ~> c) : x ~> c := rg_mul ∘ f △ g.
Definition hone {x : C} : x ~> c := rg_unit ∘ one.

#[export] Program Instance hmul_respects {x : C} :
  Proper (equiv ==> equiv ==> equiv) (@hmul x).
Next Obligation. proper; unfold hmul; now rewrite X, X0. Qed.

Lemma hmul_assoc {x : C} (f g h : x ~> c) :
  hmul (hmul f g) h ≈ hmul f (hmul g h).
Proof.
  unfold hmul.
  assert (E1 : rg_mul ∘ Cartesian.split rg_mul id ∘ ((f △ g) △ h)
                 ≈ rg_mul ∘ (rg_mul ∘ f △ g) △ h)
    by (rewrite <- comp_assoc, split_fork; cat).
  rewrite <- E1, rg_assoc_law, <- !comp_assoc.
  assert (E2 : ((exl ∘ exl) △ ((exr ∘ exl) △ exr)) ∘ ((f △ g) △ h)
                 ≈ f △ (g △ h)) by (now unfork).
  rewrite E2, split_fork.
  now rewrite id_left.
Qed.

Lemma hmul_unit_l {x : C} (f : x ~> c) : hmul hone f ≈ f.
Proof.
  unfold hmul, hone.
  rewrite <- (id_left f) at 1.
  rewrite <- split_fork, comp_assoc, rg_unit_left_law.
  now rewrite exr_fork.
Qed.

Lemma hmul_unit_r {x : C} (f : x ~> c) : hmul f hone ≈ f.
Proof.
  unfold hmul, hone.
  rewrite <- (id_left f) at 1.
  rewrite <- split_fork, comp_assoc, rg_unit_right_law.
  now rewrite exl_fork.
Qed.

Lemma hmul_comp {x y : C} (f g : x ~> c) (h : y ~> x) :
  hmul f g ∘ h ≈ hmul (f ∘ h) (g ∘ h).
Proof. unfold hmul; rewrite <- comp_assoc; now rewrite fork_comp. Qed.

Lemma hone_comp {x y : C} (h : y ~> x) : @hone x ∘ h ≈ @hone y.
Proof.
  unfold hone; rewrite <- comp_assoc.
  now rewrite (one_unique (one ∘ h) one).
Qed.

Definition monoid_object_hom_data : HomMonoidData c :=
  {| hmd_mul  := @hmul
   ; hmd_unit := @hone
   ; hmd_mul_respects := @hmul_respects
   ; hmd_assoc := @hmul_assoc
   ; hmd_unit_l := @hmul_unit_l
   ; hmd_unit_r := @hmul_unit_r
   ; hmd_mul_natural := @hmul_comp
   ; hmd_unit_natural := @hone_comp |}.

End HomMonoidEngine.

Section HomGroupEngine.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (G : @GroupObject C CC_CartesianMonoidal c).

Definition rg_monoid : @MonoidObject C CC_Monoidal c :=
  @groupobject_is_monoid C CC_CartesianMonoidal c G.
Definition rg_inv : c ~> c :=
  @Category.Structure.Group.inverse C CC_CartesianMonoidal c G.

Lemma rg_inv_left_law :
  rg_mul c rg_monoid ∘ Cartesian.split rg_inv id ∘ (id △ id)
    ≈ rg_unit c rg_monoid ∘ one.
Proof. exact (@left_inverse C CC_CartesianMonoidal c G). Qed.

Lemma rg_inv_right_law :
  rg_mul c rg_monoid ∘ Cartesian.split id rg_inv ∘ (id △ id)
    ≈ rg_unit c rg_monoid ∘ one.
Proof. exact (@right_inverse C CC_CartesianMonoidal c G). Qed.

Definition hinv {x : C} (f : x ~> c) : x ~> c := rg_inv ∘ f.

#[export] Program Instance hinv_respects {x : C} :
  Proper (equiv ==> equiv) (@hinv x).
Next Obligation. proper; unfold hinv; now rewrite X. Qed.

Lemma hmul_inv_l {x : C} (f : x ~> c) :
  hmul c rg_monoid (hinv f) f ≈ hone c rg_monoid.
Proof.
  unfold hmul, hinv, hone.
  assert (E : rg_mul c rg_monoid ∘ Cartesian.split rg_inv id ∘ (id △ id) ∘ f
                ≈ rg_mul c rg_monoid ∘ (rg_inv ∘ f) △ f).
  { rewrite <- !comp_assoc, <- fork_comp, !id_left, split_fork.
    now rewrite id_left. }
  rewrite <- E, rg_inv_left_law, <- comp_assoc.
  now rewrite (one_unique (one ∘ f) one).
Qed.

Lemma hmul_inv_r {x : C} (f : x ~> c) :
  hmul c rg_monoid f (hinv f) ≈ hone c rg_monoid.
Proof.
  unfold hmul, hinv, hone.
  assert (E : rg_mul c rg_monoid ∘ Cartesian.split id rg_inv ∘ (id △ id) ∘ f
                ≈ rg_mul c rg_monoid ∘ f △ (rg_inv ∘ f)).
  { rewrite <- !comp_assoc, <- fork_comp, !id_left, split_fork.
    now rewrite id_left. }
  rewrite <- E, rg_inv_right_law, <- comp_assoc.
  now rewrite (one_unique (one ∘ f) one).
Qed.

Lemma hinv_comp {x y : C} (f : x ~> c) (h : y ~> x) :
  hinv f ∘ h ≈ hinv (f ∘ h).
Proof. unfold hinv; now rewrite comp_assoc. Qed.

Definition group_object_hom_data : HomGroupData c :=
  {| hgd_monoid := monoid_object_hom_data c rg_monoid
   ; hgd_inv := @hinv
   ; hgd_inv_respects := @hinv_respects
   ; hgd_inv_l := @hmul_inv_l
   ; hgd_inv_r := @hmul_inv_r
   ; hgd_inv_natural := @hinv_comp |}.

End HomGroupEngine.

(*
   本节说明Yoneda、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ToPresheaf.

Context {C : Category}.
Context (e : C).

Definition RepPresheaf : [C^op, Sets] := Curried_CoHom C e.

Context (D : HomMonoidData e).

Program Definition rep_mul_nt :
  (RepPresheaf × RepPresheaf)%object ~> RepPresheaf := {|
  transform := fun x => {| morphism := fun p => hmd_mul D (fst p) (snd p) |}
|}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg]; simpl in *; now rewrite Hf, Hg.
Qed.
Next Obligation. now rewrite hmd_mul_natural. Qed.
Next Obligation. now rewrite hmd_mul_natural. Qed.

Program Definition rep_unit_nt : (1 : [C^op, Sets]) ~> RepPresheaf := {|
  transform := fun x => {| morphism := fun _ => hmd_unit D |}
|}.
Next Obligation. now rewrite hmd_unit_natural. Qed.
Next Obligation. now rewrite hmd_unit_natural. Qed.

Program Definition RepPresheaf_Monoid :
  @MonoidObject ([C^op, Sets]) CC_Monoidal RepPresheaf := {|
  mempty  := rep_unit_nt;
  mappend := rep_mul_nt
|}.
Next Obligation. rewrite id_right; apply hmd_unit_l. Qed.
Next Obligation. rewrite id_right; apply hmd_unit_r. Qed.
Next Obligation. rewrite !id_right; apply hmd_assoc. Qed.

End ToPresheaf.

Section ToPresheafGroup.

Context {C : Category}.
Context (e : C).
Context (D : HomGroupData e).

Program Definition rep_inv_nt : RepPresheaf e ~> RepPresheaf e := {|
  transform := fun x => {| morphism := fun f => hgd_inv D f |}
|}.
Next Obligation. intros f f' Hf; simpl in *; now rewrite Hf. Qed.
Next Obligation. now rewrite hgd_inv_natural. Qed.
Next Obligation. now rewrite hgd_inv_natural. Qed.

Program Definition RepPresheaf_Group :
  @GroupObject ([C^op, Sets]) CC_CartesianMonoidal (RepPresheaf e) := {|
  groupobject_is_monoid := RepPresheaf_Monoid e (hgd_monoid D);
  Category.Structure.Group.inverse := rep_inv_nt
|}.
Next Obligation. rewrite !id_right; apply hgd_inv_l. Qed.
Next Obligation. rewrite !id_right; apply hgd_inv_r. Qed.

End ToPresheafGroup.

(*
   本节说明hom、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FromPresheaf.

Context {C : Category}.
Context (e : C).
Context (P : @MonoidObject ([C^op, Sets]) CC_Monoidal (RepPresheaf e)).

Definition psh_mul : (RepPresheaf e × RepPresheaf e)%object ~> RepPresheaf e :=
  @mappend ([C^op, Sets]) CC_Monoidal _ P.
Definition psh_unit : (1 : [C^op, Sets]) ~> RepPresheaf e :=
  @mempty ([C^op, Sets]) CC_Monoidal _ P.

Definition pmul {x : C} (f g : x ~> e) : x ~> e := transform[psh_mul] x (f, g).
Definition punit {x : C} : x ~> e := transform[psh_unit] x ttt.

#[export] Program Instance pmul_respects {x : C} :
  Proper (equiv ==> equiv ==> equiv) (@pmul x).
Next Obligation.
  proper; unfold pmul; apply proper_morphism; now split.
Qed.

Lemma pmul_natural {x y : C} (f g : x ~> e) (h : y ~> x) :
  pmul f g ∘ h ≈ pmul (f ∘ h) (g ∘ h).
Proof.
  unfold pmul.
  exact (naturality[psh_mul] x y h (f, g)).
Qed.

Lemma punit_natural {x y : C} (h : y ~> x) : @punit x ∘ h ≈ @punit y.
Proof.
  unfold punit.
  exact (naturality[psh_unit] x y h ttt).
Qed.

Lemma pmul_unit_l {x : C} (f : x ~> e) : pmul punit f ≈ f.
Proof.
  pose proof (@mempty_left ([C^op, Sets]) CC_Monoidal _ P x (ttt, f)) as HL.
  simpl in HL; rewrite id_right in HL; exact HL.
Qed.

Lemma pmul_unit_r {x : C} (f : x ~> e) : pmul f punit ≈ f.
Proof.
  pose proof (@mempty_right ([C^op, Sets]) CC_Monoidal _ P x (f, ttt)) as HR.
  simpl in HR; rewrite id_right in HR; exact HR.
Qed.

Lemma pmul_assoc {x : C} (f g h : x ~> e) :
  pmul (pmul f g) h ≈ pmul f (pmul g h).
Proof.
  pose proof (@mappend_assoc ([C^op, Sets]) CC_Monoidal _ P x ((f, g), h))
    as HA.
  simpl in HA; rewrite !id_right in HA; exact HA.
Qed.

Definition psh_monoid_hom_data : HomMonoidData e :=
  {| hmd_mul  := @pmul
   ; hmd_unit := @punit
   ; hmd_mul_respects := @pmul_respects
   ; hmd_assoc := @pmul_assoc
   ; hmd_unit_l := @pmul_unit_l
   ; hmd_unit_r := @pmul_unit_r
   ; hmd_mul_natural := @pmul_natural
   ; hmd_unit_natural := @punit_natural |}.

End FromPresheaf.

Section FromPresheafGroup.

Context {C : Category}.
Context (e : C).
Context (P : @GroupObject ([C^op, Sets]) CC_CartesianMonoidal
                          (RepPresheaf e)).

Definition psh_gmonoid :
  @MonoidObject ([C^op, Sets]) CC_Monoidal (RepPresheaf e) :=
  @groupobject_is_monoid _ CC_CartesianMonoidal _ P.

Definition psh_inv_nt : RepPresheaf e ~> RepPresheaf e :=
  @Category.Structure.Group.inverse ([C^op, Sets]) CC_CartesianMonoidal _ P.

Definition pinv {x : C} (f : x ~> e) : x ~> e := transform[psh_inv_nt] x f.

#[export] Program Instance pinv_respects {x : C} :
  Proper (equiv ==> equiv) (@pinv x).
Next Obligation. proper; unfold pinv; now apply proper_morphism. Qed.

Lemma pinv_natural {x y : C} (f : x ~> e) (h : y ~> x) :
  pinv f ∘ h ≈ pinv (f ∘ h).
Proof. unfold pinv; exact (naturality[psh_inv_nt] x y h f). Qed.

Lemma pinv_l {x : C} (f : x ~> e) :
  pmul e psh_gmonoid (pinv f) f
    ≈ punit e psh_gmonoid.
Proof.
  pose proof (@left_inverse ([C^op, Sets]) CC_CartesianMonoidal _ P x f) as HI.
  simpl in HI; rewrite !id_right in HI; exact HI.
Qed.

Lemma pinv_r {x : C} (f : x ~> e) :
  pmul e psh_gmonoid f (pinv f)
    ≈ punit e psh_gmonoid.
Proof.
  pose proof (@right_inverse ([C^op, Sets]) CC_CartesianMonoidal _ P x f) as HI.
  simpl in HI; rewrite !id_right in HI; exact HI.
Qed.

Definition psh_group_hom_data : HomGroupData e :=
  {| hgd_monoid := psh_monoid_hom_data e psh_gmonoid
   ; hgd_inv := @pinv
   ; hgd_inv_respects := @pinv_respects
   ; hgd_inv_l := @pinv_l
   ; hgd_inv_r := @pinv_r
   ; hgd_inv_natural := @pinv_natural |}.

End FromPresheafGroup.

(*
   本节说明hom、幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ToObject.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (D : HomMonoidData c).

Definition data_mul : c × c ~> c := hmd_mul D exl exr.
Definition data_unit : 1 ~{C}~> c := @hmd_unit C c D 1.

Lemma data_mul_eval {x : C} (f g : x ~> c) :
  hmd_mul D f g ≈ data_mul ∘ f △ g.
Proof.
  unfold data_mul.
  rewrite hmd_mul_natural.
  now rewrite exl_fork, exr_fork.
Qed.

Lemma data_unit_eval {x : C} : @hmd_unit C c D x ≈ data_unit ∘ one.
Proof. unfold data_unit; now rewrite hmd_unit_natural. Qed.

Lemma fork_exl_exl_exr_exl {x y z : C} :
  ((@exl C _ x y ∘ exl) △ (exr ∘ exl)) ≈ @exl C _ (x × y) z.
Proof. rewrite fork_comp, fork_exl_exr; cat. Qed.

Program Definition data_MonoidObject :
  @MonoidObject C CC_Monoidal c := {|
  mempty  := data_unit;
  mappend := data_mul
|}.
Next Obligation.
  pose proof (hmd_unit_l D (@exr C _ 1 c)) as HL.
  rewrite data_unit_eval, data_mul_eval in HL.
  rewrite id_left, (one_unique (@exl C _ 1 c) one).
  exact HL.
Qed.
Next Obligation.
  pose proof (hmd_unit_r D (@exl C _ c 1)) as HR.
  rewrite data_unit_eval, data_mul_eval in HR.
  rewrite id_left, (one_unique (@exr C _ c 1) one).
  exact HR.
Qed.
Next Obligation.
  pose proof (hmd_assoc D (exl ∘ exl) (exr ∘ exl) (@exr C _ (c × c) c)) as HA.
  rewrite !data_mul_eval in HA.
  rewrite fork_exl_exl_exr_exl in HA.
  rewrite !id_left, HA.
  rewrite <- comp_assoc, <- fork_comp, <- !comp_assoc.
  now rewrite exl_fork, exr_fork.
Qed.

End ToObject.

Section ToObjectGroup.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (D : HomGroupData c).

Definition data_inv : c ~> c := hgd_inv D id.

Lemma data_inv_eval {x : C} (f : x ~> c) : hgd_inv D f ≈ data_inv ∘ f.
Proof.
  unfold data_inv.
  rewrite hgd_inv_natural.
  now rewrite id_left.
Qed.

Program Definition data_GroupObject :
  @GroupObject C CC_CartesianMonoidal c := {|
  groupobject_is_monoid := data_MonoidObject c (hgd_monoid D);
  Category.Structure.Group.inverse := data_inv
|}.
Next Obligation.
  pose proof (hgd_inv_l D (@id C c)) as HI.
  rewrite data_inv_eval, data_mul_eval, data_unit_eval in HI.
  rewrite <- comp_assoc, <- fork_comp, <- !comp_assoc.
  rewrite exl_fork, exr_fork, id_left.
  exact HI.
Qed.
Next Obligation.
  pose proof (hgd_inv_r D (@id C c)) as HI.
  rewrite data_inv_eval, data_mul_eval, data_unit_eval in HI.
  rewrite <- comp_assoc, <- fork_comp, <- !comp_assoc.
  rewrite exl_fork, exr_fork, id_left.
  exact HI.
Qed.

End ToObjectGroup.

(** ** Mac Lane Proposition 1 and remark 2 *)

Definition RepresentablyMonoid {C : Category} (e : C) : Type :=
  @MonoidObject ([C^op, Sets]) CC_Monoidal (RepPresheaf e).

Definition RepresentablyGroup {C : Category} (e : C) : Type :=
  @GroupObject ([C^op, Sets]) CC_CartesianMonoidal (RepPresheaf e).

Section Headline.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).

Definition monoid_object_representable
  (M : @MonoidObject C CC_Monoidal c) : RepresentablyMonoid c :=
  RepPresheaf_Monoid c (monoid_object_hom_data c M).

Definition representable_monoid_object
  (P : RepresentablyMonoid c) : @MonoidObject C CC_Monoidal c :=
  data_MonoidObject c (psh_monoid_hom_data c P).

Theorem monoid_object_iff_representable :
  @MonoidObject C CC_Monoidal c ↔ RepresentablyMonoid c.
Proof.
  split.
  - exact monoid_object_representable.
  - exact representable_monoid_object.
Defined.

Definition group_object_representable
  (G : @GroupObject C CC_CartesianMonoidal c) : RepresentablyGroup c :=
  RepPresheaf_Group c (group_object_hom_data c G).

Definition representable_group_object
  (P : RepresentablyGroup c) : @GroupObject C CC_CartesianMonoidal c :=
  data_GroupObject c (psh_group_hom_data c P).

Theorem group_object_iff_representable :
  @GroupObject C CC_CartesianMonoidal c ↔ RepresentablyGroup c.
Proof.
  split.
  - exact group_object_representable.
  - exact representable_group_object.
Defined.

End Headline.

(*
   本节说明函子、hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomGrpFunctor.

Context {C : Category}.
Context (e : C).
(*
   本节说明hom、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (HP : forall x : C, PropEquiv (@homset C x e)).
Context (D : HomGroupData e).

(* Named rather than inline: a [Program] record literal cannot carry a
   [PropEquiv] field naming a setoid written inline in the same literal. *)
Definition hom_grp_setoid (x : C) : SetoidObject :=
  {| carrier := x ~> e ; is_setoid := @homset C x e |}.

Program Definition HomGrpObject (x : C) : GrpObject := {|
  grp_setoid := hom_grp_setoid x;
  grp_unit := hmd_unit D;
  grp_mul  := @hmd_mul C e D x;
  grp_inv  := @hgd_inv C e D x;
  grp_prop := HP x
|}.
Next Obligation. now rewrite hmd_assoc. Qed.
Next Obligation. now rewrite hmd_unit_l. Qed.
Next Obligation. now rewrite hgd_inv_l. Qed.

Program Definition HomGrpHom {x y : C} (h : y ~> x) :
  GrpHom (HomGrpObject x) (HomGrpObject y) := {|
  grp_map := {| morphism := fun f => f ∘ h |}
|}.
Next Obligation. now rewrite hmd_unit_natural. Qed.
Next Obligation. now rewrite hmd_mul_natural. Qed.

Program Definition HomGrpFunctor : C^op ⟶ Grp := {|
  fobj := fun x => HomGrpObject x;
  fmap := fun x y (h : x ~{C^op}~> y) => HomGrpHom h
|}.

Definition HomGrpFunctor_Forget_agrees (x : C) :
  carrier (grp_setoid (HomGrpObject x)) = (x ~> e) := eq_refl.

End HomGrpFunctor.

(** ** Round trips, measured strict-first *)

Section RoundTrips.

Context {C : Category}.
Context (e : C).
Context (D : HomGroupData e).

Example data_psh_data_mul {x : C} (f g : x ~> e) :
  hmd_mul (psh_monoid_hom_data e (RepPresheaf_Monoid e (hgd_monoid D))) f g
    = hmd_mul D f g := eq_refl.

Example data_psh_data_unit {x : C} :
  @hmd_unit C e (psh_monoid_hom_data e
                   (RepPresheaf_Monoid e (hgd_monoid D))) x
    = @hmd_unit C e (hgd_monoid D) x := eq_refl.

Example data_psh_data_inv {x : C} (f : x ~> e) :
  hgd_inv (psh_group_hom_data e (RepPresheaf_Group e D)) f
    = hgd_inv D f := eq_refl.

(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example data_psh_data_law {x : C} (f g h : x ~> e) :
  @hmd_assoc C e (psh_monoid_hom_data e
                    (RepPresheaf_Monoid e (hgd_monoid D))) x f g h
    = @hmd_assoc C e (hgd_monoid D) x f g h := eq_refl.

Example data_psh_data_law_control {x : C} (f g h : x ~> e) :
  @hmd_assoc C e (hgd_monoid D) x f g h
    = @hmd_assoc C e (hgd_monoid D) x f g h := eq_refl.

Fail Example data_psh_data_whole :
  psh_group_hom_data e (RepPresheaf_Group e D) = D := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example data_psh_data_whole_control : D = D := eq_refl.

End RoundTrips.

Section RoundTripsObject.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context (c : C).
Context (M : @MonoidObject C CC_Monoidal c).

Example rt_mul_control : rg_mul c M = rg_mul c M := eq_refl.

Fail Example rt_mul_strict :
  rg_mul c (representable_monoid_object c (monoid_object_representable c M))
    = rg_mul c M := eq_refl.

Lemma rt_mul :
  rg_mul c (representable_monoid_object c (monoid_object_representable c M))
    ≈ rg_mul c M.
Proof.
  change (hmul c M exl exr ≈ rg_mul c M).
  unfold hmul.
  now rewrite fork_exl_exr, id_right.
Qed.

Lemma rt_unit :
  rg_unit c (representable_monoid_object c (monoid_object_representable c M))
    ≈ rg_unit c M.
Proof.
  change (@hone C _ _ c M 1 ≈ rg_unit c M).
  unfold hone.
  now rewrite (one_unique (one : 1 ~{C}~> 1) id), id_right.
Qed.

End RoundTripsObject.

(** ** Clause (a): the exponential of a group object

    The group analogue of [Hom_Monoid] (Structure/Monoid.v),
    obtained by transporting the hom-set data along curry/uncurry rather
    than by an internal diagram chase. *)

Section Exponential.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context `{CL : @Closed C _}.
Context (x y : C).

Section ExpMonoid.

Context (D : HomMonoidData y).

Program Definition exp_hom_monoid_data : HomMonoidData (y ^ x) := {|
  hmd_mul := fun z f g => curry (hmd_mul D (uncurry f) (uncurry g));
  hmd_unit := fun z => curry (@hmd_unit C y D (z × x))
|}.
Next Obligation.
  intros f f' Hf g g' Hg.
  now rewrite Hf, Hg.
Qed.
Next Obligation. now rewrite !uncurry_curry, hmd_assoc. Qed.
Next Obligation. now rewrite !uncurry_curry, hmd_unit_l, curry_uncurry. Qed.
Next Obligation. now rewrite !uncurry_curry, hmd_unit_r, curry_uncurry. Qed.
Next Obligation.
  rewrite curry_comp_l, hmd_mul_natural.
  now rewrite <- !uncurry_comp.
Qed.
Next Obligation.
  rewrite curry_comp_l.
  now rewrite hmd_unit_natural.
Qed.

Definition exp_MonoidObject : @MonoidObject C CC_Monoidal (y ^ x) :=
  data_MonoidObject (y ^ x) exp_hom_monoid_data.

End ExpMonoid.

Section ExpCompare.

Context (M : @MonoidObject C CC_Monoidal y).

Definition exp_MonoidObject_of :=
  exp_MonoidObject (monoid_object_hom_data y M).

Example exp_mappend_is_Hom_Monoid :
  @mappend C CC_Monoidal _ exp_MonoidObject_of
    = @mappend C CC_Monoidal _ (@Hom_Monoid C _ _ CL x y M) := eq_refl.

Fail Example exp_mempty_is_Hom_Monoid :
  @mempty C CC_Monoidal _ exp_MonoidObject_of
    = @mempty C CC_Monoidal _ (@Hom_Monoid C _ _ CL x y M) := eq_refl.

Lemma exp_mempty_agrees :
  @mempty C CC_Monoidal _ exp_MonoidObject_of
    ≈ @mempty C CC_Monoidal _ (@Hom_Monoid C _ _ CL x y M).
Proof.
  simpl.
  apply proper_morphism.
  unfold hone.
  now rewrite (one_unique (one : 1 × x ~> 1) exl).
Qed.

End ExpCompare.

Section ExpGroup.

Context (D : HomGroupData y).

Program Definition exp_hom_group_data : HomGroupData (y ^ x) := {|
  hgd_monoid := exp_hom_monoid_data (hgd_monoid D);
  hgd_inv := fun z f => curry (hgd_inv D (uncurry f))
|}.
Next Obligation. intros f f' Hf; now rewrite Hf. Qed.
Next Obligation. now rewrite !uncurry_curry, hgd_inv_l. Qed.
Next Obligation. now rewrite !uncurry_curry, hgd_inv_r. Qed.
Next Obligation.
  rewrite curry_comp_l, hgd_inv_natural.
  now rewrite <- !uncurry_comp.
Qed.

Definition exp_GroupObject : @GroupObject C CC_CartesianMonoidal (y ^ x) :=
  data_GroupObject (y ^ x) exp_hom_group_data.

End ExpGroup.

End Exponential.

(** ** Clause (c): the computation in Sets *)

Require Import Category.Instance.Sets.Products.

Section SetsComputation.

Context (gobj : Sets).
(*
   本节说明 Representable 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (Pg : PropEquiv (is_setoid gobj)).
Context (G : @GroupObject Sets CC_CartesianMonoidal gobj).

Definition sets_group_monoid : @MonoidObject Sets CC_Monoidal gobj :=
  @rg_monoid Sets _ _ gobj G.

Example sets_mul_pointwise (X : Sets) (f h : X ~{Sets}~> gobj)
  (a : carrier X) :
  @hmul Sets _ _ gobj sets_group_monoid X f h a
    = @mappend Sets CC_Monoidal gobj sets_group_monoid (f a, h a)
  := eq_refl.

Example sets_unit_pointwise (X : Sets) (a : carrier X) :
  @hone Sets _ _ gobj sets_group_monoid X a
    = @mempty Sets CC_Monoidal gobj sets_group_monoid ttt := eq_refl.

Example sets_inv_pointwise (X : Sets) (f : X ~{Sets}~> gobj)
  (a : carrier X) :
  @hinv Sets _ _ gobj G X f a = @rg_inv Sets _ _ gobj G (f a) := eq_refl.

Program Definition const_elt (a : carrier gobj) : (1 : Sets) ~{Sets}~> gobj :=
  {| morphism := fun _ => a |}.

Program Definition elem_GrpObject : GrpObject := {|
  grp_setoid := gobj;
  grp_unit := @mempty Sets CC_Monoidal gobj sets_group_monoid ttt;
  grp_mul  := fun a b =>
                @mappend Sets CC_Monoidal gobj sets_group_monoid (a, b);
  grp_inv  := fun a => @rg_inv Sets _ _ gobj G a;
  grp_prop := Pg
|}.
Next Obligation.
  intros u u' Hu v v' Hv; apply proper_morphism; now split.
Qed.
Next Obligation.
  exact (@hmul_assoc Sets _ _ gobj sets_group_monoid _
           (const_elt a) (const_elt b) (const_elt c) ttt).
Qed.
Next Obligation.
  exact (@hmul_unit_l Sets _ _ gobj sets_group_monoid _ (const_elt a) ttt).
Qed.
Next Obligation. exact (@hmul_inv_l Sets _ _ gobj G _ (const_elt a) ttt). Qed.

Definition DiscSet (A : Type) : Sets :=
  {| carrier := A ; is_setoid := eq_Setoid A |}.

Program Definition iprod_GrpObject (A : Type) : GrpObject := {|
  grp_setoid := Sets_iprod_obj (fun _ : A => gobj);
  grp_unit := fun _ => grp_unit elem_GrpObject;
  grp_mul  := fun s t a => grp_mul elem_GrpObject (s a) (t a);
  grp_inv  := fun s a => grp_inv elem_GrpObject (s a);
  (* An indexed product of one propositional setoid, pointwise. *)
  grp_prop := iprod_PropEquiv (fun _ : A => gobj) (fun _ => Pg)
|}.
Next Obligation.
  intros s s' Hs t t' Ht i; now rewrite (Hs i), (Ht i).
Qed.
Next Obligation.
  intro w; exact (grp_mul_assoc elem_GrpObject (a w) (b w) (c w)).
Qed.
Next Obligation. intro w; exact (grp_mul_unit_l elem_GrpObject (a w)). Qed.
Next Obligation. intro w; exact (grp_mul_inv_l elem_GrpObject (a w)). Qed.

Context (A : Type).

(* [HomGrpObject] is applied at [C := Sets], which is not locally
   propositional; its hypothesis is discharged from the section's [Pg]
   through [hom_PropEquiv], which constrains only the CODOMAIN. *)
Definition HomGrpA : GrpObject :=
  @HomGrpObject Sets gobj (fun x : Sets => @hom_PropEquiv x gobj Pg)
                (@group_object_hom_data Sets _ _ gobj G)
                (DiscSet A).

Program Definition sets_hom_to_iprod :
  GrpHom HomGrpA (iprod_GrpObject A) := {|
  grp_map := {| morphism := fun f a => f a |}
|}.
Next Obligation. intro w; reflexivity. Qed.
Next Obligation. intro w; reflexivity. Qed.

Program Definition sets_iprod_to_hom :
  GrpHom (iprod_GrpObject A) HomGrpA := {|
  grp_map := {| morphism := fun s => {| morphism := s |} |}
|}.

Program Definition sets_hom_iprod_iso :
  @Isomorphism Grp HomGrpA (iprod_GrpObject A) := {|
  to := sets_hom_to_iprod;
  from := sets_iprod_to_hom
|}.
Next Obligation. intro w; reflexivity. Qed.

End SetsComputation.
