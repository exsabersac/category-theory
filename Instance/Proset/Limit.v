Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/thin+category
 nLab: https://ncatlab.org/nlab/show/join
 Wikipedia: https://en.wikipedia.org/wiki/Infimum_and_supremum

   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Bounds over a preorder *)

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* [m] is a lower bound of the family [d]. *)
Definition IsLowerBound {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type :=
  ∀ i : Ix, R m (d i).

(* [m] is a greatest lower bound (an infimum, a meet) of [d]: a lower
   bound that every other lower bound precedes. *)
Definition IsGLB {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type :=
  IsLowerBound R d m * (∀ n : A, IsLowerBound R d n → R n m).

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition op_rel {A : Type} (R : relation A) : relation A :=
  fun x y => R y x.

Definition op_PreOrder {A : Type} {R : relation A} (P : PreOrder R) :
  PreOrder (op_rel R) :=
  {| PreOrder_Reflexive := fun x => @PreOrder_Reflexive A R P x;
     PreOrder_Transitive :=
       fun x y z Hxy Hyz => @PreOrder_Transitive A R P z y x Hyz Hxy |}.

Definition IsUpperBound {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type := IsLowerBound (op_rel R) d m.

Definition IsLUB {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type := IsGLB (op_rel R) d m.

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition glb_unique {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m m' : A) (G : IsGLB R d m) (G' : IsGLB R d m') :
  R m m' * R m' m :=
  (snd G' m (fst G), snd G m' (fst G')).

Definition lub_unique {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m m' : A) (G : IsLUB R d m) (G' : IsLUB R d m') :
  R m' m * R m m' :=
  glb_unique (op_rel R) d m m' G G'.

(* The binary family, used to read a two-element meet as a product. *)
Definition pair_family {A : Type} (x y : A) : bool → A :=
  fun b => if b then x else y.

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition empty_family {A : Type} : False → A := fun e => match e with end.

Lemma greatest_iff_empty_glb {A : Type} (R : relation A) (top : A) :
  (∀ x, R x top) ↔ IsGLB R (@empty_family A) top.
Proof.
  split.
  - intro Htop; split; [ intros [] | intros n _; exact (Htop n) ].
  - intros [_ Hg] x; exact (Hg x (fun e => match e with end)).
Qed.

Definition least_iff_empty_lub {A : Type} (R : relation A) (bot : A) :
  (∀ x, R bot x) ↔ IsLUB R (@empty_family A) bot :=
  greatest_iff_empty_glb (op_rel R) bot.

(* Completeness order, form bicompleteness statement
 所消耗 below. （已译） *)
Definition HasAllMeets {A : Type} (R : relation A) : Type :=
  ∀ (Ix : Type) (d : Ix → A), { m : A & IsGLB R d m }.

Definition HasAllJoins {A : Type} (R : relation A) : Type :=
  HasAllMeets (op_rel R).

Section Proset_Limits.

Context {A : Type} {R : relation A} (P : PreOrder R).

(** ** Thinness, stated concretely *)

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma proset_equiv_is_True (x y : A) (f g : x ~{Proset P}~> y) :
  (f ≈ g) = True.
Proof. reflexivity. Qed.

(** ** Binary products are meets *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cartesian_product_IsGLB (CP : @Cartesian (Proset P)) (x y : A) :
  IsGLB R (pair_family x y) (@product_obj (Proset P) CP x y).
Proof.
  split.
  - intros [|].
    + exact (@exl (Proset P) CP x y).
    + exact (@exr (Proset P) CP x y).
  - intros n Hn.
    exact (@fork (Proset P) CP n x y (Hn true) (Hn false)).
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Proset_Cartesian
  (glb : A → A → A)
  (glb_l : ∀ x y, R (glb x y) x)
  (glb_r : ∀ x y, R (glb x y) y)
  (glb_greatest : ∀ n x y, R n x → R n y → R n (glb x y)) :
  @Cartesian (Proset P) := {|
  product_obj := glb;
  fork := fun x y z f g => glb_greatest x y z f g;
  exl := fun x y => glb_l x y;
  exr := fun x y => glb_r x y
|}.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Proset_Cocartesian
  (lub : A → A → A)
  (lub_l : ∀ x y, R x (lub x y))
  (lub_r : ∀ x y, R y (lub x y))
  (lub_least : ∀ n x y, R x n → R y n → R (lub x y) n) :
  @Cocartesian (Proset P) := {|
  product_obj := lub;
  fork := fun x y z f g => lub_least x y z f g;
  exl := fun x y => lub_l x y;
  exr := fun x y => lub_r x y
|}.

(* The dual of [cartesian_product_IsGLB]: a chosen coproduct is a join. *)
Lemma cocartesian_coproduct_IsLUB (CP : @Cocartesian (Proset P)) (x y : A) :
  IsLUB R (pair_family x y) (@product_obj ((Proset P)^op) CP x y).
Proof.
  split.
  - intros [|].
    + exact (@exl ((Proset P)^op) CP x y).
    + exact (@exr ((Proset P)^op) CP x y).
  - intros n Hn.
    exact (@fork ((Proset P)^op) CP n x y (Hn true) (Hn false)).
Qed.

(* 相关说明。 （已译） *)

Program Definition Proset_Terminal (top : A) (Htop : ∀ x, R x top) :
  @Terminal (Proset P) := {| terminal_obj := top; one := Htop |}.

Definition terminal_is_greatest (T : @Terminal (Proset P)) :
  ∀ x, R x (@terminal_obj (Proset P) T) := fun x => @one (Proset P) T x.

(* 相关说明。 （已译） *)
Program Definition Proset_Initial (bot : A) (Hbot : ∀ x, R bot x) :
  @Initial (Proset P) := {| terminal_obj := bot; one := Hbot |}.

Definition initial_is_least (Iobj : @Initial (Proset P)) :
  ∀ x, R (@terminal_obj ((Proset P)^op) Iobj) x :=
  fun x => @one ((Proset P)^op) Iobj x.

(* 相关说明。 （已译） *)

(** ** Cones over a thin category *)

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition proset_cone {J : Category} (F : J ⟶ Proset P) (n : A)
  (Hn : IsLowerBound R (fobj[F]) n) : Cone F.
Proof.
  unshelve econstructor.
  - exact n.                             (* apex: the candidate bound *)
  - unshelve econstructor.
    + exact Hn.                          (* legs: the lower-bound clause *)
    + intros x y f; exact Logic.I.       (* coherence: degenerate, thin *)
Defined.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition proset_op_cone {J : Category} (G : J ⟶ (Proset P)^op) (n : A)
  (Hn : ∀ j : J, R (G j) n) : Cone G.
Proof.
  unshelve econstructor.
  - exact n.
  - unshelve econstructor.
    + exact Hn.
    + intros x y f; exact Logic.I.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Proset_IsALimit {J : Category} (F : J ⟶ Proset P) (m : A)
  (H : IsGLB R (fobj[F]) m) : IsALimit F m.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + exact (fst H).
    + intros x y f; exact Logic.I.
  - intro N.
    unshelve econstructor.
    + exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
    + intro x; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

Definition isalimit_IsGLB {J : Category} (F : J ⟶ Proset P) (c : A)
  (H : IsALimit F c) : IsGLB R (fobj[F]) c.
Proof.
  split.
  - exact (fun j => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) j).
  - intros n Hn.
    exact (unique_obj (@ump_limit _ _ _ _ H (proset_cone F n Hn))).
Defined.

Theorem proset_limit_iff_glb {J : Category} (F : J ⟶ Proset P) (c : A) :
  IsALimit F c ↔ IsGLB R (fobj[F]) c.
Proof.
  split.
  - exact (isalimit_IsGLB F c).
  - exact (Proset_IsALimit F c).
Defined.

(* 相关说明。 （已译） *)
Program Definition Proset_Limit_general {J : Category} (F : J ⟶ Proset P)
  (m : A) (H : IsGLB R (fobj[F]) m) : Limit F := {|
  limit_cone := proset_cone F m (fst H)
|}.
Next Obligation.
  unshelve econstructor.
  - exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
  - intro x; exact Logic.I.
  - intros v Hv; exact Logic.I.
Defined.

Definition limit_general_IsGLB {J : Category} (F : J ⟶ Proset P)
  (L : Limit F) : IsGLB R (fobj[F]) (vertex_obj[L]) :=
  isalimit_IsGLB F _ (limit_is_alimit L).

(* Dually: an object is a colimit of [F] exactly when it is a least
   upper bound of the family of objects of [F]. [IsAColimit F c] is
   [IsALimit (F^op) c] (Structure/Limit/Preservation.v), whose legs run
   [F j ~> c] in [Proset P], that is [R (F j) c]. *)

Definition Proset_IsAColimit {J : Category} (F : J ⟶ Proset P) (m : A)
  (H : IsLUB R (fobj[F]) m) : IsAColimit F m.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + exact (fst H).
    + intros x y f; exact Logic.I.
  - intro N.
    unshelve econstructor.
    + exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
    + intro x; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

Definition isacolimit_IsLUB {J : Category} (F : J ⟶ Proset P) (c : A)
  (H : IsAColimit F c) : IsLUB R (fobj[F]) c.
Proof.
  split.
  - exact (fun j => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) j).
  - intros n Hn.
    exact (unique_obj (@ump_limit _ _ _ _ H (proset_op_cone (F^op) n Hn))).
Defined.

Theorem proset_colimit_iff_lub {J : Category} (F : J ⟶ Proset P) (c : A) :
  IsAColimit F c ↔ IsLUB R (fobj[F]) c.
Proof.
  split.
  - exact (isacolimit_IsLUB F c).
  - exact (Proset_IsAColimit F c).
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Proset_Limit {Ix : Type} (d : Ix → A) (m : A)
  (H : IsGLB R d m) :
  Limit (DiscreteCat_Functor (C:=Proset P) d) :=
  Proset_Limit_general (DiscreteCat_Functor (C:=Proset P) d) m H.

Definition limit_IsGLB {Ix : Type} (d : Ix → A)
  (L : Limit (DiscreteCat_Functor (C:=Proset P) d)) :
  IsGLB R d (iprod (C:=Proset P) d L).
Proof.
  split.
  - intro i; exact (iprod_proj (C:=Proset P) d L i).
  - intros n Hn.
    exact (unique_obj (iprod_ump (C:=Proset P) d L n Hn)).
Defined.

(* 相关说明。 （已译） *)
Definition Proset_IsIndexedProduct {Ix : Type} (d : Ix → A) (m : A)
  (H : IsGLB R d m) :
  IsIndexedProduct (C:=Proset P) d m (fst H).
Proof.
  constructor; intros c pi.
  unshelve econstructor.
  - exact (snd H c pi).
  - intro a; exact Logic.I.
  - intros v Hv; exact Logic.I.
Defined.

(** ** Bicompleteness *)

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem proset_Complete_iff_all_meets :
  @Complete (Proset P) ↔ HasAllMeets R.
Proof.
  split.
  - intros HC Ix d.
    exists (vertex_obj[HC (DiscreteCat Ix)
                          (@DiscreteCat_Functor Ix (Proset P) d)]).
    exact (limit_general_IsGLB
             (@DiscreteCat_Functor Ix (Proset P) d)
             (HC (DiscreteCat Ix) (@DiscreteCat_Functor Ix (Proset P) d))).
  - intros HM D F.
    exact (Proset_Limit_general F
             (projT1 (HM (obj[D]) (fun j : D => F j)))
             (projT2 (HM (obj[D]) (fun j : D => F j)))).
Defined.

(** ** Pushouts from joins *)

(*
   本节说明（余）极限、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Proset_HasPushouts
  (lub : A → A → A)
  (lub_l : ∀ x y, R x (lub x y))
  (lub_r : ∀ x y, R y (lub x y))
  (lub_least : ∀ n x y, R x n → R y n → R (lub x y) n) :
  HasPushouts (Proset P) := {| pushout := fun x y z f g => _ |}.
Next Obligation.
  unshelve econstructor.
  - exact (lub y z).
  - exact (lub_l y z).
  - exact (lub_r y z).
  - exact Logic.I.
  - intros q i1 i2 Hc.
    unshelve econstructor.
    + exact (lub_least q y z i1 i2).
    + split; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

(* 相关说明。 （已译） *)
Lemma proset_pushout_IsLUB {x y z : A}
  (f : x ~{Proset P}~> y) (g : x ~{Proset P}~> z)
  (Q : IsPushout (C:=Proset P) f g) :
  IsLUB R (pair_family y z) (pushout_apex Q).
Proof.
  split.
  - intros [|].
    + exact (pushout_in1 Q).
    + exact (pushout_in2 Q).
  - intros n Hn.
    exact (unique_obj (pushout_ump Q n (Hn true) (Hn false) Logic.I)).
Qed.

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem proset_Cocomplete_iff_all_joins : @Cocomplete (Proset P) ↔ HasAllJoins R.
Proof.
  split.
  - intros HC Ix d.
    exists (vertex_obj[HC (DiscreteCat Ix)
                        (@DiscreteCat_Functor Ix (Proset P) d)]).
    exact (isacolimit_IsLUB (@DiscreteCat_Functor Ix (Proset P) d) _
             (limit_is_alimit (HC (DiscreteCat Ix)
                                 (@DiscreteCat_Functor Ix (Proset P) d)))).
  - intros HJ D F.
    unshelve econstructor.
    + exact (proset_op_cone (F^op)
               (projT1 (HJ (obj[D]) (fun j : D => F j)))
               (fst (projT2 (HJ (obj[D]) (fun j : D => F j))))).
    + intro N.
      unshelve econstructor.
      * exact (snd (projT2 (HJ (obj[D]) (fun j : D => F j))) _
                 (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
      * intro x; exact Logic.I.
      * intros v Hv; exact Logic.I.
Defined.

(*
   本节说明拉回/推出、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition pushout_is_coproduct_of_feet (CP : @Cocartesian (Proset P))
  {x y z : A} (f : x ~{Proset P}~> y) (g : x ~{Proset P}~> z)
  (Q : IsPushout (C:=Proset P) f g) :
  R (@product_obj ((Proset P)^op) CP y z) (pushout_apex Q)
  * R (pushout_apex Q) (@product_obj ((Proset P)^op) CP y z) :=
  lub_unique R (pair_family y z) (pushout_apex Q)
    (@product_obj ((Proset P)^op) CP y z)
    (proset_pushout_IsLUB f g Q)
    (cocartesian_coproduct_IsLUB CP y z).

End Proset_Limits.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Proset_LUB_Limit {A : Type} {R : relation A} (P : PreOrder R)
  {Ix : Type} (d : Ix → A) (m : A) (H : IsLUB R d m) :
  Limit (DiscreteCat_Functor (C:=Proset (op_PreOrder P)) d) :=
  Proset_Limit (op_PreOrder P) d m H.

(* Named what it concludes: [Complete] at REVERSED preorder. The
 genuine cocompleteness 推论 follows biconditional above. （已译） *)
Definition Proset_op_Complete_of_all_joins {A : Type} {R : relation A}
  (P : PreOrder R) (H : HasAllJoins R) :
  @Complete (Proset (op_PreOrder P)) :=
  snd (proset_Complete_iff_all_meets (op_PreOrder P)) H.

Definition Proset_Cocomplete_of_all_joins {A : Type} {R : relation A}
  (P : PreOrder R) (H : HasAllJoins R) :
  @Cocomplete (Proset P) :=
  snd (proset_Cocomplete_iff_all_joins P) H.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Complete_Invariance.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

Definition Complete_equivalence_invariant (HC : @Complete C) : @Complete D :=
  fun J H =>
    @equivalence_creates_limits D C (@quasi_inverse C D F E)
      (@EquivalenceOfCategories_sym C D F E) J H
      (HC J (@quasi_inverse C D F E ◯ H)).

Definition Cocomplete_equivalence_invariant (HC : @Cocomplete C) :
  @Cocomplete D :=
  fun J H =>
    @equivalence_creates_colimits D C (@quasi_inverse C D F E)
      (@EquivalenceOfCategories_sym C D F E) J H
      (HC J (@quasi_inverse C D F E ◯ H)).

End Complete_Invariance.

(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hom_le (C : Category) (x y : C) : Prop := inhabited (x ~{C}~> y).

Program Definition hom_le_preorder (C : Category) : PreOrder (hom_le C) :=
  Build_PreOrder _ _ _.
Next Obligation. intro x; exact (inhabits id). Qed.
Next Obligation. intros x y z [f] [g]; exact (inhabits (g ∘ f)). Qed.

Definition cartesian_is_glb (C : Category) (CP : @Cartesian C) (x y : C) :
  IsGLB (hom_le C) (pair_family x y) (@product_obj C CP x y).
Proof.
  split.
  - intros [|].
    + exact (inhabits (@exl C CP x y)).
    + exact (inhabits (@exr C CP x y)).
  - intros n Hn.
    destruct (Hn true) as [f]; destruct (Hn false) as [g].
    exact (inhabits (@fork C CP n x y f g)).
Defined.

Definition cocartesian_is_lub (C : Category) (CP : @Cocartesian C) (x y : C) :
  IsLUB (hom_le C) (pair_family x y) (@product_obj (C^op) CP x y) :=
  cartesian_is_glb (C^op) CP x y.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition props_product_is_glb (p q : Prop) :=
  cartesian_is_glb Props Props_Cartesian p q.

Definition props_coproduct_is_lub (p q : Prop) :=
  cocartesian_is_lub Props Props_Cocartesian p q.

Definition two_product_is_glb (x y : TwoObj) :=
  cartesian_is_glb _2 Two_Cartesian x y.

(* 相关说明。 （已译） *)

(* [Instance/Proset.v]'s [LessThanEqualTo_Category] is the thin category
   of [(nat, <=)]. The name is also defined in Instance/Poset.v, over
   [Poset] rather than [Proset]; it is written qualified here so the
   intended one is unambiguous. *)
Definition Nat_Proset : Category :=
  Category.Instance.Proset.LessThanEqualTo_Category.

(* [Nat.min] binary meet [<=], so it produces genuine
 cartesian structure thin 范畴. （已译） *)
Definition Nat_Cartesian : @Cartesian Nat_Proset :=
  Proset_Cartesian Nat.le_preorder Nat.min
    Nat.le_min_l Nat.le_min_r
    (fun n x y Hx Hy => Nat.min_glb x y n Hx Hy).

Definition nat_meet (x y : nat) : nat :=
  @product_obj Nat_Proset Nat_Cartesian x y.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example nat_product_3_5 : nat_meet 3 5 = 3%nat := eq_refl.

Definition nat_product_IsGLB (x y : nat) :
  IsGLB le (pair_family x y) (@product_obj Nat_Proset Nat_Cartesian x y) :=
  cartesian_product_IsGLB Nat.le_preorder Nat_Cartesian x y.

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma nat_glb_not_4 : IsGLB le (pair_family 3%nat 5%nat) 4%nat → False.
Proof.
  intros [Hlb _].
  pose proof (Hlb true) as H4.
  apply Nat.nle_succ_diag_l with (n:=3%nat).
  exact H4.
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Nat_Initial : @Initial Nat_Proset :=
  Proset_Initial Nat.le_preorder 0%nat Nat.le_0_l.

(* 相关说明。 （已译） *)
#[export] Existing Instance Nat_Initial.

(* A terminal object of this thin category would be an upper bound of
   every natural, in particular of its own successor. *)
Theorem Nat_no_Terminal : @Terminal Nat_Proset → False.
Proof.
  intros T.
  pose proof (@one Nat_Proset T (S (@terminal_obj Nat_Proset T))) as H.
  simpl in H.
  exact (Nat.nle_succ_diag_l _ H).
Qed.

Definition nat_indexed_limit (x y : nat) :
  Limit (DiscreteCat_Functor (C:=Nat_Proset) (pair_family x y)) :=
  Proset_Limit Nat.le_preorder (pair_family x y) (Nat.min x y)
    (nat_product_IsGLB x y).

(* 相关说明。 （已译） *)

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition bool_eq_preorder : PreOrder (@eq bool) :=
  Build_PreOrder (@eq bool) (@eq_Reflexive bool) (@eq_Transitive bool).

Lemma discrete_two_no_initial :
  @Initial (Proset bool_eq_preorder) → False.
Proof.
  intro Iobj.
  pose proof (initial_is_least bool_eq_preorder Iobj true) as Ht.
  pose proof (initial_is_least bool_eq_preorder Iobj false) as Hf.
  rewrite Ht in Hf; discriminate.
Qed.

Lemma discrete_two_no_cartesian :
  @Cartesian (Proset bool_eq_preorder) → False.
Proof.
  intro CP.
  assert (Hl : @product_obj (Proset bool_eq_preorder) CP true false = true)
    by exact (@exl (Proset bool_eq_preorder) CP true false).
  assert (Hr : @product_obj (Proset bool_eq_preorder) CP true false = false)
    by exact (@exr (Proset bool_eq_preorder) CP true false).
  rewrite Hl in Hr; discriminate.
Qed.
