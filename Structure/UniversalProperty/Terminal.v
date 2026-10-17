Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件给出终对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma poly_unit_uniq (u : poly_unit) : u = ttt.
Proof. now destruct u. Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Terminal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance IsInitialObj_Setoid {C : Category} (c : C) :
  Setoid (IsInitialObj c) := {|
  equiv := fun u v => ∀ x : C, unique_obj (u x) ≈ unique_obj (v x)
|}.
Next Obligation.
  equivalence.
  now transitivity (unique_obj (y x0)).
Qed.

(* 相关说明。 （已译） *)
Lemma IsInitialObj_irrelevant {C : Category} (c : C) (u v : IsInitialObj c) :
  u ≈ v.
Proof. intro x; symmetry; apply (uniqueness (v x)); exact I. Qed.

(* The 函子 being 已表示的: 常值 函子 at singleton
 setoid, i.e. 终对象 [Sets] read diagram over C. （已译） *)
Program Definition ConstOne (C : Category) : C ⟶ Sets := {|
  fobj := fun _ => {| carrier := poly_unit ; is_setoid := Unit_Setoid |};
  fmap := fun _ _ _ => {| morphism := fun u => u |}
|}.

Section InitialUP.
Context (C : Category).

(* Hom(c, −) ⟹ 1: thing map 进入 singleton can be. （已译） *)
Program Definition hom_to_one (c : C) :
  @Transform C Sets [Hom c,─] (ConstOne C) :=
  @Build_Transform' C Sets [Hom c,─] (ConstOne C)
    (fun x => {| morphism := fun _ => ttt |}) _.

(* 1 ⟹ Hom(c, −): pick out canonical arrow `c ~> x`. Naturality is
 precisely uniqueness -- `f ∘ !ₓ ≈ !_y` because both arrows out an
 始对象. （已译） *)
Program Definition one_to_hom (c : C) (u : IsInitialObj c) :
  @Transform C Sets (ConstOne C) [Hom c,─] :=
  @Build_Transform' C Sets (ConstOne C) [Hom c,─]
    (fun x => {| morphism := fun _ => unique_obj (u x) |}) _.
Next Obligation. simpl; intros; symmetry; now apply (uniqueness (u y)). Qed.

(* Initiality of `c` yields the representation Hom(c, −) ≅ 1. *)
Program Definition initial_to_repr (c : C) (u : IsInitialObj c) :
  @Isomorphism ([C, Sets]) [Hom c,─] (ConstOne C) := {|
  to   := hom_to_one c ;
  from := one_to_hom c u
|}.
Next Obligation. simpl; intros; symmetry; apply poly_unit_uniq. Qed.
Next Obligation. simpl; intros; now apply (uniqueness (u x)). Qed.

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition repr_to_initial (c : C)
  (t : @Isomorphism ([C, Sets]) [Hom c,─] (ConstOne C)) : IsInitialObj c :=
  fun x => {| unique_obj := from t x ttt ; unique_property := I |}.
Next Obligation.
  assert (K := iso_from_to t x v).
  simpl in K.
  rewrite (poly_unit_uniq (to t x v)) in K.
  rewrite id_left in K; exact K.
Qed.

(* The instance. Being initial IS 表示 常值-singleton
 函子, 同构 setoids [Sets]. （已译） *)
Definition InitialIsUniversalProperty :
  IsUniversalProperty C (@IsInitialObj C) (@IsInitialObj_Setoid C).
Proof.
  unshelve econstructor; [ exact (ConstOne C) | ].
  intro c; unshelve econstructor.
  - unshelve econstructor.
    + exact (initial_to_repr c).
    + (* 相关说明。 （已译） *)
      abstract (repeat intro; apply to_equiv_implies_iso_equiv;
                intros ? ?; reflexivity).
  - unshelve econstructor.
    + exact (repr_to_initial c).
    + abstract (intros t t' Heq x; exact (snd Heq x ttt)).
  - abstract (simpl; intro t; apply to_equiv_implies_iso_equiv;
              intros ? ?; symmetry; apply poly_unit_uniq).
  - abstract (simpl; intros u x; reflexivity).
Defined.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition initial_obj_unique_up_to_unique_iso (c d : C)
  (Hc : IsInitialObj c) (Hd : IsInitialObj d) :
  Unique (fun _ : c ≅ d => True) := {|
  unique_obj := unique_obj (univ_property_unique_up_to_unique_iso
                              C (@IsInitialObj C) (@IsInitialObj_Setoid C)
                              InitialIsUniversalProperty c d Hc Hd);
  unique_property := I
|}.
Next Obligation.
  apply (uniqueness (univ_property_unique_up_to_unique_iso
                       C (@IsInitialObj C) (@IsInitialObj_Setoid C)
                       InitialIsUniversalProperty c d Hc Hd)).
  apply IsInitialObj_irrelevant.
Qed.

End InitialUP.

(* ---- the terminal case, by instantiation at C^op ---- *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsTerminalObj_op {C : Category} (c : C) :
  IsTerminalObj c -> @IsInitialObj (C^op) c := fun u => u.

Definition op_IsTerminalObj {C : Category} (c : C) :
  @IsInitialObj (C^op) c -> IsTerminalObj c := fun u => u.

(* Terminality 普遍性质: literally initial instance,
 instantiated at opposite 范畴. （已译） *)
Definition TerminalIsUniversalProperty (C : Category) :
  IsUniversalProperty (C^op) (@IsInitialObj (C^op)) (@IsInitialObj_Setoid (C^op))
  := InitialIsUniversalProperty (C^op).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition iso_from_op {C : Category} {x y : C}
  (i : @Isomorphism (C^op) x y) : @Isomorphism C x y := {|
  to   := from i ;
  from := to i
|}.
Next Obligation. exact (iso_to_from i). Qed.
Next Obligation. exact (iso_from_to i). Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition terminal_obj_unique_up_to_unique_iso {C : Category} (c d : C)
  (Hc : IsTerminalObj c) (Hd : IsTerminalObj d) :
  Unique (fun _ : c ≅ d => True) := {|
  unique_obj :=
    iso_from_op (unique_obj (initial_obj_unique_up_to_unique_iso
                               (C^op) c d (IsTerminalObj_op c Hc)
                                          (IsTerminalObj_op d Hd)));
  unique_property := I
|}.
Next Obligation.
  assert (K := uniqueness (initial_obj_unique_up_to_unique_iso
                             (C^op) c d (IsTerminalObj_op c Hc)
                                        (IsTerminalObj_op d Hd))
                          (Isomorphism_Opposite v) I).
  destruct K as [K1 K2].
  split; [ exact K2 | exact K1 ].
Qed.

(* ---- bundled structures satisfy 对象-level predicates ---- （已译） *)

Program Definition Terminal_IsTerminalObj {C : Category} (T : @Terminal C) :
  IsTerminalObj (@terminal_obj C T) :=
  fun x => {| unique_obj := @one C T x ; unique_property := I |}.
Next Obligation. apply (@one_unique C T). Qed.

Program Definition Initial_IsInitialObj {C : Category} (I0 : @Initial C) :
  IsInitialObj (@initial_obj C I0) :=
  fun x => {| unique_obj := @zero C I0 x ; unique_property := I |}.
Next Obligation. apply (@zero_unique C I0). Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition terminal_unique_up_to_unique_iso_via_UP {C : Category}
  (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ≅ @terminal_obj C T2 => True) :=
  terminal_obj_unique_up_to_unique_iso _ _
    (Terminal_IsTerminalObj T1) (Terminal_IsTerminalObj T2).

Definition initial_unique_up_to_unique_iso_via_UP {C : Category}
  (I1 I2 : @Initial C) :
  Unique (fun _ : @initial_obj C I1 ≅ @initial_obj C I2 => True) :=
  initial_obj_unique_up_to_unique_iso C _ _
    (Initial_IsInitialObj I1) (Initial_IsInitialObj I2).

(** ------------------------------------------------------------------------ *)