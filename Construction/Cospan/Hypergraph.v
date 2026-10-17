Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Span.Category.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(*
   nLab: https://ncatlab.org/nlab/show/hypergraph+category
   nLab: https://ncatlab.org/nlab/show/Frobenius+algebra
   Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、（余）极限、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CospanHypergraphData.

Context {C : Category}.
Context `{@Cocartesian C}.
Context `{@Initial C}.
Context (HP : HasPushouts C).

(** ** Object-level tensor and unit *)

Definition Cospan_tensor_obj (X Y : C) : C := X + Y.
Definition Cospan_unit_obj : C := initial_obj.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cospan_tensor
           {X Y X' Y' : C}
           (f : CospanArrow X Y) (g : CospanArrow X' Y')
  : CospanArrow (X + X') (Y + Y') :=
  Build_CospanArrow (cospan_apex f + cospan_apex g)
                    (cover (cospan_in1 f) (cospan_in1 g))
                    (cover (cospan_in2 f) (cospan_in2 g)).

(* * ** SCFA-witness data each 对象 [X] （已译） *)

(** Multiplication [μ_X] : cospan [X + X] [X] apex [X],
 leg1 = codiagonal [id ▽ id], leg2 = 恒等. （已译） *)
Definition cospan_scfa_mu (X : C) : CospanArrow (X + X) X :=
  Build_CospanArrow X (id[X] ▽ id[X]) id[X].

(** Unit [η_X] : cospan [0] [X] apex [X],
 leg1 = [zero], leg2 = 恒等. （已译） *)
Definition cospan_scfa_eta (X : C) : CospanArrow Cospan_unit_obj X :=
  Build_CospanArrow X zero id[X].

(** Comultiplication [δ_X] : cospan [X] [X + X] apex [X],
 leg1 = 恒等, leg2 = codiagonal.

 Note: cospan X X+X, leg1 : X ~> apex leg2 : X+X ~> apex. （已译） *)
Definition cospan_scfa_delta (X : C) : CospanArrow X (X + X) :=
  Build_CospanArrow X id[X] (id[X] ▽ id[X]).

(** 本节：Counit [ε_X] : cospan [X] [0] apex [X], leg1 = id, leg2 = zero. （已译） *)
Definition cospan_scfa_epsilon (X : C) : CospanArrow X Cospan_unit_obj :=
  Build_CospanArrow X id[X] zero.

End CospanHypergraphData.

Arguments Cospan_tensor_obj {C _} X Y.
Arguments Cospan_unit_obj   {C _}.
Arguments cospan_tensor     {C _} {X Y X' Y'} f g.
Arguments cospan_scfa_mu      {C _} X.
Arguments cospan_scfa_eta     {C _} X.
Arguments cospan_scfa_delta   {C _} X.
Arguments cospan_scfa_epsilon {C _} X.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CospanTensorBasics.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(** Tensor 恒等 cospans 恒等 cospan, witnessed the
 codiagonal 恒等 [inl ▽ inr ≈ id]. （已译） *)
Lemma cospan_tensor_id (X Y : C) :
  cospan_equiv (cospan_tensor (cospan_id X) (cospan_id Y))
               (cospan_id (X + Y)).
Proof.
  unfold cospan_tensor, cospan_id; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    apply merge_inl_inr.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    apply merge_inl_inr.
Defined.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cospan_tensor_respects
      {X Y X' Y' : C}
      (f f' : CospanArrow X Y) (g g' : CospanArrow X' Y') :
  cospan_equiv f f' ->
  cospan_equiv g g' ->
  cospan_equiv (cospan_tensor f g) (cospan_tensor f' g').
Proof.
  intros [phi [Hf1 Hf2]] [psi [Hg1 Hg2]].
  unfold cospan_tensor; simpl.
  exists (@coprod_respects_iso C H_Coc _ _ phi _ _ psi); simpl; split.
  - (* cover (to phi) (to psi) ∘ cover (cospan_in1 f) (cospan_in1 g)
       ≈ cover (cospan_in1 f') (cospan_in1 g') *)
    rewrite cover_comp.
    rewrite Hf1, Hg1.
    reflexivity.
  - rewrite cover_comp.
    rewrite Hf2, Hg2.
    reflexivity.
Defined.

End CospanTensorBasics.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CospanSCFALaws.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(*
   本节说明幺半结构、拉回/推出、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

End CospanSCFALaws.

(*
   本节说明幺半结构、函子、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MorphismAsCospan.

Context {C : Category}.

Definition mor_as_cospan {X Y : C} (f : X ~> Y) : CospanArrow X Y :=
  Build_CospanArrow Y f id[Y].

(** Identity in C lifts to the identity cospan. *)
Lemma mor_as_cospan_id (X : C) :
  cospan_equiv (mor_as_cospan id[X]) (cospan_id X).
Proof.
  unfold mor_as_cospan, cospan_id; simpl.
  exists iso_id; simpl; split; cat.
Defined.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mor_iso_as_cospan_iso {X Y : C} (phi : X ≅ Y) :
  CospanArrow X Y := mor_as_cospan (to phi).

(** [mor_as_cospan] respects [≈] on the C-morphism. *)
Lemma mor_as_cospan_proper {X Y : C} (f g : X ~> Y) :
  f ≈ g -> cospan_equiv (mor_as_cospan f) (mor_as_cospan g).
Proof.
  intros Hfg.
  unfold mor_as_cospan; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left.
    exact Hfg.
  - cat.
Defined.

#[export] Program Instance mor_as_cospan_Proper {X Y : C} :
  Proper (equiv ==> equiv) (mor_as_cospan (X := X) (Y := Y)).
Next Obligation.
  intros f g Hfg.
  apply mor_as_cospan_proper, Hfg.
Defined.

(* 相关说明。 （已译） *)

Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.

(** Left unitor cospan:  cospan from [0 + X] to [X]. *)
Definition cospan_unit_left (X : C) : CospanArrow (0 + X)%object X :=
  mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini X)).

(** Right unitor cospan:  cospan from [X + 0] to [X]. *)
Definition cospan_unit_right (X : C) : CospanArrow (X + 0)%object X :=
  mor_as_cospan (to (@coprod_zero_r C H_Coc H_Ini X)).

(** Associator cospan:  cospan from [(X + Y) + Z] to [X + (Y + Z)]. *)
Definition cospan_tensor_assoc (X Y Z : C)
  : CospanArrow ((X + Y) + Z)%object (X + (Y + Z))%object :=
  mor_as_cospan (to (@coprod_assoc C H_Coc X Y Z)).

(** Braid cospan:  cospan from [X + Y] to [Y + X]. *)
Definition cospan_braid (X Y : C) : CospanArrow (X + Y)%object (Y + X)%object :=
  mor_as_cospan (to (@coprod_comm C H_Coc X Y)).

End MorphismAsCospan.

Arguments mor_as_cospan {C X Y} f.
Arguments cospan_unit_left {C _ _} X.
Arguments cospan_unit_right {C _ _} X.
Arguments cospan_tensor_assoc {C _} X Y Z.
Arguments cospan_braid {C _} X Y.

(*
   本节说明函子、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PushoutIdCollapse.

Context {C : Category}.
Context (HP : HasPushouts C).

(** Pushout of [(id_Y, g)] collapses to Z (the codomain of g). *)
Lemma pushout_id_left_apex {Y Z : C} (g : Y ~> Z) :
  pushout_apex (pushout id[Y] g) ≅ Z.
Proof.
  set (P := pushout id[Y] g).
  assert (Hcomm : g ∘ id ≈ id ∘ g) by cat.
  set (m := pushout_med P Hcomm).
  assert (Hm1 : m ∘ pushout_in1 P ≈ g) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ id[Z]) by (apply pushout_med_in2).
  refine {| to   := m;
            from := pushout_in2 P;
            iso_to_from := _;
            iso_from_to := _ |}.
  - exact Hm2.
  - (* pushout_in2 P ∘ m ≈ id at apex P, by uniqueness on identity cocone. *)
    transitivity (pushout_med P (pushout_commutes P)).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc, Hm1.
        pose proof (pushout_commutes P) as PC.
        rewrite <- PC; cat.
      * rewrite <- comp_assoc, Hm2; cat.
    + apply pushout_med_unique; cat.
Defined.

(** Pushout of [(g, id_Y)] collapses to Z (codomain of g). *)
Lemma pushout_id_right_apex {Y Z : C} (g : Y ~> Z) :
  pushout_apex (pushout g id[Y]) ≅ Z.
Proof.
  set (P := pushout g id[Y]).
  assert (Hcomm : id ∘ g ≈ g ∘ id) by cat.
  set (m := pushout_med P Hcomm).
  assert (Hm1 : m ∘ pushout_in1 P ≈ id[Z]) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ g) by (apply pushout_med_in2).
  refine {| to   := m;
            from := pushout_in1 P;
            iso_to_from := _;
            iso_from_to := _ |}.
  - exact Hm1.
  - transitivity (pushout_med P (pushout_commutes P)).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc, Hm1; cat.
      * rewrite <- comp_assoc, Hm2.
        pose proof (pushout_commutes P) as PC.
        rewrite PC; cat.
    + apply pushout_med_unique; cat.
Defined.

End PushoutIdCollapse.

(* * ** [mor_as_cospan] functorial

 Composition two 态射-as-cospans agrees 态射-as-
 cospan 复合. Witnessed via pushout-of-id collapse. （已译） *)

Section MorAsCospanFunctorial.

Context {C : Category}.
Context (HP : HasPushouts C).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mor_as_cospan_compose {X Y Z : C} (g : Y ~> Z) (f : X ~> Y) :
  cospan_equiv
    (cospan_compose HP (mor_as_cospan g) (mor_as_cospan f))
    (mor_as_cospan (g ∘ f)).
Proof.
  unfold cospan_compose, mor_as_cospan; simpl.
  pose (P := pushout (id[Y] : Y ~{C}~> Y) g).
  (* Apex of LHS is pushout_apex P; apex of RHS is Z.
     pushout_id_left_apex gives the iso pushout_apex P ≅ Z. *)
  exists (pushout_id_left_apex HP g); simpl.
  split.
  - (* to (collapse) ∘ (pushout_in1 P ∘ f) ≈ g ∘ f *)
    rewrite comp_assoc.
    apply compose_respects; [|reflexivity].
    (* to (collapse) ∘ 推出_in1 P ≈ g; 定义 推出_id_left_apex,
 [to] is [pushout_med P (Hcomm: g ∘ id ≈ id ∘ g)], its first
 leg equation is [m ∘ pushout_in1 P ≈ g].（已译） *)
    apply pushout_med_in1.
  - (* to (collapse) ∘ (pushout_in2 P ∘ id) ≈ id *)
    rewrite (id_right (pushout_in2 _)).
    apply pushout_med_in2.
Defined.

End MorAsCospanFunctorial.

(*
   本节说明函子、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PushoutCoproductCompat.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pushout_cover_split_cocone
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g') :
  cover (pushout_in1 P) (pushout_in1 P') ∘ cover f f'
  ≈ cover (pushout_in2 P) (pushout_in2 P') ∘ cover g g'.
Proof.
  rewrite !cover_comp.
  pose proof (pushout_commutes P) as PC.
  pose proof (pushout_commutes P') as PC'.
  unfold pushout_in1, pushout_in2 in *.
  rewrite PC, PC'.
  reflexivity.
Qed.

(** Forward iso direction: pushout of covers ⟶ coproduct of pushouts. *)
Definition pushout_cover_split
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g'))
  : pushout_apex Pcov ~> (pushout_apex P + pushout_apex P')%object
  := pushout_med Pcov (pushout_cover_split_cocone f g f' g' P P').

(** Sub-cocone: pushout_in1 Pcov composed [inl] leg 进入
 pushout-of-covers apex via X-side coproduct. （已译） *)
Lemma pushout_cover_left_cocone
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  (pushout_in1 Pcov ∘ inl) ∘ f
  ≈ (pushout_in2 Pcov ∘ inl) ∘ g.
Proof.
  pose proof (pushout_commutes Pcov) as PC.
  rewrite <- !comp_assoc.
  rewrite <- (cover_inl f f').
  rewrite <- (cover_inl g g').
  rewrite !comp_assoc.
  rewrite PC.
  reflexivity.
Qed.

Lemma pushout_cover_right_cocone
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  (pushout_in1 Pcov ∘ inr) ∘ f'
  ≈ (pushout_in2 Pcov ∘ inr) ∘ g'.
Proof.
  pose proof (pushout_commutes Pcov) as PC.
  rewrite <- !comp_assoc.
  rewrite <- (cover_inr f f').
  rewrite <- (cover_inr g g').
  rewrite !comp_assoc.
  rewrite PC.
  reflexivity.
Qed.

(** Reverse iso direction: coproduct of pushouts ⟶ pushout of covers.
    Built via two applications of [pushout_med] (one per component),
    combined by [merge]. *)
Definition pushout_cover_combine
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g'))
  : (pushout_apex P + pushout_apex P')%object ~> pushout_apex Pcov :=
  merge (pushout_med P (pushout_cover_left_cocone f g f' g' Pcov))
        (pushout_med P' (pushout_cover_right_cocone f g f' g' Pcov)).

(* 相关说明。 （已译） *)

Lemma pushout_cover_split_combine
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  pushout_cover_combine f g f' g' P P' Pcov
    ∘ pushout_cover_split f g f' g' P P' Pcov
  ≈ id.
Proof.
  unfold pushout_cover_combine, pushout_cover_split.
  (* Use joint-epi via [fork_inv]: 态射 余积 is determined
 its restrictions inl/inr. The plan:
 1. transitive through 推出_med Pcov (推出_commutes Pcov)
 2. apply 推出_med_唯一
 3. each 推出-in, use cover_inl / cover_inr split.（已译） *)
  transitivity (pushout_med Pcov (pushout_commutes Pcov)).
  - symmetry.
    apply pushout_med_unique.
    + (* Goal: (m1 ▽ m2) ∘ pushout_med Pcov (...) ∘ pushout_in1 Pcov ≈ pushout_in1 Pcov. *)
      rewrite <- comp_assoc, (pushout_med_in1 Pcov).
      pose proof (pushout_med_in1 P (pushout_cover_left_cocone f g f' g' Pcov)) as Hl.
      pose proof (pushout_med_in1 P' (pushout_cover_right_cocone f g f' g' Pcov)) as Hr.
      (* Goal: (m1 ▽ m2) ∘ cover (in1 P) (in1 P') ≈ pushout_in1 Pcov.
         Unfold cover, distribute via merge_comp:
         = (m1 ∘ in1 P) ▽ (m2 ∘ in1 P')
         By Hl, Hr: = (in1 Pcov ∘ inl) ▽ (in1 Pcov ∘ inr)
                   = in1 Pcov ∘ (inl ▽ inr)
                   = in1 Pcov ∘ id = in1 Pcov. *)
      unfold cover.
      rewrite <- !merge_comp.
      rewrite (comp_assoc _ inl), (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite Hl, Hr.
      rewrite merge_comp.
      rewrite merge_inl_inr.
      cat.
    + rewrite <- comp_assoc, (pushout_med_in2 Pcov).
      pose proof (pushout_med_in2 P (pushout_cover_left_cocone f g f' g' Pcov)) as Hl.
      pose proof (pushout_med_in2 P' (pushout_cover_right_cocone f g f' g' Pcov)) as Hr.
      unfold cover.
      rewrite <- !merge_comp.
      rewrite (comp_assoc _ inl), (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite Hl, Hr.
      rewrite merge_comp.
      rewrite merge_inl_inr.
      cat.
  - apply pushout_med_unique; cat.
Qed.

Lemma pushout_cover_combine_split
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  pushout_cover_split f g f' g' P P' Pcov
    ∘ pushout_cover_combine f g f' g' P P' Pcov
  ≈ id.
Proof.
  unfold pushout_cover_combine, pushout_cover_split.
  rewrite <- merge_inl_inr.
  rewrite <- merge_comp.
  apply (snd (merge_inv _ _ _ _)).
  split.
  - (*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    assert (HC : (@inl C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in1 P ∘ f
                 ≈ (@inl C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in2 P ∘ g).
    { rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      apply (pushout_commutes P). }
    transitivity (pushout_med P HC).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in1 P).
        rewrite (comp_assoc _ (pushout_in1 Pcov)).
        rewrite (pushout_med_in1 Pcov).
        unfold cover.
        apply inl_merge.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in2 P).
        rewrite (comp_assoc _ (pushout_in2 Pcov)).
        rewrite (pushout_med_in2 Pcov).
        unfold cover.
        apply inl_merge.
    + apply pushout_med_unique; cat.
  - assert (HC : (@inr C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in1 P' ∘ f'
                 ≈ (@inr C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in2 P' ∘ g').
    { rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      apply (pushout_commutes P'). }
    transitivity (pushout_med P' HC).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in1 P').
        rewrite (comp_assoc _ (pushout_in1 Pcov)).
        rewrite (pushout_med_in1 Pcov).
        unfold cover.
        apply inr_merge.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in2 P').
        rewrite (comp_assoc _ (pushout_in2 Pcov)).
        rewrite (pushout_med_in2 Pcov).
        unfold cover.
        apply inr_merge.
    + apply pushout_med_unique; cat.
Qed.

End PushoutCoproductCompat.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CospanTensorBifunctoriality.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).

(** Helper: [merge] distributes through [cover]. *)
Lemma merge_cover_compose {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e) (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ cover h1 h2 ≈ (m1 ∘ h1) ▽ (m2 ∘ h2).
Proof.
  unfold cover.
  rewrite <- !merge_comp.
  rewrite (comp_assoc _ inl).
  rewrite (comp_assoc _ inr).
  rewrite inl_merge, inr_merge.
  reflexivity.
Qed.

Lemma cospan_tensor_compose_compat
  {X Y Z X' Y' Z' : C}
  (g : CospanArrow Y Z) (f : CospanArrow X Y)
  (g' : CospanArrow Y' Z') (f' : CospanArrow X' Y') :
  cospan_equiv
    (cospan_tensor (cospan_compose HP g f) (cospan_compose HP g' f'))
    (cospan_compose HP (cospan_tensor g g') (cospan_tensor f f')).
Proof.
  unfold cospan_tensor, cospan_compose; simpl.
  pose (P  := pushout (cospan_in2 f)  (cospan_in1 g)).
  pose (P' := pushout (cospan_in2 f') (cospan_in1 g')).
  pose (Pcov := pushout (cover (cospan_in2 f) (cospan_in2 f'))
                        (cover (cospan_in1 g) (cospan_in1 g'))).
  (* Iso of apexes: pushout_apex P + pushout_apex P' ≅ pushout_apex Pcov,
     given by pushout_cover_combine / pushout_cover_split. *)
  unshelve refine (existT _ _ _).
  - refine {| to   := pushout_cover_combine _ _ _ _ P P' Pcov;
              from := pushout_cover_split   _ _ _ _ P P' Pcov;
              iso_to_from := pushout_cover_split_combine _ _ _ _ P P' Pcov;
              iso_from_to := pushout_cover_combine_split _ _ _ _ P P' Pcov |}.
  - simpl; split; fold P P' Pcov.
    + (* pushout_cover_combine ∘ cover (in1 P ∘ in1 f) (in1 P' ∘ in1 f')
         ≈ in1 Pcov ∘ cover (in1 f) (in1 f') *)
      unfold pushout_cover_combine.
      rewrite merge_cover_compose.
      pose proof (pushout_med_in1 P
                    (pushout_cover_left_cocone _ _ _ _ Pcov)) as Hl.
      pose proof (pushout_med_in1 P'
                    (pushout_cover_right_cocone _ _ _ _ Pcov)) as Hr.
      rewrite !comp_assoc.
      rewrite Hl, Hr.
      (* Goal: (in1 Pcov ∘ inl) ∘ in1 f ▽ (in1 Pcov ∘ inr) ∘ in1 f'
              ≈ in1 Pcov ∘ cover (in1 f) (in1 f') *)
      rewrite <- (comp_assoc (pushout_in1 Pcov) inl).
      rewrite <- (comp_assoc (pushout_in1 Pcov) inr).
      rewrite merge_comp.
      reflexivity.
    + (* pushout_cover_combine ∘ cover (in2 P ∘ in2 g) (in2 P' ∘ in2 g')
         ≈ in2 Pcov ∘ cover (in2 g) (in2 g') *)
      unfold pushout_cover_combine.
      rewrite merge_cover_compose.
      pose proof (pushout_med_in2 P
                    (pushout_cover_left_cocone _ _ _ _ Pcov)) as Hl.
      pose proof (pushout_med_in2 P'
                    (pushout_cover_right_cocone _ _ _ _ Pcov)) as Hr.
      rewrite !comp_assoc.
      rewrite Hl, Hr.
      rewrite <- (comp_assoc (pushout_in2 Pcov) inl).
      rewrite <- (comp_assoc (pushout_in2 Pcov) inr).
      rewrite merge_comp.
      reflexivity.
Defined.

End CospanTensorBifunctoriality.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CospanBifunctor.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).

Program Definition Cospan_Bifunctor
  : ((CospanCat C HP) ∏ (CospanCat C HP)) ⟶ (CospanCat C HP) := {|
  fobj := fun xy => @Cospan_tensor_obj C H_Coc (fst xy) (snd xy);
  fmap := fun xy uv fg => cospan_tensor (fst fg) (snd fg)
|}.
Next Obligation.
  proper; simpl in *.
  apply cospan_tensor_respects; assumption.
Defined.
Next Obligation.
  (* fmap id ≈ id  i.e.  cospan_tensor (cospan_id x) (cospan_id y) ≈ cospan_id (x + y) *)
  apply cospan_tensor_id.
Defined.
Next Obligation.
  (* fmap (f ∘ g) ≈ fmap f ∘ fmap g
     i.e.  cospan_tensor (f1 ∘ g1) (f2 ∘ g2)
         ≈ cospan_tensor f1 f2 ∘ cospan_tensor g1 g2
     in CospanCat (composition is cospan_compose HP). *)
  apply cospan_tensor_compose_compat.
Defined.

End CospanBifunctor.

(*
   本节说明幺半结构、幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CospanMonoidal.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(** [cospan_tensor] two [mor_as_cospan]s agrees [mor_as_cospan]
 [cover] underlying C-态射. （已译） *)
Lemma cospan_tensor_mor_as_cospan
      {X Y X' Y' : C} (f : X ~> Y) (g : X' ~> Y') :
  cospan_equiv (cospan_tensor (mor_as_cospan f) (mor_as_cospan g))
               (mor_as_cospan (cover f g)).
Proof.
  unfold cospan_tensor, mor_as_cospan; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left; reflexivity.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    apply merge_inl_inr.
Defined.

(** Lift a C-iso [phi : X ≅ Y] to a [CospanCat]-iso via [mor_as_cospan]. *)
Definition mor_iso_lift {X Y : C} (phi : X ≅ Y)
  : @Isomorphism (CospanCat C HP) X Y.
Proof.
  unshelve refine
    {| to   := (mor_as_cospan (to phi) : X ~{CospanCat C HP}~> Y);
       from := (mor_as_cospan (from phi) : Y ~{CospanCat C HP}~> X);
       iso_to_from := _;
       iso_from_to := _ |}.
  - (* mor_as_cospan (to phi) ∘ mor_as_cospan (from phi) ≈ id in CospanCat *)
    eapply cospan_equiv_trans.
    + apply mor_as_cospan_compose.
    + eapply cospan_equiv_trans.
      * apply mor_as_cospan_proper. apply iso_to_from.
      * apply mor_as_cospan_id.
  - eapply cospan_equiv_trans.
    + apply mor_as_cospan_compose.
    + eapply cospan_equiv_trans.
      * apply mor_as_cospan_proper. apply iso_from_to.
      * apply mor_as_cospan_id.
Defined.

(*
   本节说明拉回/推出、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma pushout_cover_id_unit_left_apex {y N : C} (g2 : y ~> N) :
  pushout_apex (pushout (cover id[0] g2 : (0 + y)%object ~> (0 + N)%object)
                        (zero ▽ id[y] : (0 + y)%object ~> y)) ≅ N.
Proof.
  set (P := pushout (cover id[0] g2 : (0 + y)%object ~> (0 + N)%object)
                    (zero ▽ id[y])).
  (* Mediator P -> N via cocone (zero ▽ id : 0+N → N, g2 : y → N). *)
  assert (HC : (zero ▽ id[N]) ∘ cover id[0] g2 ≈ g2 ∘ (zero ▽ id[y])).
  { unfold cover.
    rewrite <- merge_comp.
    rewrite (comp_assoc _ inl).
    rewrite (comp_assoc _ inr).
    rewrite inl_merge, inr_merge.
    rewrite id_left, id_right.
    rewrite <- merge_comp.
    rewrite id_right, zero_comp.
    reflexivity. }
  set (m := pushout_med P HC).
  assert (Hm1 : m ∘ pushout_in1 P ≈ zero ▽ id[N]) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ g2) by (apply pushout_med_in2).
  unshelve refine
    {| to := m;
       from := pushout_in1 P ∘ inr;
       iso_to_from := _;
       iso_from_to := _ |}.
  - (* m ∘ (pushout_in1 P ∘ inr) ≈ id at N *)
    rewrite comp_assoc.
    rewrite Hm1.
    apply inr_merge.
  - (* (pushout_in1 P ∘ inr) ∘ m ≈ id at apex P. UMP against identity. *)
    apply (pushout_med_eq P (pushout_commutes P)
            ((pushout_in1 P ∘ inr) ∘ m) id).
    + (* ((pushout_in1 P ∘ inr) ∘ m) ∘ pushout_in1 P ≈ pushout_in1 P *)
      rewrite <- !comp_assoc.
      rewrite Hm1.
      (* Goal: pushout_in1 P ∘ (inr ∘ (zero ▽ id[N])) ≈ pushout_in1 P *)
      assert (Hinr : (@inr C _ 0 N) ∘ (zero[N] ▽ id[N]) ≈ id[0 + N]).
      { rewrite <- merge_comp.
        rewrite id_right.
        rewrite <- merge_inl_inr.
        apply (snd (merge_inv _ _ _ _)).
        split.
        - apply (@zero_unique C H_Ini _ _ _).
        - reflexivity. }
      rewrite Hinr.
      apply id_right.
    + (* ((pushout_in1 P ∘ inr) ∘ m) ∘ pushout_in2 P ≈ pushout_in2 P *)
      rewrite <- !comp_assoc.
      rewrite Hm2.
      (* Goal: pushout_in1 P ∘ (inr ∘ g2) ≈ pushout_in2 P *)
      pose proof (pushout_commutes P) as PC.
      (* PC : pushout_in1 P ∘ cover id g2 ≈ pushout_in2 P ∘ (zero ▽ id) *)
      rewrite <- (cover_inr id[0] g2).
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite inr_merge.
      apply id_right.
    + cat.
    + cat.
Defined.

(* 相关说明。 （已译） *)

(** 本节：Helpers associator-cover proofs. （已译） *)

Lemma assoc_to_inl_inl {x y z : C} :
  to (@coprod_assoc C H_Coc x y z) ∘ (inl ∘ inl) ≈ inl.
Proof.
  unfold to, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inl_merge.
  apply inl_merge.
Qed.

Lemma assoc_to_inl_inr {x y z : C} :
  to (@coprod_assoc C H_Coc x y z) ∘ (inl ∘ inr) ≈ inr ∘ inl.
Proof.
  unfold to, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inl_merge.
  apply inr_merge.
Qed.

Lemma assoc_to_inr {x y z : C} :
  to (@coprod_assoc C H_Coc x y z) ∘ inr ≈ inr ∘ inr.
Proof.
  unfold to, coprod_assoc; simpl.
  apply inr_merge.
Qed.

Lemma assoc_from_inl {x y z : C} :
  from (@coprod_assoc C H_Coc x y z) ∘ inl ≈ inl ∘ inl.
Proof.
  unfold from, coprod_assoc; simpl.
  apply inl_merge.
Qed.

Lemma assoc_from_inr_inl {x y z : C} :
  from (@coprod_assoc C H_Coc x y z) ∘ (inr ∘ inl) ≈ inl ∘ inr.
Proof.
  unfold from, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inr_merge.
  apply inl_merge.
Qed.

Lemma assoc_from_inr_inr {x y z : C} :
  from (@coprod_assoc C H_Coc x y z) ∘ (inr ∘ inr) ≈ inr.
Proof.
  unfold from, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inr_merge.
  apply inr_merge.
Qed.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cover_assoc_from {a a' b b' c c' : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') :
  from coprod_assoc ∘ cover f (cover g h)
  ≈ cover (cover f g) h ∘ from coprod_assoc.
Proof.
  apply coprod_ext.
  - (* ∘ inl: reduces to inl ∘ inl ∘ f *)
    rewrite <- !comp_assoc.
    rewrite cover_inl.
    rewrite (comp_assoc (from coprod_assoc) inl f).
    rewrite assoc_from_inl.
    rewrite assoc_from_inl.
    symmetry.
    rewrite <- comp_assoc.
    rewrite (comp_assoc (cover (cover f g) h) inl inl).
    rewrite cover_inl.
    rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    reflexivity.
  - apply coprod_ext.
    + (* ∘ (inr ∘ inl) on (b+c) side → b → inl ∘ inr ∘ g *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover f (cover g h)) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (cover g h) inl).
      rewrite cover_inl.
      rewrite (comp_assoc inr inl g).
      rewrite (comp_assoc (from coprod_assoc) (inr ∘ inl) g).
      rewrite assoc_from_inr_inl.
      rewrite assoc_from_inr_inl.
      symmetry.
      rewrite <- comp_assoc.
      rewrite (comp_assoc (cover (cover f g) h) inl inr).
      rewrite cover_inl.
      rewrite <- comp_assoc.
      rewrite cover_inr.
      rewrite !comp_assoc.
      reflexivity.
    + (* ∘ (inr ∘ inr) on (b+c) side → c → inr ∘ h *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover f (cover g h)) inr inr).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (cover g h) inr).
      rewrite cover_inr.
      rewrite (comp_assoc inr inr h).
      rewrite (comp_assoc (from coprod_assoc) (inr ∘ inr) h).
      rewrite assoc_from_inr_inr.
      rewrite assoc_from_inr_inr.
      symmetry.
      apply cover_inr.
Qed.

Lemma cover_assoc_to {a a' b b' c c' : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') :
  to coprod_assoc ∘ cover (cover f g) h
  ≈ cover f (cover g h) ∘ to coprod_assoc.
Proof.
  apply coprod_ext.
  - apply coprod_ext.
    + (* ∘ (inl ∘ inl): both reduce to inl ∘ f *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover (cover f g) h) inl inl).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (cover f g) inl).
      rewrite cover_inl.
      rewrite (comp_assoc inl inl f).
      rewrite (comp_assoc (to coprod_assoc) (inl ∘ inl) f).
      rewrite assoc_to_inl_inl.
      (* Goal: inl ∘ f ≈ cover f (cover g h) ∘ (to coprod_assoc ∘ (inl ∘ inl)) *)
      rewrite assoc_to_inl_inl.
      symmetry.
      apply cover_inl.
    + (* ∘ (inl ∘ inr): both reduce to inr ∘ inl ∘ g *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover (cover f g) h) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (cover f g) inr).
      rewrite cover_inr.
      rewrite (comp_assoc inl inr g).
      rewrite (comp_assoc (to coprod_assoc) (inl ∘ inr) g).
      rewrite assoc_to_inl_inr.
      (* Goal now: inr ∘ inl ∘ g ≈ cover f (cover g h) ∘ (to coprod_assoc ∘ (inl ∘ inr)) *)
      rewrite assoc_to_inl_inr.
      (* Goal: inr ∘ inl ∘ g ≈ cover f (cover g h) ∘ (inr ∘ inl) *)
      symmetry.
      rewrite <- comp_assoc.
      rewrite (comp_assoc (cover f (cover g h)) inr inl).
      rewrite cover_inr.
      rewrite <- comp_assoc.
      rewrite cover_inl.
      rewrite comp_assoc.
      reflexivity.
  - (* ∘ inr: both reduce to inr ∘ inr ∘ h *)
    rewrite <- !comp_assoc.
    rewrite cover_inr.
    rewrite (comp_assoc (to coprod_assoc) inr h).
    rewrite assoc_to_inr.
    (* RHS *)
    rewrite assoc_to_inr.
    (* Goal: inr ∘ inr ∘ h ≈ cover f (cover g h) ∘ (inr ∘ inr) *)
    symmetry.
    rewrite <- comp_assoc.
    rewrite (comp_assoc (cover f (cover g h)) inr inr).
    rewrite cover_inr.
    rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    reflexivity.
Qed.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma paws_inl {x y : C} :
  (@paws C H_Coc x y) ∘ inl ≈ inr.
Proof.
  unfold paws, swap, inl, inr; simpl.
  apply (@exl_fork _ H_Coc).
Qed.

Lemma paws_inr {x y : C} :
  (@paws C H_Coc x y) ∘ inr ≈ inl.
Proof.
  unfold paws, swap, inl, inr; simpl.
  apply (@exr_fork _ H_Coc).
Qed.

(** Braid-naturality at C level: [paws ∘ cover g h ≈ cover h g ∘ paws]. *)
Lemma cover_paws {a a' b b' : C} (g : a ~> a') (h : b ~> b') :
  paws ∘ cover g h ≈ cover h g ∘ paws.
Proof.
  apply coprod_ext.
  - (* ∘ inl: LHS = paws ∘ (cover g h ∘ inl) = paws ∘ (inl ∘ g) = (paws ∘ inl) ∘ g = inr ∘ g
       RHS = (cover h g ∘ paws) ∘ inl = cover h g ∘ (paws ∘ inl) = cover h g ∘ inr = inr ∘ g  *)
    rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite paws_inl.
    rewrite <- comp_assoc.
    rewrite paws_inl.
    rewrite cover_inr.
    reflexivity.
  - (* ∘ inr: LHS = paws ∘ (cover g h ∘ inr) = paws ∘ (inr ∘ h) = (paws ∘ inr) ∘ h = inl ∘ h
       RHS = (cover h g ∘ paws) ∘ inr = cover h g ∘ (paws ∘ inr) = cover h g ∘ inl = inl ∘ h *)
    rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite paws_inr.
    rewrite <- comp_assoc.
    rewrite paws_inr.
    rewrite cover_inl.
    reflexivity.
Qed.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma pushout_along_iso_apex {Y Z N : C} (m : Y ~> N) (phi : Y ≅ Z) :
  pushout_apex (pushout m (to phi)) ≅ N.
Proof.
  set (P := pushout m (to phi)).
  assert (HC : id[N] ∘ m ≈ (m ∘ from phi) ∘ to phi).
  { rewrite id_left.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    rewrite id_right.
    reflexivity. }
  pose (k := pushout_med P HC).
  assert (Hk1 : k ∘ pushout_in1 P ≈ id) by (apply pushout_med_in1).
  assert (Hk2 : k ∘ pushout_in2 P ≈ m ∘ from phi) by (apply pushout_med_in2).
  unshelve refine
    {| to := k;
       from := pushout_in1 P;
       iso_to_from := _;
       iso_from_to := _ |}.
  - exact Hk1.
  - apply (pushout_med_eq P (pushout_commutes P)
            (pushout_in1 P ∘ k) id).
    + rewrite <- comp_assoc.
      rewrite Hk1; cat.
    + rewrite <- comp_assoc.
      rewrite Hk2.
      pose proof (pushout_commutes P) as PC.
      rewrite comp_assoc.
      (* Need: 推出_in1 P ∘ m ∘ from phi ≈ 推出_in2 P.
 By PC: 推出_in1 P ∘ m ≈ 推出_in2 P ∘ phi.
 Hence 推出_in1 P ∘ m ∘ from phi ≈ 推出_in2 P ∘ phi ∘ from phi
 ≈ 推出_in2 P ∘ id ≈ 推出_in2 P.（已译） *)
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite iso_to_from.
      apply id_right.
    + cat.
    + cat.
Defined.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cospan_compose_mor_as_cospan_right
      {X Y Z : C} (f : CospanArrow Y Z) (h : X ~> Y) :
  cospan_equiv (cospan_compose HP f (mor_as_cospan h))
               (Build_CospanArrow (cospan_apex f)
                                  (cospan_in1 f ∘ h)
                                  (cospan_in2 f)).
Proof.
  unfold cospan_compose, mor_as_cospan; simpl.
  exists (pushout_id_left_apex HP (cospan_in1 f)); simpl.
  split.
  - rewrite comp_assoc.
    apply compose_respects; [|reflexivity].
    apply pushout_med_in1.
  - rewrite comp_assoc.
    rewrite pushout_med_in2.
    apply id_left.
Defined.

(** 本节：Dual bridging: composing cospan [mor_as_cospan (to phi)] on
 LEFT where [phi] C-iso. By [pushout_along_iso_apex], the
 apex collapses apex(f), adjusted in2. （已译） *)

Lemma cospan_compose_mor_iso_left
      {X Y Z : C} (f : CospanArrow X Y) (phi : Y ≅ Z) :
  cospan_equiv (cospan_compose HP (mor_as_cospan (to phi)) f)
               (Build_CospanArrow (cospan_apex f)
                                  (cospan_in1 f)
                                  (cospan_in2 f ∘ from phi)).
Proof.
  unfold cospan_compose, mor_as_cospan; simpl.
  pose (P := pushout (cospan_in2 f) (to phi)).
  assert (HC : id[cospan_apex f] ∘ cospan_in2 f
              ≈ (cospan_in2 f ∘ from phi) ∘ to phi).
  { rewrite id_left.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    rewrite id_right.
    reflexivity. }
  pose (k := pushout_med P HC).
  assert (Hk1 : k ∘ pushout_in1 P ≈ id) by (apply pushout_med_in1).
  assert (Hk2 : k ∘ pushout_in2 P ≈ cospan_in2 f ∘ from phi)
    by (apply pushout_med_in2).
  unshelve refine
    (existT _ {| to := k;
                 from := pushout_in1 P;
                 iso_to_from := _;
                 iso_from_to := _ |} _).
  - exact Hk1.
  - apply (pushout_med_eq P (pushout_commutes P)
            (pushout_in1 P ∘ k) id).
    + rewrite <- comp_assoc.
      rewrite Hk1; cat.
    + rewrite <- comp_assoc.
      rewrite Hk2.
      pose proof (pushout_commutes P) as PC.
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite iso_to_from.
      apply id_right.
    + cat.
    + cat.
  - simpl; split; fold P.
    + rewrite comp_assoc.
      rewrite Hk1.
      apply id_left.
    + rewrite id_right.
      exact Hk2.
Defined.

(*
   本节说明拉回/推出、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cospan_unit_left_natural
      {x y : C} (g : CospanArrow x y) :
  cospan_equiv
    (cospan_compose HP g (mor_as_cospan (zero ▽ id[x])))
    (cospan_compose HP (mor_as_cospan (zero ▽ id[y]))
       (cospan_tensor (cospan_id 0%object) g)).
Proof.
  (* LHS simplifies via bridging. *)
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_as_cospan_right|].
  apply cospan_equiv_sym.
  unfold cospan_compose, mor_as_cospan, cospan_tensor; simpl.
  (* Inline the apex iso construction so [to] reduces by [pushout_med_in1/2]. *)
  pose (Pcov := pushout (cover id[0] (cospan_in2 g) : (0 + y)%object ~> (0 + cospan_apex g)%object)
                        (zero ▽ id[y] : (0 + y)%object ~> y)).
  assert (HC : (zero ▽ id[cospan_apex g]) ∘ cover id[0] (cospan_in2 g)
              ≈ cospan_in2 g ∘ (zero ▽ id[y])).
  { unfold cover.
    rewrite <- merge_comp.
    rewrite (comp_assoc _ inl).
    rewrite (comp_assoc _ inr).
    rewrite inl_merge, inr_merge.
    rewrite id_left, id_right.
    rewrite <- merge_comp.
    rewrite id_right, zero_comp.
    reflexivity. }
  pose (m := pushout_med Pcov HC).
  assert (Hm1 : m ∘ pushout_in1 Pcov ≈ zero ▽ id[cospan_apex g])
    by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 Pcov ≈ cospan_in2 g)
    by (apply pushout_med_in2).
  unshelve refine
    (existT _ {| to := m;
                 from := pushout_in1 Pcov ∘ inr;
                 iso_to_from := _;
                 iso_from_to := _ |} _).
  - (* m ∘ (pushout_in1 Pcov ∘ inr) ≈ id at apex g *)
    rewrite comp_assoc.
    rewrite Hm1.
    apply inr_merge.
  - (* (pushout_in1 Pcov ∘ inr) ∘ m ≈ id at apex Pcov *)
    apply (pushout_med_eq Pcov (pushout_commutes Pcov)
            ((pushout_in1 Pcov ∘ inr) ∘ m) id).
    + rewrite <- !comp_assoc.
      rewrite Hm1.
      assert (Hinr : (@inr C _ 0 (cospan_apex g))
                       ∘ (zero[cospan_apex g] ▽ id[cospan_apex g])
                     ≈ id[0 + cospan_apex g]).
      { rewrite <- merge_comp.
        rewrite id_right.
        rewrite <- merge_inl_inr.
        apply (snd (merge_inv _ _ _ _)).
        split.
        - apply (@zero_unique C H_Ini _ _ _).
        - reflexivity. }
      rewrite Hinr.
      apply id_right.
    + rewrite <- !comp_assoc.
      rewrite Hm2.
      pose proof (pushout_commutes Pcov) as PC.
      rewrite <- (cover_inr id[0] (cospan_in2 g)).
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite inr_merge.
      apply id_right.
    + cat.
    + cat.
  - simpl; split; fold Pcov.
    + rewrite comp_assoc.
      rewrite Hm1.
      unfold cover.
      rewrite <- merge_comp.
      rewrite (comp_assoc _ inl).
      rewrite (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite id_left, id_right.
      rewrite <- merge_comp.
      rewrite id_right, zero_comp.
      reflexivity.
    + rewrite id_right.
      exact Hm2.
Defined.

(* * ** Right-unitor 自然性, dual left.

 [unit_right = mor_as_cospan (id ▽ zero : x + 0 → x)] and
 [bimap g id = cospan_tensor g (cospan_id 0)]. （已译） *)

Lemma cospan_unit_right_natural
      {x y : C} (g : CospanArrow x y) :
  cospan_equiv
    (cospan_compose HP g (mor_as_cospan (id[x] ▽ zero)))
    (cospan_compose HP (mor_as_cospan (id[y] ▽ zero))
       (cospan_tensor g (cospan_id 0%object))).
Proof.
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_as_cospan_right|].
  apply cospan_equiv_sym.
  unfold cospan_compose, mor_as_cospan, cospan_tensor; simpl.
  pose (Pcov := pushout (cover (cospan_in2 g) id[0] : (y + 0)%object ~> (cospan_apex g + 0)%object)
                        (id ▽ zero : (y + 0)%object ~> y)).
  assert (HC : (id[cospan_apex g] ▽ zero) ∘ cover (cospan_in2 g) id[0]
              ≈ cospan_in2 g ∘ (id ▽ zero)).
  { unfold cover.
    rewrite <- merge_comp.
    rewrite (comp_assoc _ inl).
    rewrite (comp_assoc _ inr).
    rewrite inl_merge, inr_merge.
    rewrite id_left, id_right.
    rewrite <- merge_comp.
    rewrite id_right, zero_comp.
    reflexivity. }
  pose (m := pushout_med Pcov HC).
  assert (Hm1 : m ∘ pushout_in1 Pcov ≈ id[cospan_apex g] ▽ zero)
    by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 Pcov ≈ cospan_in2 g)
    by (apply pushout_med_in2).
  unshelve refine
    (existT _ {| to := m;
                 from := pushout_in1 Pcov ∘ inl;
                 iso_to_from := _;
                 iso_from_to := _ |} _).
  - rewrite comp_assoc.
    rewrite Hm1.
    apply inl_merge.
  - apply (pushout_med_eq Pcov (pushout_commutes Pcov)
            ((pushout_in1 Pcov ∘ inl) ∘ m) id).
    + rewrite <- !comp_assoc.
      rewrite Hm1.
      assert (Hinl : (@inl C _ (cospan_apex g) 0)
                       ∘ (id[cospan_apex g] ▽ zero[cospan_apex g])
                     ≈ id[cospan_apex g + 0]).
      { rewrite <- merge_comp.
        rewrite id_right.
        rewrite <- merge_inl_inr.
        apply (snd (merge_inv _ _ _ _)).
        split.
        - reflexivity.
        - apply (@zero_unique C H_Ini _ _ _). }
      rewrite Hinl.
      apply id_right.
    + rewrite <- !comp_assoc.
      rewrite Hm2.
      pose proof (pushout_commutes Pcov) as PC.
      rewrite <- (cover_inl (cospan_in2 g) id[0]).
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite inl_merge.
      apply id_right.
    + cat.
    + cat.
  - simpl; split; fold Pcov.
    + rewrite comp_assoc.
      rewrite Hm1.
      unfold cover.
      rewrite <- merge_comp.
      rewrite (comp_assoc _ inl).
      rewrite (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite id_left, id_right.
      rewrite <- merge_comp.
      rewrite id_right, zero_comp.
      reflexivity.
    + rewrite id_right.
      exact Hm2.
Defined.

(* * ** Tensor-associator 自然性

 For arbitrary cospans [f : x → x'], [g : y → y'], [h : z → z']:
 [bimap f (bimap g h) ∘ tensor_assoc
 ≈ tensor_assoc ∘ bimap (bimap f g) h]
 [CospanCat C HP], where [tensor_assoc = mor_as_cospan (to coprod_assoc)]
 [bimap = cospan_tensor]. （已译） *)

Lemma cospan_tensor_assoc_natural
      {x x' y y' z z' : C}
      (f : CospanArrow x x') (g : CospanArrow y y') (h : CospanArrow z z') :
  cospan_equiv
    (cospan_compose HP (cospan_tensor f (cospan_tensor g h))
                       (mor_as_cospan (to coprod_assoc)))
    (cospan_compose HP (mor_as_cospan (to coprod_assoc))
                       (cospan_tensor (cospan_tensor f g) h)).
Proof.
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_as_cospan_right|].
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_iso_left|].
  apply cospan_equiv_sym.
  unfold cospan_tensor; simpl.
  exists (iso_sym (@coprod_assoc C H_Coc (cospan_apex f) (cospan_apex g) (cospan_apex h))).
  simpl; split.
  - (* from coprod_assoc ∘ (cover (in1 f) (cover (in1 g) (in1 h)) ∘ to coprod_assoc)
       ≈ cover (cover (in1 f) (in1 g)) (in1 h) *)
    rewrite comp_assoc.
    rewrite cover_assoc_from.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    apply id_right.
  - (* 相关说明。 （已译） *)
    apply cover_assoc_from.
Defined.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma from_naturality_of_to {D : Category} {X Y W : D}
      (phi : @Isomorphism D X Y)
      (g : Y ~{D}~> W) (h : X ~{D}~> W)
      (Hto : g ∘ to phi ≈ h) :
  g ≈ h ∘ from phi.
Proof.
  rewrite <- Hto.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  rewrite id_right.
  reflexivity.
Qed.

Lemma from_naturality_of_to_2 {D : Category} {X Y A B : D}
      (phi : @Isomorphism D X Y) (psi : @Isomorphism D A B)
      (g : Y ~{D}~> B) (h : X ~{D}~> A)
      (Hto : g ∘ to phi ≈ to psi ∘ h) :
  from psi ∘ g ≈ h ∘ from phi.
Proof.
  apply (from_naturality_of_to phi (from psi ∘ g) h).
  rewrite <- comp_assoc.
  rewrite Hto.
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.

(** Variant matching Monoidal 自然性 shape:
 to-自然性 [g ∘ phi_X ≈ phi_Y ∘ h]
 derive from-自然性 [h ∘ phi_X ≈ phi_Y ∘ g]. （已译） *)
Lemma from_naturality_of_to_M {D : Category} {X Y A B : D}
      (phi_X : @Isomorphism D X A) (phi_Y : @Isomorphism D Y B)
      (g : A ~{D}~> B) (h : X ~{D}~> Y)
      (Hto : g ∘ to phi_X ≈ to phi_Y ∘ h) :
  h ∘ from phi_X ≈ from phi_Y ∘ g.
Proof.
  assert (H1 : from phi_Y ∘ g ∘ to phi_X ≈ h).
  { rewrite <- comp_assoc.
    rewrite Hto.
    rewrite comp_assoc.
    rewrite iso_from_to.
    apply id_left. }
  rewrite <- H1.
  rewrite <- (comp_assoc _ (to phi_X) (from phi_X)).
  rewrite iso_to_from.
  apply id_right.
Qed.

(* * ** Triangle 恒等 at C level (for coproducts).

 [cover (to coprod_zero_r) id ≈ cover id (to coprod_zero_l) ∘ coprod_assoc]
 i.e., (X+0)+Y → X+Y two paths agree. （已译） *)

Lemma coprod_triangle_aux {x y : C} :
  cover (to (@coprod_zero_r C H_Coc H_Ini x)) id[y]
  ≈ cover id[x] (to (@coprod_zero_l C H_Coc H_Ini y))
    ∘ to (@coprod_assoc C H_Coc x 0 y).
Proof.
  apply coprod_ext.
  - apply coprod_ext.
    + (* ∘ (inl ∘ inl), i.e., x part *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover _ id[y]) inl inl).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (to coprod_zero_r) inl).
      (* RHS: cover id coprod_zero_l ∘ (coprod_assoc ∘ (inl ∘ inl)) = inl *)
      rewrite assoc_to_inl_inl.
      (* LHS: inl ∘ (to coprod_zero_r ∘ inl)
         to coprod_zero_r = id ▽ zero, so (id ▽ zero) ∘ inl = id *)
      assert (Hzr : to (@coprod_zero_r C H_Coc H_Ini x) ∘ (@inl C _ x 0) ≈ id[x]).
      { unfold to, coprod_zero_r; simpl. apply inl_merge. }
      rewrite Hzr.
      rewrite id_right.
      symmetry.
      rewrite cover_inl.
      apply id_right.
    + (* ∘ (inl ∘ inr), i.e., 0 part - both go to zero *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover _ id[y]) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (to coprod_zero_r) inr).
      assert (Hzr_inr : to (@coprod_zero_r C H_Coc H_Ini x) ∘ (@inr C _ x 0) ≈ zero).
      { unfold to, coprod_zero_r; simpl. apply inr_merge. }
      rewrite Hzr_inr.
      (* RHS: cover id coprod_zero_l ∘ (coprod_assoc ∘ (inl ∘ inr)) *)
      rewrite assoc_to_inl_inr.
      (* Goal: inl ∘ zero[x] ≈ cover id coprod_zero_l ∘ (inr ∘ inl) *)
      rewrite (comp_assoc (cover id[x] _) inr inl).
      rewrite cover_inr.
      rewrite <- comp_assoc.
      assert (Hzl : to (@coprod_zero_l C H_Coc H_Ini y) ∘ (@inl C _ 0 y) ≈ zero).
      { unfold to, coprod_zero_l; simpl. apply inl_merge. }
      rewrite Hzl.
      apply (@zero_unique C H_Ini _ _ _).
  - (* ∘ inr, i.e., y part *)
    rewrite cover_inr.
    rewrite id_right.
    rewrite <- (comp_assoc (cover id[x] _) (to coprod_assoc) inr).
    rewrite assoc_to_inr.
    rewrite (comp_assoc (cover id[x] _) inr inr).
    rewrite cover_inr.
    rewrite <- (comp_assoc inr _ inr).
    assert (Hzl_inr : to (@coprod_zero_l C H_Coc H_Ini y) ∘ (@inr C _ 0 y) ≈ id[y]).
    { unfold to, coprod_zero_l; simpl. apply inr_merge. }
    rewrite Hzl_inr.
    symmetry. apply id_right.
Qed.

(* * ** C-level pentagon 恒等 [coprod_assoc].

 [cover id (to coprod_assoc) ∘ coprod_assoc ∘ cover (to coprod_assoc) id
 ≈ coprod_assoc ∘ coprod_assoc]
 at types [(((X+Y)+Z)+W) → (X+(Y+(Z+W)))]. （已译） *)

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Reduce one composite alpha against `inl ∘ inl ∘ inl` to inl.
    Key fact: alpha ∘ (inl ∘ inl) = inl by [assoc_to_inl_inl].  So
    alpha ∘ (inl ∘ inl) ∘ inl = inl ∘ inl, and then cover α id ∘ (inl ∘ inl)
    = inl ∘ α ∘ inl = inl ∘ inl... etc. *)

Lemma pentagon_lhs_iii {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ ((inl ∘ inl) ∘ inl)
  ≈ inl.
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (cover (to coprod_assoc) id[W]) inl (inl ∘ inl)).
  rewrite cover_inl.
  (* Goal: cover id α ∘ (α ∘ ((inl ∘ α) ∘ (inl ∘ inl))) *)
  rewrite <- (comp_assoc inl (to coprod_assoc) (inl ∘ inl)).
  (* Goal: cover id α ∘ (α ∘ (inl ∘ (α ∘ (inl ∘ inl)))) *)
  rewrite assoc_to_inl_inl.
  (* Goal: cover id α ∘ (α ∘ (inl ∘ inl)) *)
  rewrite assoc_to_inl_inl.
  (* Goal: cover id α ∘ inl *)
  rewrite cover_inl.
  apply id_right.
Qed.

Lemma pentagon_rhs_iii {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ ((inl ∘ inl) ∘ inl)
  ≈ inl.
Proof.
  rewrite <- !comp_assoc.
  (* Goal: α ∘ (α' ∘ (inl ∘ (inl ∘ inl))) where α, α' are at different types *)
  rewrite (comp_assoc inl inl inl).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inl) inl).
  rewrite assoc_to_inl_inl.
  rewrite assoc_to_inl_inl.
  reflexivity.
Qed.

Lemma pentagon_lhs_iir {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ ((inl ∘ inl) ∘ inr)
  ≈ inr ∘ inl.
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (cover (to coprod_assoc) id[W]) inl (inl ∘ inr)).
  rewrite cover_inl.
  rewrite <- (comp_assoc inl (to coprod_assoc) (inl ∘ inr)).
  rewrite assoc_to_inl_inr.
  (* Goal: cover id α ∘ (α ∘ (inl ∘ (inr ∘ inl))) ≈ inr ∘ inl *)
  rewrite (comp_assoc inl inr inl).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inr) inl).
  rewrite assoc_to_inl_inr.
  (* Goal: cover id α ∘ ((inr ∘ inl) ∘ inl) ≈ inr ∘ inl *)
  rewrite <- (comp_assoc inr inl inl).
  rewrite (comp_assoc (cover id[X] _) inr (inl ∘ inl)).
  rewrite cover_inr.
  rewrite <- (comp_assoc inr (to coprod_assoc) (inl ∘ inl)).
  rewrite assoc_to_inl_inl.
  reflexivity.
Qed.

Lemma pentagon_rhs_iir {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ ((inl ∘ inl) ∘ inr)
  ≈ inr ∘ inl.
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc inl inl inr).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inl) inr).
  rewrite assoc_to_inl_inl.
  rewrite assoc_to_inl_inr.
  reflexivity.
Qed.

Lemma pentagon_lhs_ir {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ (inl ∘ inr)
  ≈ inr ∘ (inr ∘ inl).
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (cover (to coprod_assoc) id[W]) inl inr).
  rewrite cover_inl.
  rewrite <- (comp_assoc inl (to coprod_assoc) inr).
  rewrite assoc_to_inr.
  (* Goal: cover id α ∘ (α ∘ (inl ∘ (inr ∘ inr))) *)
  rewrite (comp_assoc inl inr inr).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inr) inr).
  rewrite assoc_to_inl_inr.
  (* Goal: cover id α ∘ ((inr ∘ inl) ∘ inr) *)
  rewrite <- (comp_assoc inr inl inr).
  rewrite (comp_assoc (cover id[X] _) inr (inl ∘ inr)).
  rewrite cover_inr.
  rewrite <- (comp_assoc inr (to coprod_assoc) (inl ∘ inr)).
  rewrite assoc_to_inl_inr.
  reflexivity.
Qed.

Lemma pentagon_rhs_ir {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ (inl ∘ inr)
  ≈ inr ∘ (inr ∘ inl).
Proof.
  rewrite <- !comp_assoc.
  rewrite assoc_to_inl_inr.
  (* Goal: α[X,Y,Z+W] ∘ (inr ∘ inl) *)
  rewrite (comp_assoc (to coprod_assoc) inr inl).
  rewrite assoc_to_inr.
  rewrite <- (comp_assoc inr inr inl).
  reflexivity.
Qed.

Lemma pentagon_lhs_r {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ inr
  ≈ inr ∘ (inr ∘ inr).
Proof.
  rewrite <- !comp_assoc.
  rewrite cover_inr.
  rewrite id_right.
  (* Goal: cover id α ∘ (α ∘ inr) *)
  rewrite assoc_to_inr.
  rewrite (comp_assoc (cover id[X] _) inr inr).
  rewrite cover_inr.
  rewrite <- (comp_assoc inr (to coprod_assoc) inr).
  rewrite assoc_to_inr.
  reflexivity.
Qed.

Lemma pentagon_rhs_r {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ inr
  ≈ inr ∘ (inr ∘ inr).
Proof.
  rewrite <- !comp_assoc.
  rewrite assoc_to_inr.
  rewrite (comp_assoc (to coprod_assoc) inr inr).
  rewrite assoc_to_inr.
  rewrite <- (comp_assoc inr inr inr).
  reflexivity.
Qed.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coprod_pentagon_aux {X Y Z W : C} :
  cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
    ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
    ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W])
  ≈ to (@coprod_assoc C H_Coc X Y (Z + W))
    ∘ to (@coprod_assoc C H_Coc (X + Y) Z W).
Proof.
  apply coprod_ext.
  - (* outer inl case: domain (X+Y)+Z *)
    apply coprod_ext.
    + (* (inl ∘ inl) on (X+Y)+Z side: domain X+Y *)
      apply coprod_ext.
      * (* ((inl ∘ inl) ∘ inl): X-injection.
           Goal is left-associated, helpers use right-associated form.
           Bridge by an explicit assertion. *)
        assert (Hl : forall (u : (X + Y + Z + W) ~> X + (Y + (Z + W))),
                   (u ∘ inl) ∘ inl ∘ inl ≈ u ∘ ((inl ∘ inl) ∘ inl)).
        { intros u; rewrite !comp_assoc; reflexivity. }
        rewrite !Hl.
        rewrite pentagon_lhs_iii.
        symmetry; rewrite pentagon_rhs_iii; reflexivity.
      * (* ((inl ∘ inl) ∘ inr): Y-injection. *)
        assert (Hl : forall (u : (X + Y + Z + W) ~> X + (Y + (Z + W))),
                   (u ∘ inl) ∘ inl ∘ inr ≈ u ∘ ((inl ∘ inl) ∘ inr)).
        { intros u; rewrite !comp_assoc; reflexivity. }
        rewrite !Hl.
        rewrite pentagon_lhs_iir.
        symmetry; rewrite pentagon_rhs_iir; reflexivity.
    + (* (inl ∘ inr): Z-injection. *)
      assert (Hl : forall (u : (X + Y + Z + W) ~> X + (Y + (Z + W))),
                 (u ∘ inl) ∘ inr ≈ u ∘ (inl ∘ inr)).
      { intros u; rewrite !comp_assoc; reflexivity. }
      rewrite !Hl.
      rewrite pentagon_lhs_ir.
      symmetry; rewrite pentagon_rhs_ir; reflexivity.
  - (* outer inr: W-injection. *)
    rewrite pentagon_lhs_r.
    symmetry; rewrite pentagon_rhs_r; reflexivity.
Qed.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma cospan_triangle_identity {x y : C} :
  cospan_equiv
    (cospan_tensor (mor_as_cospan (to (@coprod_zero_r C H_Coc H_Ini x))) (cospan_id y))
    (cospan_compose HP
       (cospan_tensor (cospan_id x) (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini y))))
       (mor_as_cospan (to (@coprod_assoc C H_Coc x 0 y)))).
Proof.
  (* LHS = cospan_tensor (mor_as_cospan _) (mor_as_cospan id[y]) (since cospan_id = mor_as_cospan id)
        ≈ mor_as_cospan (cover (to coprod_zero_r) id[y])  [by cospan_tensor_mor_as_cospan]
     RHS = cospan_compose (cospan_tensor (mor_as_cospan id[x]) (mor_as_cospan _)) (mor_as_cospan _)
        ≈ cospan_compose (mor_as_cospan (cover id[x] (to coprod_zero_l))) (mor_as_cospan _)
        ≈ mor_as_cospan ((cover id[x] (to coprod_zero_l)) ∘ (to coprod_assoc))  [by mor_as_cospan_compose]
     Use coprod_triangle_aux to equate the C-level morphisms. *)
  eapply cospan_equiv_trans.
  { (* cospan_id x = mor_as_cospan id[x] up to cospan_equiv via mor_as_cospan_id (reversed) *)
    apply cospan_tensor_respects.
    - apply cospan_equiv_refl.
    - apply cospan_equiv_sym, mor_as_cospan_id. }
  eapply cospan_equiv_trans.
  { apply cospan_tensor_mor_as_cospan. }
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  symmetry.
  apply coprod_triangle_aux.
Defined.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Cospan-level pentagon, parallel to [cospan_triangle_identity]. *)
Lemma cospan_pentagon_identity {x y z w : C} :
  cospan_equiv
    (cospan_compose HP
       (cospan_tensor (cospan_id x)
          (mor_as_cospan (to (@coprod_assoc C H_Coc y z w))))
       (cospan_compose HP
          (mor_as_cospan (to (@coprod_assoc C H_Coc x (y + z) w)))
          (cospan_tensor (mor_as_cospan (to (@coprod_assoc C H_Coc x y z)))
                         (cospan_id w))))
    (cospan_compose HP
       (mor_as_cospan (to (@coprod_assoc C H_Coc x y (z + w))))
       (mor_as_cospan (to (@coprod_assoc C H_Coc (x + y) z w)))).
Proof.
  (* LHS lifts via cospan_tensor_mor_as_cospan + mor_as_cospan_compose to
     mor_as_cospan (cover id α ∘ α ∘ cover α id).
     RHS lifts via mor_as_cospan_compose to mor_as_cospan (α ∘ α).
     Equate via mor_as_cospan_proper from coprod_pentagon_aux. *)
  eapply cospan_equiv_trans.
  { (* Outer compose: g = cospan_tensor (cospan_id x) ..., f = compose ... *)
    apply cospan_compose_respects_aux.
    - (* f' = compose (mor_as_cospan α) (cospan_tensor (cospan_id w) ...)
         Want Hf : f ≈ f'. *)
      apply cospan_compose_respects_aux.
      + (* Inner f': cospan_tensor (mor_as_cospan id[w]) ... after subst *)
        apply cospan_tensor_respects.
        * apply cospan_equiv_refl.
        * apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl.
    - (* g': cospan_tensor (mor_as_cospan id[x]) ... *)
      apply cospan_tensor_respects.
      + apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_mor_as_cospan.
      + apply cospan_equiv_refl.
    - apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply mor_as_cospan_compose.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  rewrite comp_assoc.
  symmetry.
  apply coprod_pentagon_aux.
Defined.

(*
   本节说明幺半结构、幺半群、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export] Program Instance Cospan_Monoidal : @Monoidal (CospanCat C HP) := {|
  I := (@Cospan_unit_obj C H_Ini : CospanCat C HP);
  tensor := Cospan_Bifunctor HP;
  unit_left    := fun X => mor_iso_lift (@coprod_zero_l C H_Coc H_Ini X);
  unit_right   := fun X => mor_iso_lift (@coprod_zero_r C H_Coc H_Ini X);
  tensor_assoc := fun X Y Z => mor_iso_lift (@coprod_assoc C H_Coc X Y Z)
|}.
Next Obligation. apply cospan_unit_left_natural. Defined.
Next Obligation.
  apply (@from_naturality_of_to_M (CospanCat C HP)
           _ _ _ _
           (mor_iso_lift (@coprod_zero_l C H_Coc H_Ini x))
           (mor_iso_lift (@coprod_zero_l C H_Coc H_Ini y))
           g (cospan_tensor (cospan_id 0%object) g)).
  apply cospan_unit_left_natural.
Defined.
Next Obligation. apply cospan_unit_right_natural. Defined.
Next Obligation.
  apply (@from_naturality_of_to_M (CospanCat C HP)
           _ _ _ _
           (mor_iso_lift (@coprod_zero_r C H_Coc H_Ini x))
           (mor_iso_lift (@coprod_zero_r C H_Coc H_Ini y))
           g (cospan_tensor g (cospan_id 0%object))).
  apply cospan_unit_right_natural.
Defined.
Next Obligation. apply cospan_tensor_assoc_natural. Defined.
Next Obligation.
  apply (@from_naturality_of_to_M (CospanCat C HP)
           _ _ _ _
           (mor_iso_lift (@coprod_assoc C H_Coc x z v))
           (mor_iso_lift (@coprod_assoc C H_Coc y w u))
           (cospan_tensor g (cospan_tensor h i))
           (cospan_tensor (cospan_tensor g h) i)).
  apply cospan_tensor_assoc_natural.
Defined.
Next Obligation. (* triangle_identity *)
  apply cospan_triangle_identity.
Defined.
Next Obligation. (* pentagon_identity *)
  (* Reassociate via cospan_compose_assoc, then apply the proved identity. *)
  eapply cospan_equiv_trans.
  { apply cospan_equiv_sym. apply cospan_compose_assoc. }
  apply cospan_pentagon_identity.
Defined.

End CospanMonoidal.

(*
   本节说明幺半结构、幺半群、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(* CLOSED(V2d-coherence): the full Monoidal (CospanCat C HP) instance is
   built as [Cospan_Monoidal] above. *)
(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
