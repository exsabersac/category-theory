From Coq Require Import DecidableTypeEx.
From Coq Require Import FMapFacts.
Require Import Category.Lib.FMapExt.
From Coq Require Import PeanoNat.

(* 相关说明。 （已译） *)
#[local] Set Warnings "-notation-overridden".
Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** Arrows-only metacategories *)

(* nLab: https://ncatlab.org/nlab/show/metacategory
   nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   范畴的单排序（「仅箭头」）公理化，归于 Mac Lane（《Categories for the Working
   Mathematician》, I.1，「仅箭头」描述）。范畴纯由箭头汇集连同偏复合（箭头上的偏岩浆）
   呈现；没有单独的对象排序。对象恢复为恒等箭头。Mac Lane 的恒等概念是条件性的——
   当 [f ∘ u] 有定义时 [f ∘ u ≈ f]，当 [u ∘ g] 有定义时 [u ∘ g ≈ g]，则 [u] 是恒等——
   但下文 [identity] 字段去掉两道守卫，要求对*每个*箭头成立两方程（见彼处注记）。
   两个后果宜直说。第一，在有限可复合对表上该条件根本无法满足，因它要求对每个
   [f : nat] 有条目 [(f, u)]：[ZeroArrows]、[OneArrow]、[TwoArrows]、[ThreeArrows]
   的箭头在此意义下都不是恒等，故 [FromArrows] 由它们建成的每个范畴——含 [Three]——
   都没有对象。第二，下文三公理*未*在此证明恰好刻画范畴：两方向皆未证，且第三公理
   [identity_law] 按书写还是空虚的（再见图注）。[FromArrows] 确立的是一方向：本意义下
   每个元范畴都产出对象为恒等箭头 [∃ i, identity M i] 的 [Category]。
   Theory/Metacategory/General.v 在任意箭头类型上携带无上述缺陷的公理，并证明两通路
   及它们在何种意义下互逆。

   本模块表明「仅箭头」元范畴足以定义范畴。使用 Mac Lane 的公理，「可复合对的定义集」
   与「复合赋值」都用 FMap 提供的键值映射编码，因它恰提供所需结构：
   [M.MapsTo (f, g) h pairs] 记录可复合对 [(f, g)] 的复合为 [h]。用自然数区分箭头。

   Theory/Metacategory/ArrowsOnly.v 是同一想法在 [arrow := N] 上的平行开发，复合更直接
   基于 [find]；它携带这些定义的打磨形式。 *)

(*
   nLab: https://ncatlab.org/nlab/show/metacategory
   SEP:  https://plato.stanford.edu/entries/category-theory/
   Paper: Eilenberg, Mac Lane, "General Theory of Natural

   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module PNN := PairUsualDecidableType Nat_as_DT Nat_as_DT.

Module Metacategory (M : WSfun PNN).

Module Import FMapExt := FMapExt PNN M.
Module P := FMapExt.P.
Module F := P.F.

Definition defined x y := M.In (elt:=nat) (x, y).

(* Mac Lane: "Since 对象 metacategory correspond exactly its
 恒等 arrows, it technically possible dispense altogether the
 对象 deal arrows." （已译） *)
Record Metacategory := {
  (* 相关说明。 （已译） *)
  arr := nat;

  (* "certain ordered pairs ⟨g, f⟩, called the composable pairs of arrows," *)
  pairs : M.t arr;

  (* "and operation assigning each composable pair ⟨g, f⟩ arrow g∙f,
 called 复合. We say 'g∙f defined' '⟨g, f⟩ a
 composable pair'". （已译） *)
  composite (f g h : arr) := M.MapsTo (f, g) h pairs;

  (* "With these data one defines 恒等 C arrow u such that
 f∙u = f whenever 复合 f∙u defined u∙g = g whenever u∙g is
 defined." （已译） *)
  (*
   本节说明 Metacategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  identity (u : arr) :=
    (∀ (f : arr), composite f u f) ∧ (∀ (g : arr), composite u g g);

  (* 相关说明。 （已译） *)

  (* First axiom: *)

  (* "The 复合 (k∙g)∙f defined if if 复合 k∙(g∙f) is
 defined. When either defined, they equal (and triple
 复合 written k∙g∙f)." （已译） *)
  composition_law (k g f kg gf : arr) :
    composite k g kg ->
    composite g f gf ->
    ∀ kgf, composite kg f kgf ↔ composite k gf kgf;

  (* Second axiom: *)

  (* "The triple 复合 k∙g∙f defined whenever both composites k∙g and
 g∙f defined." （已译） *)
  triple_composition (k g f kg gf : arr) :
    composite k g kg ->
    composite g f gf → (exists kgf : arr, composite kg f kgf)%type;

  (* Third axiom: *)

  (* "For each arrow g C there exist 恒等 arrows u u' C such
 u'∙g g∙u defined." （已译） *)
  (*
   本节说明 Metacategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  identity_law (g : arr) :
    ∃ u,  identity u  ->
    ∃ u', identity u' ->
      defined g u pairs ∧ defined u' g pairs;
}.

Definition composite_defined (M : Metacategory) (f g h : arr M) :
  composite M f g h → defined f g (pairs M) := fun H =>
  proj2 (@in_mapsto_iff _ _ _) (ex_intro _ h H).

Program Definition defined_composite (M : Metacategory) (f g : arr M) :
  defined f g (pairs M) → ∃ h : arr M, composite M f g h.
Proof.
  intro H.
  unfold defined in H.
  destruct (M.find (f, g) (pairs M)) eqn:Heqe.
  - exists n.
    apply (M.find_2 Heqe).
  - apply F.in_find_iff in H.
    contradiction.
Defined.

Lemma identity_morphism (M : Metacategory) (i : arr M) :
  identity M i → composite M i i i.
Proof. intro H; apply H. Qed.

Lemma identity_composition_between (M : Metacategory) :
  ∀ f g u,
    identity M u ->
    defined f u (pairs M) ->
    defined u g (pairs M) ->
    defined f g (pairs M).
Proof.
  intros.
  destruct H as [c c0].
  pose proof (@triple_composition M f u g f g (c f) (c0 g)) as H3;
  simpl in H3.
  destruct H3.
  apply composite_defined with (h:=x).
  exact H.
Defined.

Lemma identity_composition_left (M : Metacategory) :
  ∀ f g fg u,
    identity M u ->
    composite M f g fg ->
    defined u f (pairs M) ->
    defined u fg (pairs M).
Proof.
  intros.
  destruct H as [_ c0].
  apply composite_defined with (h:=fg); auto;
  try solve [ apply c0 ].
Qed.

Lemma identity_composition_right (M : Metacategory) :
  ∀ f g fg u,
    identity M u ->
    composite M f g fg ->
    defined g u (pairs M) ->
    defined fg u (pairs M).
Proof.
  intros.
  destruct H as [c _].
  apply composite_defined with (h:=fg); auto;
  try solve [ apply c ].
Qed.

#[local] Obligation Tactic := intros.

Program Definition FromArrows (M : Metacategory) : Category := {|
  (* The 对象 范畴 given all 恒等 arrows the
 arrows-only metacategory. （已译） *)
  obj := ∃ i : arr M, identity M i;

  (* The 态射 范畴 id[x] id[y] given those
 arrows whose domain composes id[x], whose codomain composes with
 id[y]. （已译） *)
  hom := fun x y =>
    ∃ f : arr M, defined f ``x (pairs M) ∧ defined ``y f (pairs M);

  homset := fun _ _ => {| Setoid.equiv := fun f g => `1 f = `1 g |}
|}.
Next Obligation.
  equivalence; simpl in *; subst; reflexivity.
Qed.
Next Obligation.                (* id *)
  destruct x as [i [Hil Hir]].
  exists i.
  split; apply composite_defined with (h:=i); auto;
  try solve [ apply Hil
            | apply Hir ].
Defined.
Next Obligation.                (* compose *)
  destruct x as [x x_id];
  destruct y as [y y_id];
  destruct z as [z z_id];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]]; simpl in *.
  pose proof (identity_composition_between M f g y y_id fl gr).
  destruct (defined_composite _ _ _ H) as [fg Hfg].
  exists fg; split.
  - eapply identity_composition_right; eauto.
  - eapply identity_composition_left; eauto.
Defined.
Next Obligation.
  proper.
  unfold FromArrows_obligation_3; simpl in *; subst.
  destruct (defined_composite _ _ _); reflexivity.
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x, y, f, i as [c c0], i0 as [c1 c2], p; simpl in *; subst.
  destruct (defined_composite _ _ _) as [x2 c3].
  pose proof (c2 x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x, y, f, i as [c c0], i0 as [c1 c2], p; simpl in *; subst.
  destruct (defined_composite _ _ _) as [x2 c3].
  pose proof (c x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x as [x [xl_id xr_id]];
  destruct y as [y [yl_id yr_id]];
  destruct z as [z [zl_id zr_id]];
  destruct w as [w [wl_id wr_id]];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]];
  destruct h as [h [hl hr]];
  simpl in *.
  repeat destruct (defined_composite _ _ _).
  unfold composite in *.
  pose proof (fst (composition_law M f g h x2 x0 c1 c x3) c2).
  simpl in H.
  apply (FMapExt.F.MapsTo_fun c0 H).
Qed.
Next Obligation.
  symmetry.
  unfold FromArrows_obligation_3; simpl.
  destruct x as [x [xl_id xr_id]];
  destruct y as [y [yl_id yr_id]];
  destruct z as [z [zl_id zr_id]];
  destruct w as [w [wl_id wr_id]];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]];
  destruct h as [h [hl hr]];
  simpl in *.
  repeat destruct (defined_composite _ _ _).
  unfold composite in *.
  pose proof (fst (composition_law M f g h x2 x0 c1 c x3) c2).
  simpl in H.
  apply (FMapExt.F.MapsTo_fun c0 H).
Qed.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac structure :=
  simpl in *;
  repeat (
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H; subst
    | [ |- ?X = ?Y → False ] =>
      let H := fresh "H" in
      intro H; inversion H; tauto
    | [ H : M.MapsTo _ _ _ |- _ ] => simplify_maps
    | [ |- M.MapsTo _ _ _ ] => simplify_maps
    | [ |- _ ↔ _ ] => split; intros
    | [ |- _ /\ _ ] => split
    | [ |- _ \/ _ ] => solve [ left; structure | right; structure ]
    end; intuition idtac; try congruence).

Ltac check_structure :=
  first [ unfold defined;
          repeat (unshelve eexists; try assumption; intros []);
          split; apply in_mapsto_iff;
          eexists; intuition
        | unshelve (structure; eexists; structure); exact 0%nat
        | structure ].

#[local] Obligation Tactic := program_simpl; check_structure.

Program Definition ZeroArrows : Metacategory := {|
  pairs := [map]
|}.

Program Definition OneArrow : Metacategory := {|
  pairs := [map (0, 0) +=> 0 ]%nat
|}.

Program Definition TwoArrows : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1

           ;    (0, 2) +=> 2
           ;    (2, 1) +=> 2 ]%nat
|}.

Program Definition ThreeArrows : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (2, 2) +=> 2

           ;    (0, 3) +=> 3
           ;    (3, 1) +=> 3

           ;    (1, 4) +=> 4
           ;    (4, 2) +=> 4

           ;    (3, 4) +=> 5

           ;    (0, 5) +=> 5
           ;    (5, 2) +=> 5 ]%nat
|}.

Definition Three : Category := FromArrows ThreeArrows.

Definition cardinality (M : Metacategory) : nat :=
  M.cardinal (P.filter (fun '(dom, cod) v =>
                          ((dom =? v)%nat && (cod =? v)%nat)%bool)
                       (pairs M)).

Lemma elements_filter {elt} (m : M.t elt) (P : M.key → elt → bool) :
  M.elements (P.filter P m)
    = filter (fun p => P (fst p) (snd p)) (M.elements m).
Proof.
  unfold P.filter.
  apply P.fold_rec; intros.
  - rewrite (proj1 (P.elements_Empty m0) H); simpl.
    apply P.elements_empty.
  - destruct (P k e) eqn:Heqe.
    + apply add_equal_iff in H1.
Abort.

Lemma length_elements_filter {elt} (m : M.t elt) k v (P : M.key * elt → bool) :
  length (filter P (M.elements (M.add k v m)))
    = length (filter P ((k, v) :: M.elements m)).
Proof.
Abort.

Theorem elements_rect {elt} (P : list (M.key * elt) → Type) :
  (∀ m1 m2, M.Equal m1 m2 → P (M.elements m1) → P (M.elements m2))
  → ∀ m k v, P ((k, v) :: M.elements m) → P (M.elements (M.add k v m)).
Proof.
Abort.

(* 相关说明。 （已译） *)
Lemma ThreeArrows_card_3 : cardinality ThreeArrows = 3%nat.
Proof.
  (* unfold cardinality; simpl. *)
  (* rewrite M.cardinal_1. *)
  (* rewrite elements_filter. *)
  (* apply elements_rect; simpl; intros. *)
  assert (P.transpose_neqkey
            M.Equal
            (λ (k : M.key) (e : nat) (m : M.t nat),
             if (let '(dom, cod) := k in
                 λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
             then k +=> e m
             else m)). {
    intros ??????.
    destruct k, k'.
    assert (n ≠ n1 \/ n0 ≠ n2). {
      destruct (Nat.eq_dec n n1); subst.
      - right; congruence.
      - left; assumption.
    }
    destruct ((n =? e)%nat && (n0 =? e)%nat) eqn:Heqe.
    - apply andb_true_iff in Heqe.
      destruct Heqe.
      apply Nat.eqb_eq in H1.
      apply Nat.eqb_eq in H2.
      subst.
      destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
      * apply andb_true_iff in Heqe2.
        destruct Heqe2.
        apply Nat.eqb_eq in H1.
        apply Nat.eqb_eq in H2.
        subst.
        apply add_associative.
        intros; congruence.
      * reflexivity.
    - destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
      * apply andb_true_iff in Heqe2.
        destruct Heqe2.
        apply Nat.eqb_eq in H1.
        apply Nat.eqb_eq in H2.
        subst.
        reflexivity.
      * reflexivity.
  }

  assert (Proper (eq ==> eq ==> M.Equal ==> M.Equal)
                 (λ (k : M.key) (e : nat) (m : M.t nat),
                  if (let '(dom, cod) := k in
                      λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
                  then k +=> e m
                  else m)). {
    intros ?????????.
    destruct x, y; subst.
    inversion H0; clear H0; subst.
    destruct ((n1 =? y0)%nat && (n2 =? y0)%nat) eqn:Heqe.
    - apply andb_true_iff in Heqe.
      destruct Heqe.
      apply Nat.eqb_eq in H0.
      apply Nat.eqb_eq in H1.
      subst.
      rewrite H2; reflexivity.
    - assumption.
  }

  unfold cardinality; simpl.
  unfold P.filter; simpl.
  repeat (rewrite P.fold_add; eauto; relational; simpl);
  try (apply not_in_mapsto_iff; intros;
       repeat (unfold not; intros; simplify_maps; try congruence)).
  rewrite P.fold_Empty; auto; [| apply M.empty_1 ].

  assert (P.transpose_neqkey eq (λ (_ : M.key) (_ : nat), S)) by proper.

  rewrite P.cardinal_fold.
  repeat (rewrite P.fold_add; eauto; relational; simpl);
  try (apply not_in_mapsto_iff; intros;
       repeat (unfold not; intros; simplify_maps; try congruence)).
  rewrite P.fold_Empty; auto; apply M.empty_1.
Qed.

(* Definition objects_of (M : Metacategory) : *)
(*   ∀ P : nat → Type, P 0%nat → (∀ n : nat, P n → P (S n)) → ∀ n : nat, P n *)

#[local] Obligation Tactic := program_simpl.

(*
Program Definition FromThree {C : Category} (c : C) : Three ⟶ C := {|
  fobj := fun x =>
   match x with
   | existT _ 0%nat _ => c
   | existT _ 1%nat _ => c
   | existT _ 2%nat _ => c
   | _ => False_rect _ _
   end
|}.
Next Obligation.
  destruct x. specialize (H1 X); contradiction.
  destruct x. specialize (H X); contradiction.
  destruct x. specialize (H0 X); contradiction.
  destruct X.
  pose proof (c0 0%nat).
  unfold composite in H2; simpl in H2.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. discriminate.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. discriminate.
  simplify_maps. structure.
Qed.
*)

End Metacategory.
