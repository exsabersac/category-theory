From Coq Require Import NArith.
From Coq Require Import Lia.

Require Import Category.Lib.
Require Import Category.Lib.MapDecide.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.
Set Transparent Obligations.

(** Arrows-only metacategories / 仅箭头的元范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/category
   nLab: https://ncatlab.org/nlab/show/metacategory
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   The single-sorted (“arrows-only”) axiomatization of a category, due to
   Mac Lane (Categories for the Working Mathematician, I.1, “arrows-only”
   description). A category is given purely by a collection of arrows together
   with a partial composition; there is no separate sort of objects. Objects
   are recovered as the identity arrows: an arrow [u] is an identity when
   [f ∘ u ≈ f] for every [f] whose composite with [u] is defined, and dually
   [u ∘ g ≈ g] for every such [g].

   Here the partial composition is represented concretely by a finite map
   [pairs : M.t arrow] over [arrow := N], where [M.find (f, g) pairs = Some h]
   records that the composite of the composable pair [(f, g)] is [h]. Thus
   [composite f g h] is the proposition “g and f compose to h”, [defined f g]
   says their composite exists, and the record's law fields impose Mac Lane's
   matchability (existence of composites for composable pairs), associativity,
   and existence of identities. [Category_from_Metacategory] below shows every
   such metacategory yields a [Category] whose objects are the identity arrows
   [{i | is_identity i}].

--------
nLab: https://ncatlab.org/nlab/show/category
nLab: https://ncatlab.org/nlab/show/metacategory
Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

单一类型（“仅箭头”）的范畴公理化，由 Mac Lane 提出（《为工作数学家准备的范畴论》，I.1，“仅箭头”描述）。一个范畴完全由一组箭头以及部分复合定义；没有独立的对象类型。对象通过恒等箭头来恢复：当对于每个与其复合定义的 [f]，箭头 [u] 都满足 [f ∘ u ≈ f] 时，箭头 [u] 是恒等箭头；反之亦然，对于每个这样的 [g]，箭头 [u ∘ g ≈ g] 也是恒等箭头。

这里部分组合通过一个有限映射具体表示为 [pairs : M.t arrow] 在 [arrow := N] 上，其中 [M.find (f, g) pairs = Some h] 记录了可组合对 [(f, g)] 的复合是 [h]。因此，[composite f g h] 是命题“g 和 f 组合成 h”，[defined f g] 表示它们的复合存在，并且记录的公理字段施加了 Mac Lane 的可匹配性（可组合对的复合存在性）、结合性以及单位元存在性。下面的 [Category_from_Metacategory] 显示，每一个这样的元范畴都会产生一个 [Category]，其对象是单位箭头 [{i | is_identity i}]。
*)

Record Metacategory := {
  arrow := N;
  pairs : M.t arrow;

  composite (f g h : arrow) := M.find (f, g) pairs = Some h;
  defined (f g : arrow) := ∃ h, composite f g h;

  composite_defined {f g h : arrow} (H : composite f g h) :
    defined f g := (h; H);

  (*
Matchability (Mac Lane C-1): whenever [fg] is the composite of [(f, g)]
     and [gh] is the composite of [(g, h)], the composite [(fg, h)] also
     exists. This is the arrows-only form of “composable pairs have a
     composite”: the composable triple [f, g, h] always has the composite
     [(f ∘ g) ∘ h].

--------
可匹配性（Mac Lane C-1）：每当 [fg] 是 [(f, g)] 的复合，而 [gh] 是 [(g, h)] 的复合时，复合 [(fg, h)] 也存在。这是“可复合对具有复合”的仅箭头形式：可复合的三元组 [f, g, h] 总是有复合 [(f ∘ g) ∘ h]。
*)
  composite_correct {f g h fg gh : arrow} :
    composite f g fg ->
    composite g h gh → ∃ fgh, composite fg h fgh;

  (*
Associativity (Mac Lane C-2): for a composable triple, associating to the
     left, [(fg, h)], agrees with associating to the right, [(f, gh)]. The
     biconditional captures that one composite is defined exactly when the
     other is, and then they are the same arrow.

--------
结合性（Mac Lane C-2）：对于一个可组合的三元组，向左结合的 [(fg, h)] 与向右结合的 [(f, gh)] 是一致的。这个双重条件表达的是，当且仅当另一个复合定义时，一个复合才定义，并且它们是相同的箭头。
*)
  composition_law {f g h fg gh : arrow} :
    composite f g fg ->
    composite g h gh ->
    ∀ fgh, composite fg h fgh ↔ composite f gh fgh;

  (*
Identity arrows (objects). [u] is an identity when it acts neutrally on
     either side of every composite in which it participates: [f ∘ u ≈ f]
     whenever [f ∘ u] is defined, and [u ∘ g ≈ g] whenever [u ∘ g] is defined.
     These are exactly the arrows that stand in for objects.

--------
恒等箭头（对象）。当 [u] 在它参与的每一个组合的任一侧上起中立作用时，它就是一个恒等：每当 [f ∘ u] 被定义时为 [f ∘ u ≈ f]，每当 [u ∘ g] 被定义时为 [u ∘ g ≈ g]。这些正是代表对象的箭头。
*)
  is_identity (u : arrow) :=
    (∀ f, defined f u → composite f u f) ∧
    (∀ g, defined u g → composite u g g);

  (*
Existence of identities (Mac Lane): to each arrow [f] there should be a
     source identity and a target identity whose composites with [f] recover
     [f]. As currently written, however, this axiom is vacuous.

     jww (TODO): The two [->] below should be [/\], and the current form does
     impose no constraint — arrow [1%N] of [Two] is genuinely not an identity,
     so it witnesses the existential and discharges both implications. But
     that substitution alone is not a repair: with conjunctions the axiom
     quantifies over all of [N], while [composable_pairs n] mentions finitely
     many arrows, so an arrow occurring in no composable pair ([100%N], say)
     has no flanking identities and the record becomes uninhabitable by every
     model in this file. A faithful repair must first fix the arrow type:
     either relativize the axiom to arrows that occur in [pairs], or take
     [arrow] to be the support of the table rather than all of [N]. Only then
     does the remaining work — supplying identity witnesses for each example
     metacategory — become possible. Theory/Metacategory/General.v states the
     axiom in Mac Lane's conjunctive form over an arrow type that is exactly
     the arrows.

     The defect does not affect [Category_from_Metacategory], which builds its
     category from objects [{i | is_identity i}], not from [identity_law].
     Note however that the [obj_def] field of [object] is doing the work this
     axiom should do: it is what excludes arrows that are identities only
     vacuously (every arrow absent from [pairs] satisfies [is_identity]). In
     General.v, where the axiom is conjunctive, [obj_def] is derivable and the
     object record carries only the identity proof.

--------
恒等的存在（Mac Lane）：每个箭头 [f] 都应该有一个
 源恒等和目标恒等，其与 [f] 组合恢复
 [f]。 然而，正如目前所写的那样，这个公理是空洞的。

jww (TODO): 下面的两个 [->] 应该是 [/\]，并且当前的形式确实
 不施加任何约束——[Two] 的箭头 [1%N] 实际上不是一个恒等式，
 因此它见证了存在主义并释放了这两种含义。 但是
 单独的替换并不是修复：使用连词公理
 对所有 [N] 进行量化，而 [composable_pairs n] 则有限地提及
 许多箭头，因此箭头出现在不可组合的对中（例如 [100%N]）
 没有侧翼恒等，并且记录变得不适合每个人居住
 该文件中的模型。 忠实的修复必须首先修复箭头类型：
 将公理与 [pairs] 中出现的箭头相对化，或者采用
 [arrow]成为该表的支持而不是[N]的全部。 只有那时
 完成剩下的工作——为每个例子提供恒等证人
 元范畴——成为可能。 Theory/Metacategory/General.v 指出
 Mac Lane 的合取形式的公理在箭头类型上恰好是
 箭头。

该缺陷不会影响 [Category_from_Metacategory]，它构建了其
 来自对象 [{i | is_identity i}] 的范畴，而不是来自 [identity_law] 的范畴。 
但请注意，[object] 的 [obj_def] 字段正在执行此工作
 axiom 应该做的：它排除仅是恒等式的箭头
 空洞（[pairs] 中缺少的每个箭头都满足 [is_identity]）。 在
 General.v，其中公理是合取的，[obj_def] 是可导的，并且
 对象记录仅携带恒等证明。
*)
  identity_law (x y f : arrow) : composite x y f ->
    ∃ u u', is_identity u → is_identity u' ->
      composite f u f ∧ composite u' f f
}.

Section Category.

Context (M : Metacategory).

Record object : Set := {
  obj_arr : arrow M;
  obj_def : composite M obj_arr obj_arr obj_arr;
  obj_id  : is_identity M obj_arr
}.

Record morphism (dom cod : object) : Set := {
  mor_arr : arrow M;
  mor_dom : composite M mor_arr (obj_arr dom) mor_arr;
  mor_cod : composite M (obj_arr cod) mor_arr mor_arr
}.

Arguments mor_arr {_ _} _.
Arguments mor_dom {_ _} _.
Arguments mor_cod {_ _} _.

Definition identity (x : object) : morphism x x :=
  {| mor_arr := obj_arr x
   ; mor_dom := obj_def x
   ; mor_cod := obj_def x |}.

Lemma composition_left {x y z : object}
      {f : morphism y z} {g : morphism x y} {fg : arrow M} :
  composite M (mor_arr f) (mor_arr g) fg ->
  composite M (obj_arr z) (mor_arr f) (mor_arr f) ->
  composite M (obj_arr z) fg fg.
Proof.
  intros.
  destruct z, obj_id0 as [c c0], f, g; simpl in *.
  specialize (c0 _ (composite_defined M H0)); clear H0.
  destruct (composite_correct M c0 H).
  spose (fst (composition_law M c0 H _) e) as X.
  unfold composite, arrow in *.
  rewrite X, <- H, <- e; reflexivity.
Qed.

Lemma composition_right {x y z : object}
      {f : morphism y z} {g : morphism x y} {fg : arrow M} :
  composite M (mor_arr f) (mor_arr g) fg ->
  composite M (mor_arr g) (obj_arr x) (mor_arr g) ->
  composite M fg (obj_arr x) fg.
Proof.
  intros.
  destruct x, obj_id0 as [c c0], f, g; simpl in *.
  specialize (c _ (composite_defined M H0)); clear H0.
  destruct (composite_correct M H c).
  spose (fst (composition_law M H c _) e) as X.
  unfold composite, arrow in *.
  rewrite e, <- H, <- X; reflexivity.
Qed.

Definition composition {x y z : object}
           (f : morphism y z) (g : morphism x y) : morphism x z :=
  let fg := composite_correct M (mor_dom f) (mor_cod g) in
  {| mor_arr := `1 fg
   ; mor_dom := composition_right (f:=f) (`2 fg) (mor_dom g)
   ; mor_cod := composition_left  (g:=g) (`2 fg) (mor_cod f) |}.

#[export] Program Instance morphism_preorder : PreOrder morphism := {
  PreOrder_Reflexive  := identity;
  PreOrder_Transitive := fun _ _ _ g f => composition f g
}.

#[export] Program Instance morphism_setoid (x y : object) :
  Setoid (morphism x y) := {
  equiv := fun f g => mor_arr f = mor_arr g
}.

Lemma composition_respects {x y z : object} :
  Proper (equiv ==> equiv ==> equiv) (@composition x y z).
Proof.
  proper.
  destruct x0, y0, x1, y1; simpl in *; subst.
  repeat destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite e in e0.
  inversion_clear e0.
  reflexivity.
Qed.

Lemma composition_identity_left {x y : object} (f : morphism x y) :
  composition (identity y) f ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite mor_cod0 in e.
  inversion_clear e.
  reflexivity.
Qed.

Lemma composition_identity_right {x y : object} (f : morphism x y) :
  composition f (identity x) ≈ f.
Proof.
  destruct f; simpl.
  destruct (composite_correct _ _ _); simpl in *.
  unfold composite, arrow in *.
  rewrite mor_dom0 in e.
  inversion_clear e.
  reflexivity.
Qed.

Lemma composition_associative {x y z w : object}
      (f : morphism z w) (g : morphism y z) (h : morphism x y) :
  composition f (composition g h) ≈ composition (composition f g) h.
Proof.
  destruct f, g, h; simpl.
  repeat destruct (composite_correct _ _ _); simpl in *.
  spose (fst (composition_law M e1 e x3) e2) as X1.
  unfold composite, arrow in *.
  rewrite e0 in X1.
  inversion_clear X1.
  reflexivity.
Qed.

(*
Every meta-category, defined wholly in terms of the axioms of category
   theory, gives rise to a category interpreted in the context of set
   theory.

--------
每一个元范畴，如果完全根据范畴论的公理来定义，就会产生一个在集合论背景下解释的范畴。
*)

Program Definition Category_from_Metacategory : Category := {|
  obj     := object;
  hom     := morphism;
  homset  := fun _ _ => {| equiv := fun f g => mor_arr f = mor_arr g |};
  id      := @identity;
  compose := @composition;

  compose_respects := @composition_respects;

  id_left    := @composition_identity_left;
  id_right   := @composition_identity_right;
  comp_assoc := @composition_associative;
  comp_assoc_sym := fun x y z w f g h =>
    symmetry (@composition_associative x y z w f g h);
|}.

End Category.

Arguments mor_arr _ {_ _} _.
Arguments mor_dom _ {_ _} _.
Arguments mor_cod _ {_ _} _.

Import FMapExt.

Lemma mapsto_inv : ∀ elt f g (fg : elt) x y z m,
  M.MapsTo (f, g) fg (M.add (x, y) z m) ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.MapsTo (f, g) fg m.
Proof.
  intros.
  apply add_mapsto_iffT in H.
  destruct H; simpl in *; intuition.
Defined.

Lemma find_add_inv : ∀ f g (fg : N) x y z m,
  M.find (f, g) (M.add (x, y) z m) = Some fg ->
    (x = f ∧ y = g ∧ z = fg) ∨ M.find (f, g) m = Some fg.
Proof.
  intros.
  destruct (N.eq_dec x f).
  - destruct (N.eq_dec y g).
    + destruct (N.eq_dec z fg).
      * subst; left; intuition.
      * contradiction n.
        rewrite F.add_eq_o in H.
        ** inversion_clear H.
           reflexivity.
        ** simpl; intuition.
    + rewrite F.add_neq_o in H; intuition.
  - rewrite F.add_neq_o in H; intuition.
Defined.

Ltac destruct_maps :=
  repeat match goal with
  | [ H : M.find (?X, ?Y) (M.empty _) = Some ?F |- _ ] =>
    inversion H
  | [ H : M.find (?X, ?Y) (M.add _ _ _) = Some ?F |- _ ] =>
    apply find_add_inv in H;
    (destruct H as [[? [? ?]]|]; [subst; try lia|])
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    vm_compute; eexists; reflexivity

  | [ H : M.find _ _ = Some _ |- _ ] =>
    apply F.find_mapsto_iff in H
  | [ |- M.find _ _ = Some _ ] =>
    apply F.find_mapsto_iff
  | [ |- ∃ v, M.find _ _ = Some v ] =>
    apply find_mapsto_iff_ex

  | [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
    contradiction (proj1 (F.empty_mapsto_iff _ _) H)

  | [ H : M.MapsTo (?X, ?Y) ?F (M.add _ _ _) |- _ ] =>
    apply mapsto_inv in H; destruct H as [[? [? ?]]|]

  | [ H : ?X = ?Y |- context[M.MapsTo (?Y, _)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo (_, ?Y)] ] =>
    rewrite <- H; cbn
  | [ H : ?X = ?Y |- context[M.MapsTo _ ?Y] ] =>
    rewrite <- H; cbn

  | [ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ] =>
    match goal with
      [ |- context[M.add (X, Y) ?F _ ] ] =>
      exists F
    end
  | [ |- M.MapsTo (?X, ?Y) ?F (M.add (?X, ?Y) ?F _) ] =>
    simplify_maps
  | [ |- M.MapsTo _ _ (M.add _ _ _) ] =>
    simplify_maps; right; split; [idtac|]
  end;
  try congruence.

Ltac reflect_on_maps :=
  simpl; intros;
  match goal with
  | [ |- ∃ _, M.find _ _ = _ ] => destruct_maps
  | [ |- _ ↔ _ ] => split; intros; map_decide
  | [ |- ∃ _ _, _ ] =>
    destruct_maps;
    eexists; eexists; split; intros; clear;
    first [ instantiate (1 := 0%N); vm_compute; reflexivity
          | instantiate (1 := 1%N); vm_compute; reflexivity
          | instantiate (1 := 2%N); vm_compute; reflexivity
          | instantiate (1 := 3%N); vm_compute; reflexivity
          | instantiate (1 := 4%N); vm_compute; reflexivity
          | instantiate (1 := 5%N); vm_compute; reflexivity
          | instantiate (1 := 6%N); vm_compute; reflexivity
          | instantiate (1 := 7%N); vm_compute; reflexivity
          | instantiate (1 := 8%N); vm_compute; reflexivity
          | instantiate (1 := 9%N); vm_compute; reflexivity ]
  end.

#[local] Open Scope N_scope.

Definition triangular_number (n : N) := (n * (n + 1)) / 2.

Definition composable_pairs_step (n : N) (z : M.t N) : M.t N :=
  let next := triangular_number (N.pred n) in
  let go i rest :=
      let k j r :=
          let mor := next + i in
          let dom := triangular_number (j + i) + i in
          let cod := mor + j in
          M.add (cod, dom) mor r in
      N.peano_rect _ rest k (n - i) in
  N.peano_rect _ z go n.

Definition composable_pairs : N → M.t N :=
  N.peano_rect _ (M.empty _) (λ n, composable_pairs_step (N.succ n)).

(* The number of composable pairs, for objects N, is the tetrahedral_number / 对于对象 N，可组合对的数量是四面体数 *)
Definition tetrahedral_number (n : N) := (n * (n + 1) * (n + 2)) / 6.

#[local] Obligation Tactic :=
  simpl; intros; vm_compute triangular_number in *; reflect_on_maps.

Program Definition Zero  : Metacategory := {| pairs := composable_pairs 0 |}.
Program Definition One   : Metacategory := {| pairs := composable_pairs 1 |}.
Program Definition Two   : Metacategory := {| pairs := composable_pairs 2 |}.
Program Definition Three : Metacategory := {| pairs := composable_pairs 3 |}.
Program Definition Four  : Metacategory := {| pairs := composable_pairs 4 |}.

Ltac elimobj X :=
  exfalso;
  unfold composite in X; simpl in X;
  clear -X;
  vm_compute triangular_number in *;
  destruct_maps; lia.

Lemma peano_rect' : ∀ P : N → Type, P 0%N → (∀ n : N, P (N.succ n)) → ∀ n : N, P n.
Proof.
  intros.
  induction n using N.peano_rect.
  - apply X.
  - apply X0.
Defined.

Ltac reflect_on_pairs X Y F D C :=
  repeat (
    destruct X using peano_rect';
    first
      [ elimobj D | elimobj C
      | repeat (
          destruct Y using peano_rect';
          first
            [ elimobj D | elimobj C
            | repeat (
                destruct F using peano_rect';
                first
                  [ elimobj D | elimobj C
                  | intuition idtac
                  | reflect_on_pairs ]) ]) ]);
  intuition.

Require Import Category.Instance.Two.

Monomorphic Lemma object_Two_rect :
  ∀ (P : object Two → Type),
  (∀ x, obj_arr Two x = 0%N → P x) ->
  (∀ x, obj_arr Two x = 2%N → P x) ->
  ∀ (x : object Two), P x.
Proof.
  intros; destruct x.
  repeat (destruct obj_arr0 using peano_rect'; elimobj obj_def0 || auto).
Defined.

Program Definition Two_2_object (x : object Two) : TwoObj.
Proof.
  induction x using object_Two_rect.
  - exact TwoX.
  - exact TwoY.
Defined.

Monomorphic Lemma morphism_Two_rect :
  ∀ {x y : object Two} (P : morphism Two x y → Type),
  (∀ f, obj_arr Two x = 0%N → obj_arr Two y = 0%N → mor_arr Two f = 0%N → P f) ->
  (∀ f, obj_arr Two x = 0%N → obj_arr Two y = 2%N → mor_arr Two f = 1%N → P f) ->
  (∀ f, obj_arr Two x = 2%N → obj_arr Two y = 2%N → mor_arr Two f = 2%N → P f) ->
  ∀ (f : morphism Two x y), P f.
Proof.
  intros; destruct x, y, f.
  reflect_on_pairs obj_arr0 obj_arr1 mor_arr0 mor_dom0 mor_cod0.
Defined.

Program Definition Two_2_morphism (x y : object Two) (f : morphism Two x y) :
  TwoHom (Two_2_object x) (Two_2_object y).
Proof.
  induction f using morphism_Two_rect;
  destruct x, y, f; simpl in *; subst; simpl.
  - exact TwoIdX.
  - exact TwoXY.
  - exact TwoIdY.
Defined.

#[local] Obligation Tactic := intros.

Program Definition Two_to_Two : Category_from_Metacategory Two ⟶ _2 := {|
  fobj := Two_2_object;
  fmap := Two_2_morphism
|}.
Next Obligation.
  proper.
  destruct x0, y0; simpl in *; subst.
  apply f_equal.
  apply f_equal2;
  apply Eqdep_dec.UIP_dec;
  decide equality;
  apply N.eq_dec.
Qed.
Next Obligation.
  simpl.
  induction x using object_Two_rect;
  destruct x;
  simpl in H; subst;
  vm_compute; reflexivity.
Qed.
Next Obligation.
  simpl in *.
  induction f using morphism_Two_rect;
  induction g using morphism_Two_rect;
  repeat match goal with
  | [ X : object _ |- _ ] => destruct X
  | [ X : morphism _ _ _ |- _ ] => destruct X
  | [ H : _ _ _ = _ |- _ ] => simpl in H
  end; subst;
  (exfalso; simpl in *; discriminate)
    || (vm_compute; reflexivity).
Qed.

#[local] Obligation Tactic :=
  program_simpl;
  try solve [ subst; unfold composite; simpl;
              subst; vm_compute; reflexivity ].

Program Definition _2_Two_object (x : TwoObj) : object Two :=
  match x with
  | TwoX => {| obj_arr := 0%N; obj_def := _; obj_id  := _ |}
  | TwoY => {| obj_arr := 2%N; obj_def := _; obj_id  := _ |}
  end.
Next Obligation.
  unfold is_identity, defined, composite.
  simpl; split; intros; destruct H; subst;
  rewrite e; destruct_maps.
  unfold triangular_number in e0.
  rewrite N.div_same in e0; lia.
Defined.
Next Obligation.
  unfold is_identity, defined, composite;
  simpl; split; intros; destruct H; subst;
  rewrite e; destruct_maps.
  unfold triangular_number in e.
  rewrite N.div_same in e; lia.
Defined.

Program Definition _2_Two_morphism (x y : TwoObj) (f : TwoHom x y) :
  morphism Two (_2_Two_object x) (_2_Two_object y) :=
  match x as x' in TwoObj
  return x = x' → morphism Two (_2_Two_object x) (_2_Two_object y) with
  | TwoX => fun _ =>
    match y as y' in TwoObj
    return y = y' → morphism Two (_2_Two_object x) (_2_Two_object y) with
    | TwoX => fun _ => {| mor_arr := 0%N; mor_dom := _; mor_cod := _ |}
    | TwoY => fun _ => {| mor_arr := 1%N; mor_dom := _; mor_cod := _ |}
    end eq_refl
  | TwoY => fun _ =>
    match y as y' in TwoObj
    return y = y' → morphism Two (_2_Two_object x) (_2_Two_object y) with
    | TwoY => fun _ => {| mor_arr := 2%N; mor_dom := _; mor_cod := _ |}
    | TwoX => fun _ => !
    end eq_refl
  end eq_refl.
Next Obligation. inversion f. Defined.

#[local] Obligation Tactic := program_simpl.

Program Definition Two_from_Two : _2 ⟶ Category_from_Metacategory Two := {|
  fobj := _2_Two_object;
  fmap := _2_Two_morphism
|}.
Next Obligation. destruct x; reflexivity. Defined.
Next Obligation.
  destruct f; simpl;
  destruct x; simpl;
  spose (TwoHom_inv _ _ g) as H; subst;
  contradiction || reflexivity.
Defined.

Require Import Category.Instance.Cat.

#[export]
Program Instance Two_iso_2 : Category_from_Metacategory Two ≅ _2 := {
  to   := Two_to_Two;
  from := Two_from_Two
}.
Next Obligation.
  unshelve eexists; intros.
  - induction x; reflexivity.
  - induction f; reflexivity.
Qed.
Next Obligation.
  unshelve eexists; intros.
  - induction x using object_Two_rect;
    destruct x; simpl in H; subst.
    + isomorphism; simpl.
      * construct; [exact 0%N|..]; auto.
      * construct; [exact 0%N|..]; auto.
      * reflexivity.
      * reflexivity.
    + isomorphism; simpl.
      * construct; [exact 2%N|..]; auto.
      * construct; [exact 2%N|..]; auto.
      * reflexivity.
      * reflexivity.
  - induction f using morphism_Two_rect;
    destruct x, y, f;
    simpl in H, H0, H1; subst;
    vm_compute; reflexivity.
Qed.

#[local] Obligation Tactic := simpl; intros.

Lemma composable_pairs_succ n :
  composable_pairs (N.succ n)
    = composable_pairs_step (N.succ n) (composable_pairs n).
Proof.
  unfold composable_pairs.
  rewrite N.peano_rect_succ; reflexivity.
Qed.

Lemma composable_pairs_step_disjoint n m :
  P.Disjoint m (composable_pairs n) ->
  P.Disjoint (composable_pairs_step (N.succ n) m) (composable_pairs n).
Proof.
  intros.
  generalize dependent m.
  induction n using N.peano_rect; intros.
  - apply P.Disjoint_alt; intros.
    inversion H1.
  - rewrite composable_pairs_succ in H.
Abort.

Lemma composable_pairs_step_find n f g fg :
  M.find (f, g) (composable_pairs_step (N.succ n) (composable_pairs n)) = Some fg
    → M.find (f, g) (composable_pairs n) = Some fg ∨
       M.find (f, g) (composable_pairs_step (N.succ n) (M.empty _)) = Some fg.
Proof.
  generalize dependent fg.
  generalize dependent g.
  generalize dependent f.
  induction n using N.peano_rect; intros.
  - right; auto.
  - rewrite composable_pairs_succ in *.
Abort.

(*
Program Definition from_composablePairs (n : N) : Metacategory := {|
  pairs := composable_pairs n
|}.
Next Obligation.
  generalize dependent gh.
  generalize dependent fg.
  generalize dependent h.
  generalize dependent g.
  generalize dependent f.
  induction n using N.peano_rect; intros.
    cbn in H; discriminate.
Next Obligation.
  generalize dependent gh.
  generalize dependent fg.
  generalize dependent h.
  generalize dependent g.
  generalize dependent f.
  induction n; cbn; intros.
    discriminate.
Next Obligation.
  generalize dependent f.
  generalize dependent y.
  generalize dependent x.
  induction n; cbn; intros; eauto.

--------
程序定义 from_composablePairs (n : N) : 元范畴 := {|
  pairs := composable_pairs n
|}。
下一步义务。
  归纳依赖 gh。
  归纳依赖 fg。
  归纳依赖 h。
  归纳依赖 g。
  归纳依赖 f。
  使用 N.peano_rect 对 n 归纳；引入。
    在 H 中简化；区分。
下一步义务。
  归纳依赖 gh。
  归纳依赖 fg。
  归纳依赖 h。
  归纳依赖 g。
  归纳依赖 f。
  对 n 归纳；简化；引入。
    区分。
下一步义务。
  归纳依赖 f。
  归纳依赖 y。
  归纳依赖 x。
  对 n 归纳；简化；引入；自动求解。
*)
