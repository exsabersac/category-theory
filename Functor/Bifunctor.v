Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** Bifunctors (functors of two variables)  / 双函子（两个变量的函子）*)

(*
nLab: https://ncatlab.org/nlab/show/bifunctor
   Wikipedia: https://en.wikipedia.org/wiki/Bifunctor

   A bifunctor is just a functor F : C ∏ D ⟶ E out of a product category, so we
   do not formalize it as a separate structure; we only provide helpers for the
   action of such an F on pairs of arrows.  The central helper is [bimap f g],
   the lift of (f, g) through F.  A functor on C ∏ D is equivalent to giving two
   “partial” actions, one in each variable, that are separately functorial and
   compatible via the interchange (middle-four exchange) law

     bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i    ([bimap_comp]),

   together with bimap id id ≈ id ([bimap_id_id]).  The two “swap” forms of
   interchange, bimap f id ∘ bimap id g ≈ bimap f g and its mirror, are recorded
   as [bimap_id_right_left] / [bimap_id_left_right].  Currying a bifunctor
   C ∏ D ⟶ E into C ⟶ [D, E] is exhibited concretely for the hom-bifunctor by
   [Curried_Hom] in Functor/Hom.v; the prototypical bifunctor, the tensor ⊗,
   appears in Structure/Monoidal. 

--------
nLab: https://ncatlab.org/nlab/show/bifunctor
   Wikipedia: https://en.wikipedia.org/wiki/Bifunctor

   双函子只是出自积范畴的函子 F : C ∏ D ⟶ E，故不单独形式化为结构；只提供此类 F
   对箭头对的作用助手。中心助手是 [bimap f g]，即 (f, g) 经 F 的提升。C ∏ D 上的函子
   等价于给出两「偏」作用（各变元一个），分别函子性，并经交换（中四交换）律相容：

     bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i    ([bimap_comp]),

   以及 bimap id id ≈ id ([bimap_id_id])。交换的两种「swap」形式
   bimap f id ∘ bimap id g ≈ bimap f g 及其镜像记为
   [bimap_id_right_left] / [bimap_id_left_right]。把双函子 C ∏ D ⟶ E curry 成
   C ⟶ [D, E] 对 hom-双函子由 Functor/Hom.v 的 [Curried_Hom] 具体展示；典范双函子
   张量 ⊗ 出现在 Structure/Monoidal。 
*)

Section Bifunctor.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

(*
A bimap takes two arrows in C and D, and lifts them to an arrow in E over
   some bifunctor F : C ∏ D ⟶ E. 

--------
双图采用 C 和 D 中的两个箭头，并将它们提升到 E 中的箭头
 一些双函子 F : C ∏ D ⟶ E。 
*)
(*
   【bimap 语法与字段展开】/ Syntax & field walkthrough

   1) 这是什么 / What this is
      双函子 = 积范畴上的函子 F : C ∏ D ⟶ E（不另开 Class）。
      Bifunctor = functor out of a product category (no separate Class).
      Haskell 对照：Data.Bifunctor 的 bimap；此处是 fmap on pairs。
      Haskell analogy: Data.Bifunctor.bimap ≈ fmap on (f, g).

   2) 中心定义 / Central definition
      bimap f g := fmap[F] (f, g) : F(x,y) ~> F(w,z)
      把一对箭头经 F 一次抬升。
      Lifts a pair of arrows through F in one go.

   3) 邻近律（下文 Corollary）/ Nearby laws
      bimap_id_id / bimap_comp / bimap_id_left_right …
      即函子律在「两变元」上的展开 + 中四交换。
      Functor laws in two variables + middle-four exchange.

   阅读：C∏D → F → bimap → 交换律。张量 ⊗ 是典范双函子（Monoidal）。
   Read: product cat → F → bimap → interchange. Tensor ⊗ is the prototype.
*)

Definition bimap {F : C ∏ D ⟶ E} {x w : C} {y z : D}
           (f : x ~{C}~> w) (g : y ~{D}~> z) :
  F (x, y) ~{E}~> F (w, z) := @fmap (C ∏ D) E F (x, y) (w, z) (f, g).

(*
[bimap] is definitionally [fmap] on a pair; this folds the [fmap] notation
   back into [bimap] during rewriting.  The equality is Leibniz (=), not ≈,
   because both sides are the very same term. 

--------
[bimap] 定义上是一对 [fmap]； 这折叠了 [fmap] 表示法
 重写期间返回 [bimap]。 等式是莱布尼茨 (=)，而不是 ≈，
 因为两边都是同一个词。 
*)
Corollary bimap_fmap {F : C ∏ D ⟶ E} {x w : C} {y z : D}
      (f : x ~{C}~> w) (g : y ~{D}~> z) :
  @fmap (C ∏ D) E F (x, y) (w, z) (f, g) = bimap f g.
Proof. reflexivity. Defined.

#[export] Program Instance bimap_respects {F : C ∏ D ⟶ E} {x w : C} {y z : D} :
  Proper (equiv ==> equiv ==> equiv) (@bimap F x w y z).
Next Obligation.
  proper.
  unfold bimap.
  apply fmap_respects.
  split; assumption.
Qed.

Lemma bimap_id_id {F : C ∏ D ⟶ E} {x y} :
  bimap (id[x]) (id[y]) ≈ id.
Proof.
  destruct F; simpl.
  apply fmap_id.
Qed.

(*
Interchange (middle-four exchange): F preserves composition in both
   variables simultaneously. 

--------
交换（中间四交换）：F 保留两者的组成
 同时变量。 
*)
Lemma bimap_comp {F : C ∏ D ⟶ E} {x y z w u v}
      (f : y ~{C}~> z) (h : x ~{C}~> y)
      (g : v ~{D}~> w) (i : u ~{D}~> v) :
  bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  reflexivity.
Qed.

(* Functoriality of the partial functor F(w, -) in the second variable.  / 第二个变量中的部分函子 F(w, -) 的函子性。*)
Lemma bimap_comp_id_left {F : C ∏ D ⟶ E} {w}
      `(f : y ~{D}~> z) `(g : x ~{D}~> y) :
  bimap (id[w]) (f ∘ g) ≈ bimap id f ∘ bimap id g.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(* Functoriality of the partial functor F(-, w) in the first variable.  / 第一个变量中的部分函子 F(-, w) 的函子性。*)
Lemma bimap_comp_id_right {F : C ∏ D ⟶ E} {w}
      `(f : y ~{C}~> z) `(g : x ~{C}~> y) :
  bimap (f ∘ g) (id[w]) ≈ bimap f id ∘ bimap g id.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(*
Interchange, swap form: acting first in D then in C agrees with the joint
   action.  Together with [bimap_id_left_right] this expresses that the two
   partial actions commute (the middle-four exchange). 

--------
Interchange，互换形式：先在D中行动，然后在C中行动，与联合一致
 行动。 与 [bimap_id_left_right] 一起表示这两个
 部分动作通勤（中间四交换）。 
*)
Lemma bimap_id_right_left {F : C ∏ D ⟶ E} {w}
      `(f : z ~{C}~> w) `(g : x ~{D}~> y) :
  bimap f id ∘ bimap id g ≈ bimap f g.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(*
Interchange, swap form: acting first in C then in D agrees with the joint
   action (mirror of [bimap_id_right_left]). 

--------
Interchange，互换形式：先在C中行动，然后在D中行动，与联合一致
 操作（[bimap_id_right_left] 的镜像）。 
*)
Lemma bimap_id_left_right {F : C ∏ D ⟶ E} {w}
      `(f : z ~{D}~> w) `(g : x ~{C}~> y) :
  bimap id f ∘ bimap g id ≈ bimap g f.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(*
A bifunctor preserves isomorphisms in each variable: isomorphic inputs in
   both factors yield isomorphic objects in E, with bimap of the component
   isos as the witness. 

--------
双函子保留每个变量中的同构：同构输入
 两个因素都在 E 中产生同构对象，并具有组件的 bimap
 isos作为见证人。 
*)
#[export] Program Instance bifunctor_respects {F : C ∏ D ⟶ E} :
  Proper ((fun p q => Isomorphism (fst p) (fst q) ∧
                      Isomorphism (snd p) (snd q))
            ==> Isomorphism) F.
Next Obligation.
  proper; simpl in *.
  isomorphism.
  - exact (bimap X H).
  - exact (bimap (X⁻¹) (H⁻¹)).
  - rewrite <- bimap_comp.
    rewrite !iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite <- bimap_comp.
    rewrite !iso_from_to.
    rewrite bimap_id_id.
    reflexivity.
Defined.

End Bifunctor.

Notation "bimap[ F ]" := (@bimap _ _ _ F%functor _ _ _ _)
  (at level 9, format "bimap[ F ]") : morphism_scope.

#[export] Hint Rewrite @bimap_id_id : categories.

Ltac bimap_left :=
  apply bimap_respects; [reflexivity|].

Ltac bimap_right :=
  apply bimap_respects; [|reflexivity].

Ltac normal :=
  repeat
    match goal with
    | [ |- context [?F ∘ (?G ∘ ?H)] ] =>
      rewrite (comp_assoc F G H)

    | [ |- context [fmap[?F] ?G ∘ fmap[?F] _] ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G)

    | [ |- context [fmap[?F] id] ] =>
      rewrite <- (@fmap_id _ _ F)

    | [ |- context [bimap ?F _ ∘ bimap _ _] ] =>
      rewrite <- (bimap_comp F)
    | [ |- context [(?F ∘ bimap ?G _) ∘ bimap _ _] ] =>
      rewrite <- (comp_assoc F (bimap _ _));
      rewrite <- (bimap_comp G)

    | [ |- context [id ∘ ?F] ] => rewrite (id_left F)
    | [ |- context [?F ∘ id] ] => rewrite (id_right F)

    | [ |- context [bimap id id] ] =>
      rewrite bimap_id_id
    | [ |- context [bimap ?F id ∘ bimap id ?G] ] =>
      rewrite (bimap_id_right_left F)
    | [ |- context [bimap id ?F ∘ bimap ?G id] ] =>
      rewrite (bimap_id_left_right F G)

    | [ H : context [fmap[?F] ?G ∘ fmap[?F] _] |- _ ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G) in H
    | [ H : context [bimap ?F id ∘ bimap id ?G] |- _ ] =>
      rewrite (bimap_id_right_left F) in H
    | [ H : context [bimap id ?F ∘ bimap ?G id] |- _ ] =>
      rewrite (bimap_id_left_right F G) in H
    | [ H : context [bimap ?F _ ∘ bimap _ _] |- _ ] =>
      rewrite <- (bimap_comp F) in H
    | [ H : context [(?F ∘ bimap ?G _) ∘ bimap _ _] |- _ ] =>
      rewrite <- (comp_assoc F (bimap _ _)) in H;
      rewrite <- (bimap_comp G) in H
    | [ H : context [id ∘ ?F] |- _ ] => rewrite (id_left F) in H
    | [ H : context [?F ∘ id] |- _ ] => rewrite (id_right F) in H
    end.
