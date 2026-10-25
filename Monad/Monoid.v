Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Monoidal.Compose.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * Monads are monoids in the category of endofunctors  / * 单子是内函子类别中的幺半群*)

(*
nLab:      https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   The endofunctor category [[C, C]] is monoidal with functor composition [∘]
   as tensor and the identity functor [Id] as unit (this monoidal structure is
   [Compose_Monoidal]). A monad on [C] is exactly a monoid object in this
   monoidal category: the carrier is the endofunctor [M], the monoid unit
   [mempty : Id ⟹ M] is the monad unit [ret] (η), and the monoid
   multiplication [mappend : M ∘ M ⟹ M] is the monad multiplication [join]
   (μ). Because the tensor here is strict composition, the unitors and
   associator are identities, so the monoid unit/associativity laws collapse to
   the bare monad laws [join_ret], [join_fmap_ret] and [join_fmap_join]; the
   naturality squares of [mempty]/[mappend] become [fmap_ret] and
   [join_fmap_fmap]. This is the precise content of the slogan "a monad is a
   monoid in the category of endofunctors".

   [Monoid_Monad] proves the correspondence as a genuine logical equivalence
   ([↔]), constructing a monad from any such monoid object and vice versa. 

--------
nLab:      https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   自函子范畴 [[C, C]] 以函子复合 [∘] 为张量、恒等函子 [Id] 为单位是幺半的（该幺半结构是
   [Compose_Monoidal]）。[C] 上的单子恰是此幺半范畴中的幺半对象：载体是自函子 [M]，
   幺半单位 [mempty : Id ⟹ M] 是单子单位 [ret]（η），幺半乘法 [mappend : M ∘ M ⟹ M]
   是单子乘法 [join]（μ）。因张量是严格复合，单位子与结合子是恒等，故幺半单位/结合律
   塌缩为裸单子定律 [join_ret]、[join_fmap_ret] 与 [join_fmap_join]；[mempty]/[mappend]
   的自然性方块变成 [fmap_ret] 与 [join_fmap_fmap]。这正是口号「单子是自函子范畴中的幺半群」
   的精确内容。

   [Monoid_Monad] 把该对应证明为真正逻辑等价（[↔]），从任一此类幺半对象构造单子，反之亦然。 
*)

Definition Endofunctors `(C : Category) := ([C, C]).

(*
The two directions are written without setoid rewriting and with every
   universe named (issue #1348), so that [Monoid_Monad] has the same four
   universes on Coq 8.19.2, Coq 8.20.1 and Rocq 9.1.1 ([About] on each).
   Its earlier proof, by [autorewrite] and [rewrite], left a universe list
   whose length depended on the version: four levels on Rocq 9.1.1 and
   twenty-six on Coq 8.19.2, measured by [About] in #468 and recorded with
   control C40 of Test/ProbeMonadMorphism468.v, so that no statement with
   fixed universe binders could use it on all three versions.  Its binder
   lists the four in the order [About] printed on Rocq 9.1.1 before the
   rewrite, and [About] there prints the same constraints as before, up to
   the names of the universes.  The two directions bind them as the
   bridges of Monad/Morphism/Monoid.v do, whose rewrite-free proofs
   (#468) they are; those bridges are now read off this equivalence.
   Outside the former [Section], [Endofunctors] has the four universes of
   its body where it had six: the two dropped were the section's, and
   occurred in no constraint and nowhere in its type ([About], before and
   after, on Rocq 9.1.1). 

--------
这两个方向都是在没有 setoid 重写的情况下编写的，并且每个
 Universe 命名（问题#1348），因此 [Monoid_Monad] 具有相同的四个
 Coq 8.19.2、Coq 8.20.1 和 Rocq 9.1.1 上的 Universe（每个上都有 [About]）。 
[autorewrite] 和 [rewrite] 的早期证明留下了宇宙列表
 其长度取决于版本：Rocq 9.1.1 上有四个级别，
 Coq 8.19.2 上的二十六，由 #468 中的 [About] 测量并记录
 控制 Test/ProbeMonadMorphism468.v 的 C40，这样就没有语句
 固定宇宙活页夹可以在所有三个版本上使用它。 它的粘合剂
 按 [About] 打印在 Rocq 9.1.1 上的顺序列出了四个
 重写，[About] 打印与之前相同的约束，最多
 宇宙的名称。 这两个方向将它们绑定为
 Monad/Morphism/Monoid.v 的桥梁，其免重写证明
 （#468）他们是； 这些桥现在被读出这个等价物。 
除了前 [Section] 之外，[Endofunctors] 还具有以下四个宇宙：
 它的身体有六个：掉落的两个是该部分的，并且
 发生在没有约束的情况下并且在其类型中没有任何地方发生（[About]，之前和
 之后，在 Rocq 9.1.1 上）。 
*)
Definition monoidobject_monad@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {M : C ⟶ C}
  (m : @MonoidObject (@Fun@{o h o h f f s} C C)
         (@Compose_Monoidal@{s f o h} C) M) :
  @Monad C M.
Proof.
  unshelve refine (@Build_Monad C M
     (fun x => transform[@mempty _ _ _ m] x)
     (fun x => transform[@mappend _ _ _ m] x) _ _ _ _ _).
  - intros x y g. symmetry. exact (naturality[@mempty _ _ _ m] _ _ g).
  - intros x.
    pose proof (@mappend_assoc _ _ _ m x) as E; simpl in E.
    symmetry.
    etransitivity; [ | etransitivity; [ exact E | ] ].
    + symmetry.
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects, fmap_respects, fmap_id | ].
      etransitivity; [ apply fmap_respects, fmap_id | ].
      apply fmap_id.
    + etransitivity;
        [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
      etransitivity; [ apply id_right | ].
      apply compose_respects; [ reflexivity | ].
      etransitivity;
        [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
      apply id_left.
  - intros x.
    pose proof (@mempty_right _ _ _ m x) as E; simpl in E.
    etransitivity; [ | etransitivity; [ exact E | apply fmap_id ] ].
    apply compose_respects; [ reflexivity | ].
    symmetry.
    etransitivity;
      [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
    apply id_left.
  - intros x.
    pose proof (@mempty_left _ _ _ m x) as E; simpl in E.
    etransitivity; [ | etransitivity; [ exact E | apply fmap_id ] ].
    apply compose_respects; [ reflexivity | ].
    symmetry.
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    apply id_right.
  - intros x y g. symmetry. exact (naturality[@mappend _ _ _ m] _ _ g).
Defined.

Definition monad_monoidobject@{o h f s | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {M : C ⟶ C} (T : @Monad C M) :
  @MonoidObject (@Fun@{o h o h f f s} C C) (@Compose_Monoidal@{s f o h} C) M.
Proof.
  unshelve refine (@Build_MonoidObject (@Fun@{o h o h f f s} C C)
     (@Compose_Monoidal@{s f o h} C) M _ _ _ _ _).
  - exact (Build_Transform'@{o h h o h h} (F := Id) (G := M)
             (fun x => @ret C M T x)
             (fun x y g => symmetry (fmap_ret g))).
  - exact (Build_Transform'@{o h h o h h} (F := M ◯ M) (G := M)
             (fun x => @join C M T x)
             (fun x y g => symmetry (join_fmap_fmap g))).
  - intros x; simpl.
    etransitivity; [ | symmetry; apply fmap_id ].
    etransitivity; [ | apply join_ret ].
    apply compose_respects; [ reflexivity | ].
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    apply id_right.
  - intros x; simpl.
    etransitivity; [ | symmetry; apply fmap_id ].
    etransitivity; [ | apply join_fmap_ret ].
    apply compose_respects; [ reflexivity | ].
    etransitivity;
      [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
    apply id_left.
  - intros x; simpl.
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity; [ | apply id_right ].
      apply compose_respects; [ reflexivity | ].
      etransitivity; [ apply fmap_respects, fmap_respects, fmap_id | ].
      etransitivity; [ apply fmap_respects, fmap_id | ].
      apply fmap_id. }
    symmetry.
    etransitivity;
      [ apply compose_respects; [ reflexivity | apply fmap_id ] | ].
    etransitivity; [ apply id_right | ].
    etransitivity.
    { apply compose_respects; [ reflexivity | ].
      etransitivity;
        [ apply compose_respects; [ apply fmap_id | reflexivity ] | ].
      apply id_left. }
    apply join_fmap_join.
Defined.

Definition Monoid_Monad@{o h s f | h < s, o <= f, h <= f +}
  {C : Category@{o h h}} {M : C ⟶ C} :
  @MonoidObject (Endofunctors C) (@Compose_Monoidal@{s f o h} C) M
    ↔ @Monad C M :=
  (@monoidobject_monad@{o h f s} C M, @monad_monoidobject@{o h f s} C M).
