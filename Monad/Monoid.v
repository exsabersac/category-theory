Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Monoidal.Compose.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* * * Monads monoids 范畴 endofunctors （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/monad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)

   自函子范畴 [[C, C]] 以函子复合 [∘] 为张量、恒等函子 [Id] 为单位是幺半的（该幺半结构是
   [Compose_Monoidal]）。[C] 上的单子恰是此幺半范畴中的幺半对象：载体是自函子 [M]，
   幺半单位 [mempty : Id ⟹ M] 是单子单位 [ret]（η），幺半乘法 [mappend : M ∘ M ⟹ M]
   是单子乘法 [join]（μ）。因张量是严格复合，单位子与结合子是恒等，故幺半单位/结合律
   塌缩为裸单子定律 [join_ret]、[join_fmap_ret] 与 [join_fmap_join]；[mempty]/[mappend]
   的自然性方块变成 [fmap_ret] 与 [join_fmap_fmap]。这正是口号「单子是自函子范畴中的幺半群」
   的精确内容。

   [Monoid_Monad] 把该对应证明为真正逻辑等价（[↔]），从任一此类幺半对象构造单子，反之亦然。 *)

Definition Endofunctors `(C : Category) := ([C, C]).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
