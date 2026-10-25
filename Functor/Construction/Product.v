Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** The product of two functors.  / 两个函子的乘积。*)

(*
nLab: https://ncatlab.org/nlab/show/product+category
   Wikipedia: https://en.wikipedia.org/wiki/Product_category

   Given functors F : C ⟶ D and G : J ⟶ K, their product F ∏⟶ G is the
   functor C ∏ J ⟶ D ∏ K acting componentwise: on objects it sends (c, j) to
   (F c, G j), and on morphisms it sends (f, g) to (fmap[F] f, fmap[G] g). The
   functor laws hold componentwise because they hold in each factor. This is
   the action of the product on morphisms of Cat, making (− ∏ −) a functor
   Cat ∏ Cat ⟶ Cat; on Wikipedia, (f × g)(x, x') = (f x, g x').

   This is the componentwise product F ∏⟶ G of two functors. It should not be
   confused with the pairing (fork) functor ⟨F, G⟩ : C ⟶ D ∏ E arising from
   the universal property of C ∏ D as a product in Cat, which is not defined
   here; ⟨F, G⟩ would send c to (F c, G c) and is recovered as (F ∏⟶ G) ◯ Δ
   along the diagonal Δ : C ⟶ C ∏ C.

   Also provided below are ProductFunctor_swap, which conjugates a bifunctor
   C ∏ J ⟶ D ∏ K by the symmetry Swap to obtain J ∏ C ⟶ K ∏ D, and the slices
   ProductFunctor_fst / ProductFunctor_snd, which recover a single-variable
   functor from a bifunctor by fixing the other argument at the monoidal unit
   I (used to project the monoidal structure of F ∏⟶ G back onto each factor). 

--------
nLab：https://ncatlab.org/nlab/show/product+category
 维基百科：https://en.wikipedia.org/wiki/Product_category

给定函子 F : C ⟶ D 和 G : J ⟶ K，它们的乘积 F ∏⟶ G 是
 函子 C ∏ J ⟶ D ∏ K 组件式作用：作用于将 (c, j) 发送到的对象
 (F c, G j)，对于态射，它将 (f, g) 发送到 (fmap[F] f, fmap[G] g)。 的
 函子定律按分量成立，因为它们对每个因子都成立。 这是
 乘积对 Cat 态射的作用，使 (− ∏ −) 成为函子
 猫∏猫⟶猫； 在维基百科上，(f × g)(x, x') = (f x, g x')。

这是两个函子的分量乘积 F ∏⟶ G。 不应该是
 与配对（分叉）函子 ⟨F, G⟩ : C ⟶ D ∏ E 混淆
 C ∏ D 作为 Cat 中的乘积的通用属性，未定义
 在这里； ⟨F, G⟩ 会将 c 发送到 (F c, G c) 并恢复为 (F ∏⟶ G) ◯ Δ
 沿对角线 Δ ： C ⟶ C ∏ C。

下面还提供了 ProductFunctor_swap，它结合了一个双函子
 C ∏ J ⟶ D ∏ K 通过对称性 Swap 得到 J ∏ C ⟶ K ∏ D，以及切片
 ProductFunctor_fst / ProductFunctor_snd，恢复单变量
 通过将另一个参数固定在幺半群单位上，从双函子中得到函子
 I（用于将 F ∏⟶ G 的幺半群结构投影回每个因子）。 
*)

#[export]
Program Instance ProductFunctor
        {C : Category} {D : Category} {F : C ⟶ D}
        {J : Category} {K : Category} {G : J ⟶ K} :
  (C ∏ J) ⟶ (D ∏ K) := {
  fobj := fun x => (F (fst x), G (snd x));            (* (c, j) ↦ (F c, G j) *)
  fmap := fun _ _ f => (fmap[F] (fst f), fmap[G] (snd f));  (* (f, g) ↦ (F f, G g) *)
  fmap_respects := fun x y f g eqv =>
    (fmap_respects (fst x) (fst y) (fst f) (fst g) (fst eqv),
     fmap_respects (snd x) (snd y) (snd f) (snd g) (snd eqv));
  fmap_id := fun x =>
    (@fmap_id C D F (fst x), @fmap_id J K G (snd x));
  fmap_comp := fun x y z f g =>
    (@fmap_comp C D F (fst x) (fst y) (fst z) (fst f) (fst g),
     @fmap_comp J K G (snd x) (snd y) (snd z) (snd f) (snd g))
}.

(* F ∏⟶ G : C ∏ J ⟶ D ∏ K, the componentwise product of functors.  / F ∏⟶ G : C ∏ J ⟶ D ∏ K，函子的分量积。*)
Notation "F ∏⟶ G" := (@ProductFunctor _ _ F _ _ G) (at level 9).

(*
Conjugating a bifunctor by the symmetry Swap (C ∏ D ⟶ D ∏ C, defined in
   Construction/Product) exchanges its two factors. Given F : C ∏ J ⟶ D ∏ K,
   this yields J ∏ C ⟶ K ∏ D as Swap ◯ F ◯ Swap, sending an object x to
   Swap (F (Swap x)). 

--------
通过对称 Swap 共轭双函子 (C ∏ D ⟶ D ∏ C，定义于
 建筑/产品）交换其两个因素。 给定 F : C ∏ J ⟶ D ∏ K，
 这会产生 J ∏ C ⟶ K ∏ D 作为 Swap ◯ F ◯ Swap，将对象 x 发送到
 互换（F（互换x））。 
*)
Program Definition ProductFunctor_swap
        {C : Category} {D : Category}
        {J : Category} {K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : (J ∏ C) ⟶ (K ∏ D) := {|
  fobj := fun x => Swap (F (Swap x));
  fmap := fun _ _ f => _
|}.
Next Obligation.
  simpl in *.
  split; apply F; split; assumption.
Defined.
Next Obligation.
  proper; simpl; simplify; simpl in *.
  - rewrite !let_snd.
    rewrites; reflexivity.
  - rewrite !let_fst.
    rewrites; reflexivity.
Qed.
Next Obligation.
  rewrite !let_fst, !let_snd; cat.
Qed.
Next Obligation.
  simpl in *.
  rewrite !let_fst, !let_snd; simplify;
  rewrite ?fst_comp, ?snd_comp;
  rewrite <- fmap_comp; reflexivity.
Qed.

(*
If one of the source factors is monoidal, so that it has a unit object I,
   we can slice a bifunctor F : C ∏ J ⟶ D ∏ K to a single-variable functor by
   fixing the other argument at I and projecting the corresponding component.
   ProductFunctor_fst holds the second argument at I : J and keeps the first
   (D) component, giving C ⟶ D; ProductFunctor_snd is the dual, holding the
   first argument at I : C and keeping the second (K) component, giving J ⟶ K.
   These are used to project the monoidal structure of F ∏⟶ G back onto each
   factor (see Functor/Construction/Product/Monoidal.v). 

--------
如果源因子之一是幺半群的，那么它有一个单位对象 I，
 我们可以将双函子 F : C ∏ J ⟶ D ∏ K 切片为单变量函子：
 将另一个参数固定在 I 处并投影相应的分量。 
ProductFunctor_fst 将第二个参数保存在 I : J 处并保留第一个参数
 (D) 分量，给出 C ⟶ D； ProductFunctor_snd 是对偶，持有
 第一个参数为 I : C 并保留第二个 (K) 分量，给出 J ⟶ K。 
这些用于将 F ∏⟶ G 的幺半群结构投影回每个
 因子（参见 Functor/Construction/Product/Monoidal.v）。 
*)

(* ProductFunctor_fst F : C ⟶ D, the slice c ↦ fst (F (c, I)).  / ProductFunctor_fst F : C ⟶ D，切片 c ↦ fst (F (c, I))。*)
Program Definition ProductFunctor_fst
        {C : Category} {D : Category}
        {J : Category} `{@Monoidal J} `{K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : C ⟶ D := {|
  fobj := fun x => fst (F (x, I));
  fmap := fun x y f => fst (@fmap _ _ F (x, I) (y, I) (f, id));
  fmap_respects := fun x y f g eqv =>
    fst (@fmap_respects _ _ F (x, I) (y, I) (f, id) (g, id)
                        (eqv, reflexivity _));
  fmap_id := fun x => fst (@fmap_id _ _ F (x, I));
  fmap_comp := fun x y z f g =>
    _ (fst (@fmap_comp _ _ F (x, I) (y, I) (z, I) (f, id) (g, id)))
|}.
Next Obligation.
  intros.
  rewrite fst_comp.
  rewrite <- fmap_comp; simpl.
  rewrite id_left; reflexivity.
Qed.

(* ProductFunctor_snd F : J ⟶ K, the slice j ↦ snd (F (I, j)).  / ProductFunctor_snd F : J ⟶ K，切片 j ↦ 和 (F (I, j))。*)
Program Definition ProductFunctor_snd
        {C : Category} `{@Monoidal C} `{D : Category}
        {J : Category} {K : Category}
        (F : (C ∏ J) ⟶ (D ∏ K)) : J ⟶ K := {|
  fobj := fun x => snd (F (I, x));
  fmap := fun x y f => snd (@fmap _ _ F (I, x) (I, y) (id, f));
  fmap_respects := fun x y f g eqv =>
    snd (@fmap_respects _ _ F (I, x) (I, y) (id, f) (id, g)
                        (reflexivity _, eqv));
  fmap_id := fun x => snd (@fmap_id _ _ F (I, x));
  fmap_comp := fun x y z f g =>
    _ (snd (@fmap_comp _ _ F (I, x) (I, y) (I, z) (id, f) (id, g)))
|}.
Next Obligation.
  intros.
  rewrite snd_comp.
  rewrite <- fmap_comp; simpl.
  rewrite id_left; reflexivity.
Qed.
