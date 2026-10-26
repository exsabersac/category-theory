Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Construction.Funny.
Require Import Category.Construction.Funny.StrictEq.
Require Import Category.Construction.Funny.Bifunctor.
Require Import Category.Instance.Two.
Require Import Coq.Lists.List.

Generalizable All Variables.

(*
   * * The comparison functor κ : C □ D ⟶ C ∏ D

   The funny tensor product C □ D (Construction/Funny.v) and the cartesian
   product C ∏ D (Construction/Product.v) have the same objects; the
   comparison functor κ ([FunnyToProduct]) is the identity on objects and
   sends a word to its componentwise composite, one generating step at a
   time:

   lstep f ↦ (f, id)        rstep g ↦ (id, g)

   κ is bijective on objects ([FunnyToProduct_obj]) and full
   ([FunnyToProduct_Full]): every (f, g) in C ∏ D is the image of the word
   “g then f” — indeed of either diagonal of the fundamental square, since
   (f, g) ≈ (f, id) ∘ (id, g) ≈ (id, g) ∘ (f, id) there.  It is NOT faithful
   ([FunnyToProduct_not_faithful]): the two diagonals are identified by κ
   but remain distinct in C □ D ([funny_diagonals_distinct]).  Finally κ is
   natural in both arguments over strict functor equality
   ([FunnyToProduct_natural]).

   The non-faithfulness witness interprets _2 □ _2 in the free monoid on the
   booleans, regarded as a one-object category ([ListMon]): L-steps are
   tagged [true], R-steps [false], and the two diagonals map to the distinct
   words [true; false] and [false; true].  This is the one-object shadow of
   Weber's observation (TAC 28:2, §2) that on monoids − □ − is the free
   product (the coproduct of monoids), whereas − ∏ − is the direct product.
   It also pins down, as a regression test, that the congruence [feq] was
   not accidentally made too coarse: no interchange is derivable.

   Weber (TAC 28:2) further factorizes κ as bijective-on-objects followed by
   fully-faithful to obtain the Gray tensor product of 2-categories, where
   the two diagonals become isomorphic rather than equal; that factorization
   is out of scope here and recorded only as this remark. 

   --------
   * * 比较函子 κ : C □ D ⟶ C ∏ D

   有趣的张量积 C □ D (Construction/Funny.v) 和笛卡尔积 C ∏ D (Construction/Product.v) 具有相同的对象；
   比较函子 κ ([FunnyToProduct]) 在对象上为恒等，并将一个单词映射到其逐分量复合，一次处理一个生成步骤：

   lstep f ↦ (f, id)        rstep g ↦ (id, g)κ 在对象上是双射的（[FunnyToProduct_obj]）并且是满的（[FunnyToProduct_Full]）：C ∏ D 中的每个 (f, g) 都是词 “先 g 后 f” 的像 —— 实际上是基本方形的任一对角线的像，因为 (f, g) ≈ (f, id) ∘ (id, g) ≈ (id, g) ∘ (f, id)。它不是忠实的（[FunnyToProduct_not_faithful]）：两条对角线被 κ 识别，但在 C □ D 中仍然是不同的（[funny_diagonals_distinct]）。最后，κ 在严格函子等价下对两个参数都是自然的（[FunnyToProduct_natural]）。不忠实的证人将 _2 □ _2 在布尔上的自由幺半群中解释为一个单对象范畴 ([ListMon])：L 步标记为 [true]，R 步标记为 [false]，两条对角线分别映射到不同的词 [true; false] 和 [false; true]。这是一对象的魏伯观察 (TAC 28:2, §2) 的影子：在幺半群上，− □ − 是自由积（幺半群的余积），而 − ∏ − 是直积。它还确定了，作为回归测试，同余 [feq] 并非偶然地被设置得过于粗糙：没有可推导的交换式。Weber（TAC 28:2）进一步将 κ 分解为先在对象上双射再完全忠实，以得到 2 范畴的 Gray 张量积，其中两个对角线变为同构而非相等；该分解在此不予讨论，仅作为此备注记录。
*)

(** ** The comparison functor / ** 比较函数对象 *)

(*
 The separately functorial data of κ: each generating step becomes the
 corresponding one-sided morphism of the cartesian product.  Interchange
 holds in C ∏ D, so this data folds words through [FunnyUP] with no
 obstruction — κ is precisely where the two diagonals get identified. 

 --------
 κ 的单独函子数据：每一个生成步骤变成笛卡尔积的对应单边态射。在 C ∏ D 中交换律成立，因此这些数据可以毫无障碍地通过 [FunnyUP] 折叠单词——κ 恰好是两个对角线被识别的地方。
*)
Program Definition FunnyToProduct_sep {C D : Category} :
  SepFunctorial (E:=C ∏ D) (fun (c : C) (d : D) => (c, d)) := {|
  sf_lmap := fun _ _ f d => (f, id);
  sf_rmap := fun c _ _ g => (id, g)
|}.

Definition FunnyToProduct {C D : Category} : (C □ D) ⟶ (C ∏ D) :=
  FunnyUP FunnyToProduct_sep.

(* κ is (definitionally) bijective on objects. / κ 在对象上是（定义上）双射的。 *)
Lemma FunnyToProduct_obj {C D : Category} (c : C) (d : D) :
  FunnyToProduct (c, d) = ((c, d) : C ∏ D).
Proof. reflexivity. Qed.

(*
 κ is full: (f, g) is the image of the word “g then f” (the R-then-L
 diagonal; the L-then-R one would do just as well). 

 --------
 κ 是满的：(f, g) 是单词“g 然后 f”的映射（R-然后-L 对角线；L-然后-R 对角线也一样适用）。
*)
#[export] Program Instance FunnyToProduct_Full {C D : Category} :
  Full (@FunnyToProduct C D) := {
  prefmap := fun x y fg => fconsR (snd fg) (fconsL (fst fg) fnil)
}.

(*
   * ** The discriminating interpretation

   The free monoid on [bool], as a one-object category: morphisms are lists
   of booleans, composition is concatenation.  Words read source-to-target
   while composition reads right-to-left, so [v ∘ u] appends [u] in front:
   [compose v u = u ++ v]. 

   --------
   * ** 区分性解释

   在 [bool] 上的自由幺半群，作为一个单对象范畴：态射是布尔值的列表，组合是连接操作。单词从源到目标读取，而组合从右到左读取，所以 [v ∘ u] 会将 [u] 添加到前面：[compose v u = u ++ v]。
*)

Program Definition ListMon : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => list bool;
  homset  := fun _ _ => Morphism_equality _ _;
  id      := fun _ => nil;
  compose := fun _ _ _ u v => (v ++ u)%list
|}.
Next Obligation. now rewrite app_nil_r. Qed.
Next Obligation. now rewrite app_assoc. Qed.
Next Obligation. now rewrite app_assoc. Qed.

(*
 Tag the single non-identity arrow of 2 with [b]; identities vanish. 

 --------
 用 [b] 标记 2 的唯一非恒等箭头；恒等消失。
*)
Definition two_tag (b : bool) {x y : TwoObj} (f : TwoHom x y) : list bool :=
  match f with
  | TwoXY => b :: nil
  | _ => nil
  end.

(*
 The separately functorial interpretation _2 □ _2 ⟶ ListMon distinguishing
 the two diagonals: L-steps are tagged [true], R-steps [false]. 

 --------
 分别函子化的解释 _2 □ _2 ⟶ ListMon 区分两个对角线：L 步标记为 [true]，R 步标记为 [false]。
*)
Program Definition FunnyTwo_sep :
  SepFunctorial (C:=_2) (D:=_2) (E:=ListMon) (fun _ _ => ttt) := {|
  sf_lmap := fun _ _ f _ => two_tag true f;
  sf_rmap := fun _ _ _ g => two_tag false g
|}.
Next Obligation. destruct c; reflexivity. Qed.
Next Obligation. destruct d; reflexivity. Qed.
Next Obligation.
  (*
 Finite case analysis on the endpoints; [TwoHom_inv] then pins each
 morphism to its unique inhabitant (Instance/Two.v idiom). 

 --------
 对端点进行有限情况分析；[TwoHom_inv] 然后将每个态射固定到其唯一的成员（Instance/Two.v 习语）。
*)
  destruct c, c', c'';
    try destruct (TwoHom_Y_X_absurd f);
    try destruct (TwoHom_Y_X_absurd f');
    pose proof (TwoHom_inv _ _ f);
    pose proof (TwoHom_inv _ _ f');
    simpl in *; subst; reflexivity.
Qed.
Next Obligation.
  destruct d, d', d'';
    try destruct (TwoHom_Y_X_absurd g);
    try destruct (TwoHom_Y_X_absurd g');
    pose proof (TwoHom_inv _ _ g);
    pose proof (TwoHom_inv _ _ g');
    simpl in *; subst; reflexivity.
Qed.

Definition FunnyTwoInterp : (_2 □ _2) ⟶ ListMon := FunnyUP FunnyTwo_sep.

(* * ** The two diagonals of the fundamental square / * ** 基本正方形的两条对角线 *)

(*
 The square in _2 □ _2 built from TwoXY in each coordinate; L first. 

 --------
 在每个坐标由 TwoXY 构建的 _2 □ _2 方形；先 L。
*)
Definition diagLR : FunHom (C:=_2) (D:=_2) TwoX TwoX TwoY TwoY :=
  fconsL (C:=_2) (D:=_2) TwoXY (fconsR (C:=_2) (D:=_2) TwoXY fnil).

(* The same square, R first. / 相同的方块，先是R。 *)
Definition diagRL : FunHom (C:=_2) (D:=_2) TwoX TwoX TwoY TwoY :=
  fconsR (C:=_2) (D:=_2) TwoXY (fconsL (C:=_2) (D:=_2) TwoXY fnil).

(*
 The separation theorem: the two diagonals are NOT identified by [feq].
 Folding through [FunnyTwo_sep] sends them to the distinct words
 [true; false] and [false; true] of the free monoid, and [ffold_respects]
 says the fold is [feq]-invariant.  This is the regression test that the
 congruence on words is not too coarse — no interchange law snuck in. 

 --------
 分离定理：两个对角线不能被  [feq]  识别。通过  [FunnyTwo_sep]  折叠将它们分别送到自由幺半群的不同词  [true; false]  和  [false; true] ，而  [ffold_respects]  表明折叠是  [feq] -不变的。这就是回归测试，用来检验词上的合同关系是否不太粗糙——没有任何交换律偷偷混进来。
*)
Theorem funny_diagonals_distinct : feq diagLR diagRL → False.
Proof.
  intro E.
  pose proof (ffold_respects FunnyTwo_sep E) as X.
  simpl in X.
  discriminate X.
Qed.

(*
 κ identifies the two diagonals (both map to (TwoXY, TwoXY)), so it cannot
 be faithful. 

 --------
 κ 标识了两条对角线（两者都映射到 (TwoXY, TwoXY)），所以它不能是忠实的。
*)
Corollary FunnyToProduct_not_faithful :
  Faithful (@FunnyToProduct _2 _2) → False.
Proof.
  intros [inj].
  apply funny_diagonals_distinct.
  apply (inj (TwoX, TwoX) (TwoY, TwoY) diagLR diagRL).
  simpl; split; reflexivity.
Qed.

(*
   * ** Naturality of κ over strict functor equality

   κ is the component at (C, D) of a transformation from the funny tensor to
   the cartesian product of functors: κ ∘ (F □ G) ≈ (F ∏⟶ G) ∘ κ, in
   [Functor_StrictEq_Setoid].  Both sides agree definitionally on objects;
   on the generating steps the fixed coordinate needs [fmap_id] (an ≈-level
   equation, which is exactly why the statement lives at strict functor
   equality and not literal equality). 

   --------
   * ** κ 关于严格函子等式的自然性

   κ 是从有趣张量到函子的笛卡尔积的变换在 (C, D) 处的分量：κ ∘ (F □ G) ≈ (F ∏⟶ G) ∘ κ，在 [Functor_StrictEq_Setoid] 中。双方在对象上的定义一致；在生成步骤上，固定坐标需要 [fmap_id]（一个 ≈-级别的等式，这正是该命题存在于严格函子等式而不是字面等式的原因）。
*)

Lemma FunnyToProduct_natural {C C' D D' : Category}
  (F : C ⟶ C') (G : D ⟶ D') :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) (C' ∏ D'))
    (FunnyToProduct ◯ FunnyBimap F G) ((F ∏⟶ G) ◯ FunnyToProduct).
Proof.
  apply (Funny_strict_eq (FunnyToProduct ◯ FunnyBimap F G)
           ((F ∏⟶ G) ◯ FunnyToProduct) (fun _ _ => eq_refl)).
  - intros c c' f d; simpl; split; cat.
  - intros c d d' g; simpl; split; cat.
Qed.
