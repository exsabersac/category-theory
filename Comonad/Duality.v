Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.CoKleisli.
Require Import Category.Comonad.Coalgebra.

Generalizable All Variables.

(** * Duality for comonads: the transfer package and both resolutions / * 余单子的对偶性：传递包与两种解析 *)

(*
nLab:      https://ncatlab.org/nlab/show/comonad
   nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   nLab:      https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   Theory/Monad.v defines [Comonad := @Monad (C^op) (W^op)], and duality is
   built into this library so that C^op^op = C and (W^op)^op = W hold by
   reflexivity.  This file packages the consequences of that choice for the
   theory of resolutions:

   - the conversions between comonads on C and monads on C^op — and,
     mirrored, between monads on C and comonads on C^op — are the identity,
     with round trips holding by [reflexivity]
     ([op_Monad_of_Comonad], [Comonad_of_op_Monad], [op_Comonad_of_Monad],
     [Monad_of_op_Comonad]);

   - every adjunction F ⊣ U (F : D ⟶ C the left adjoint) induces a comonad
     on C with endofunctor F ◯ U ([Adjunction_Comonad]), the formal dual of
     [Adjunction_Monad] in Monad/Adjunction.v: dualize the adjunction with
     Adjunction/Opposite.v to U^op ⊣ F^op and take the monad it induces on
     C^op.  That monad lives on the composite F^op ◯ U^op, while the goal
     [@Comonad C (F ◯ U)] unfolds to a monad on (F ◯ U)^op.  The two
     composites share their object and morphism maps definitionally, but
     Compose rebuilds its functor-law fields per application, so the two
     functor records are distinct terms; the comonad is therefore assembled
     by [Build_Monad] with every field taken unchanged from the dual monad
     (the field types are convertible across the two composites — no law is
     re-proved);

   - the two canonical resolutions of a comonad arise from the monad
     resolutions of Monad/Kleisli/Adjunction.v and
     Monad/Eilenberg/Moore/Adjunction.v by dualizing: for the co-Kleisli
     category the forgetful functor x ↦ W x is LEFT adjoint to the cofree
     one ([CoKleisli_Adjunction]), and likewise for the co-Eilenberg–Moore
     category of coalgebras ([CoEM_Adjunction]) — under op the free/
     forgetful pair of the monad world trades sides, which is why a comonad
     is resolved as forgetful ⊣ cofree.  Each adjunction is literally the
     [Opposite_Adjunction] of its monad counterpart; the covariant reading
     lemmas beside them record what the functors, units and counits are in
     terms of [extract], [duplicate] and [extend] of Comonad/Core.v, each
     holding by [reflexivity] or by a single identity law.  The composite
     Forget ◯ Cofree recovers W on the nose for both resolutions
     ([CoKleisli_Comonad_agrees], [CoEM_Comonad_agrees]), dually to
     [Kleisli_Monad_agrees] and [EM_Monad_agrees].

--------
nLab:      https://ncatlab.org/nlab/show/comonad
   nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   nLab:      https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   Theory/Monad.v 定义 [Comonad := @Monad (C^op) (W^op)]，且本库对偶使 C^op^op = C 与
   (W^op)^op = W 由 reflexivity 成立。本文件打包该选择对分解理论的后果：

   - C 上余单子与 C^op 上单子之间的转换——镜像地，C 上单子与 C^op 上余单子——是恒等，
     往返由 [reflexivity] 成立（[op_Monad_of_Comonad]、[Comonad_of_op_Monad] 等）；

   - 每个伴随 F ⊣ U（F : D ⟶ C 左伴随）在 C 上以自函子 F ◯ U 诱导余单子
     （[Adjunction_Comonad]），是 Monad/Adjunction.v 中 [Adjunction_Monad] 的形式对偶：
     用 Adjunction/Opposite.v 对偶伴随得 U^op ⊣ F^op，取其在 C^op 上诱导的单子；

   - 余单子的两种典范分解来自 Monad/Kleisli/Adjunction.v 与
     Monad/Eilenberg/Moore/Adjunction.v 的单子分解经对偶：对 co-Kleisli 范畴，遗忘
     x ↦ W x 是余自由的*左*伴随（[CoKleisli_Adjunction]），余代数的 co-Eilenberg–Moore
     同理（[CoEM_Adjunction]）——在 op 下单子世界的自由/遗忘对换边，故余单子分解为
     遗忘 ⊣ 余自由。复合 Forget ◯ Cofree 对两分解在表面上恢复 W。
*)

(*
The two resolutions as extremes

   nLab: https://ncatlab.org/nlab/show/Eilenberg-Moore+category
   nLab: https://ncatlab.org/nlab/show/comonadic+functor

   Among the adjunctions inducing a given comonad, the two resolutions
   of this file occupy the extreme positions.  On the monad side the
   Kleisli adjunction is initial and the Eilenberg–Moore adjunction
   terminal in the category of adjunctions inducing T; and because
   (−)^op is covariant on functors, dualization preserves that
   orientation, so the co-Kleisli resolution is likewise initial and the
   co-Eilenberg–Moore resolution terminal.  Every inducing adjunction
   therefore receives a canonical comparison functor from the former and
   sends one into the latter, and the comparison into coalgebras being
   an equivalence is what it means for the inducing adjunction's left
   adjoint to be comonadic.

   CORRECTION (#475).  On the monad side, the comparison functor out of
   the Kleisli category did not exist when this was written; it is now
   Monad/Kleisli/Comparison.v's [Kleisli_Comparison] (Mac Lane's L,
   Theorem VI.5.2), unique by [Kleisli_Comparison_unique] when the object
   equations of its two triangles cohere (the right one's the image under
   the right adjoint of the left one's), beside Monad/Comparison.v's
   [EM_Comparison] into the algebras.  Neither comparison is stated on
   the comonad side.  The initiality and terminality asserted above are
   Mac Lane's Theorem VI.5.3, which issue #476 tracks.

   The transfer package below is what makes this duality a theorem
   scheme rather than a pair of parallel constructions.  Since
   [Comonad C W] IS [@Monad (C^op) (W^op)] and the op involution is
   definitional, every monad theorem in the library is already a comonad
   theorem: instantiate it at (C^op, W^op) and read the composites
   backwards.  The files of the Comonad/ directory are exactly such
   readings, and no comonad law is ever proved twice.

   A single adjunction exhibits the whole family of standard examples.
   On a cartesian closed category the currying adjunction e × − ⊣ e ⇒ −
   induces, in one order, the state monad e ⇒ (e × −) and, in the other,
   the store comonad (e ⇒ −) × e; its left adjoint e × − is itself the
   environment comonad, and its right adjoint e ⇒ − the reader monad.
   Env, Reader, State and Store are in this sense one adjunction viewed
   four ways (Instance/Coq/Comonad/Env.v, Instance/Coq/Comonad/Store.v).

--------
两个极端的决议

nLab：https://ncatlab.org/nlab/show/Eilenberg-Moore+category
nLab：https://ncatlab.org/nlab/show/comonadic+functor

在引出给定余幺范畴的伴随对中，本文件的两个分解处于极端位置。在幺范畴方面，Kleisli 伴随对在引出 T 的伴随对类别中是初始的，而 Eilenberg–Moore 伴随对是终的；并且因为 (−)^op 在函子上是协变的，对偶化保留了这个方向性，因此 co-Kleisli 分解同样是初始的，而 co-Eilenberg–Moore 分解是终的。因此，每一个引出的伴随对都从前者接收一个规范的比较函子，并将一个函子送入后者，而到余代数的比较是等价的，这就是引出伴随对的左伴随是余幂范畴的意思。

修正 (#475)。在单子侧，从 Kleisli 范畴出的比较函子在撰写本文时不存在；它现在是 Monad/Kleisli/Comparison.v 中的 [Kleisli_Comparison]（Mac Lane 的 L，定理 VI.5.2），当其两个三角形的对象方程一致时，由 [Kleisli_Comparison_unique] 唯一确定（右侧的三角形是左侧三角形在右伴随下的像），以及 Monad/Comparison.v 中的 [EM_Comparison] 进入代数。两者在余单子侧都没有说明比较。上面断言的初始性和终极性是 Mac Lane 的定理 VI.5.3，问题 #476 跟踪了该定理。

下面的传递包使这种对偶性成为一个定理方案，而不是一对平行构造。由于 [Comonad C W] 等于 [@Monad (C^op) (W^op)] 且操作逆变是定义性的，库中的每个单子定理已经是一个余单子定理：在 (C^op, W^op) 上实例化它，然后倒着读取复合。Comonad/ 目录下的文件正是这样的读取，并且没有任何余单子定律被证明过两次。

一个单一的伴随关系展示了整个标准示例家族。在笛卡尔闭范畴上，柯里伴随关系 e × − ⊣ e ⇒ − 导致，一种顺序下，是状态单子 e ⇒ (e × −)，而在另一种顺序下，是存储余单子 (e ⇒ −) × e；它的左伴随 e × − 本身是环境余单子，而它的右伴随 e ⇒ − 是读者单子。从这个意义上说，Env、Reader、State 和 Store 是一个伴随关系的四种视角（Instance/Coq/Comonad/Env.v，Instance/Coq/Comonad/Store.v）。
*)

(**
** The transfer package

    [Comonad C W] IS [@Monad (C^op) (W^op)] by definition, so all four
    conversions below are the identity function and both round trips hold
    by [reflexivity].  They are provided as named coercion points: writing
    [op_Monad_of_Comonad H] in a proof records the direction in which a
    witness is being read, which the bare [H] does not.

--------
** 传输包

    [Comonad C W] 根据定义是 [@Monad (C^op) (W^op)]，因此下面的四种转换都是恒等函数，并且两次往返都由 [reflexivity] 保证。它们作为命名强制转换点提供：在证明中写入 [op_Monad_of_Comonad H] 可以记录读取证据的方向，而单独的 [H] 则不能。
*)

Section MonadComonadDuality.

Context {C : Category}.
Context {W : C ⟶ C}.

Definition op_Monad_of_Comonad (H : @Comonad C W) : @Monad (C^op) (W^op) := H.

Definition Comonad_of_op_Monad (H : @Monad (C^op) (W^op)) : @Comonad C W := H.

Lemma Comonad_of_op_Monad_of_Comonad (H : @Comonad C W) :
  Comonad_of_op_Monad (op_Monad_of_Comonad H) = H.
Proof. reflexivity. Qed.

Lemma op_Monad_of_Comonad_of_op_Monad (H : @Monad (C^op) (W^op)) :
  op_Monad_of_Comonad (Comonad_of_op_Monad H) = H.
Proof. reflexivity. Qed.

(**
Mirrored: a monad on C is the same thing as a comonad on C^op.  Both
    typecheck because (C^op)^op = C and (W^op)^op = W hold by
    reflexivity.

--------
镜像：C 上的单子与 C^op 上的余单子是同一件事。两者都可以类型检查，因为 (C^op)^op = C 且 (W^op)^op = W 通过自反性成立。
*)

Definition op_Comonad_of_Monad (H : @Monad C W) : @Comonad (C^op) (W^op) := H.

Definition Monad_of_op_Comonad (H : @Comonad (C^op) (W^op)) : @Monad C W := H.

Lemma Monad_of_op_Comonad_of_Monad (H : @Monad C W) :
  Monad_of_op_Comonad (op_Comonad_of_Monad H) = H.
Proof. reflexivity. Qed.

Lemma op_Comonad_of_Monad_of_op_Comonad (H : @Comonad (C^op) (W^op)) :
  op_Comonad_of_Monad (Monad_of_op_Comonad H) = H.
Proof. reflexivity. Qed.

End MonadComonadDuality.

(**
** The comonad induced by an adjunction

    Every adjunction F ⊣ U induces the monad U ◯ F on the domain of F
    (Monad/Adjunction.v) and, dually, the comonad F ◯ U on its codomain:
    the counit ε is the counit of the adjunction, and the comultiplication
    is F η U.  (These covariant readings hold inside the sealed proof of the
    Qed-opaque [Adjunction_Monad], so — unlike the reflexivity-backed
    agreement lemmas elsewhere in this file — they are not exposed here as
    lemmas about [extract]/[duplicate] of the induced comonad.)  Rather than
    re-deriving the laws from the zig-zag
    identities, dualize: Adjunction/Opposite.v turns A : F ⊣ U into
    A^op : U^op ⊣ F^op, whose [Adjunction_Monad] is a monad on C^op with
    endofunctor F^op ◯ U^op.  The target class [@Comonad C (F ◯ U)]
    unfolds to [@Monad (C^op) ((F ◯ U)^op)]; the two composites agree on
    objects and morphisms definitionally (only their Qed-sealed functor-law
    fields are distinct terms), so every monad field transports unchanged
    and [Build_Monad] just repackages the dual monad.

--------
** 由伴随关系引起的余单子

每个伴随 F ⊣ U 都会在 F 的定义域上产生单子 U ◯ F（Monad/Adjunction.v），并且，对偶地，在其值域上产生余单子 F ◯ U：余单位 ε 是伴随的余单位，共乘是 F η U。（这些协变解释在 Qed-opaque [Adjunction_Monad] 的封闭证明内成立，因此——与本文件其他地方依赖自反性的对应引理不同——它们不会作为关于诱导余单子的 [extract]/[duplicate] 的引理被公开。）与其从锯齿形恒等式重新推导定律，不如对偶化：Adjunction/Opposite.v 将 A : F ⊣ U 转变为 A^op : U^op ⊣ F^op，其 [Adjunction_Monad] 是 C^op 上的一个单子，具有自函子 F^op ◯ U^op。目标类 [@Comonad C (F ◯ U)] 展开为 [@Monad (C^op) ((F ◯ U)^op)]；两个复合在对象和态射上定义上是一致的（只有它们的 Qed-封闭函子律字段是不同的项），因此每个单子字段传递时保持不变，[Build_Monad] 仅仅重新打包了对偶单子。
*)

Section AdjunctionComonad.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Definition Adjunction_Comonad (A : F ⊣ U) : @Comonad C (F ◯ U) :=
  let M : @Monad (C^op) (F^op ◯ U^op) :=
    Adjunction_Monad (Opposite_Adjunction F U A) in
  @Build_Monad (C^op) ((F ◯ U)^op)
    (fun x => @ret (C^op) (F^op ◯ U^op) M x)
    (fun x => @join (C^op) (F^op ◯ U^op) M x)
    (fun x y f => @fmap_ret (C^op) (F^op ◯ U^op) M x y f)
    (fun x => @join_fmap_join (C^op) (F^op ◯ U^op) M x)
    (fun x => @join_fmap_ret (C^op) (F^op ◯ U^op) M x)
    (fun x => @join_ret (C^op) (F^op ◯ U^op) M x)
    (fun x y f => @join_fmap_fmap (C^op) (F^op ◯ U^op) M x y f).

End AdjunctionComonad.

(**
** The co-Kleisli resolution: forgetful ⊣ cofree

    Dualizing the Kleisli resolution of the opposite monad
    (Monad/Kleisli/Adjunction.v) yields the initial resolution of the
    comonad W through its co-Kleisli category (Comonad/CoKleisli.v):

    - [CoKleisli_Forget] : CoKleisli ⟶ C sends x to W x and a co-Kleisli
      morphism f : W x ~> y to its extension [extend f] — under the
      comparison with coalgebras it forgets a cofree coalgebra to its
      carrier, whence the name;
    - [CoKleisli_Cofree] : C ⟶ CoKleisli is the identity on objects and
      sends f : x ~> y to the co-Kleisli morphism f ∘ extract;
    - [CoKleisli_Adjunction] : CoKleisli_Forget ⊣ CoKleisli_Cofree — for a
      comonad the forgetful side is the LEFT adjoint, since op trades the
      sides of the free ⊣ forgetful resolution of the monad W^op.

    Because both hom-sets of the transposition are literally the same
    setoid W x ~> y, the adjunction isomorphism is the identity map, and
    the readings of the functors, unit and counit below are definitional
    except where a single identity law intervenes.

--------
** 共Kleisli分解：忘记 ⊣ 共自由

对偶化对偶单子的 Kleisli 分解式（Monad/Kleisli/Adjunction.v）会通过其协 Kleisli 范畴（Comonad/CoKleisli.v）生成余单子 W 的初始分解式：

- [CoKleisli_Forget]：CoKleisli ⟶ C 将 x 映射到 W x，并将一个 co-Kleisli 态射 f : W x ~> y 映射到它的扩展 [extend f] —— 在与余代数的比较下，它将一个共自由余代数忘记到它的载体，因此得名；
- [CoKleisli_Cofree]：C ⟶ CoKleisli 在对象上是恒等，并且将 f : x ~> y 映射到 co-Kleisli 态射 f ∘ extract；
- [CoKleisli_Adjunction]：CoKleisli_Forget ⊣ CoKleisli_Cofree —— 对于一个余单子，忘记一边是左伴随，因为 op 会交换单子 W^op 的自由 ⊣ 忘记解析的两边。

因为换位的两个同态集合在字面上都是相同的集合 W x ~> y，伴随同构是恒等映射，以下函子、单位和余单位的读法都是定义上的，除非有单一的恒等律介入。
*)

Section CoKleisliAdjunction.

Context {C : Category}.
Context {W : C ⟶ C}.
Context {H : @Comonad C W}.

Definition CoKleisli_Forget : @CoKleisli C W H ⟶ C :=
  Opposite_Functor (@Kleisli_Forget (C^op) (W^op) H).

Definition CoKleisli_Cofree : C ⟶ @CoKleisli C W H :=
  Opposite_Functor (@Kleisli_Free (C^op) (W^op) H).

(** Covariant readings of the two functors, all definitional. / 两个函子的协变取值，都是定义性的。 *)

Lemma CoKleisli_Forget_obj (x : C) : CoKleisli_Forget x = W x.
Proof. reflexivity. Qed.

Lemma CoKleisli_Forget_fmap {x y : C} (f : W x ~{C}~> y) :
  fmap[CoKleisli_Forget] f ≈ extend f.
Proof. reflexivity. Qed.

Lemma CoKleisli_Cofree_obj (x : C) : CoKleisli_Cofree x = x.
Proof. reflexivity. Qed.

Lemma CoKleisli_Cofree_fmap {x y : C} (f : x ~{C}~> y) :
  fmap[CoKleisli_Cofree] f ≈ f ∘ extract.
Proof. reflexivity. Qed.

Definition CoKleisli_Adjunction : CoKleisli_Forget ⊣ CoKleisli_Cofree :=
  Opposite_Adjunction _ _ (@Kleisli_Adjunction (C^op) (W^op) H).

(** The counit of the adjunction is the counit of the comonad. / 伴随的余单位是余单子的余单位。 *)

Lemma CoKleisli_counit_agrees {x : C} :
  @counit _ _ _ _ CoKleisli_Adjunction x ≈ @extract C W H x.
Proof. reflexivity. Qed.

(**
The unit at x is the identity arrow on W x, read as the co-Kleisli
    morphism x ~{CoKleisli}~> CoKleisli_Cofree (W x).

--------
x 处的单位是 W x 的恒等箭头，读作共 Kleisli 映射 x ~{CoKleisli}~> CoKleisli_Cofree (W x)。
*)

Lemma CoKleisli_unit_agrees {x : C} :
  @unit _ _ _ _ CoKleisli_Adjunction x ≈ id[W x].
Proof. reflexivity. Qed.

(**
The comultiplication of the comonad induced by this adjunction (dually
    to Monad/Adjunction.v it is the CoKleisli_Forget-image of the unit) is
    duplicate.

--------
由此伴随诱导的余单子（与 Monad/Adjunction.v 对偶，它是单位的 CoKleisli_Forget 像）的余乘法是 duplicate。
*)

Lemma CoKleisli_duplicate_agrees {x : C} :
  fmap[CoKleisli_Forget] (@unit _ _ _ _ CoKleisli_Adjunction x)
    ≈ @duplicate C W H x.
Proof.
  simpl.
  rewrite fmap_id.
  cat.
Qed.

(**
The resolution recovers W: the composite Forget ◯ Cofree is naturally
    isomorphic to W, with identity components.

--------
该分解恢复了 W：复合 Forget ◯ Cofree 天然同构于 W，并且具有恒等分量。
*)

Theorem CoKleisli_Comonad_agrees : CoKleisli_Forget ◯ CoKleisli_Cofree ≈ W.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  exact (@fmap_extend_extract C W H x y f).
Qed.

End CoKleisliAdjunction.

(**
** The co-Eilenberg–Moore resolution: forgetful ⊣ cofree

    Dualizing the Eilenberg–Moore resolution of the opposite monad
    (Monad/Eilenberg/Moore/Adjunction.v) yields the terminal resolution of
    W through its category of coalgebras (Comonad/Coalgebra.v):

    - [CoEM_Forget] : CoEilenbergMoore ⟶ C projects a coalgebra to its
      carrier and a coalgebra homomorphism to its underlying arrow;
    - [CoEM_Cofree] : C ⟶ CoEilenbergMoore sends x to the cofree coalgebra
      (W x, δ_x) — its costructure map is duplicate — and f : x ~> y to
      the homomorphism carried by fmap[W] f;
    - [CoEM_Adjunction] : CoEM_Forget ⊣ CoEM_Cofree, with the forgetful
      side again the left adjoint.

--------
** 协 Eilenberg–Moore 分解：忘记 ⊣ 共自由

对对偶单子(Eilenberg–Moore 分解)进行对偶化
(Monad/Eilenberg/Moore/Adjunction.v) 会产生 W 的终端分解
通过其余的余代数类别 (Comonad/Coalgebra.v)：

- [CoEM_Forget] : CoEilenbergMoore ⟶ C 将一个余代数投影到其载体，将一个余代数同态投影到底层箭头；
- [CoEM_Cofree] : C ⟶ CoEilenbergMoore 将 x 发送到共自由余代数 (W x, δ_x) —— 其余结构映射是复制 —— 并将 f : x ~> y 发送到由 fmap[W] f 承载的同态；
- [CoEM_Adjunction] : CoEM_Forget ⊣ CoEM_Cofree，其中忘记侧仍然是左伴随。
*)

Section CoEilenbergMooreAdjunction.

Context {C : Category}.
Context {W : C ⟶ C}.
Context {H : @Comonad C W}.

Definition CoEM_Forget : @CoEilenbergMoore C W H ⟶ C :=
  Opposite_Functor (@EM_Forget (C^op) (W^op) H).

Definition CoEM_Cofree : C ⟶ @CoEilenbergMoore C W H :=
  Opposite_Functor (@EM_Free (C^op) (W^op) H).

(** Covariant readings of the two functors, all definitional. / 两个函子的协变取值，都是定义性的。 *)

Lemma CoEM_Forget_obj (x : @CoEilenbergMoore C W H) : CoEM_Forget x = `1 x.
Proof. reflexivity. Qed.

Lemma CoEM_Forget_fmap {x y : @CoEilenbergMoore C W H}
      (f : x ~{@CoEilenbergMoore C W H}~> y) :
  fmap[CoEM_Forget] f ≈ t_alg_hom[f].
Proof. reflexivity. Qed.

Lemma CoEM_Cofree_carrier (x : C) : `1 (CoEM_Cofree x) = W x.
Proof. reflexivity. Qed.

(** The costructure map of the cofree coalgebra on x is duplicate. / x 上余自由余代数的余代数结构图是重复的。 *)

Lemma CoEM_Cofree_coalg (x : C) :
  t_alg[`2 (CoEM_Cofree x)] ≈ @duplicate C W H x.
Proof. reflexivity. Qed.

Lemma CoEM_Cofree_fmap {x y : C} (f : x ~{C}~> y) :
  t_alg_hom[fmap[CoEM_Cofree] f] ≈ fmap[W] f.
Proof. reflexivity. Qed.

Definition CoEM_Adjunction : CoEM_Forget ⊣ CoEM_Cofree :=
  Opposite_Adjunction _ _ (@EM_Adjunction (C^op) (W^op) H).

(** The counit of the adjunction is the counit of the comonad. / 伴随的余单位是余单子的余单位。 *)

Lemma CoEM_counit_agrees {x : C} :
  @counit _ _ _ _ CoEM_Adjunction x ≈ @extract C W H x.
Proof.
  unfold counit; cbn.
  cat.
Qed.

(**
The unit at a coalgebra acts by its costructure map, stated on the
    underlying arrow of the coalgebra homomorphism.

--------
余代数中的单位通过其余结构映射作用，作用于余代数同态的基础箭头上。
*)

Lemma CoEM_unit_agrees {y : @CoEilenbergMoore C W H} :
  t_alg_hom[@unit _ _ _ _ CoEM_Adjunction y] ≈ t_alg[`2 y].
Proof.
  unfold unit; cbn.
  rewrite fmap_id.
  cat.
Qed.

(**
The comultiplication of the comonad induced by this adjunction is
    duplicate.

--------
由此伴随引起的余函子的余乘法是 duplicate。
*)

Lemma CoEM_duplicate_agrees {x : C} :
  fmap[CoEM_Forget] (@unit _ _ _ _ CoEM_Adjunction (CoEM_Cofree x))
    ≈ @duplicate C W H x.
Proof.
  cbn.
  rewrite fmap_id.
  cat.
Qed.

(**
The resolution recovers W: the composite Forget ◯ Cofree is naturally
    isomorphic to W, with identity components.

--------
该分解恢复了 W：复合 Forget ◯ Cofree 天然同构于 W，并且具有恒等分量。
*)

Theorem CoEM_Comonad_agrees : CoEM_Forget ◯ CoEM_Cofree ≈ W.
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.

End CoEilenbergMooreAdjunction.
