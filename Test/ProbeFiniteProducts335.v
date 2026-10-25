(**
* Boundary probe for Structure/Limit/Product/Finite.v (issue #335)

    Structure/Limit/Product/Finite.v measures ten refutations -- seven
    CONVERSION failures and three FORMABILITY (universe) rejections -- and
    ships no [Fail] of its own.  THIS FILE IS WHERE THEY ARE PINNED, so
    that a later edit which quietly makes one of them SUCCEED breaks the
    build instead of silently invalidating the target's header.  (An
    earlier draft of this paragraph said the ten were "checked in scratch
    files outside the tree" and that the target "pins none of them".  That
    described the state BEFORE this file existed, and both files ship in
    one commit; the target's header names this probe.)

    TWO KINDS, kept lexically apart:

      * CONVERSION (negatives 1-7) -- [Fail Definition … := eq_refl].
        The fold pads with the terminal object and the round trip through
        [HasFiniteProducts] does not return its inputs on the nose.

      * FORMABILITY (negatives 8-10) -- [Fail Check] under a declared
        [Constraint uh < up].  Each of [Cartesian], [Terminal] and
        [IsIndexedProduct] independently identifies the hom and proof
        universes; NO ONE of them is "the" cause, which is why all three
        are pinned rather than one.

    Every negative was stripped of its [Fail] once and its failure KIND
    confirmed -- "cannot unify" for 1-7, "universe inconsistency" for
    8-10.  The instrument check below guarantees [Fail] is live.  The
    import list is the target's own; a shortened one would let these pass
    vacuously.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others.

--------
* 用于 Structure/Limit/Product/Finite.v 的边界探测（问题 #335）

Structure/Limit/Product/Finite.v 测量了十个反驳——七个转换失败和三个可形成性（宇宙）拒绝——并且自身不包含任何 [Fail]。这个文件是它们被固定的地方，因此稍后的编辑如果悄悄让其中一个成功，会导致构建失败，而不是悄悄地使目标的头文件无效。（这一段的早期草稿说十个反驳“在树外的临时文件中检查”，并且目标“没有固定它们中的任何一个”。那描述的是这个文件存在之前的状态，而这两个文件在一次提交中一起发布；目标的头文件命名了这个探测。）

两种类型，词汇上分开：

* 转换（负数 1-7）-- [Fail Definition … := eq_refl]。
        将折叠垫与终端对象配合使用，通过 [HasFiniteProducts] 的来回操作不会精确返回其输入。

* 成形性（负面 8-10）——在声明的 [Constraint uh < up] 下的 [Fail Check]。[Cartesian]、[Terminal] 和 [IsIndexedProduct] 每一个都独立地标识了 hom 和 proof 宇宙；没有任何一个是“原因”，这就是为什么三个都被固定而不是只固定其中一个。

每个否定都被剥离了它的 [Fail]，一旦完成，其失败类型 KIND 就被确认 —— 对 1-7 是“无法统一”，对 8-10 是“宇宙不一致”。下面的仪器检查保证 [Fail] 是活跃的。导入列表是目标自身的；一个缩短的列表会让这些默认为通过。测得的重命名模拟分数在最后，针对的是 NEGATIVES 名称的常量，而不是其他名称。
*)

Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Product.Finite.

Generalizable All Variables.

(** ** Instrument check: [Fail] is live in this file / ** 仪器检查：[Fail] 在此文件中处于活动状态 *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

Section Conversions.

Context {C : Category}.
Context (CP : @Cartesian C) (T : @Terminal C).
Context (x y z : C) (f1 : Fin.t 1 → C) (f2 : Fin.t 2 → C).

(** ** Negative 1 (CONVERSION): the unary fold keeps its terminal pad / ** 负一（转换）：一元折叠保持其终端填充 *)

Fail Definition probe_fin_prod_one :
  @fin_prod C CP T 1 f1 = f1 Fin.F1 := eq_refl.

(** ** Negative 2 (CONVERSION): the binary fold keeps its terminal pad / ** 负2（转换）：二进制折叠保持其终端垫 *)

Fail Definition probe_fin_prod_two :
  @fin_prod C CP T 2 f2 = (f2 Fin.F1 × f2 (Fin.FS Fin.F1))%object := eq_refl.

(** ** Negative 3 (CONVERSION): out to the class and back pads the product / ** 负 3（转换）：向外到班级再回来会增加产品 *)

Fail Definition probe_roundtrip_product_obj :
  @product_obj C (HasFiniteProducts_Cartesian
                    (Cartesian_Terminal_HasFiniteProducts CP T)) x y
  = (x × y)%object := eq_refl.

(** ** Negative 4 (CONVERSION): the recovered [Cartesian] is not the input / ** 负 4（转换）：恢复的 [Cartesian] 不是输入 *)

Fail Definition probe_roundtrip_cartesian :
  HasFiniteProducts_Cartesian (Cartesian_Terminal_HasFiniteProducts CP T)
  = CP := eq_refl.

(** ** Negative 5 (CONVERSION): the recovered [Terminal] is not the input / ** 负 5（转换）：恢复的 [Terminal] 不是输入 *)

Fail Definition probe_roundtrip_terminal :
  HasFiniteProducts_Terminal (Cartesian_Terminal_HasFiniteProducts CP T)
  = T := eq_refl.

(**
** Negative 6 (CONVERSION): the whole round trip is not the identity

    Negative 3 propagated, not an independent fact -- the target's header
    says so, and it is pinned separately because a repair to 3 need not
    repair this one.

--------
** 负6（转换）：整个往返不是恒等式

负3 已传播，并非独立事实——目标的标题是这样说的，并且它是单独固定的，因为修复3不需要修复这个。
*)

Fail Definition probe_roundtrip_whole :
  Cartesian_Terminal_HasFiniteProducts
    (HasFiniteProducts_Cartesian
       (Cartesian_Terminal_HasFiniteProducts CP T))
    (HasFiniteProducts_Terminal
       (Cartesian_Terminal_HasFiniteProducts CP T))
  = Cartesian_Terminal_HasFiniteProducts CP T := eq_refl.

(**
** Negative 7 (CONVERSION): right fold and left fold differ

    This is why [awodey_fold_iso] is an isomorphism and nothing stronger.

--------
** 负 7（转换）：右折与左折不同

    这就是为什么 [awodey_fold_iso] 是同构而没有更强的性质。
*)

Fail Definition probe_right_vs_left_fold :
  @fin_prod C CP T 3 (fin3 x y z) = awodey_prod CP x y z := eq_refl.

End Conversions.

(**
** Controls for the conversion negatives

    Each names constants the negatives above name.

--------
** 转换负数的控件

每个名称都是上面负数名称的常量。
*)

Check @fin_prod.
Check @fin_proj.
Check @fin3.
Check @awodey_prod.
Check @awodey_fold_iso.
Check @HasFiniteProducts.
Check @HasFiniteProducts_Cartesian.
Check @HasFiniteProducts_Terminal.
Check @Cartesian_Terminal_HasFiniteProducts.
Check @product_obj.

(**
** Positive identifications, pinned beside their refutations

    The target's header measured these outside the tree.  They are the
    POSITIVE counterparts of negatives 3-5, and pinning both halves is
    what makes the boundary exact -- in particular the [Terminal] RECORD
    is not recovered (negative 5) while the terminal OBJECT is (below).

--------
** 正面识别，附在其反驳旁边

目标的头部在树外进行了测量。它们是负面3-5的正面对应物，而将两半部分固定在一起正是使边界精确的原因——特别是[Terminal]记录未恢复（负面5），而终端对象则恢复了（如下）。
*)

Section Positives.

Context {C : Category}.
Context (CP : @Cartesian C) (T : @Terminal C).
Context (x y : C) (n : nat) (f : Fin.t n → C).

Example probe_class_returns_the_fold :
  @finite_product C (Cartesian_Terminal_HasFiniteProducts CP T) n f
  = @fin_prod C CP T n f := eq_refl.

Example probe_class_returns_the_projections :
  @finite_product_proj C (Cartesian_Terminal_HasFiniteProducts CP T) n f
  = @fin_proj C CP T n f := eq_refl.

Example probe_terminal_obj_is_recovered :
  @terminal_obj C
    (HasFiniteProducts_Terminal (Cartesian_Terminal_HasFiniteProducts CP T))
  = @terminal_obj C T := eq_refl.

Example probe_padded_product_is_what_it_is :
  @product_obj C (HasFiniteProducts_Cartesian
                    (Cartesian_Terminal_HasFiniteProducts CP T)) x y
  = (x × (y × 1))%object := eq_refl.

End Positives.

(**
** Negatives 8-10 (FORMABILITY, universe)

    A DIFFERENT KIND from 1-7.  With C's hom universe declared strictly
    below its proof universe, all three donors are rejected -- so the
    hom-and-proof identification the target inherits has three
    independent sources and cannot be attributed to any single one.

--------
** 负数 8-10（可形成性，宇宙）

    与 1-7 不同的一类。在 C 的同构宇宙被严格声明在其证明宇宙之下的情况下，所有三个捐赠者都被拒绝——因此目标继承的同构与证明的识别具有三个独立来源，不能归因于任何单一来源。
*)

Section UniverseIdentification.

Universe uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).

(*
Control: naming a hom at these levels IS formable, so the rejections
   below are about the three donors and not about C itself.

--------
控制：在这些级别上命名一个 hom 是可形成的，因此下面的拒绝是关于三个供体的，而不是关于 C 本身的。
*)
Check (fun x y : C => x ~{C}~> y).

Fail Check (@Cartesian C).
Fail Check (@Terminal C).
(*
The category argument is given EXPLICITLY.  Written with [C] left
   implicit, this [Fail] fired on an unresolved evar ("expected to have
   type A → obj[?C]") rather than on the universe identification -- a
   FALSE GUARD, caught by stripping the [Fail] and reading the error
   KIND rather than merely observing that it failed.

--------
类别参数是明确给出的。用 [C] 写成隐式时，这个 [Fail] 在未解析的 evar（“预期为类型 A → obj[?C]”）上触发，而不是在宇宙识别上触发——一个 FALSE GUARD，通过去掉 [Fail] 并读取错误类型而不是仅仅观察其失败而捕获。
*)
Fail Check (fun (A : Type) (f : A → C) (p : C)
                (pr : ∀ a, p ~{C}~> f a) =>
              @IsIndexedProduct C A f p pr).

End UniverseIdentification.

(** ** Controls naming the three donors / ** 控制命名三位捐赠者 *)

Check @Cartesian.
Check @Terminal.
Check @IsIndexedProduct.

(** ** Controls for the delivered results / ** 已交付结果的控制 *)

Check @fin_IsIndexedProduct.
Check @Cartesian_Terminal_HasFiniteProducts.
Check @HasFiniteProducts_iff.
Check @iprod_unique_iso.
Check @fin_prod_unique_iso.
Check @awodey_IsIndexedProduct.
Check @fin_zero_IsTerminalObj.
Check @fin_two_IsCartesianProduct.
Check @fin_coprod.
Check @HasFiniteCoproducts.
(*
NOTE: written WITHOUT the [@].  Structure/Cocartesian.v declares
   [Notation "@Cocartesian C"], which captures [@Cocartesian_Initial_...]
   and fails with "The reference _Initial_HasFiniteCoproducts was not
   found".  The bare name parses; measured both ways.

--------
注意：文档中没有写入 [@]。Structure/Cocartesian.v 声明了 [Notation "@Cocartesian C"]，它捕获了 [@Cocartesian_Initial_...] 并出现错误“未找到引用 _Initial_HasFiniteCoproducts”。裸名称可以解析；两种方式均已测量。
*)
Check Cocartesian_Initial_HasFiniteCoproducts.

(**
** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negatives 1-2:  [fin_prod]
      Negative  3:    [product_obj], [HasFiniteProducts_Cartesian],
                      [Cartesian_Terminal_HasFiniteProducts]
      Negatives 4-6:  [HasFiniteProducts_Terminal] (with the above)
      Negative  7:    [fin3], [awodey_prod]
      Negatives 8-10: [Cartesian], [Terminal], [IsIndexedProduct]

    That is TEN.  The denominator is not padded with control-only names:
    [fin_proj], [awodey_fold_iso], [HasFiniteProducts] and every constant
    under "Controls for the delivered results" appear in NO [Fail] here
    and are deliberately EXCLUDED from the score.

--------
** 测量重命名模拟得分

    NEGATIVES 常量的命名：

      Negatives 1-2:  [fin_prod]
      Negative  3:    [product_obj], [HasFiniteProducts_Cartesian],
                      [Cartesian_Terminal_HasFiniteProducts]
      Negatives 4-6:  [HasFiniteProducts_Terminal]（与上述一起）
      Negative  7:    [fin3], [awodey_prod]
      Negatives 8-10: [Cartesian], [Terminal], [IsIndexedProduct]

    总共有十个。分母未添加仅控制名称：
    [fin_proj], [awodey_fold_iso], [HasFiniteProducts] 以及“交付结果的控制”下的每个常量
    在此处的 [Fail] 中都不存在，并且故意从得分中排除。
*)
