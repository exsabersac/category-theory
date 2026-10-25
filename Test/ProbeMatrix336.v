(**
* Boundary probe for Structure/Bicartesian/Matrix.v (issue #336)

    The target MEASURES three boundaries and ships no [Fail] of its own.
    THIS FILE IS WHERE THEY ARE PINNED, so that a later edit which quietly
    makes one of them SUCCEED breaks the build instead of silently
    invalidating the target's header.

    TWO KINDS, kept lexically apart:

      * CONVERSION (negatives 1-2) -- [Fail Definition … := eq_refl].
        The Kronecker delta does not reduce to [id] on the diagonal even
        at closed indices, and the n-ary comparison is not convertible
        with the hand-written binary one.

      * FORMABILITY (negative 3) -- [Fail Check] under a declared
        [Constraint uh < up].  The target's [mat_entry] carries EXPLICIT
        universe binders; written WITHOUT them the same body elaborates
        at [Category@{uo uh uh}] and is then rejected at that setting.
        The annotation is therefore load-bearing, and the identification
        it removes was universe MINIMIZATION rather than content.

    Each negative was stripped of its [Fail] once and its failure KIND
    confirmed by reading the error TAIL, not by observing that it failed.
    The import list is the target's own; a shortened one would let these
    pass vacuously.  The measured rename-simulation score is at the end,
    over the constants the NEGATIVES name and no others.

--------
* Structure/Bicartesian/Matrix.v 的边界探测（问题 #336）

目标测量三个边界，并且没有自己的 [Fail]。
这个文件就是它们被固定的位置，这样以后对其中一个的悄悄编辑
如果使其成功，就会破坏构建，而不是默默地
使目标的头文件无效。

两种类型，词汇上分开：

* 转换（负数 1-2）-- [Fail Definition … := eq_refl]。
        克罗内克δ即使在封闭索引上，对角线上也不会化简为 [id]，
        并且 n 元比较无法与手写的二元比较互相转换。

* 可成形性（负3）——[Fail Check] 在声明的 [Constraint uh < up] 下。目标的 [mat_entry] 携带明确的宇宙绑定器；如果没有它们写入，相同的主体将在 [Category@{uo uh uh}] 展开，然后在该设置下被拒绝。因此，该注释是承重的，它移除的识别是宇宙最小化，而不是内容。

每个负样本的一次 [Fail] 被去除，并通过读取错误 TAIL 而不是通过观察它失败来确认其失败 KIND。导入列表是目标本身的；缩短的列表会让这些样本虚假地通过。测量的重命名模拟得分在末尾，是基于 NEGATIVES 名称的常量，而不是其他名称。
*)

Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Bicartesian.Matrix.

Generalizable All Variables.

(** ** Instrument check: [Fail] is live in this file / ** 仪器检查：[Fail] 在此文件中处于活动状态 *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** Negative 1 (CONVERSION): the Kronecker delta is not [id] on the
       diagonal, even at two closed indices

    The target locates the cause precisely: the BRANCH SELECTION does
    reduce -- which is why its [kron_off_computes] succeeds off the
    diagonal -- but the equality proof [Fin.eq_dec] returns is not
    [eq_refl], so the [eq_rect] transport in the diagonal branch is
    stuck.  That is a property of the DECIDER, not of [kron].

--------
** 负 1（转换）：克罗内克δ在对角线上不是[id]，即使在两个封闭的指标上也是如此

目标精确定位了原因：分支选择确实会减少——这就是为什么它在对角线外的[kron_off_computes]成功——但是等式证明[Fin.eq_dec]返回的不是[eq_refl]，因此在对角线分支中的[eq_rect]传输被卡住。这是判定器（DECIDER）的属性，而不是[kron]的属性。
*)

Section KroneckerDiagonal.

Context {C : Category} (Z : @ZeroObject C) (fam : Fin.t 2 → C).

Fail Definition probe_kron_diag_computes :
  @kron C Z (Fin.t 2) fam Fin.eq_dec Fin.F1 Fin.F1 = id := eq_refl.

End KroneckerDiagonal.

(**
** Negative 2 (CONVERSION): the n-ary comparison is not the binary one

    They ARE equal at [≈] -- that is the target's
    [binary_can_is_can_comparison] -- but not convertible: [binary_can]
    is a cotuple of tuples produced by two descent data, while
    [can_comparison] is the hand-written [(id △ zero_mor) ▽ (zero_mor △ id)].

--------
** 负 2（转换）：n 元比较不是二元比较

它们在 [≈] 时是相等的——那是目标的 [binary_can_is_can_comparison]——但不可转换：[binary_can] 是由两个下降数据生成的 tuple 的 cotuple，而 [can_comparison] 是手写的 [(id △ zero_mor) ▽ (zero_mor △ id)]。
*)

Section BinaryComparison.

Context {C : Category} (Z : @ZeroObject C).
Context (CP : @Cartesian C) (CC : @Cocartesian C).
Context (x y : C).

Fail Definition probe_binary_can_is_can_comparison :
  @binary_can C Z CP CC x y = can_comparison x y := eq_refl.

End BinaryComparison.

(** ** Controls for the conversion negatives / ** 冲洗反片的控制 *)

Check @kron.
Check @kron_diag.
Check @kron_off.
Check @binary_can.
Check @can_comparison.
Check @binary_can_is_can_comparison.
Check @Fin.eq_dec.

(**
** Negative 3 (FORMABILITY, universe): the explicit binders on
       [mat_entry] are load-bearing

    A DIFFERENT KIND from 1-2.  [mat_entry] as SHIPPED is annotated
    [@{uo uh up uj uk}] with constraint block [uh <= up], keeping the
    category's hom and proof universes APART.  Written WITHOUT binders
    the same body minimizes to [Category@{uo uh uh}], and is then
    rejected where the annotated form is accepted.

--------
** 负 3（可形成性，宇宙）：[mat_entry] 上的显式绑定器是承重的

与 1-2 不同。出厂的 [mat_entry] 被标注为 [@{uo uh up uj uk}]，带有约束块 [uh <= up]，保持类别的同态和证明宇宙分离。未使用绑定器书写时，同样的主体最小化为 [Category@{uo uh uh}]，然后在标注形式被接受的情况下被拒绝。
*)

Section UniverseMinimization.

Universe uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).

(*
Controls: the ambient vocabulary IS formable at these levels, so the
   rejection below is about the unannotated definition and not about C.

--------
控制：在这些级别上环境词汇是可以形成的，因此下面的拒绝是关于未标注的定义，而不是关于 C 的。
*)
Check (fun x y : C => x ~{C}~> y).
Check (fun (x y z : C) (f : x ~{C}~> y) (g : y ~{C}~> z) => g ∘ f).

(* Control: the SHIPPED, annotated [mat_entry] is formable here. / 控制：此处可以形成已发运、带注释的 [mat_entry]。 *)
Check (fun (J K : Type) (g : J → C) (fm : K → C)
           (q p : C) (inj : ∀ j, g j ~{C}~> q)
           (proj : ∀ k, p ~{C}~> fm k) (u : q ~{C}~> p) (j : J) (k : K) =>
         @mat_entry C J K g fm q p inj proj u j k).

(*
The negative: the same body with the binders dropped.  Written as an
   unannotated local definition, elaboration minimizes its category to
   [Category@{uo uh uh}] and it cannot be applied to C.

--------
负面：相同的主体与绑定器被移除。作为未注释的本地定义书写，展开将其类别最小化为 [Category@{uo uh uh}]，并且它不能应用于 C。
*)
Definition mat_entry_unannotated {D : Category}
  {J K : Type} {g : J → D} {fm : K → D} {q p : D}
  (inj : ∀ j, g j ~{D}~> q) (proj : ∀ k, p ~{D}~> fm k)
  (u : q ~{D}~> p) (j : J) (k : K) : g j ~{D}~> fm k :=
  proj k ∘ u ∘ inj j.

Fail Check (fun (J K : Type) (g : J → C) (fm : K → C)
                (q p : C) (inj : ∀ j, g j ~{C}~> q)
                (proj : ∀ k, p ~{C}~> fm k) (u : q ~{C}~> p) (j : J) (k : K) =>
              @mat_entry_unannotated C J K g fm q p inj proj u j k).

End UniverseMinimization.

(** ** Controls naming the constants of negative 3 / ** 控制命名负3的常量 *)

Check @mat_entry.
Check @mat_entry_unfold.

(** ** Controls for the delivered results / ** 已交付结果的控制 *)

Check @matrix_ext.
Check @matrix_determined.
Check @matrix_mor.
Check @matrix_entry.
Check @matrix_ump.
Check @matrix_mor_entry.
Check @can_matrix.
Check @can_matrix_diag.
Check @can_matrix_off.
Check @can_matrix_unique.
Check @can_matrix_ump.
Check @indexed_inj_Section.
Check @indexed_inj_SplitMono.
Check @indexed_inj_Monic.
Check @inl_Section.
Check @inr_Section.
Check @inl_Monic.
Check @inr_Monic.
Check @fin_matrix.
Check @fin_matrix_entry.
Check @fin_matrix_ext.

(**
** Exercise 3.1.ix, witnessed at a concrete category

    Structure/Bicartesian/Matrix.v proves the injection results as
    CONDITIONALS on a zero object plus coproducts, and instantiates them
    at no concrete category -- its own witness category [Coq] has no zero
    object.  The tree has six registered [ZeroObject] instances, and [Ab]
    supplies both hypotheses as exported instances, so the witness is pure
    instantiation with no new proof.

    It is shipped HERE rather than in the target for a measured reason:
    [Instance/Ab] is not in that file's dependency closure (0 of 19
    modules) while Instance/Ab/Coproduct.v's own closure is 17, so
    importing it there would nearly double a [Structure/] file's footprint
    for two [Example]s.  A probe is a leaf and pays no such cost.

    Identified by the fess audit of this commit, which compiled it
    independently before it was added here.

--------
** 练习 3.1.ix，在一个具体范畴中见证

Structure/Bicartesian/Matrix.v 证明了作为零对象加上余积的条件语句的注入结果，并在没有具体范畴的情况下实例化它们——它自己的见证范畴 [Coq] 没有零对象。该树有六个已注册的 [ZeroObject] 实例，而 [Ab] 作为导出实例提供了两个假设，因此该见证是纯粹的实例化，没有新的证明。

它是运送到这里而不是目标位置，有一个经过衡量的原因：
[Instance/Ab] 不在该文件的依赖闭包中（19 个模块中为 0），而 Instance/Ab/Coproduct.v 自身的闭包是 17，因此在那儿导入它几乎会使一个 [Structure/] 文件的占用增加一倍，而这是为了两个 [Example]。探针是叶子节点，不会产生这样的成本。

通过对该提交的 fess 审计识别，它在添加到这里之前已独立编译。
*)

Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.

Example ab_inl_Section (x y : Ab) : Section (@inl Ab Ab_Cocartesian x y) :=
  inl_Section x y.

Example ab_inl_Monic (x y : Ab) : Monic (@inl Ab Ab_Cocartesian x y) :=
  inl_Monic x y.

Example ab_inr_Monic (x y : Ab) : Monic (@inr Ab Ab_Cocartesian x y) :=
  inr_Monic x y.

(**
** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [kron]
      Negative 2: [binary_can], [can_comparison]
      Negative 3: [mat_entry_unannotated] (declared HERE, so a rename of
                  it is not a tree edit and is excluded), with [mat_entry]
                  named by its own positive control

    That is THREE renameable tree constants: [kron], [binary_can],
    [can_comparison].  The denominator is NOT padded with control-only
    names -- [kron_diag], [kron_off], [mat_entry], [mat_entry_unfold] and
    everything under "Controls for the delivered results" appear in no
    [Fail] here and are deliberately EXCLUDED.

    [Fin.eq_dec] is excluded on a DIFFERENT ground, and an earlier draft
    of this paragraph gave a false one: it listed [Fin.eq_dec] among the
    names appearing in no [Fail], but negative 1 names it.  The real
    ground is that it is a STDLIB constant, not a renameable constant of
    this tree, so renaming it is not an edit this simulation is meant to
    catch; it has its own [Check] control above regardless.  Excluding it
    therefore UNDERSTATES the score rather than padding it.

--------
** 测量的重命名模拟分数

NEGATIVES 命名的常数：

负面1：[kron]
      负面2：[binary_can], [can_comparison]
      负面3：[mat_entry_unannotated]（在此处声明，因此对它的重命名不是树编辑且被排除），以及通过其自身正向控制命名的[mat_entry]

那是三个可重命名的树常量：[kron]、[binary_can]、[can_comparison]。分母没有填充仅用于控制的名称——[kron_diag]、[kron_off]、[mat_entry]、[mat_entry_unfold]，以及“交付结果的控制”下的所有内容在此没有出现 [Fail]，并且是刻意排除的。

[Fin.eq_dec] 是基于不同的理由被排除的，而本段的早期草稿给出了一个错误的理由：它将 [Fin.eq_dec] 列在没有出现于 [Fail] 的名称中，但 negative 1 却命名了它。真正的理由是它是一个 STDLIB 常量，而不是此树的可重命名常量，因此重命名它不是该模拟旨在捕捉的编辑；无论如何，它在上方有自己的 [Check] 控制。因此，排除它会低估分数，而不是增加分数。
*)
