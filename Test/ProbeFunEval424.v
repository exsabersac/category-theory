(**
* Probe for Instance/Fun/Eval.v and Instance/Fun/Eval/Cat.v (issue #424)

    Pins the measured boundaries of the evaluation functor on a functor
    category: the new [Eval] is Adjunction/Diagonal/Connected.v's [EvalAt]
    in both data fields but not as a record, and the partial application of
    the two-variable evaluation agrees with it on arrows up to [≈] only.  It
    also carries, as positive controls, the identifications with every
    evaluation-shaped functor already in the tree ([EvalAt], [YoEvalAt],
    [One_Eval], [Cat_Closed]'s own [eval]) and Awodey's [ev1] re-expressed
    through the general one.  Every refutation command below was stripped
    ONE AT A TIME in a copy of the whole file and compiled alone with its
    error read, so each refusal is of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [Eval p = EvalAt p] is refused at [eq_refl] ("cannot
                     unify Eval p and EvalAt p"): both are [Program
                     Definition]s whose law fields are separate opaque
                     constants (Lib.v makes obligations opaque).  Controls:
                     [fobj] and [fmap] convert at [eq_refl], under
                     [EvalAt]'s own universe annotation.
     N2 CONVERSION   [fmap[Eval p] s = fmap[Partial_l EvalBi p] s] is refused
                     at [eq_refl]: [Partial_l]'s arrow action is [bimap s
                     id], which still carries the [fmap id] the functor law
                     removes.  Controls: the object actions convert, and
                     [eval_partial_map] closes the arrow case at [≈], packaged
                     as [eval_partial_iso].
     N3 CONVERSION   the [Partial_r] twin: [fmap[Partial_r EvalBi H] f =
                     fmap[H] f] is refused at [eq_refl] for the same reason
                     ([bimap id f]); controls [eval_partial_r_obj] at
                     [eq_refl] and [eval_partial_r_map] at [≈].  Added after
                     the audit, which found the boundary measured but
                     unguarded.

    Positive controls, deliberately NOT written as refutations: the
    identifications with [YoEvalAt] and [One_Eval] (both fields each),
    [Cat_Closed]'s evaluation ([CatEval_map]) and the transpose
    ([eval_transpose]); [p424_prior_nat], the one-object instance of
    [Eval_nat] already in the tree (Functor/Representable/Functorial.v's
    [wit_ev_tau]), component for component at [eq_refl]; and
    [p424_ev1_via_Eval], Theory/Lawvere/Sets.v's [ev1] as [Eval (law_of_nat
    1) ◯ Incl], agreeing with [ev1] in both data fields at [eq_refl] (a
    twin: [ev1] itself is not re-expressed).  The universe COLLAPSE of
    routing through [Cat]'s exponential typechecks and so cannot be
    refuted; it is measured by [About] in the headers, not faked as a
    probe.  Note the parenthesised [(Eval p)] wherever the constant heads a
    term: bare [Eval p] at a definition-body head is read as the [Eval … in]
    vernacular.

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the three names the refuted
    declarations would introduce, the binder [s] and the instrument's
    absent name — so a renamed or removed constant breaks the build on a
    positive line rather than letting a refutation pass for the wrong
    reason.

--------
* 探查 Instance/Fun/Eval.v 和 Instance/Fun/Eval/Cat.v（问题 #424）

固定在函子范畴上的评估函子的测量边界：新的 [Eval] 是 Adjunction/Diagonal/Connected.v 的 [EvalAt]，在两个数据字段中都是如此，但不是作为记录，并且双变量评估的部分应用在箭头上仅与其在 [≈] 上一致。它还作为阳性对照，携带与树中已存在的每个评估形状函子（[EvalAt]、[YoEvalAt]、[One_Eval]、[Cat_Closed] 自身的 [eval]）以及通过通用函数重新表达的 Awodey 的 [ev1] 的识别。下面的每条反驳命令都是在整个文件的一份副本中逐条去掉并单独编译，其错误信息被读取，因此每个拒绝都是其标签所示的类型。

编号：
     工具      缺少名称，拒绝——反驳关键字在该文件中是 live。N1 转换   [Eval p = EvalAt p] 在 [eq_refl] 拒绝（"无法统一 Eval p 和 EvalAt p"）：两者都是 [程序定义]，其法则字段是独立的不透明常量（Lib.v 使义务不透明）。控制：
     [fobj] 和 [fmap] 在 [eq_refl] 处转换，在 [EvalAt] 自身的宇宙注释下。N2 转换   [fmap[Eval p] s = fmap[Partial_l EvalBi p] s] 在 [eq_refl] 处被拒绝：[Partial_l] 的箭头操作是 [bimap s id]，它仍然携带 [fmap id]，被函子定律移除。
控件：对象操作转换，并且 [eval_partial_map] 在 [≈] 关闭箭头箱，打包为 [eval_partial_iso]。N3 转换 [Partial_r] 双: [fmap[Partial_r EvalBi H] f = fmap[H] f] 在 [eq_refl] 被拒绝，原因相同 ([bimap id f])；控件 [eval_partial_r_obj] 在 [eq_refl] 和 [eval_partial_r_map] 在 [≈]。审计后添加，发现边界已测量但未受保护。

积极对照，故意未写为反驳：与 [YoEvalAt] 和 [One_Eval]（各字段）的识别，[Cat_Closed] 的评估（[CatEval_map]）以及转置（[eval_transpose]）；[p424_prior_nat]，树中已有的 [Eval_nat] 的单一对象实例（Functor/Representable/Functorial.v 的 [wit_ev_tau]），逐组件在 [eq_refl]；以及 [p424_ev1_via_Eval]，Theory/Lawvere/Sets.v 的 [ev1] 作为 [Eval (law_of_nat 1) ◯ Incl]，在 [eq_refl] 的两个数据字段上与 [ev1] 一致（一个双胞胎：[ev1] 本身未被重新表达）。通过 [Cat] 的指数类型检查的路由宇宙 COLLAPSE 因此无法被反驳；它通过头部的 [About] 测量，而非作为探针伪造。注意每当常量引导项时，括号内的 [(Eval p)]：定义主体头部的裸 [Eval p] 被读取为 [Eval … in] 的通俗语。

守卫覆盖：每一个被反驳命名的常量也在反驳命令之外被命名（位于末尾的守卫块）——例外情况是，在去掉注释的普通标识符标记下，包括关键字本身、被反驳声明会引入的三个名称、绑定器 [s] 以及仪器缺失的名称——因此，被重命名或删除的常量会在正向行上导致构建失败，而不是让反驳因错误原因通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Exponential.
Require Import Category.Instance.Fun.Eval.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Theory.Shapes.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Representable.Functorial.
Require Import Category.Adjunction.Diagonal.Connected.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Theory.Lawvere.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe424_absent_name.

(**
** A: the new evaluation IS Adjunction/Diagonal/Connected.v's [EvalAt]
       in both data fields, but not as a record

--------
** A：新的评估在两个数据字段中都是 Adjunction/Diagonal/Connected.v 的 [EvalAt]，但不是作为记录
*)

Section EvalAtAgreement.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}} (p : P).

(* controls: the two data fields convert / 控件：两个数据字段转换 *)
Example p424_EvalAt_obj : fobj[Eval p] = fobj[@EvalAt P X p] := eq_refl.

Example p424_EvalAt_map (H K : [P, X]) :
  @fmap _ _ (Eval p) H K = @fmap _ _ (@EvalAt P X p) H K := eq_refl.

(*
N1 CONVERSION: the whole records do not — both are [Program
   Definition]s whose law fields are separate opaque constants

--------
N1 转换：整个记录不——两者都是 [程序定义]，其法律字段是独立的不透明常量
*)
Fail Example p424_EvalAt_record : Eval p = @EvalAt P X p := eq_refl.

End EvalAtAgreement.

(** ** B: partial application agrees on arrows up to ≈ only / ** B：部分应用仅在 ≈ 上一致箭头 *)

Section PartialAgreement.

Context {P X : Category} (p : P) (H K : [P, X]).

(* control: on objects, on the nose / 控制：对象上，鼻子上 *)
Example p424_partial_obj : fobj[Eval p] H = fobj[Partial_l EvalBi p] H := eq_refl.

(*
N2 CONVERSION: on arrows the partial's action is [bimap s id], carrying
   the [fmap id] the functor law removes

--------
N2 转换：在箭头上，偏函数的作用是 [bimap s id]，携带 [fmap id] 时函子定律会去除
*)
Fail Example p424_partial_map (s : H ~{[P, X]}~> K) :
  @fmap _ _ (Eval p) H K s = @fmap _ _ (Partial_l EvalBi p) H K s := eq_refl.

(* control: it closes at ≈, and is packaged as an isomorphism / 控制：它在 ≈ 处关闭，并以同构的形式打包 *)
Check (eval_partial_map p H K).
Check (eval_partial_iso p).

(*
N3 CONVERSION: the same on the other partial — [Partial_r]'s action is
   [bimap id f], again carrying an [fmap id]

--------
N3 转换：在另一个部分上也是一样 —— [Partial_r] 的动作是 [bimap id f]，再次携带一个 [fmap id]
*)
Fail Example p424_partial_r_map (q : P) (f : p ~> q) :
  @fmap _ _ (Partial_r EvalBi H) p q f = @fmap _ _ H p q f := eq_refl.

(* controls: on objects on the nose, on arrows at ≈ / 控件：在鼻子上的物体上，在≈处的箭头上 *)
Example p424_partial_r_obj : fobj[Partial_r EvalBi H] p = fobj[H] p := eq_refl.
Check (fun (q : P) (f : p ~> q) => eval_partial_r_map H p q f).

End PartialAgreement.

(** ** C: the same data as the tree's other evaluation functors / ** C: 与树的其他评估函数相同的数据 *)

(* at [X := Sets]: Functor/Hom/Yoneda/Natural.v's [YoEvalAt] / 在 [X := Sets]: Functor/Hom/Yoneda/Natural.v 的 [YoEvalAt] *)
Example p424_YoEvalAt_obj {C : Category} (c : C) :
  fobj[@Eval C Sets c] = fobj[@YoEvalAt C c] := eq_refl.

Example p424_YoEvalAt_map {C : Category} (c : C) (F G : [C, Sets]) :
  @fmap _ _ (@Eval C Sets c) F G = @fmap _ _ (@YoEvalAt C c) F G := eq_refl.

(* at [P := _1]: Theory/Shapes.v's [One_Eval], both fields / 在 [P := _1]: Theory/Shapes.v 的 [One_Eval]，两者字段 *)
Example p424_One_Eval_obj {X : Category} :
  fobj[@Eval _1 X ttt] = fobj[@One_Eval X] := eq_refl.

Example p424_One_Eval_map {X : Category} (F G : [_1, X]) :
  @fmap _ _ (@Eval _1 X ttt) F G = @fmap _ _ (@One_Eval X) F G := eq_refl.

(*
the one-object instance of [Eval_nat] already in the tree:
   Functor/Representable/Functorial.v's [wit_ev_tau] over the delooping of
   (ℕ, +) and [Sets], the same component (its [BNat] notation is
   section-local there)

--------
已经在树中的 [Eval_nat] 的单对象实例：
   Functor/Representable/Functorial.v 中的 [wit_ev_tau]，关于 (ℕ, +) 的去环化以及 [Sets]，相同的组件（它的 [BNat] 符号在那里是节局部的）
*)
Local Notation BNat := (Deloop Nat_Plus).

Example p424_prior_nat (n : nat) (F : [BNat, Sets]) :
  transform[wit_ev_tau n] F = transform[@Eval_nat BNat Sets ttt ttt n] F
  := eq_refl.

(* [Cat_Closed]'s own evaluation, named in Instance/Fun/Eval/Cat.v / [Cat_Closed] 自己的评估，命名在 Instance/Fun/Eval/Cat.v 中 *)
Check (@CatEval_map).
Check (@eval_transpose).

(**
** D: the Awodey increment — Theory/Lawvere/Sets.v's [ev1] through the
       general evaluation

--------
** D：Awodey 增量——Theory/Lawvere/Sets.v 的 [ev1] 通过一般评估
*)

Section Ev1.

Context (T : LawvereTheory).

(*
[Models T Sets] is the full subcategory of [[law_cat T, Sets]] cut out
   by [Models_sub]; [ev1] is evaluation at the generator after the
   inclusion.

--------
[Models T Sets] 是 [[law_cat T, Sets] 的完整子类别，由 [Models_sub] 切出；[ev1] 是包含后的生成元上的评价。
*)
Definition p424_ev1_via_Eval : Models T Sets ⟶ Sets :=
  @Eval (@law_cat T) Sets (law_of_nat 1%nat)
    ◯ @Incl (@Fun (@law_cat T) Sets) (Models_sub T Sets).

Example p424_ev1_obj (M : Models T Sets) :
  fobj[ev1 T] M = fobj[p424_ev1_via_Eval] M := eq_refl.

Example p424_ev1_map (M N : Models T Sets) :
  @fmap _ _ (ev1 T) M N = @fmap _ _ p424_ev1_via_Eval M N := eq_refl.

End Ev1.

(** ** E: readbacks / ** E：复读 *)

Check (@EvalFunctor_obj).
Check (@EvalFunctor_map).
Check (@eval_partial_r_obj).
Check (@eval_partial_r_map).

(** ** Guard block / ** 防守格挡 *)

Check @Eval.
Check @EvalBi.
Check @Eval_nat.
Check @EvalFunctor.
Check @eval_partial_obj.
Check @eval_partial_map.
Check @eval_partial_iso.
Check @CatEval.
Check @CatEval_obj.
Check @eval_is_CatEval_partial_obj.
Check @eval_is_CatEval_partial_map.
Check @EvalAt.
Check @Partial_l.
Check @Partial_r.
Check @bimap.
Check @fmap.
Check @fobj.
