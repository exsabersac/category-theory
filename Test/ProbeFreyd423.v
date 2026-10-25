(**
* Probe for Structure/Complete/Freyd.v (issue #423)

    Pins the measured boundaries of Freyd's collapse: a [Complete] instance
    reaches an indexed product WITHOUT a [Set] pin only through the
    annotated discrete-diagram donor, the op-dual of an [ArrowIndex] needs
    the explicit constructor, the smallness hypothesis is not vacuous, and
    the constructive wall is an INJECTION no refutation can pin.  Every
    refutation command below was stripped ONE AT A TIME in a copy of the
    whole file and compiled alone with its error read, so each refusal is
    of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 UNIVERSE     under [Constraint Set < uh], feeding a [Complete]
                     instance to Structure/Limit/Product.v's
                     [limit_is_indexed_product] through the UNANNOTATED
                     [DiscreteCat_Functor] is refused with "Cannot enforce
                     Set = uh": that donor is stated at
                     [C : Category@{_ Set Set}].  Freyd.v's [complete_iprod]
                     at the same category is the control (it runs through
                     Structure/Limit/Comparison.v's [DiscreteCat_Functor']).
     N2 TYPING       the anonymous record literal for the dual elaborates
                     its binders at [obj[C]] and is refused against
                     [ArrowIndex (C^op)] ("has type ArrowIndex C while it
                     is expected to have type ArrowIndex C^op");
                     [ArrowIndex_op] with [@Build_ArrowIndex (C^op)] is the
                     control, and it is an involution at [eq_refl]
                     ([p423_op_round]).

    Positive controls, deliberately NOT written as refutations:
     - [canonical_ArrowIndex]: every category with decidable object
       equality carries an [ArrowIndex], so the hypothesis is not disguised
       thinness or finiteness.
     - [fr_inj_injective]: from [f ≉ g] alone an injection [(K → bool) → K]
       on the nose.  That this injection cannot be refuted without deciding
       the hom-setoid is METATHEORETIC (Hyland's effective-topos model,
       Structure/Complete.v); unprovability is not a refusal, so no
       refutation command is written for it.
     - [p423_small_and_products]: Theory/Size.v's [Small] and products over
       the category's own total arrow collection coexist in one binder.
       This is a coexistence check, not a refutation of a wall: [Small]'s
       extra levels are fresh and bounded only below by C's, so the binder
       adds no refutable constraint; what it witnesses is that
       [indexed_product] applies at [TotalMor C] beside [Small].  The one
       universe obstruction measured is the [Set] pin of N1.

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the binder names and keywords of
    the record literal ([_], [fun], [d], [h], [m], [x], [y]), the notation
    token [op] of [C^op], the name the refuted declaration would introduce
    and the instrument's absent name — so a renamed or removed constant
    breaks the build on a positive line rather than letting a refutation
    pass for the wrong reason.

--------
* 探测结构/完成/Freyd.v（问题 #423）

钉住弗雷德崩溃的测量边界：一个 [Complete] 实例只能通过带注释的离散图捐赠者到达没有 [Set] 钉子的索引产品，[ArrowIndex] 的对偶操作需要显式构造函数，小性假设不是空的，并且构造墙是一个没有任何反驳可以钉住的 INJECTION。下面的每个反驳命令都在整个文件的副本中被一次一次地移除，并单独编译以读取其错误，因此每个拒绝都是其标签所示的类型。

编号：
     工具   一个缺失的名称，被拒绝 —— 驳回关键字存在于此文件中。N1 UNIVERSE     在 [Constraint Set < uh] 下，将一个 [Complete] 实例提供给 Structure/Limit/Product.v 的
     [limit_is_indexed_product] 通过 UNANNOTATED [DiscreteCat_Functor] 被拒绝，并显示“Cannot enforce Set = uh”：该捐赠者注明于 [C : Category@{_ Set Set}]。Freyd.v 在相同类别的 [complete_iprod] 是控制（它通过 Structure/Limit/Comparison.v 的 [DiscreteCat_Functor'] 运行）。N2 打字       双重匿名记录字面量在 [obj[C] 处展开其绑定器，但在 [ArrowIndex (C^op)] 处被拒绝（“类型为 ArrowIndex C，而预期类型为 ArrowIndex C^op”）；[ArrowIndex_op] 与 [@Build_ArrowIndex (C^op)] 是控制，并且在 [eq_refl]（[p423_op_round]）处是自反的。

正向控制，故意不写成反驳：
     - [canonical_ArrowIndex]：每个具有可判定对象相等的范畴都携带一个 [ArrowIndex]，因此假设并未伪装为稀薄性或有限性。- [fr_inj_injective]：仅凭 [f ≉ g] 就可以直接得到一个注入 [(K → bool) → K]。这个注入无法在不决定同态集合的情况下被反驳，这是元理论的（Hyland 的有效拓扑模，Structure/Complete.v）；不可证性不是拒绝，所以没有为其写反驳命令。- [p423_small_and_products]：Theory/Size.v 中的 [Small] 和该类别自身总箭头集合之外的产品共存于同一个文档夹中。这是共存检查，而不是对墙的反驳：[Small] 的额外层是新的，并且仅在下方受限于 C，因此文档夹不会增加可反驳的约束；它所见证的是 [indexed_product] 在 [TotalMor C] 旁边的 [Small] 上的应用。测量的唯一宇宙障碍是 N1 的 [Set] 引脚。

守卫覆盖：每一个常量引用名称在反驳命令之外（末尾的守卫块）也被命名——在去除注释后的普通标识符标记下的例外包括关键字本身、绑定器名称以及记录字面量的关键字（[_]、[fun]、[d]、[h]、[m]、[x]、[y]）、[C^op] 的符号标记 [op]、被反驳声明将引入的名称以及仪器的缺失名称——因此，重命名或删除常量会在正行上破坏构建，而不是让反驳因错误原因通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Structure.Complete.Freyd.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe423_absent_name.

(** ** A: the [Set] pin of the unannotated discrete-diagram donor / ** A：未注释离散图中供体的 [Set] 引脚 *)

Section SetPin.

Universe uo uh.
Constraint Set < uh.

Context {C : Category@{uo uh uh}} (comp : @Complete C) (fam : TotalMor C → C).

(*
Former N1, now a positive control.

   RECORDED CORRECTION.  An earlier revision read: "N1 UNIVERSE: through
   Structure/Limit/Product.v's unannotated [DiscreteCat_Functor], a
   [Complete] instance yields an indexed product only at a category whose
   hom level IS [Set]."  The attribution to [DiscreteCat_Functor] was
   right; in the PR "algebraic carriers are sets" (2026-09-17) that donor
   was annotated in place (Instance/Discrete.v) and the command is
   ACCEPTED.  It is kept at the same levels as a positive control, so
   dropping the annotation refuses it again and breaks this file.  What
   the section now records is that the direct [limit_is_indexed_product]
   route and Freyd.v's [complete_iprod] route -- which reached the same
   place through [DiscreteCat_Functor'] and was written precisely to
   avoid the pin -- agree in what they can express.

--------
前 N1，现在是一个正向控制。

已记录更正。早期的修订版本写道：“N1 宇宙：通过 Structure/Limit/Product.v 中未注释的 [DiscreteCat_Functor]，[Complete] 实例仅在其同类层为 [Set] 的类别上生成索引产品。”归功于 [DiscreteCat_Functor] 是正确的；在 PR “代数承载器是集合”（2026-09-17）中，该捐赠者已在（Instance/Discrete.v）中原位注释，并且该命令已被接受。它保留在与正向控制相同的层级，因此删除注释会再次拒绝它，并导致此文件损坏。现在本节记录的是直接 [limit_is_indexed_product] 路径和 Freyd.v 的 [complete_iprod] 路径——通过 [DiscreteCat_Functor'] 到达相同位置，并被精确编写以避免该针——在它们可以表达的内容上是一致的。
*)
Check (@limit_is_indexed_product C (TotalMor C) fam
         (comp _ (@DiscreteCat_Functor (TotalMor C) C fam))).

(* control: the annotated route of Freyd.v at the same category / 控制：Freyd.v 在相同范畴下的注释路径 *)
Check (complete_iprod comp fam).
Check (complete_iprod_obj comp fam).

End SetPin.

(** ** B: the dual's record literal / ** B：二重的记录字面值 *)

Section OpLiteral.

Context {C : Category} (AI : ArrowIndex C).

(*
N2 TYPING: the anonymous record literal elaborates its binders at
   [obj[C]] and is refused against [ArrowIndex (C^op)]

--------
N2 打字：匿名记录字面值在 [obj[C] 处展开其绑定器，并且在 [ArrowIndex (C^op)] 处被拒绝
*)
Fail Definition p423_op_literal : ArrowIndex (C^op) :=
  {| ai_index   := ai_index AI
   ; ai_enc     := fun x y h => ai_enc AI h
   ; ai_dec     := fun x y m d => ai_dec AI m d
   ; ai_dec_enc := fun x y h d => ai_dec_enc AI h d |}.

(* control: the explicit constructor at [C^op] / 控制：[C^op] 的显式构造函数 *)
Check (ArrowIndex_op AI).

(* readback: the dual is an involution at [eq_refl] / 回读：[eq_refl] 的对偶是一个自反映射 *)
Example p423_op_round : ArrowIndex_op (ArrowIndex_op AI) = AI := eq_refl.

End OpLiteral.

(**
** C: positive controls — the hypothesis is not vacuous, and the
       constructive wall is an injection

--------
** C: 阳性对照——假设不是空洞的，而且构造墙是一个注入
*)

(* every category with decidable object equality carries an [ArrowIndex] / 每个具有可判定对象相等性的范畴都具有 [ArrowIndex] *)
Check (@canonical_ArrowIndex).

(* from [f ≉ g] alone: an injection [(K → bool) → K] on the nose / 仅来自 [f ≉ g]：在鼻子上注射 [(K → bool) → K] *)
Check (@fr_inj_injective).

(*
Theory/Size.v's [Small] and products over the category's own arrows
   coexist: no universe wall

--------
Theory/Size.v 的 [Small] 及该范畴自身箭头的积共存：没有宇宙墙
*)
Definition p423_small_and_products {C : Category} `{@Small C}
  (HP : HasIndexedProducts C) (fam : TotalMor C → C) : C :=
  indexed_product fam.

(** ** D: the headline statements / ** D：主要声明 *)

Check (@freyd_no_separated_pair).
Check (@freyd_thin).
Check (@small_complete_is_thin).
Check (@small_cocomplete_is_thin).
Check (@complete_has_glbs).
Check (@complete_Proset_Complete).

(** ** Guard block / ** 防守格挡 *)

Check @ArrowIndex.
Check @ai_index.
Check @ai_enc.
Check @ai_dec.
Check @ai_dec_enc.
Check @ArrowIndex_op.
Check @ObjDecEq.
Check @canonical_ArrowIndex.
Check @DecHom.
Check @DecHom_op.
Check @freyd_thin_canonical.
Check @freyd_thin_dual.
Check @fr_inj.
Check @complete_iprod.
Check @complete_iprod_obj.
Check @complete_iprod_proj.
Check @limit_is_indexed_product.
Check @DiscreteCat_Functor.
Check @DiscreteCat_Functor'.
Check @Complete.
Check @TotalMor.
Check @Small.
Check @HasIndexedProducts.
Check @indexed_product.
