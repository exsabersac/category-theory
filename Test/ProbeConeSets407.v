Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Diagram.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Instance.Sets.Karoubi.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * Probe for issue #407: Mac Lane SV.1, completeness of Sets / * 针对问题 #407 的探查：Mac Lane SV.1，集合的完备性 *)

(*
The boundary of Instance/Sets/Complete.v's cone-set section and of
   Instance/Sets/Cone.v.  Nine refutation commands, plus one instrument
   check on a name that does not exist.  Each was stripped ONE AT A TIME,
   compiled alone, and its WHOLE error read; the classification below is by
   the error TEXT, not by expectation:

     FORMABILITY  the error ends in a universe clause
     CONVERSION   "cannot unify", no universe clause
     TYPING       a plain has-type mismatch, neither of the above
     RESOLUTION   "Cannot infer the implicit parameter ..."

   Count by kind: 7 CONVERSION, 1 TYPING, 1 RESOLUTION.

   RECORDED CORRECTION: an earlier revision counted eleven refutation
   commands, of which 2 FORMABILITY.  Both FORMABILITY refusals were the
   [Set] pin of the unannotated [DiscreteCat_Functor]; annotated in the PR
   "algebraic carriers are sets" (2026-09-17) both are accepted, and §(5)
   and (6) keeps them as positive controls.  No FORMABILITY refusal
   remains in this file.

   Every constant any refutation command names is also named OUTSIDE every
   such command, in a [Check] below, so that renaming it in its own library
   file breaks this file at a [Check] rather than turning a guard silently
   green.

   The [Require] list is the UNION of the two new library files' own, plus
   Category.Theory.Universal.Element, which this issue also extends and
   whose new constant is guarded below though no refutation names it.

   ONE TRAP, MEASURED AND WORKED AROUND.  Negative 2 must be a
   [Definition], not a [Check]: a bare [Check] of the same expression is
   ACCEPTED, printing an open evar for the missing [Setoid] instance, so a
   refutation command against it would be a FALSE PASS.

--------
Instance/Sets/Complete.v 的锥集合部分与 Instance/Sets/Cone.v 的边界。九个反驳命令，加上一个对不存在名称的工具检查。每个命令都被单独剥离，一次编译，并读取其整个错误；以下分类是根据错误文本，而不是根据预期：

可形成性  错误出现在一个宇宙子句中
转换  “无法统一”，没有宇宙子句
类型检查  类型不匹配的普通错误，以上都不是
解析  “无法推断隐式参数 ...”

按类型计数：7 转换，1 打字，1 解析。

已记录的更正：早期修订统计了十一条反驳指令，其中2条为FORMABILITY。两条FORMABILITY拒绝都是未标注的[DiscreteCat_Functor]的[Set]引脚；在PR“代数载体是集合”（2026-09-17）中都已被接受，§(5)和(6)保留它们作为阳性对照。此文件中不再存在FORMABILITY拒绝。

每个常量以及任何反驳命令的名称，也都会在每个此类命令之外被命名，在下面的 [Check] 中，因此在其自身的库文件中重命名它会在 [Check] 处破坏此文件，而不是悄悄地让保护变绿。

[Require] 列表是两个新库文件自身的联合，再加上 Category.Theory.Universal.Element，该元素此问题也扩展了，并且其新常量在下面被保护，尽管没有反驳名称引用它。

一个陷阱，已测量并绕过。负2必须是[Definition]，而不是[Check]：同一表达式的裸露[Check]是被接受的，会打印出缺失[Setoid]实例的开放evar，所以针对它的反驳命令将是错误通过。
*)

(** ** Guard block: every constant the refutations name, named outside them / ** Guard block: every constant the refutations name, named outside them / ** 防护块：每个反驳所命名的常量，在它们之外命名 *)

Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @Sets_limit_compatible.
Check @cone_apex.
Check @cone_leg_at.
Check @cone_set_IsALimit.
Check @cone_set_Limit.
Check @cone_set_med.
Check @ConeSet_Complete.
Check @discrete_limit.
Check @discrete_iprod_iso.
Check @Sets_iprod_proj.
Check @iprod_proj.
Check @DiscreteCat.
Check @DiscreteCat_Functor.
Check @IsALimit.
Check @Cone.
Check @ACone.
Check @cone_apex_iso.
Check @cone_transpose.
Check @cone_untranspose.
Check @ConeSet_Natural_Iso.
Check @ConeSet_Representable.
Check @ConeSet_HasLimitsOfShape.
Check @ConeSet_Diagonal_Limit_Adjunction.
Check @Sets_Diagonal_Limit_Adjunction.
Check @Sets_HasLimitsOfShape.
Check @Cone_Natural_Transform.
Check @adj.
Check @Isomorphism.
Check @sets_eq_obj.
Check @sets_eq_incl.
Check @sets_IsEqualizer.
Check @concrete_vs_existing.
Check @existing_IsEqualizer.
Check @Sets_HasEqualizers.
Check @APair.
Check @karoubi_IsEqualizer.
Check @sets_split_obj.
Check @tuple_obj.
Check @tuple_compat.
Check @tuple_iso.
Check @tuple_proj.
Check @FunctorOfDiagram.
Check @Diagram.
Check @Quiver.
Check @Srestr.
Check @pres_iso.
Check @PresentedQuiver.
Check @PathRel.
Check @global_elements_natural.
Check @SetoidObject.
Check @fst.
Check @snd.
Check @from.
Check @to.

(** ** Instrument check / ** 仪表检查 *)

(*
If a refutation command can pass on a name that does not exist, none of
   the ones below measures anything.  This one must pass.

--------
如果反驳命令可以传递一个不存在的名称，那么下面的任何一个都不能测量任何东西。这个必须传递。
*)
Fail Check @coneset_probe_instrument_absent.

(** ** (1) The two apexes are not equal -- CONVERSION / ** (1) 这两个顶点不相等——转换 *)

(*
One is a sigma of a dependent function with a compatibility witness, the
   other an [ACone] record.  Whole error tail:
     (cannot unify "Sets_limit_obj F" and "cone_apex F").

--------
一个是带有兼容性证明的依赖函数的 sigma，另一个是 [ACone] 记录。完整错误尾：
  （无法统一 "Sets_limit_obj F" 和 "cone_apex F"）。
*)
Fail Example neg_apex_strict {D : Category} (F : D ⟶ Sets) :
  Sets_limit_obj F = cone_apex F := eq_refl.

(** ** (2) There is no [≈] grade on objects -- RESOLUTION / ** (2) 对象上没有 [≈] 等级 -- 分辨率 *)

(*
Objects of [Sets] carry no setoid.  Whole error:
     The following term contains unresolved implicit arguments ...
     ?Setoid: Cannot infer the implicit parameter Setoid of equiv whose
     type is "Setoid SetoidObject" (no type class instance found).
   A [Check] here is ACCEPTED (open evar), so this is a [Definition].

--------
[Sets] 对象不携带集合等价关系。完整错误信息：
     以下项包含未解析的隐式参数...
     ?Setoid：无法推断 equiv 的隐式参数 Setoid，其类型为“Setoid SetoidObject”（未找到类型类实例）。
   此处的 [Check] 是 ACCEPTED（开放变量），因此这是一个 [Definition]。
*)
Fail Definition neg_apex_equiv {D : Category} (F : D ⟶ Sets) : Type :=
  (Sets_limit_obj F ≈ cone_apex F).

(** ** (3) The discrete leg equation is [≈], not [eq_refl] -- CONVERSION / ** (3) 离散腿方程是 [≈]，而不是 [eq_refl] -- 转换 *)

(*
[∘] in [Sets] rebuilds a [SetoidMorphism] record.  The [≈] form is
   [discrete_iprod_iso_leg], which holds.

--------
[∘] 在 [Sets] 中重建了一个 [SetoidMorphism] 记录。[≈] 表单是 [discrete_iprod_iso_leg]，它保持不变。
*)
Fail Example neg_discrete_leg {A : Set} (f : A → obj[Sets]) (a : A) :
  Sets_iprod_proj f a ∘ to (discrete_iprod_iso f)
  = iprod_proj f (discrete_limit f) a := eq_refl.

(** ** (4) Which limit oracle the adjunction is fed -- TYPING / ** (4) 附加所使用的极限预言机是哪一个 -- 类型 *)

(*
Fed the PRE-EXISTING [Sets_HasLimitsOfShape], the transposition does not
   land at the cone set, and not even at the same TYPE: a plain has-type
   mismatch, no "cannot unify" and no universe clause.  The accepted
   control below is the SAME statement at the cone-set oracle, which is
   what makes this negative discriminate between the two oracles rather
   than merely record that something failed.

--------
供给了先前存在的 [Sets_HasLimitsOfShape]，置换没有落在锥集上，甚至没有落在相同的类型上：只是普通的类型不匹配，没有“无法统一”也没有宇宙子句。下面接受的控制是在锥集预言机处的相同语句，这就是使得这个负例能够区分这两个预言机，而不仅仅是记录某个操作失败的原因。
*)
Fail Definition neg_wrong_oracle {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) :
  @Isomorphism Sets
     {| carrier := @hom ([J, Sets]) (Δ[J](X)) F |}
     {| carrier := X ~{Sets}~> cone_apex F |}
  := @adj _ _ _ _ (Sets_Diagonal_Limit_Adjunction J) X F.

Definition ctrl_right_oracle {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) :
  @Isomorphism Sets
     {| carrier := @hom ([J, Sets]) (Δ[J](X)) F |}
     {| carrier := X ~{Sets}~> cone_apex F |}
  := @adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F.

(**
** (5) and (6) The former [Set] pin of the discrete shape

    RECORDED CORRECTION.  An earlier revision headed this section "The
    [Set] pin of the discrete shape -- FORMABILITY" and stated two
    negatives.  Its text was:

      "Instance/Sets/Complete.v's discrete section is stated with
       [{A : Set}] and not [{A : Type}].  That is forced, and it takes TWO
       donors.  Both are pinned here, and [Cone] is the discriminating
       control: it is ACCEPTED at hom levels declared strictly above
       [Set], so the pin is not 'the cone vocabulary'."

    There was only ever ONE donor.  Donor 2, [IsALimit] identifying the
    shape's hom-and-proof universes with the ambient's, is a real
    identification but carries no [Set] of its own: it merely transmitted
    the one that donor 1, the unannotated [DiscreteCat_Functor], minimized
    into existence.  With that constant annotated in the PR "algebraic
    carriers are sets" (2026-09-17), Instance/Discrete.v, both lines
    are ACCEPTED and are kept below as positive controls at the same
    levels.  [Cone] remains the discriminating control it always was.

    WHAT STILL HOLDS: the [IsALimit] identification itself is unchanged,
    and Instance/Sets/Complete.v's discrete section keeps whatever reason
    it has for [{A : Set}] -- that is a claim about THAT file and is not
    measured here.

--------
** (5) 和 (6) 离散形状的前 [Set] 引脚

已记录更正。之前的修订将本节标题为“离散形状的 [Set] 引脚——可成型性”，并陈述了两个否定内容。其文本为：

“Instance/Sets/Complete.v 的离散部分是用 [{A : Set}] 而不是 [{A : Type}] 来声明的。这是被强制的，并且需要两个供体。两者都在此处被固定，而 [Cone] 是区分控制：它在严格高于 [Set] 声明的同源水平下被接受，所以固定点不是‘锥体词汇’。”

只有一个捐赠者。捐赠者 2，[IsALimit]，将形状的同态和证明宇宙与环境宇宙进行识别，这是一个真实的识别，但自身不携带任何 [Set]：它只是传输了捐赠者 1，即未批注的 [DiscreteCat_Functor]，所最小化生成的 [Set]。在 PR“代数载体是集合”（2026-09-17）中批注该常数后，Instance/Discrete.v 中的两行都被接受，并作为阳性对照保持在相同水平。[Cone] 仍然是它一直以来的判别对照。

仍然保持不变的是：[IsALimit] 的标识本身没有改变，Instance/Sets/Complete.v 的离散部分保留了它对 [{A : Set}] 的任何原因——那是对那个文件的声明，这里不进行衡量。
*)

Section SetPin.

Universes io co ch cp.
Constraint Set < ch.
Context (A : Type@{io}).
Context (C : Category@{co ch cp}).
Context (f : A → obj[C]).

(* Controls, all accepted at these very levels. / 控制，所有这些水平都被接受。 *)
Check (DiscreteCat@{io ch cp} A).
Check (DiscreteCat_Functor f).
Check (Cone (DiscreteCat_Functor f)).
Check (@ACone (DiscreteCat A) C).

(*
Former donor 1: [DiscreteCat_Functor] used to pin its own SOURCE at
   [DiscreteCat@{_ Set Set}], with the error tail
     (universe inconsistency: Cannot enforce Set = ch).
   Annotated, it reaches these levels.

--------
前捐赠者 1：[DiscreteCat_Functor] 曾经将其自身的 SOURCE 固定在 [DiscreteCat@{_ Set Set}]，带有错误尾部 (宇宙不一致：无法强制执行 Set = ch)。注释后，它达到这些级别。
*)
Check (DiscreteCat_Functor f : DiscreteCat@{io ch cp} A ⟶ C).

(*
Former donor 2: [IsALimit] identifies the shape's hom-and-proof
   universes with the ambient category's.  It still does; what it no
   longer transmits is a [Set].

--------
前捐赠者2：[IsALimit] 将形状的同类和证明宇宙与环境范畴的宇宙相对应。它仍然这样做；它不再传输的是 [Set]。
*)
Check (IsALimit (DiscreteCat_Functor f)).

End SetPin.

(** ** (7) The forward transposition is [≈], not [eq_refl] -- CONVERSION / ** (7) 正向移位是 [≈]，而不是 [eq_refl] -- 转换 *)

(*
NO CAUSE IS ISOLATED, and the obvious localization is refuted.  The
   [ACone] round trip of [Cone_Natural_Transform] does return the leg
   family on the nose (measured, accepted) while rebuilding the whole
   record, whose [cone_coherence] proof is [abstract]ed at
   Structure/Cone/Const.v -- but these two sides differ ALREADY at a
   point [x : X], and again at the produced cone's leg at [d], both
   measured, so the refusal is not confined to that law field.  The [≈]
   form is [coneset_adj_to_is_transpose], which holds.

--------
没有原因是孤立的，明显的局部化是被驳斥的。[ACone] 对 [Cone_Natural_Transform] 的往返确实返回了腿家族（测量过的，被接受），同时重建了整个记录，其 [cone_coherence] 证明在 Structure/Cone/Const.v 上被 [abstract] 了——但这两边已经在 [x : X] 点上不同，并且在生成的锥体的腿上在 [d] 点再次不同，两者都经过测量，因此拒绝并不限于该法律领域。[≈] 形式是 [coneset_adj_to_is_transpose]，其成立。
*)
Fail Example neg_adj_to_strict {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) (p : ACone X F) :
  to (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F)
     (snd (Cone_Natural_Transform F X) p)
  = cone_transpose F X p := eq_refl.

(** ** (8) ... and so is the backward one, at whole-record level / ** (8) … 反向的也是如此，在全记录级别上 *)

(*
Same donor, same cause.  What DOES hold on the nose is the LEG-BY-LEG
   form, [coneset_adj_from_is_untranspose]. -- CONVERSION

--------
相同的捐助者，相同的原因。真正准确的是逐腿形式，[coneset_adj_from_is_untranspose]。-- 转换
*)
Fail Example neg_adj_from_strict {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) (h : X ~{Sets}~> cone_apex F) :
  fst (Cone_Natural_Transform F X)
      (from (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F) h)
  = cone_untranspose F X h := eq_refl.

(** ** (9) Awodey's subset is not the existing apex -- CONVERSION / ** (9) Awodey 的子集不是现有的顶点 -- 转换 *)

(*
The existing [HasEqualizers Sets] apex is the compatible-family setoid
   over the walking parallel pair.  The bridge is [concrete_vs_existing],
   an isomorphism and nothing stronger.

--------
现有的 [HasEqualizers Sets] 顶点是关于步行平行对的兼容族集。桥是 [concrete_vs_existing]，是一个同构，并且没有更强的性质。
*)
Fail Example neg_awodey_strict {X Y : SetoidObject} (f g : X ~{Sets}~> Y) :
  sets_eq_obj f g = Sets_limit_obj (APair f g) := eq_refl.

(** ** (10) The tuple form is an isomorphism, not an equality -- CONVERSION / ** (10) 元组形式是一种同构，而不是相等 -- 转换 *)

(*
The two compatibility predicates quantify over paths and over generating
   edges respectively.  The bridge is [tuple_iso].

--------
这两个兼容性谓词分别对路径和生成边进行量化。桥接是 [tuple_iso]。
*)
Fail Example neg_tuple_strict {G : Quiver} (D : Diagram G Sets) :
  Sets_limit_obj (FunctorOfDiagram D) = tuple_obj D := eq_refl.

(** ** (11) Presentation-independence, at object level -- CONVERSION / ** (11) 表现独立性，在对象层面 -- 转换 *)

(*
The CARRIER is Leibniz-equal and so is the compatibility predicate --
   both are [Example]s in Instance/Sets/Cone.v -- so the obstruction is
   confined to the [is_setoid] field, whose [setoid_equiv] is
   [Sets_limit_obj_obligation_1] applied to two functors that [Compose]
   rebuilds.  The three accepted Examples beside this refusal are what
   locate it there.

--------
载体（CARRIER）是莱布尼茨相等的，兼容谓词也是如此——它们都是 Instance/Sets/Cone.v 中的 [Example]——所以障碍被限制在 [is_setoid] 字段，其 [setoid_equiv] 是 [Sets_limit_obj_obligation_1] 应用于两个由 [Compose] 重建的函子。这次拒绝之外的三个被接受的示例就是将其定位在那里。
*)
Fail Example neg_pres_strict (G : Quiver) (R : PathRel G)
  (S : PresentedQuiver G R ⟶ Sets) :
  Sets_limit_obj S = Sets_limit_obj (Srestr G R S) := eq_refl.

(** ** Controls for the three grades that DO hold / ** 适用于三个等级的控制 *)

Example ctrl_pres_carrier (G : Quiver) (R : PathRel G)
  (S : PresentedQuiver G R ⟶ Sets) :
  Sets_limit_carrier S = Sets_limit_carrier (Srestr G R S) := eq_refl.

Example ctrl_apex_is_conepresheaf {D : Category} (F : D ⟶ Sets) :
  carrier (cone_apex F)
  = @ACone D Sets (@terminal_obj Sets Sets_Terminal) F := eq_refl.

Example ctrl_iso_to_is_med {D : Category} (F : D ⟶ Sets) :
  to (cone_apex_iso F)
  = cone_set_med F (alimit_cone (limit_is_alimit (Sets_Limit F)))
  := eq_refl.
