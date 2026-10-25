Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sieve.
Require Import Category.Theory.Subobject.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Structure.Topos.Colimits.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Pushout.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Sets.Topos.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Classifier.
Require Import Category.Instance.Fun.Topos.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Adjunction.GAFT.Sets.

Open Scope category_scope.

(**
* Probe for issue #404: Sets and presheaf categories as toposes

    Guards Instance/Fun/Topos.v and Instance/Sets/Topos.v.  Its Require
    list is the UNION of theirs plus Structure/Topos/{Power,Monadic,
    Colimits}.v, Monad/Comparison.v, Structure/SubobjectClassifier/
    Natural.v, Theory/Subobject.v, the four shape modules
    (One, Two, Ordinal, Parallel, Roof), the three further Sets colimit
    modules and Adjunction/GAFT/Sets.v.  Those extras live here, and not
    in the library files, because Structure/Topos/{Monadic,Colimits}.v
    alone take the presheaf file's closure from 108 to 133 and the
    setoid file's from 74 to 101.

    NINETEEN refutation commands: ONE instrument check plus EIGHTEEN
    negatives, of FOUR kinds, told apart by the error TEXT and not by
    label.

      FORMABILITY  the error ends in a universe clause
                   ("universe inconsistency: Cannot enforce ...").
      CONVERSION   "cannot unify" between two terms of one type.
      TYPING       a plain has-type mismatch, no "cannot unify" and no
                   universe clause.
      RESOLUTION   "Cannot infer this placeholder ... (no type class
                   instance found)".

    Count by kind: 11 FORMABILITY (negatives 1-7 and 10-13), 4 CONVERSION
    (14-17), 2 TYPING (9 and 18), 1 RESOLUTION (8).

    Every negative was stripped from its Fail ONE AT A TIME, compiled
    alone in a scratch file mirroring this Require list, and its WHOLE
    error read before being classified.  Every constant a negative names
    is also Checked outside every Fail, in the guard block at the end.

--------
* 探讨问题 #404：集合与预层范畴作为拓扑学

保护实例/Fun/Topos.v 和 实例/Sets/Topos.v。它的 Require 列表是它们的并集，加上 Structure/Topos/{Power,Monadic, Colimits}.v, Monad/Comparison.v, Structure/SubobjectClassifier/Natural.v, Theory/Subobject.v, 四个形状模块（One, Two, Ordinal, Parallel, Roof）、三个额外的 Sets 上极限模块和 Adjunction/GAFT/Sets.v。这些额外的内容在这里，而不在库文件中，因为仅 Structure/Topos/{Monadic,Colimits}.v 就将 presheaf 文件的闭包从 108 扩展到 133，将 setoid 文件的闭包从 74 扩展到 101。

十九条反驳命令：一个仪器检查加上十八条否定，其中有四种类型，通过错误文本区分，而不是通过标签。

可形成性 错误终止于一个宇宙子句（"宇宙不一致：无法强制 ..."）。
转换 在一个类型的两个项之间出现"无法统一"。
类型检查 普通的类型不匹配，没有"无法统一"也没有宇宙子句。
解析 "无法推断此占位符 ...（未找到类型类实例）"。

按类别计数：11 可成形性（负面 1-7 和 10-13），4 转换（14-17），2 打字（9 和 18），1 分辨率（8）。

每一个负面都从其失败中一次只移除一个，单独编译在一个与此需求列表相对应的临时文件中，并在分类之前阅读其整个错误。每个负面所命名的常量也会在每个失败之外检查，在末尾的保护块中进行。
*)

(* ==================================================================== *)
(** ** Instrument: a Fail that passes because the name is absent / ** 工具：因为名称缺失而通过的失败 *)

Fail Check p404_instrument_absent.

(* ==================================================================== *)
(** ** (A) Presheaf negatives / ** (A) 预层负数 *)

Section PshNegatives.

Context (C : Category) (UT : Untruncate).

(*
NEGATIVE 1 (FORMABILITY).  The classification theorem is not statable
   at this topos: it carries objects <= homs, while the presheaf
   category's objects sit strictly above its homs.  Stripped:

     The term "topos_terminal" has type "Terminal@{n1.41 n1.23}"
     while it is expected to have type "Terminal@{n1.26 n1.27}"
     (universe inconsistency: Cannot enforce n1.23 = n1.27 because
      n1.23 < n1.31 <= n1.26 <= n1.27).

--------
NEGATIVE 1（可构造性）。在这个拓扑中分类定理无法表述：它携带对象 <= 同态，而预层范畴的对象严格位于其同态之上。简化后：

“topos_terminal” 的类型是 “Terminal@{n1.41 n1.23}”，但期望的类型是 “Terminal@{n1.26 n1.27}”（宇宙不一致：无法强制 n1.23 = n1.27，因为 n1.23 < n1.31 <= n1.26 <= n1.27）。
*)
Fail Check (@classifier_classifies ([C^op, Sets])
              (@topos_terminal _ (Presheaf_Topos C UT))
              (@topos_pullbacks _ (Presheaf_Topos C UT))
              (@topos_classifier _ (Presheaf_Topos C UT))).

(*
NEGATIVE 2 (FORMABILITY).  [relations_iso] is built as
   [iso_compose exp_iso (classifier_classifies (a × b))] and inherits
   the refusal.  Stripped:

     The term "Presheaf_Topos C UT" has type
      "ElementaryTopos@{n2.41 n2.41 n2.23} ([C^op, Sets@{n2.23 n2.41}])"
     while it is expected to have type
      "ElementaryTopos@{n2.26 n2.27 n2.27} ([C^op, Sets@{n2.23 n2.30}])"
     (universe inconsistency: Cannot enforce n2.23 = n2.27 because
      n2.23 < n2.30 <= n2.27).

--------
NEGATIVE 2（可形成性）。[relations_iso] 构建为 [iso_compose exp_iso (classifier_classifies (a × b))] 并继承了拒绝。剥离后：

术语 “Presheaf_Topos C UT” 的类型为
“ElementaryTopos@{n2.41 n2.41 n2.23} ([C^op, Sets@{n2.23 n2.41}])”
而期望的类型为
“ElementaryTopos@{n2.26 n2.27 n2.27} ([C^op, Sets@{n2.23 n2.30}])”
（宇宙不一致：无法强制 n2.23 = n2.27 因为 n2.23 < n2.30 <= n2.27）。
*)
Fail Check (@relations_iso ([C^op, Sets]) (Presheaf_Topos C UT)).

(*
NEGATIVE 3 (FORMABILITY).  The naturality upgrade likewise.
   Stripped:

     The term "topos_terminal" has type "Terminal@{n3.41 n3.23}"
     while it is expected to have type "Terminal@{n3.26 n3.27}"
     (universe inconsistency: Cannot enforce n3.23 = n3.27 because
      n3.23 < n3.31 <= n3.26 <= n3.27).

--------
负面 3（可构性）。自然性升级同样如此。
   精简版：

     术语“topos_terminal”的类型是“Terminal@{n3.41 n3.23}”，
     而期望的类型是“Terminal@{n3.26 n3.27}”
     （宇宙不一致：无法强制 n3.23 = n3.27，因为
      n3.23 < n3.31 <= n3.26 <= n3.27）。
*)
Fail Check (@Sub_classifier_natural ([C^op, Sets])
              (@topos_terminal _ (Presheaf_Topos C UT))
              (@topos_pullbacks _ (Presheaf_Topos C UT))
              (@topos_classifier _ (Presheaf_Topos C UT))).

(*
NEGATIVE 9 (TYPING).  The restriction readback must ascribe its arrow
   into [C^op]; written through the [morphism] coercion instead, the
   coercion is left an evar [?s] and [eq_refl] does not close.  No
   "cannot unify", no universe clause.  The ACCEPTED spelling is the
   control immediately below.  Stripped:

     The term "eq_refl" has type
      "?s (fmap[Sieve_Presheaf C] h) S = ?s (fmap[Sieve_Presheaf C] h) S"
     while it is expected to have type
      "?s (fmap[Sieve_Presheaf C] h) S = sieve_restrict h S".

--------
消极 9（打字）。限制回读必须将其箭头归属到 [C^op]；相反，写入通过 [morphism] 强制转换，该强制转换被保留为一个 evar [?s]，且 [eq_refl] 并未关闭。没有“无法统一”，没有宇宙子句。被接受的拼写如下所示。简化版：

术语“eq_refl”的类型为
  "?s (fmap[Sieve_Presheaf C] h) S = ?s (fmap[Sieve_Presheaf C] h) S"
而它预期的类型为
  "?s (fmap[Sieve_Presheaf C] h) S = sieve_restrict h S"。
*)
Fail Example p404_restrict (c d : C) (h : d ~{C}~> c) (S : Sieve c) :
  morphism (fmap[Sieve_Presheaf C] h) S = sieve_restrict h S := eq_refl.

Example p404_restrict_ctrl (c d : C) (h : d ~{C}~> c) (S : Sieve c) :
  fmap[@Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))]
      (h : c ~{C^op}~> d) S
  = sieve_restrict h S := eq_refl.

End PshNegatives.

(*
NEGATIVE 5 (FORMABILITY).  [_2] is declared with hom AND proof at the
   literal [Set], and [Fun_Classifier] carries the strict lower bound
   [Set < u].  The DISCRIMINATING CONTROL is the line above it:
   [Functor_Category_Closed _2] IS accepted, so the exclusion is the
   CLASSIFIER's and not the exponential's.  Stripped:

     The term "_2" has type "Category@{n5.32 Set Set}"
     while it is expected to have type "Category@{n5.29 n5.30 n5.30}"
     (universe inconsistency: Cannot enforce Set = n5.30 because
      Set < n5.30).

--------
负 5（可形成性）。[_2] 在字面 [Set] 被声明为 hom 和 proof，而 [Fun_Classifier] 带有严格下界 [Set < u]。区分控制是其上方的行：[Functor_Category_Closed _2] 被接受，因此排除的是分类器而不是指数。简化如下：

_2 的类型为 "Category@{n5.32 Set Set}"，而期望类型为 "Category@{n5.29 n5.30 n5.30}"（宇宙不一致：无法强制 Set = n5.30，因为 Set < n5.30）。
*)
Check (Functor_Category_Closed _2).
Fail Definition p404_two (UT : Untruncate) := Presheaf_Topos _2 UT.

(*
NEGATIVE 8 (RESOLUTION).  The bundle does not resolve: [ElementaryTopos]
   has no registered instance and its constructor is not one.  Stripped:

     The following term contains unresolved implicit arguments:
       (fun (C : Category) (UT : Untruncate) => ?e)
     More precisely:
     - ?e: Cannot infer this placeholder of type
       "ElementaryTopos ([C^op, Sets])" (no type class instance found)
       in environment: C : Category, UT : Untruncate

--------
否定 8（解析）。该捆绑包无法解析：[ElementaryTopos] 没有注册的实例，其构造函数也不是实例。剥离后：

以下术语包含未解析的隐式参数：
  (fun (C : Category) (UT : Untruncate) => ?e)
具体来说：
- ?e：无法推导此占位符的类型
  "ElementaryTopos ([C^op, Sets])"（未找到类型类实例）
  环境中：C : Category, UT : Untruncate
*)
Fail Definition p404_resolve (C : Category) (UT : Untruncate) :
  ElementaryTopos ([C^op, Sets]) := _.

(* -------------------------------------------------------------------- *)
(** ** (B) The two donors of the smallness bound [objects <= homs] / ** (B) 小界限 [objects <= homs] 的两个捐赠者 *)

(*
A section declaring C's OBJECTS STRICTLY ABOVE its homs.  The
   terminal, cartesian and pullback donors are all ACCEPTED there; the
   exponential and the classifier are each refused ALONE.

--------
一个部分声明 C 的 OBJECTS 严格在其 homs 之上。终端、笛卡尔积和拉回捐赠者都在此被接受；指数和分类器各自单独被拒绝。
*)

Section DonorClosed.
Universes co ch cso.
Constraint ch < co.
Constraint Set < ch.
Constraint ch < cso.
Context (Cq : Category@{co ch ch}) (UTq : Untruncate@{ch}).

Check (@Functor_Category_Terminal (Cq^op) Sets@{ch cso} Sets_Terminal).
Check (@Functor_Category_Cartesian (Cq^op) Sets@{ch cso} Sets_Cartesian).
Check (@Fun_HasPullbacks (Cq^op) Sets@{ch cso} Sets_HasPullbacks).

(*
NEGATIVE 6 (FORMABILITY).  Stripped:

     The term "Cq" has type "Category@{co ch ch}"
     while it is expected to have type "Category@{n6.55 n6.56 n6.56}"
     (universe inconsistency: Cannot enforce ch = n6.56 because
      ch < co <= n6.56).

--------
负 6（可形成性）。剥离：

     术语“Cq”的类型是“Category@{co ch ch}”，
     而它预期的类型是“Category@{n6.55 n6.56 n6.56}”
     （宇宙不一致：无法强制 ch = n6.56 因为
      ch < co <= n6.56）。
*)
Fail Check (Functor_Category_Closed Cq).

(*
NEGATIVE 7 (FORMABILITY), with no exponential in the command at all,
   so the two donors are measured independently.  Stripped:

     The term "Cq" has type "Category@{co ch ch}"
     while it is expected to have type "Category@{n7.37 n7.35 n7.35}"
     (universe inconsistency: Cannot enforce ch = n7.35 because
      ch < co <= n7.35).

--------
负7（可形成性），在命令中完全没有指数，因此两个供体是独立测量的。简化后：

术语“Cq”的类型为“Category@{co ch ch}”，而它预期的类型是“Category@{n7.37 n7.35 n7.35}”（宇宙不一致：无法强制 ch = n7.35，因为 ch < co <= n7.35）。
*)
Fail Check (@Fun_Classifier Cq UTq).

End DonorClosed.

(* -------------------------------------------------------------------- *)
(** ** (C) The small reading is blocked, and at the CLOSED field / ** (C) 小读数被阻塞，且处于关闭字段 *)

Section SmallReading.
Universes co o so OO HH.
Constraint Set < o.
Constraint o < so.
Constraint so <= OO.
Constraint OO <= HH.
Context (Cs : Category@{co o o}) (UTs : Untruncate@{o}).

(* the four fields that DO fit the lifted reading / 适合提升阅读的四个领域 *)
Check (PShSmall_Terminal Cs : @Terminal (PShSmall Cs)).
Check (@Functor_Category_Cartesian (Cs^op) Sets@{o so} Sets_Cartesian
       : @Cartesian (PShSmall Cs)).
Check (Fun_HasPullbacks Sets_HasPullbacks : @HasPullbacks (PShSmall Cs)).
Check (Fun_Classifier_small Cs UTs
       : @SubobjectClassifier (PShSmall Cs) (PShSmall_Terminal Cs)).

(*
NEGATIVE 4 (FORMABILITY).  The fifth does not.  Stripped:

     The term "Functor_Category_Closed Cs" has type
      "@Closed ([Cs^op, Sets])
         (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)"
     while it is expected to have type
      "@Closed (PShSmall Cs)
         (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)"
     (universe inconsistency: Cannot enforce o = n4.97 because
      o < so <= n4.96 <= n4.97).

--------
负 4（可构造性）。第五条不是。剥离后：

“Functor_Category_Closed Cs” 的类型是
“@Closed ([Cs^op, Sets])
   (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)”
而它期望的类型是
“@Closed (PShSmall Cs)
   (Functor_Category_Cartesian Cs^op Sets Sets_Cartesian)” 
（宇宙不一致：无法强制 o = n4.97 因为 o < so <= n4.96 <= n4.97）。
*)
Fail Check (Functor_Category_Closed Cs
            : @Closed (PShSmall Cs)
                (@Functor_Category_Cartesian (Cs^op) Sets@{o so}
                   Sets_Cartesian)).

End SmallReading.

(* ==================================================================== *)
(** ** (D) Setoid negatives / ** (D) 设点否定 *)

(*
The [Set]-reach split.  In a section declaring [Set < su], the four
   unconditional donors and the DECIDABLE route all reach the [Sets]
   whose carrier universe is the literal [Set]; the truncation route
   does not.

--------
[Set] 分裂。在声明 [Set < su] 的部分中，四个无条件捐助者和 DECIDABLE 路线都到达 [Sets]，其载体宇宙是文字 [Set]；截断路线则不到达。
*)

Section SetReach.
Universe su.
Constraint Set < su.

Check Sets@{Set su}.
Check Sets_Terminal@{su Set}.
Check Sets_Cartesian@{su Set}.
Check Sets_HasPullbacks@{su Set}.
Check Sets_Closed@{su Set}.
Check Sets_Classifier_dec@{Set su}.
Check Sets_Topos_dec@{Set su}.

(*
NEGATIVE 10 (FORMABILITY).  Stripped:

     Universe inconsistency. Cannot enforce Set < Set because Set = Set.

--------
负10（可成型性）。删除：

     宇宙不一致。无法执行 Set < Set，因为 Set = Set。
*)
Fail Check Sets_Topos@{Set su}.

(*
NEGATIVE 11 (FORMABILITY), the same refusal one layer in, at the
   classifier the bundle carries.  Stripped:

     Universe inconsistency. Cannot enforce Set < Set because Set = Set.

--------
负 11（可成型性），同样的拒绝在一层内，在分类器上捆绑携带。剥离：

宇宙不一致。无法强制执行 Set < Set 因为 Set = Set。
*)
Fail Check Sets_Classifier@{Set su}.

End SetReach.

Section SetsNegatives.

Context (U : Untruncate) (a b : obj[Sets]).

(*
[Pow] DOES reach this topos: the accepted control for negatives 12
   and 13.

--------
[Pow] 确实达到了这个拓扑：对于负数 12 和 13 的公认控制。
*)
Check (@Pow Sets (Sets_Topos U) b).

(*
NEGATIVE 12 (FORMABILITY).  [classifier_classifies] carries
   objects <= homs and [Sets@{o so} : Category@{so o o}] has o < so.
   Stripped:

     The term "Sets" has type "Category@{n12.34 n12.33 n12.33}"
     while it is expected to have type "Category@{n12.30 n12.31 n12.31}"
     (universe inconsistency: Cannot enforce n12.34 = n12.30 because
      n12.30 <= n12.31 < n12.34).

--------
负面 12（可构造性）。[classifier_classifies] 携带对象 <= homs，[Sets@{o so} : Category@{so o o}] 拥有 o < so。
剥离后：

术语“Sets”的类型为“Category@{n12.34 n12.33 n12.33}”，而预期类型为“Category@{n12.30 n12.31 n12.31}”（宇宙不一致：无法强制 n12.34 = n12.30，因为 n12.30 <= n12.31 < n12.34）。
*)
Fail Check (@classifier_classifies Sets Sets_Terminal Sets_HasPullbacks
              (Sets_Classifier U)).

(*
NEGATIVE 13 (FORMABILITY).  So one of Structure/Topos.v's own two
   derived constants is not statable at this genuine topos.  Stripped:

     The term "Sets" has type "Category@{n13.43 n13.42 n13.42}"
     while it is expected to have type "Category@{n13.41 n13.41 n13.41}"
     (universe inconsistency: Cannot enforce n13.43 = n13.41 because
      n13.41 < n13.43).

--------
负面 13（可形成性）。因此，Structure/Topos.v 自身的两个派生常量之一在这个真正的拓扑中无法表述。简化如下：

术语“Sets”的类型为“Category@{n13.43 n13.42 n13.42}”，而期望的类型为“Category@{n13.41 n13.41 n13.41}”（宇宙不一致：无法强制 n13.43 = n13.41，因为 n13.41 < n13.43）。
*)
Fail Check (@relations_iso Sets (Sets_Topos U) a b).

End SetsNegatives.

(*
The four strict forms of Mac Lane's App.1 clause (b), each refused.
   The apex is a SIGMA carrying the agreement witness, so it is not the
   product carrier and its first projection is not [exl].

--------
Mac Lane 的附录 1 条款 (b) 的四种严格形式，每一种都被拒绝。
   顶点是携带协议证据的 SIGMA，因此它不是产物载体，而且它的第一个投影不是 [exl]。
*)

(*
NEGATIVE 14 (CONVERSION).  Stripped:

     The term "eq_refl" has type "pbone a b = pbone a b"
     while it is expected to have type "pbone a b = a × b"
     (cannot unify "pbone a b" and "a × b").

--------
负 14（转换）。剥离：

     术语 "eq_refl" 的类型为 "pbone a b = pbone a b"
     而它期望的类型为 "pbone a b = a × b"
     （无法统一 "pbone a b" 与 "a × b"）。
*)
Fail Example p404_pbone_prod (a b : obj[Sets]) : pbone a b = a × b := eq_refl.

(*
NEGATIVE 15 (CONVERSION), one layer in, at the CARRIERS.  Stripped:

     The term "eq_refl" has type "pbone a b = pbone a b"
     while it is expected to have type "pbone a b = a × b"
     (cannot unify "carrier (pbone a b)" and "carrier (a × b)").

--------
负 15（转换），在载体处，一层内。拆解：

     术语 “eq_refl”的类型是 “pbone a b = pbone a b”
     而期望的类型是 “pbone a b = a × b”
     （无法统一 “carrier (pbone a b)” 和 “carrier (a × b)”）。
*)
Fail Example p404_pbone_carrier (a b : obj[Sets]) :
  carrier (pbone a b) = carrier (a × b) := eq_refl.

(*
NEGATIVE 16 (CONVERSION).  The leg equations hold at the setoid
   relation and not on the nose.  Stripped:

     The term "eq_refl" has type
      "exl ∘ pbone_to_prod a b = exl ∘ pbone_to_prod a b"
     while it is expected to have type
      "exl ∘ pbone_to_prod a b = pbone_fst a b"
     (cannot unify "exl ∘ pbone_to_prod a b" and "pbone_fst a b").

--------
负面 16（转换）。腿方程在集合等价关系下成立，而不是精确成立。简化如下：

术语“eq_refl”的类型为
"exl ∘ pbone_to_prod a b = exl ∘ pbone_to_prod a b"
而期望的类型为
"exl ∘ pbone_to_prod a b = pbone_fst a b"
（无法统一“exl ∘ pbone_to_prod a b”和“pbone_fst a b”）。
*)
Fail Example p404_pbone_leg (a b : obj[Sets]) :
  exl ∘ pbone_to_prod a b = pbone_fst a b := eq_refl.

(*
NEGATIVE 18 (TYPING).  The projection is not [exl]: the two morphisms
   do not share a source, so the mismatch is a plain has-type one, with
   no "cannot unify" and no universe clause.  Stripped:

     The term "exl" has type "a × b ~{ Sets }~> a"
     while it is expected to have type "pbone a b ~{ Sets }~> a".

--------
负 18（打字）。该投影不是 [exl]：两个态射没有共享源，因此不匹配只是一个普通的类型不匹配，没有“无法统一”和没有宇宙子句。简化后：

该项“exl”的类型是“a × b ~{ Sets }~> a”，而期望的类型是“pbone a b ~{ Sets }~> a”。
*)
Fail Example p404_pbone_fst_exl (a b : obj[Sets]) :
  pbone_fst a b = @exl Sets Sets_Cartesian a b := eq_refl.

(*
NEGATIVE 17 (CONVERSION).  On the DECIDABLE route the power object is
   the decidable power set, not the [Prop]-valued one.  Its carrier IS
   [SetoidMorphism b BoolSetoid], which is the accepted control in
   Instance/Sets/Topos.v's [app1_pow_dec_carrier].  Stripped:

     The term "eq_refl" has type "Pow b = Pow b"
     while it is expected to have type "Pow b = Powerset_Prop_obj b"
     (cannot unify "Pow b" and "Powerset_Prop_obj b").

--------
负 17（转换）。在可判定路径上，幂对象是可判定幂集，而不是 [Prop] 值的幂集。它的承载体是 [SetoidMorphism b BoolSetoid]，这是在 Instance/Sets/Topos.v 的 [app1_pow_dec_carrier] 中接受的控制。简化：

术语“eq_refl”的类型是“Pow b = Pow b”，而期望的类型是“Pow b = Powerset_Prop_obj b”（无法统一“Pow b”和“Powerset_Prop_obj b”）。
*)
Fail Example p404_pow_dec (D : DecImage) (b : obj[Sets]) :
  @Pow Sets (Sets_Topos_dec D) b = Powerset_Prop_obj b := eq_refl.

(* ==================================================================== *)
(**
** (E) The #405 flagships, at BOTH toposes

    All four elaborate at each.  On the presheaf side the five colimit
    legs projected out of [topos_has_finite_colimits] would each be the
    FIRST inhabitant of its class at any functor category in this tree
    (criterion, three sweeps, in Instance/Fun/Topos.v's header); on the
    setoid side all five are SECOND inhabitants, and the existing ones
    are Checked beside them so the TYPES are seen to line up.  NO
    AGREEMENT PROOF IS BUILT and none is claimed.

--------
** (E) #405 旗舰机，在两个拓扑上  

所有四个在每个拓扑上详细说明。在预层面（presheaf）方面，从 [topos_has_finite_colimits] 投射出的五个余极限（colimit）腿中的每一个，都会是该类别在树中任意函子范畴（functor category）中的第一个成员（criterion, three sweeps，见 Instance/Fun/Topos.v 的头部）；在集合等价类（setoid）方面，所有五个都是第二个成员，并且现有的成员在它们旁边被标记为 Checked，所以类型（TYPES）可以被看到对齐。没有建立任何一致性证明（AGREEMENT PROOF），也未声称存在。
*)

Section PshFlagships.
Context (C : Category) (UT : Untruncate).

Definition psh_Pow (P : C^op ⟶ Sets) :=
  @Pow ([C^op, Sets]) (Presheaf_Topos C UT) P.
Definition psh_monadic :=
  @power_object_monadic ([C^op, Sets]) (Presheaf_Topos C UT).
Definition psh_fincomplete :=
  @topos_finitely_complete ([C^op, Sets]) (Presheaf_Topos C UT).
Definition psh_colimits :=
  @topos_has_finite_colimits ([C^op, Sets]) (Presheaf_Topos C UT).

Definition psh_eq : @HasEqualizers ([C^op, Sets]) :=
  @topos_HasEqualizers ([C^op, Sets]) (Presheaf_Topos C UT).
Definition psh_init : @Initial ([C^op, Sets]) :=
  fst (fst (fst psh_colimits)).
Definition psh_cocart : @Cocartesian ([C^op, Sets]) :=
  snd (fst (fst psh_colimits)).
Definition psh_coeq : @HasCoequalizers ([C^op, Sets]) :=
  snd (fst psh_colimits).
Definition psh_push : @HasPushouts ([C^op, Sets]) := snd psh_colimits.

End PshFlagships.

Section SetsFlagships.
Context (U : Untruncate).

Definition sets_Pow (b : obj[Sets]) := @Pow Sets (Sets_Topos U) b.
Definition sets_monadic := @power_object_monadic Sets (Sets_Topos U).
Definition sets_fincomplete := @topos_finitely_complete Sets (Sets_Topos U).
Definition sets_colimits := @topos_has_finite_colimits Sets (Sets_Topos U).

Definition sets_derived_eq : @HasEqualizers Sets :=
  @topos_HasEqualizers Sets (Sets_Topos U).
Definition sets_derived_init : @Initial Sets := fst (fst (fst sets_colimits)).
Definition sets_derived_cocart : @Cocartesian Sets :=
  snd (fst (fst sets_colimits)).
Definition sets_derived_coeq : @HasCoequalizers Sets :=
  snd (fst sets_colimits).
Definition sets_derived_push : @HasPushouts Sets := snd sets_colimits.

End SetsFlagships.

(* the five pre-existing Sets inhabitants, at the same types / 五个预先存在的集合的居民，同时类型相同 *)
Check (Sets_Initial : @Initial Sets).
Check (Sets_Cocartesian : @Cocartesian Sets).
Check (Sets_HasCoequalizers : @HasCoequalizers Sets).
Check (Sets_HasPushouts : @HasPushouts Sets).
Check (Sets_HasEqualizers : @HasEqualizers Sets).

(* ==================================================================== *)
(**
** (F) Non-vacuity

    The presheaf topos at four named shapes -- [_2] being excluded by
    negative 5 -- with three definitional readbacks over them.  NOTHING
    COMPUTES TO A NUMERAL here and none is claimed: sieve membership is
    [Prop]-valued and truncated, so there is no analogue of
    Instance/FinSet/Topos.v's [Pow 2 = 4].

--------
** (F) 非虚空性

    在四个指定形状上的预丛范畴——[_2] 被负五排除——以及它们上的三个定义性回读。在这里没有任何东西可以计算为一个数字，也没有人声称可以：筛的成员资格是 [Prop] 值的且被截断，因此没有 Instance/FinSet/Topos.v 中 [Pow 2 = 4] 的类似物。
*)

Definition PT_one (UT : Untruncate) := Presheaf_Topos _1 UT.
Definition PT_ord2 (UT : Untruncate) := Presheaf_Topos (Ordinal 2) UT.
Definition PT_par (UT : Untruncate) := Presheaf_Topos Parallel UT.
Definition PT_roof (UT : Untruncate) := Presheaf_Topos Roof UT.

Example PT_one_truth (UT : Untruncate) (c : _1)
  (u : carrier (fobj[@terminal_obj ([_1^op, Sets])
                       (@topos_terminal _ (PT_one UT))] c)) :
  transform[@truth ([_1^op, Sets]) _ (@topos_classifier _ (PT_one UT))] c u
  = @total_sieve _1 c := eq_refl.

Example PT_one_pow (UT : Untruncate) (P : _1^op ⟶ Sets) :
  @Pow ([_1^op, Sets]) (PT_one UT) P = PshExp P (Sieve_Presheaf _1) := eq_refl.

Example PT_par_omega (UT : Untruncate) :
  @Ω ([Parallel^op, Sets]) _ (@topos_classifier _ (PT_par UT))
  = Sieve_Presheaf Parallel := eq_refl.

(* ==================================================================== *)
(**
** (G) Guard block

    Every constant any refutation command above names, Checked OUTSIDE
    every Fail.  Without this a rename would leave the negatives
    vacuously green.

--------
** (G) 守卫块

    每个常量、任何反驳命令在上方命名，都会在每个失败之外被检查。没有这个，重命名会让否定项空洞地显示为绿色。
*)

Check @classifier_classifies.
Check @relations_iso.
Check @Sub_classifier_natural.
Check @Presheaf_Topos.
Check @Presheaf_Topos_IEM.
Check @Copresheaf_Topos.
Check @Copresheaf_Topos_IEM.
Check @Sets_Topos.
Check @Sets_Topos_dec.
Check @Sets_Topos_IEM.
Check @ElementaryTopos.
Check @topos_terminal.
Check @topos_cartesian.
Check @topos_pullbacks.
Check @topos_closed.
Check @topos_classifier.
Check @Pow.
Check @PShSmall.
Check @PShSmall_Terminal.
Check @Fun_Classifier.
Check @Fun_Classifier_small.
Check @Fun_Classifier_cov.
Check @Functor_Category_Terminal.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Closed.
Check @Functor_Category_Closed_cov.
Check @Fun_HasPullbacks.
Check @Fun_Pullback.
Check @PshExp.
Check @presheaf_terminal.
Check @Sets_Terminal.
Check @Sets_Cartesian.
Check @Sets_HasPullbacks.
Check @Sets_Closed.
Check @Sets_Classifier.
Check @Sets_Classifier_dec.
Check @Sets_Classifier_IEM.
Check @Sets.
Check _1.
Check _2.
Check @Ordinal.
Check @Parallel.
Check @Roof.
Check @OneLevel.Untruncate.
Check @OneLevel.DecImage.
Check @OneLevel.IEM.
Check @Ω.
Check @truth.
Check @char.
Check @Sieve.
Check @Sieve_Presheaf.
Check @sieve_truth.
Check @sieve_restrict.
Check @sieve_mem.
Check @total_sieve.
Check @morphism.
Check @carrier.
Check @fmap.
Check @exl.
Check @exr.
Check @PBONE.
Check @pbone.
Check @pbone_fst.
Check @pbone_snd.
Check @pbone_to_prod.
Check @pbone_from_prod.
Check @pullback_over_one_is_product.
Check @Powerset_Prop_obj.
Check @Powerset_Omega.
Check @Powerset_truth_point.
Check @Powerset_squash.
Check @BoolSetoid.
Check @poly_bool.
Check @SetoidMorphism.
Check @Terminal.
Check @Cartesian.
Check @Closed.
Check @HasPullbacks.
Check @SubobjectClassifier.
Check (@Initial Sets).
Check (@Cocartesian Sets).
Check @HasCoequalizers.
Check @HasPushouts.
Check @HasEqualizers.
Check @topos_HasEqualizers.
Check @topos_finitely_complete.
Check @topos_has_finite_colimits.
Check @power_object_monadic.
Check @app1_char_rule_U.
Check @app1_char_rule_dec.
Check @app1_classifying_square.
Check @app1_classifying_unique.
Check @app1_truth_monic.
Check @psh_op_invol.
