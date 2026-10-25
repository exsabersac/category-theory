Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Adjunction.SAFT.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(**
* Probe for Structure/Generator.v, Structure/Generator/Dual.v and
      Structure/Generator/Concrete.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.7
    Definition 4, printed p. 127; Awodey §7.2 p. 154; Riehl 4.7.7 p. 177.
    Issue #447.  The witnesses at Sets, Grp and Ab have their own probe,
    Test/ProbeGeneratorWitnesses447.v; this file guards the general
    theory and the duality bridge.

    The import list above is the UNION of the three target files' own
    import lists, unabbreviated.  A short prefix is what makes a probe
    pass vacuously, so nothing is trimmed even where a require is
    redundant.

    Every statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read; a refutation that holds prints nothing under
    this repo's coqc, so a whole-file rc=0 would establish only THAT each
    command does not typecheck and never WHY.  Each negative is classified
    by the error TEXT, under THIS import list:

      CONVERSION  - "The term T has type X while it is expected to have
                    type Y (cannot unify A and B)".
      TYPING      - the same opener with NO "cannot unify" parenthetical:
                    the two types are not even candidates for conversion.

    The instrument check comes first: a name that does not exist, refused
    for a reason unrelated to any boundary.  Every LIBRARY constant a
    negative names appears in a positive control outside any refutation
    command, so that a rename cannot leave a negative refused for
    reference-not-found and therefore vacuously green.

--------
* 探测 Structure/Generator.v、Structure/Generator/Dual.v 和 Structure/Generator/Concrete.v

Mac Lane，《为工作数学家准备的范畴论》，第二版，第 V.7 节 第 4 条定义，印刷版第 127 页；Awodey 第 7.2 节，第 154 页；Riehl 第 4.7.7 节，第 177 页。问题 #447。在 Sets、Grp 和 Ab 中的见证者有他们自己的探针，Test/ProbeGeneratorWitnesses447.v；该文件保护一般理论和对偶桥梁。

上面的导入列表是三个目标文件自身导入列表的并集，未缩写。 一个简短的前缀会让探针形式上通过，因此即使某个 require 是多余的，也不会被删减。

下面声称被驳斥的每个陈述都已经在本文件的副本中被去掉了驳斥关键字，单独编译，并读取其完整错误；在本仓库的 coqc 下，一个成立的驳斥不会打印任何内容，因此整个文件的 rc=0 只会证明每条命令都无法类型检查，而永远不会说明原因。每个否定项根据错误文本进行分类，在此导入列表下：

转换  - “术语 T 的类型为 X，而预期类型为 Y（无法统一 A 和 B）”。
类型检查  - 相同的开头，但没有“无法统一”的括号说明：这两种类型甚至不是可转换的候选类型。

仪器检查首先进行：一个不存在的名称，被拒绝，原因与任何边界无关。每一个 LIBRARY 常量中的负名称出现在任何反驳命令之外的正控制中，因此重命名不能因为未找到引用而留下负拒绝，从而空泛地为绿色。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check generator_447_no_such_constant.

(** ** Positive controls: every constant the negatives depend on / ** 阳性对照：每一个负对照所依赖的常数 *)

Check @Generator.
Check @Build_Generator.
Check @gen_index.
Check @gen_obj.
Check @gen_separates.
Check @IsSeparator.
Check @JointlyFaithful.
Check @Separates.
Check @generator_iff_jointly_faithful.
Check @Generator_of_separator.
Check @separator_of_generator.
Check @separator_faithful.
Check @faithful_separator.
Check @generator_jointly_faithful.
Check @Cogenerator.
Check @Build_Cogenerator.
Check @cog_index.
Check @cog_obj.
Check @cog_separates.
Check @gen_of_cog.
Check @cog_of_gen.
Check @Faithful.
Check @Build_Faithful.
Check @fmap_inj.
Check @Curried_Hom.
Check @Curried_CoHom.
Check @Separator.
Check @Separator_of_IsSeparator.
Check @IsSeparator_of_Separator.

(** ** Readbacks that HOLD, at the strength stated / ** 按照所述强度保持的回读 *)

Section Readbacks.

Context {C : Category}.

(* F1: the duality bridge round-trips on the nose, both ways. / F1：二元桥在鼻子上双向往返。 *)
Example p447_rt1 (G : Generator C) : gen_of_cog (cog_of_gen G) = G := eq_refl.
Example p447_rt2 (G : Cogenerator (C^op)) :
  cog_of_gen (gen_of_cog G) = G := eq_refl.

(* The single-object round trip is an equation, not a re-inhabitation. / 单对象的往返是一个等式，不是重新居住。 *)
Example p447_roundtrip (c : C) (H : IsSeparator c) :
  separator_of_generator (Generator_of_separator c H) tt
    (fun j => match j with tt => eq_refl end) = H := eq_refl.

(*
The wrong-variance STATEMENT is well formed -- it says the family
   COseparates -- so negative N3 below pins the DERIVATION and not the
   statement; a refusal of the statement would be vacuous.

--------
错误方差声明是良构的——它表示家族 CO 分离——因此下面的负 N3 锁定的是推导而不是声明；拒绝该声明将是空洞的。
*)
Definition p447_wrong_variance_type (G : Generator C) : Type :=
  JointlyFaithful (fun j : gen_index G => [Hom ─, gen_obj G j]).

End Readbacks.

(** ** Negatives / ** 负面 *)

Section Negatives.

Context {C : Category}.

(*
N1 -- CONVERSION.  The bridge needs the two object quantifiers
   exchanged: the field applied at the objects in the order the record
   declares them is refused, "cannot unify "x ~{ C }~> y" and
   "x ~{ C^op }~> y"".

--------
N1 -- 转换。桥需要交换两个对象量词：按照记录声明的顺序应用于对象的字段被拒绝，"无法统一"x ~{ C }~> y"和"x ~{ C^op }~> y"。
*)
Fail Definition n1 (G : Cogenerator (C^op)) : Generator C :=
  @Build_Generator C (cog_index G) (cog_obj G) (@cog_separates (C^op) G).

(*
N2 -- CONVERSION.  The two TYPES are not equal: two distinct
   inductives over the same data, "cannot unify "Generator C" and
   "Cogenerator C^op"".  The eq_refl round trips above are therefore the
   strongest statement available.

--------
N2 -- 转换。 这两种类型不相等：在相同数据上的两个不同归纳，"无法统一 \"生成器 C\" 和 \"协生成器 C^op\""。 因此，上述 eq_refl 往返是可用的最强语句。
*)
Fail Example n2 : Generator C = Cogenerator (C^op) := eq_refl.

(*
N3 -- TYPING.  Deriving the contravariant (coseparating) statement
   from a Generator with the covariant proof term: "The term "k" has type
   "gen_obj G j ~{ C }~> y" while it is expected to have type
   "carrier (fobj[fobj[Curried_CoHom C] (gen_obj G j)] x)"" -- the probe
   object sits at the wrong end of the arrow.

--------
N3 -- 打字。从具有协变证明项的生成器导出逆变（对分隔）语句：“术语‘k’的类型为‘gen_obj G j ~{ C }~> y’，然而预期类型为‘carrier (fobj[fobj[Curried_CoHom C] (gen_obj G j)] x)’”——探针对象位于箭头的错误一端。
*)
Fail Definition n3 (G : Generator C) :
  JointlyFaithful (fun j : gen_index G => [Hom ─, gen_obj G j]) :=
  fun x y f g H => gen_separates G f g (fun j k => H j k).

(*
N4 -- TYPING.  The bare coercion from the separation clause to the
   faithfulness class: "The term "H" has type "IsSeparator c" while it is
   expected to have type "Faithful (fobj[C] c)"" -- a class record is not
   a function, hence [Build_Faithful] in [separator_faithful].

--------
N4 -- 输入。 从分离子句到忠诚类的直接强制转换："术语 'H' 的类型是 'IsSeparator c'，而它预期的类型是 'Faithful (fobj[C] c)'" —— 类记录不是函数，因此 [Build_Faithful] 在 [separator_faithful] 中。
*)
Fail Example n4 (c : C) (H : IsSeparator c) : Faithful [Hom c,─] := H.

(*
N5 -- TYPING.  The record builder without an explicit category infers
   the record's parameter as C^op from [gen_obj := cog_obj G] and then
   rejects the separation field: "The term "f" has type "x ~{ C^op }~> y"
   while it is expected to have type "y ~{ C^op }~> x"".

--------
N5 -- 输入。没有显式类别的记录构建器会从 [gen_obj := cog_obj G] 推断记录的参数为 C^op，然后拒绝分离字段：“术语 'f' 的类型是 'x ~{ C^op }~> y'，而它预期的类型是 'y ~{ C^op }~> x'。”
*)
Fail Definition n5 (G : Cogenerator (C^op)) : Generator C :=
  {| gen_index := cog_index G; gen_obj := cog_obj G;
     gen_separates := fun x y f g H => @cog_separates (C^op) G y x f g H |}.

End Negatives.
