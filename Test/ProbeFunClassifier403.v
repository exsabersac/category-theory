Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Fun.Classifier.
Require Import Category.Instance.Two.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.

Generalizable All Variables.

(** * Probe for issue #403 — the sieve classifier of a functor category / * 调查问题 #403 — 函子范畴的筛分类器 *)

(*
Every refutation command below was stripped ONE AT A TIME, compiled
   alone, and its WHOLE error read; the kind is read off the error TEXT.
   FORMABILITY = "universe inconsistency"/"Cannot enforce"; CONVERSION =
   "cannot unify" between two terms of ONE type; TYPING = a plain
   "has type ... while it is expected to have type ..." with neither a
   cannot-unify nor a universe clause, or "Illegal application";
   RESOLUTION = "Cannot infer this placeholder".

   1 instrument check + 16 negatives, classified by reading the whole
   error of each after stripping it alone:
     10 FORMABILITY  (lines with "universe inconsistency")
      2 RESOLUTION   ("Cannot infer this placeholder")
      3 TYPING       (a plain has-type clause, or "Illegal application")
      1 CONVERSION   ("cannot unify" between two terms of one type)
   The labels run 1-10 and 12-14 (with 4a/4b, 5a/5b and 6a/6b): there is
   no NEGATIVE 11 — the prediction it would have pinned was refuted and
   ships as the positive [probe403_med_strict] instead.

   The probe mirrors the UNION of the three library files' Require lines
   (a short prefix is what makes negatives pass for the wrong reason),
   plus Instance/Sets/Powerset/Universal.v for the squash control and
   Instance/FinSet/Classifier.v for [FinSet_Pullbacks].

   GUARD COVERAGE, measured mechanically over the comment-stripped file: 67
   identifiers occur inside a refutation command and 55 of them also occur
   outside every one.  The twelve exceptions are exhaustively the keyword
   itself, three bound variables (P, h, p), the seven [probe403_*] names
   DECLARED inside a refutation command (which therefore never enter the
   environment), and the instrument's deliberately absent name.

   RENAME SIMULATION, 11/11.  Eleven TARGET constants are named inside a
   refutation command — [Sieve], [total_sieve], [sieve_subpresheaf],
   [sieve_incl], [sieve_incl_Monic], [Fun_Classifier],
   [Fun_Classifier_cov], [Fun_Classifier_small], [PShSmall],
   [PShSmall_Terminal], [Fun_HasPullbacks].  Each was renamed in a SCRATCH
   COPY of the three library files (never in the worktree), compiled under
   a shadowing logical root, and this file recompiled against it: every one
   broke at a [Check] line of the guard block below and NONE inside a
   refutation command.  One vacuous guard was found that way and closed:
   [sieve_incl_Monic] was named only inside negative 5b, so renaming it
   left this file compiling; its [Check] was added, and so were [Check]s
   for the three [SubObj] field names the same negative uses.  The guard
   block was extended after the simulation ran, which can only add breaking
   lines; every one of the eleven has its [Check] in the file as shipped,
   verified mechanically.

--------
下面的每个反驳命令都是一个一个地被剥离出来，单独编译，并读取其整个错误；类型是从错误文本中读出的。FORMABILITY = “宇宙不一致”/“无法强制执行”；CONVERSION = “无法统一”两者属于同一类型的项；TYPING = 简单的“类型为……而预期类型为……”且无无法统一或宇宙条款，或者“非法应用”；RESOLUTION = “无法推断此占位符”。

1 次工具检查 + 16 个负面案例，通过独立剥离后读取每个错误来分类：
  10 个可形成性错误（包含“宇宙不一致”的行）
  2 个解析错误（“无法推断此占位符”）
  3 个类型错误（一个普通的 has-type 条款，或“非法应用”）
  1 个转换错误（两个同类型项之间“无法统一”）
标签编号为 1-10 和 12-14（带有 4a/4b、5a/5b 和 6a/6b）：没有负面案例 11 —— 它原本预测的案例已被证伪，并作为正面 [probe403_med_strict] 发布。

探针反映了三个库文件的 Require 行的联合
   （一个短前缀是使否定项因为错误原因通过的原因），
   以及 Instance/Sets/Powerset/Universal.v 用于 squash 控制 和
   Instance/FinSet/Classifier.v 用于 [FinSet_Pullbacks]。

保护覆盖率，通过对去掉注释的文件进行机械测量：67 个标识符出现在反驳命令中，其中有 55 个也出现在每一个命令之外。十二个例外完全包括关键词本身、三个绑定变量（P, h, p）、七个在反驳命令中声明的 [probe403_*] 名称（因此从未进入环境），以及工具故意缺失的名称。

重命名模拟，11/11。在一个反驳命令中有十一项 TARGET 常量被命名——[Sieve]、[total_sieve]、[sieve_subpresheaf]、[sieve_incl]、[sieve_incl_Monic]、[Fun_Classifier]、[Fun_Classifier_cov]、[Fun_Classifier_small]、[PShSmall]、[PShSmall_Terminal]、[Fun_HasPullbacks]。每个都在三个库文件的 SCRATCH 副本中被重命名（从不在工作树中），在一个影子逻辑根下编译，然后这个文件针对它重新编译：每一个都在下面守卫块的 [Check] 行出现错误，而在反驳命令中没有一个出错。通过这种方式发现了一个空的守卫并关闭：[sieve_incl_Monic] 仅在负 5b 中命名，所以重命名它后这个文件仍能编译；它的 [Check] 被添加，并且三个负例使用的 [SubObj] 字段名也添加了 [Check]。模拟运行后，守卫块被扩展，这只能增加出错行；十一项中每一项的 [Check] 都存在于发货文件中，并经过机械验证。
*)

(* ------------------------------------------------------------------ *)
(** ** Instrument check / ** 仪表检查 *)

(*
A deliberately absent name: if this were to succeed, the refutation
   commands below would be measuring nothing.

--------
一个故意缺席的名字：如果这能成功，下面的反驳命令将不会测量任何东西。
*)
Fail Check probe403_this_name_does_not_exist.

(* ------------------------------------------------------------------ *)
(** ** Guard controls — every constant a negative names, named outside / ** 守卫控制——每个常量都是负名称，在外部命名 *)

Check @Sieve.
Check @SieveObj.
Check @Sieve_Presheaf.
Check @total_sieve.
Check @sieve_mem.
Check @sieve_respects.
Check @sieve_closed.
Check @sieve_truth.
Check @char_nat.
Check @char_sieve.
Check @char_square.
Check @presheaf_char_unique.
Check @presheaf_char_pullback.
Check @sieve_subpresheaf.
Check @sieve_incl.
Check @sieve_subobject.
Check @sieve_incl_Monic.
Check @sieve_cone.
Check @Fun_Classifier.
Check @Fun_Classifier_IEM.
Check @Fun_Classifier_cov.
Check @Fun_Classifier_small.
Check @fun_classifier_classifies.
Check @fun_sub_classifier_natural.
Check @fun_Sub_Representable.
Check @PShSmall.
Check @PShSmall_Terminal.
Check @Fun_HasPullbacks.
Check @Fun_Pullback.
Check @Fun_IsPullback.
Check @Fun_Pullback_Functor.
Check @Fun_Pullback_fst.
Check @Fun_Pullback_snd.
Check @fpb_at.
Check @fun_pullback_med_at.
Check @fun_char_roundtrip.
Check @fun_pullback_roundtrip.
Check @MacOmega.
Check @macj.
Check @jmap.
Check @mac_dictionary.
Check @twoX_total.
Check @twoX_mid.
Check @twoX_empty.
Check @twoY_total.
Check @twoY_empty.
Check @twoX_code.
Check @twoY_code.
Check @twoX_three_sieves.
Check @twoY_two_sieves.
Check @classifier_classifies.
Check @Sub_classifier_natural.
Check @Untruncate.
Check @IEM.
Check @Powerset_squash.
Check @powerset_squash_prop_inert.
Check @Sets_HasPullbacks.
Check @FinSet_Pullbacks.
Check @Functor_Category_Terminal.
Check @Sets_Terminal.
Check @Fun.
Check @Opposite.
Check @Functor.
Check @HasPullbacks.
Check @SubobjectClassifier.
Check @Sets.
Check @FinSet.
Check @_2.
Check @Curried_CoHom.
Check @presheaf_monic_iff_injective.
Check @Monic.
Check @SubObj.
Check @Representable.
Check @Terminal.
Check @IsPullback.
Check @ump_pullbacks.
Check @pullback.
Check @Ω.
Check @truth.
Check @char.
Check @sub_reindex.
Check @Build_SubObj.
Check @sub_dom.
Check @sub_mono.
Check @sub_is_monic.

(* ------------------------------------------------------------------ *)
(** ** Positive controls the file's claims rest on / ** 积极控制文件所声称的内容 *)

(*
Mac Lane's Sets^2 is [_2, Sets], which is presheaves on [_2^op]:
   the double opposite is the identity here, ON THE NOSE.

--------
Mac Lane 的 Sets^2 是 [_2, Sets]，它是 [_2^op] 上的预层：在这里，双对偶就是恒等式，完全精确。
*)
Example probe403_op_op_two : (_2^op)^op = _2 := eq_refl.

(*
The five computations of Mac Lane's j, restated from OUTSIDE the
   target so a rename in the target breaks this file.

--------
Mac Lane 的 j 的五个计算，从目标之外重新陈述，因此目标中的重命名会破坏此文件。
*)
Example probe403_j_total : jmap twoX_total ≈ twoY_total := j_total.
Example probe403_j_mid : jmap twoX_mid ≈ twoY_total := j_mid.
Example probe403_j_empty : jmap twoX_empty ≈ twoY_empty := j_empty.
Example probe403_j_identifies : jmap twoX_total ≈ jmap twoX_mid
  := j_identifies.
Example probe403_j_separates : jmap twoX_total ≈ jmap twoX_empty -> False
  := j_separates.

(* Mac Lane's explicit three-element object, computing. / 麦克莱恩的显式三元素对象，计算中。 *)
Example probe403_macj_0 : macj Fin.F1 = Fin.F1 := eq_refl.
Example probe403_macj_1 : macj (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example probe403_macj_2 :
  macj (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.
Example probe403_macOmega_X : fobj[MacOmega] TwoX = 3%nat := eq_refl.
Example probe403_macOmega_Y : fobj[MacOmega] TwoY = 2%nat := eq_refl.
Example probe403_macOmega_fmap : fmap[MacOmega] TwoXY = macj := eq_refl.

(* The classifier's data, read back from outside. / 从外部读取的分类器数据。 *)
Example probe403_omega {C : Category} (UT : Untruncate) :
  @Ω ([C^op, Sets]) _ (Fun_Classifier UT) = Sieve_Presheaf C := eq_refl.
Example probe403_truth {C : Category} (UT : Untruncate) :
  @truth ([C^op, Sets]) _ (Fun_Classifier UT) = sieve_truth C := eq_refl.

(* The pointwise pullback, read back from outside. / 逐点拉回，从外部读取。 *)
Example probe403_pb_obj {C D : Category} (HP : @HasPullbacks D)
  {F G H : C ⟶ D} (a : F ~{[C, D]}~> H) (b : G ~{[C, D]}~> H) (x : C) :
  fobj[Pull _ _ (Fun_Pullback HP a b)] x
    = Pull _ _ (pullback (transform[a] x) (transform[b] x)) := eq_refl.

(* ------------------------------------------------------------------ *)
(** ** (1)-(2) [classifier_classifies] at the presheaf category / ** (1)-(2) [classifier_classifies] 在预层范畴 *)

Section CC.
Context {C : Category}.
Context (HPB : @HasPullbacks ([C^op, Sets])).
Context (HS : @SubobjectClassifier ([C^op, Sets])
                (Functor_Category_Terminal Sets_Terminal)).
Context (UT : Untruncate).

(*
CONTROL: the theorem IS formable at an ABSTRACT classifier of a
   presheaf category — unlike at [Sets], where #402 records that it is
   not statable at all.

--------
控制：该定理可以在一个预层范畴的抽象分类器上形成——不像在 [Sets] 中，#402 记录它根本无法表述。
*)
Check (@classifier_classifies ([C^op, Sets])
         (Functor_Category_Terminal Sets_Terminal) HPB HS).
Check (@Sub_classifier_natural ([C^op, Sets])
         (Functor_Category_Terminal Sets_Terminal) HPB HS).

(*
NEGATIVE 1 (FORMABILITY).  It is NOT applicable to the built
   [Fun_Classifier], whose elaboration minimizes the presheaf category's
   hom universe below its object universe.  The stripped error ends
   "Cannot enforce ... because ... <= ... < ...".

--------
否定 1（可形成性）。它不适用于已构建的 [Fun_Classifier]，其构造最小化了预层范畴的同宇宙低于其对象宇宙。剥离的错误以“无法强制执行 ... 因为 ... <= ... < ...”结束。
*)
Fail Check (@classifier_classifies ([C^op, Sets])
              (Functor_Category_Terminal Sets_Terminal)
              (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT)).

(* NEGATIVE 2 (FORMABILITY).  Nor is the naturality upgrade. / 负面 2（可成型性）。自然性提升也没有。 *)
Fail Check (@Sub_classifier_natural ([C^op, Sets])
              (Functor_Category_Terminal Sets_Terminal)
              (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier UT)).
End CC.

(*
CONTROL: at the SECOND reading of the presheaf category — objects at
   or below homs — both DO apply, which is what section (I) of the
   target ships.  This pair is the precise form of the sentence
   "classifier_classifies is not statable for presheaf categories",
   which is false as stated.

--------
控制：在预层范畴的第二次阅读中——对象在或低于Hom——两者都适用，这正是目标部分(I)所表达的。这一对是句子“classifier_classifies 对于预层范畴是不可陈述的”的精确形式，而该陈述本身是错误的。
*)
Section CCSmall.
Universes co o so OO HH.
Constraint Set < o.
Constraint o < so.
Constraint so <= OO.
Constraint OO <= HH.
Context (Cs : Category@{co o o}).
Context (UTs : Untruncate@{o}).
Check (@classifier_classifies (PShSmall Cs) (PShSmall_Terminal Cs)
         (Fun_HasPullbacks Sets_HasPullbacks) (Fun_Classifier_small Cs UTs)).
Check (fun_classifier_classifies Cs UTs).
Check (fun_sub_classifier_natural Cs UTs).
Check (fun_Sub_Representable Cs UTs).

(*
NEGATIVE 3 (FORMABILITY).  The BUILT [Fun_Classifier] still cannot be
   re-typed at those levels — a re-annotated REDEFINITION is what
   escapes, not a re-ascription of the constant.

--------
负面 3（可形成性）。在这些级别上，内置的 [Fun_Classifier] 仍然无法重新输入——逃脱的是重新注释的重新定义，而不是对常量的重新指定。
*)
Fail Check (Fun_Classifier (C:=Cs) UTs
              : @SubobjectClassifier (PShSmall Cs) (PShSmall_Terminal Cs)).
End CCSmall.

(* ------------------------------------------------------------------ *)
(** ** (4) No [HasPullbacks] for a functor category by resolution / ** (4) 通过分解解析没有用于函子范畴的 [HasPullbacks] *)

(*
CONTROLS: the two base categories DO have registered instances, and
   the target's plain [Definition] supplies the functor-category ones.

--------
控制：两个基本类别确实有注册实例，而目标的普通 [Definition] 提供了函子类别的那些。
*)
Definition probe403_pb_sets : @HasPullbacks Sets := _.
Definition probe403_pb_finset : @HasPullbacks FinSet := _.
Check (Fun_HasPullbacks Sets_HasPullbacks : @HasPullbacks ([_2, Sets])).
Check (Fun_HasPullbacks FinSet_Pullbacks : @HasPullbacks ([_2, FinSet])).

(*
NEGATIVE 4a, 4b (RESOLUTION).  [Fun_HasPullbacks] is deliberately a
   plain [Definition] and not an [Instance], so resolution still finds
   nothing; the stripped errors read "Cannot infer this placeholder ...
   (no type class instance found)".  Note [Fail Check (_ : T)] is NOT a
   valid negative here — Coq accepts it and prints the evar.

--------
NEGATIVE 4a, 4b（解决方案）。[Fun_HasPullbacks] 故意是一个普通的 [Definition]，而不是 [Instance]，因此 resolution 仍然找不到任何内容；被剥除的错误显示“无法推断此占位符……（未找到类型类实例）”。注意 [Fail Check (_ : T)] 在这里不是有效的负面示例——Coq 会接受它并打印 evar。
*)
Fail Definition probe403_no_pb_sets : @HasPullbacks ([_2, Sets]) := _.
Fail Definition probe403_no_pb_finset : @HasPullbacks ([_2, FinSet]) := _.

(* ------------------------------------------------------------------ *)
(**
** (5) The class takes TWO arguments, and its literals want the
        category written out

--------
** (5) 该类接受两个参数，并且它的字面量希望类别被写出来
*)

Section Arity.
Context {C : Category}.

(* CONTROL: the two-argument form. / 控制：两个参数的形式。 *)
Check (@SubobjectClassifier ([C^op, Sets])
         (Functor_Category_Terminal Sets_Terminal)).

(*
NEGATIVE 5a (TYPING).  Offering a [HasPullbacks] as a third argument
   is an "Illegal application (Non-functional construction)": the
   [HasPullbacks] of the class's declaring section is used by the
   theorems BELOW the class, not by the class.

--------
负面 5a（打字）。提供 [HasPullbacks] 作为第三个参数是“非法应用（非功能性构造）”：类声明部分的 [HasPullbacks] 被类下面的定理使用，而不是被类使用。
*)
Fail Check (@SubobjectClassifier ([C^op, Sets])
              (Functor_Category_Terminal Sets_Terminal)
              (Fun_HasPullbacks Sets_HasPullbacks)).

(*
CONTROL: the subobject of the representable, with the category
   written out.

--------
控制：可表示对象的子对象，并写出类别。
*)
Check (fun (c : C) (S : Sieve c) => sieve_subobject c S).

(*
NEGATIVE 5b (TYPING).  The same record literal WITHOUT the explicit
   category is refused: the [sub_dom] field elaborates against
   [obj[?C]], and the stripped error is a plain "has type ... while it
   is expected to have type "obj[?C]"" with no cannot-unify and no
   universe clause.

--------
否定 5b（打字）。相同的记录字面量如果没有显式类别会被拒绝：[sub_dom] 字段与 [obj[?C] 相冲突，而去掉的错误只是一个简单的“具有类型 ... 而预期类型是 obj[?C]”，没有 cannot-unify 也没有 universe 子句。
*)
Fail Definition probe403_sub_literal (c : C) (S : Sieve c) :
  @SubObj ([C^op, Sets]) (Curried_CoHom C c) :=
  {| sub_dom := sieve_subpresheaf c S
   ; sub_mono := sieve_incl c S
   ; sub_is_monic := sieve_incl_Monic c S |}.
End Arity.

(* ------------------------------------------------------------------ *)
(** ** (6) The presheaf category's two universe identifications / ** (6) 预层范畴的两个宇宙识别 *)

Section DonorA.
Universes co ch cp o so.
Constraint ch < cp.
Constraint o < so.
Context (Cu : Category@{co ch cp}).

(*
CONTROLS accepted at levels where hom and proof are DECLARED APART:
   the hom type, an identity, and functors in both directions.  So
   [Functor] is NOT a donor of [ch = cp].

--------
在 hom 和证明被声明分开时接受的控制：
   同态类型、一个恒等式，以及双向的函子。因此
   [Functor] 不是 [ch = cp] 的捐赠者。
*)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x : Cu) => @id Cu x).
Check (@Functor Cu Cu).
Check (@Functor Cu Sets@{o so}).

(* NEGATIVE 6a (FORMABILITY).  [Opposite] forces [ch = cp] on its own. / 负面 6a（可成形性）。[Opposite] 会强迫 [ch = cp] 自行执行。 *)
Fail Check (Cu^op).

(*
NEGATIVE 6b (FORMABILITY).  So does [Fun], with NO [^op] anywhere in
   the command — two INDEPENDENT donors.

--------
NEGATIVE 6b（可成型性）。[Fun] 也是如此，命令中没有 [^op] —— 两个独立的供体。
*)
Fail Check ([Cu, Sets@{o so}]).
End DonorA.

Section DonorB.
Universes co2 ch2 o2 so2.
Constraint ch2 < o2.
Constraint o2 < so2.
Context (Cv : Category@{co2 ch2 ch2}).

(*
CONTROLS: the opposite and both functor types elaborate with C's hom
   universe DECLARED BELOW [Sets]' carrier universe.  So neither
   [Opposite] nor [Functor] is a donor of [ch = o].

--------
控制：相反和两种函子类型在 C 的同态宇宙中详细说明，在下面声明的 [Sets] 承载宇宙中。因此，[Opposite] 和 [Functor] 都不是 [ch = o] 的供体。
*)
Check (Cv^op).
Check (@Functor (Cv^op) Sets@{o2 so2}).
Check (@Functor Cv Sets@{o2 so2}).
Check (Sets@{o2 so2}).

(*
NEGATIVE 7 (FORMABILITY).  [Fun] identifies its source and target hom
   universes, so the presheaf category pins C's hom universe to [Sets]'
   carrier universe.  The covariant reading is refused identically; the
   file's [Fun_Classifier_cov] therefore inherits the same bound.

--------
负 7（可形成性）。[Fun] 识别其源和目标 Hom 宇宙，因此预层范畴将 C 的 Hom 宇宙固定到 [Sets] 的承载宇宙。协变读取被同样拒绝；因此文件的 [Fun_Classifier_cov] 继承了相同的界限。
*)
Fail Check ([Cv^op, Sets@{o2 so2}]).
End DonorB.

Section DonorC.
Universes co3 ch3 do3 dh3.
Constraint ch3 < dh3.
Context (Cw : Category@{co3 ch3 ch3}).
Context (Dw : Category@{do3 dh3 dh3}).

(*
CONTROL: the bare functor type elaborates at hom levels declared
   apart, so [Functor] is not the donor of Instance/Fun/Pullback.v's
   block equation [u0 = u2].

--------
控制：裸函数子类型在单独声明的同态层次上进行展开，因此 [Functor] 不是 Instance/Fun/Pullback.v 的块方程 [u0 = u2] 的提供者。
*)
Check (@Functor Cw Dw).

(*
NEGATIVE 8 (FORMABILITY).  [Fun] is: the functor CATEGORY is
   refused at the same levels.

--------
负 8（可成形性）。[Fun] 是：泛函 CATEGORY 在相同级别被拒绝。
*)
Fail Check ([Cw, Dw]).
End DonorC.

(* ------------------------------------------------------------------ *)
(** ** (3) A [Type]-valued sieve is not an object of [Sets] / ** (3) 一个 [Type] 值的筛子不是 [Sets] 的对象 *)

Section TypeSieve.
Universes co4 ch4 cp4 o4 so4.
Constraint Set < o4.
Constraint o4 < so4.
Context (Cx : Category@{co4 ch4 ch4}).
Context (cx : obj[Cx]).

(* The [Type]-valued analogue of the record. / 该记录的 [Type] 值模拟品。 *)
Record TSieve@{} (c : obj[Cx]) : Type@{max(co4,ch4,o4+1)} := {
  tsieve_mem : ∀ (d : obj[Cx]), (d ~{Cx}~> c) → Type@{o4};
  tsieve_closed : ∀ (d e : obj[Cx]) (f : d ~{Cx}~> c) (g : e ~{Cx}~> d),
      tsieve_mem d f → tsieve_mem e (f ∘ g)
}.

(* CONTROL: the [Prop]-valued carrier IS a [Type@{o4}]. / 控制：[Prop] 值的载体是 [Type@{o4}]。 *)
Check (Sieve cx : Type@{o4}).

(*
NEGATIVE 9 (FORMABILITY).  The [Type@{o4}]-valued one sits at
   [o4 + 1]; the stripped error is "Cannot enforce o4 < o4 because
   o4 = o4".  This is why membership is [Prop]-valued and the
   characteristic sieve must truncate.

--------
负9（可成形性）。值为[Type@{o4}]的一项位于[o4 + 1]；去掉的错误是“无法强制执行 o4 < o4 因为 o4 = o4”。这就是为什么成员资格是[Prop]值，并且特征筛必须截断。
*)
Fail Check (TSieve cx : Type@{o4}).
End TypeSieve.

(* ------------------------------------------------------------------ *)
(** ** (10) The truncation is not eliminable without [Untruncate] / ** (10) 没有 [Untruncate]，截断是不可消除的 *)

(* CONTROL: over a [Prop] the squash is inert. / 控制：在 [Prop] 上，南瓜是惰性的。 *)
Check @powerset_squash_prop_inert.

(*
NEGATIVE 10 (FORMABILITY).  The naive elimination is refused with
   "Cannot enforce ... <= Prop" — #402's wall, at the same level, and
   what [Untruncate] buys.

--------
负 10（可形成性）。天真的消除被拒绝，显示“无法强制执行 ... <= Prop” — #402 的限制，在同一级别，以及 [Untruncate] 所提供的内容。
*)
Fail Definition probe403_naive_untruncate@{o} : Untruncate@{o} :=
  fun P h => h P (fun p => p).

(* ------------------------------------------------------------------ *)
(** ** (9) The pointwise mediator is [≈] and not [eq_refl] / ** (9) 点位中介是 [≈]，而不是 [eq_refl] *)

Section Med.
Context {C D : Category}.
Context (HP : @HasPullbacks D).
Context {F G H : C ⟶ D}.
Context (a : F ~{[C, D]}~> H) (b : G ~{[C, D]}~> H).
Context {Q : C ⟶ D} (q1 : Q ~{[C, D]}~> F) (q2 : Q ~{[C, D]}~> G).
Context (Hq : a ∘ q1 ≈ b ∘ q2).

(*
POSITIVE, and it REFUTES a prediction: the mediator's component IS
   D's mediator at [eq_refl], not merely at [≈].  The brief expected a
   CONVERSION refutation here on the ground that the bundled
   [Fun_Pullback] reaches its universal property through
   [is_pullback_pullback] of [Fun_IsPullback]; measurement says
   otherwise, because [is_pullback_pullback] is a field repackaging and
   [Build_Transform'] is transparent, so the whole chain reduces.

--------
积极的，它反驳了一个预测：中介组件是在 [eq_refl] 处作为 D 的中介，而不仅仅是在 [≈] 处。该简报原本预期这里会有一个 CONVERSION 反驳，理由是绑定的 [Fun_Pullback] 通过 [Fun_IsPullback] 的 [is_pullback_pullback] 达到其普遍属性；测量结果表明情况并非如此，因为 [is_pullback_pullback] 是一个字段重新打包，而 [Build_Transform'] 是透明的，因此整个链条会缩减。
*)
Example probe403_med_strict (x : C) :
  transform[unique_obj (ump_pullbacks _ _ (Fun_Pullback HP a b) Q q1 q2 Hq)] x
    = unique_obj (ump_pullbacks _ _ (fpb_at HP a b x) (Q x)
                    (transform[q1] x) (transform[q2] x) (Hq x))
  := eq_refl.

(*
The [≈] form is then a weakening, kept in the target because it is
   the shape a consumer rewrites with.

--------
[≈] 形式随后是一种弱化，保留在目标中，因为它是消费者用来重写的形态。
*)
Check (fun x : C => fun_pullback_med_at HP a b q1 q2 Hq x).
End Med.

(* ------------------------------------------------------------------ *)
(** ** (11) The two classifier readings are not the same constant / ** (11) 这两个分类符的读数不是相同的常数 *)

Section TwoReadings.
Universes co5 o5 so5 OO5 HH5.
Constraint Set < o5.
Constraint o5 < so5.
Constraint so5 <= OO5.
Constraint OO5 <= HH5.
Context (Cz : Category@{co5 o5 o5}).
Context (UTz : Untruncate@{o5}).

(*
CONTROL: both readings have the same truth object at [eq_refl],
   each against [Sieve_Presheaf] in its own category.

--------
控制：两次读数在 [eq_refl] 上具有相同的真值对象，各自在其自己的类别中对应 [Sieve_Presheaf]。
*)
Check (@eq_refl _ (Sieve_Presheaf Cz)
        : @Ω (PShSmall Cz) (PShSmall_Terminal Cz)
             (Fun_Classifier_small Cz UTz) = Sieve_Presheaf Cz).

(*
NEGATIVE 12 (FORMABILITY, and the kind was a prediction measurement
   corrected).  The two readings are not comparable at all: the refusal
   is a universe inconsistency, "Cannot enforce o5 = ... because
   o5 < ... <= ... <= ...", not the "cannot unify" a conversion
   refutation would give.  So the two classifiers do not even share a
   type, and NO equation between the readings is claimed anywhere.

--------
负 12（可形成性，以及这种类型是经过修正的预测测量）。这两个读数完全不可比较：拒绝是一个宇宙不一致性，“无法强制执行 o5 = ... 因为 o5 < ... <= ... <= ...”，而不是转换反驳会给出的“无法统一”。因此这两个分类器甚至没有共享类型，并且在任何地方都没有声明两个读数之间的任何方程。
*)
Fail Definition probe403_two_readings :
  Fun_Classifier_small Cz UTz = Fun_Classifier (C:=Cz) UTz := eq_refl.
End TwoReadings.

(* ------------------------------------------------------------------ *)
(** ** (12) [Fun_Classifier_cov] is a conversion, not a transport / ** (12) [Fun_Classifier_cov] 是一种转换，而不是传输 *)

(*
CONTROL: the covariant reading IS [Fun_Classifier] at the opposite,
   supplied by [:=] with no tactic — [(D^op)^op = D] by [eq_refl].

--------
控制：协变读数为 [Fun_Classifier]，在相反位置，由 [:=] 提供，没有策略 —— [(D^op)^op = D] 由 [eq_refl] 提供。
*)
Example probe403_cov {D : Category} (UT : Untruncate) :
  @Fun_Classifier_cov D UT = @Fun_Classifier (D^op) UT := eq_refl.

(*
NEGATIVE 13 (TYPING).  The two ARE at different categories all the
   same: [Fun_Classifier_cov] is at [[D, Sets]] and cannot be ascribed
   at the presheaf category of the same D.  The stripped error is a
   plain has-type clause with no cannot-unify and no universe clause.

--------
负13（打字）。这两个仍然处于不同的类别：[Fun_Classifier_cov] 位于 [[D, Sets]]，不能在同一 D 的预层范畴中归属。被剥离的错误是一个简单的具有类型的条款，没有无法统一条款，也没有宇宙条款。
*)
Section Cov.
Context {D : Category}.
Context (UT : Untruncate).
Fail Definition probe403_cov_bad :
  @SubobjectClassifier ([D^op, Sets])
    (Functor_Category_Terminal Sets_Terminal) :=
  @Fun_Classifier_cov D UT.
End Cov.

(* ------------------------------------------------------------------ *)
(**
** (13) The sieve subpresheaf of the total sieve is not the
        representable ON THE NOSE

--------
** （13）总格滤子的筛子子上滤子并不是严格可表示的
*)

Section TotalSub.
Context {C : Category}.
Context (c : C).

(*
CONTROLS: both ARE objects of the same presheaf category, so the
   refusal below is about conversion and not about formability.

--------
控制：两者都是同一个预层范畴的对象，因此下面的拒绝是关于转换的，而不是关于可构形性的。
*)
Check (sieve_subpresheaf c (total_sieve c)).
Check (fobj[Curried_CoHom C] c).

(*
NEGATIVE 14 (CONVERSION) — the file's ONLY one.  The subpresheaf cut
   by the total sieve has carrier [{ g : k ~> c & True }] where the
   representable has [k ~> c]; the stripped error is "cannot unify"
   between two terms of one type.  An isomorphism between them is NOT
   built: the classifier never needs one, since the uniqueness clause
   feeds the pullback the subpresheaf directly.

--------
负 14（转换）——文件中唯一的一个。由全筛割下的子预层的承载对象是 [{ g : k ~> c & True }]，而可表对象是 [k ~> c]；剥离的错误是“无法统一”两个同类型的项。它们之间没有构建同构：分类器从不需要一个，因为唯一性条款直接将子预层传入拉回。
*)
Fail Definition probe403_total_sub :
  sieve_subpresheaf c (total_sieve c) = fobj[Curried_CoHom C] c := eq_refl.
End TotalSub.
