Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.CokernelPair.

Generalizable All Variables.

(**
* Probes guarding Theory/Morphisms/CokernelPair.v and
      Instance/Sets/CokernelPair.v

--------
* 探针保护 Theory/Morphisms/CokernelPair.v 和 Instance/Sets/CokernelPair.v
*)

(*
This file exists so that the strength claims in those two headers break
   LOUDLY rather than silently.  Every [Fail] below was stripped once and
   the failure KIND confirmed at the message, and every negative is paired
   with a positive control that must SUCCEED, so a rename or a record
   change cannot turn a [Fail] vacuously green.

   The import list is the union of the two targets' own import lists, in
   target order — a shortened prefix is exactly what makes a probe pass
   for the wrong reason.

   The two kinds of negative are kept LEXICALLY APART:

     - CONVERSION negatives, [Fail Definition … := eq_refl], asserting
       that two well-typed terms are NOT definitionally equal;
     - FORMABILITY negatives, [Fail Check], asserting that an expression
       does not elaborate at all.

   Instrument sanity: in batch mode a [Fail] that succeeds prints nothing
   and a [Fail] that does not fail aborts the file with "The command has
   not failed!", so a green build is genuine evidence.

--------
这个文件存在的目的是为了让那两个头文件中的强度声明在出错时大声报错，而不是默默失败。下面的每个 [Fail] 都曾被剥离一次，并且在消息中确认了失败类型，每个负面情况都配有一个必须成功的阳性对照，因此重命名或更改记录不能让 [Fail] 无中生有地显示为成功。

导入列表是两个目标自身导入列表的并集，按目标顺序排列——正是缩短的前缀使探查因错误的原因而通过。

这两种否定在词汇上是分开的：

- 转换否定，[Fail Definition … := eq_refl]，断言两个类型良好的项在定义上不相等；
- 可形成性否定，[Fail Check]，断言一个表达式根本无法展开。

仪器状态：在批处理模式下，成功的 [Fail] 不会打印任何内容，而没有失败的 [Fail] 会以“命令没有失败！”中止文件，所以绿色构建是真实的证据。
*)

(** ** Positive controls: what IS definitional / ** 阳性对照：什么是定义性的 *)

Section Controls.

Context {C : Category}.
Context {x y z : C} (f : x ~> y) (g : x ~> z).

(*
The bundled/pinned round trip is a field repackaging both ways, so it
   closes on the whole record.  Control for the header's claim that both
   conversions cost nothing.

--------
捆绑/固定的往返是一个双向字段重新打包，因此它会关闭整个记录。 控制标题中关于两次转换都不花费的声明。
*)
Definition ctl_roundtrip (P : IsPushout f g) :
  is_pushout_square_pushout (pushout_is_pushout_square f g P) = P := eq_refl.

(* [IsCokernelPair] IS [IsPushoutSquare] at a repeated leg. / [IsCokernelPair] 在重复的腿上是 [IsPushoutSquare]。 *)
Definition ctl_ckp_is_square (P : C) (u v : y ~> P) :
  IsCokernelPair f P u v = IsPushoutSquare f f P u v := eq_refl.

(*
Controls for negative 2 below.  Without these, renaming either leg of
   the round trip would make that [Fail] pass VACUOUSLY, which the header's
   blanket guarantee forbids; an audit found exactly that gap.

--------
针对-2以下的控制。没有这些控制，重命名往返行程的任一条腿都会使[Fail]虚空地通过，而头文件的全面保证是禁止的；一次审计正好发现了这个漏洞。
*)
Definition ctl_epic_pushout_square (E : Epic f) := epic_pushout_square f E.
Definition ctl_pushout_square_epic (S : IsPushoutSquare f f y id id) :=
  pushout_square_epic f S.

(*
The duality collapse that carries every [Monic] statement of the target
   file.  Control for [op_collapse_pushout_square].

--------
承载目标文件每个 [Monic] 语句的二元性崩溃。控制 [op_collapse_pushout_square]。
*)
Definition ctl_op_collapse :
  @IsPushoutSquare (C^op) y x x f f x id id
    = @IsPullback C x x y f f x id id := eq_refl.

(* The chosen cokernel pair's legs ARE the chosen pushout's injections. / 所选余核对的两条腿就是所选推断的注入。 *)
Definition ctl_ckp_left `{H : @HasPushouts C} :
  ckp_left (cokernel_pair f) = pushout_in1 (pushout f f) := eq_refl.

(*
Control for formability negative 4: the pinned form DOES take an apex
   and two legs, and the bundled form IS formable on the span alone.

--------
可成形性控制负4：固定形式确实有顶点和两条边，而捆绑形式仅靠跨度本身即可成形。
*)
Check (IsPushoutSquare f f y id id).
Check (IsPushout f f).

(*
Control for conversion negative 1: the two [IsIsomorphism] readings are
   inter-derivable, so what negative 1 refutes is CONVERTIBILITY and not
   the mathematics.

--------
转换负1的控制：两个[IsIsomorphism]读数是可相互推导的，所以负1所反驳的是可转换性，而不是数学本身。
*)
Check (@IsIsomorphism_of_op C x y).
Check (@op_IsIsomorphism_of C x y).

End Controls.

Section SetsControls.

Context {A B Q : SetoidObject}.
Context (f : A ~{Sets}~> B) (q1 q2 : B ~{Sets}~> Q).
Context (Hc : q1 ∘[Sets] f ≈ q2 ∘[Sets] f).

(*
Control for conversion negative 3, and the sharp diagnosis: the two
   sides of the left triangle agree POINTWISE at Leibniz equality.  So
   what negative 3 refutes is the equality of [SetoidMorphism] RECORDS —
   the composite rebuilds its [proper_morphism] certificate — and not any
   disagreement of the underlying functions.

--------
控制转换负3，以及尖锐的诊断：左三角形的两边在莱布尼茨等式处点对点一致。因此，负3否定的是[SetoidMorphism]记录的等式——复合体重建了它的[proper_morphism]证书——而不是底层函数的任何不一致。
*)
Definition ctl_sets_triangle_pointwise (b : carrier B) :
  (sets_ck_med f q1 q2 Hc ∘[Sets] ck_left f) b = q1 b := eq_refl.

Definition ctl_sets_triangle_pointwise_r (b : carrier B) :
  (sets_ck_med f q1 q2 Hc ∘[Sets] ck_right f) b = q2 b := eq_refl.

End SetsControls.

(*
Control for formability negatives 5-7: a category whose hom universe is
   STRICTLY below its proof universe is itself perfectly formable, and its
   hom-sets can be named.  So the rejections below are attributable to the
   named constants and not to the section's own declarations.

--------
控制可形成性负面 5-7：一个同构宇宙严格低于其证明宇宙的类别本身是完全可形成的，并且其同构集可以被命名。因此，下面的拒绝是由命名常数引起的，而不是由本节自己的声明引起的。
*)
Section SeparatedUniverseControl.

Universes uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).
Context (x y : C) (f : x ~> y).

Check (x ~> y).
Check f.

End SeparatedUniverseControl.

(** ** CONVERSION negatives / ** 转化否定 *)

Section ConversionNegatives.

Context {C : Category}.
Context {x y : C} (f : x ~> y).
Context (a b : C) (h : b ~> a).

(*
1. [IsIsomorphism] at C^op is NOT the C reading on the nose.  Both
      records carry the same inverse, but their two law fields are
      SWAPPED, so the conversion is a field permutation and the header
      says so rather than claiming [eq_refl].
      Stripped: "cannot unify @IsIsomorphism C^op a b h and
      @IsIsomorphism C b a h" — a conversion failure.

--------
1. C^op 上的 [IsIsomorphism] 并不是精确的 C 读取。两个记录都携带相同的逆，但它们的两个关联字段被交换了，因此转换是字段置换，并且头部说明了这一点，而不是声称 [eq_refl]。
精简信息："无法统一 @IsIsomorphism C^op a b h 和 @IsIsomorphism C b a h" — 转换失败。
*)
Fail Definition neg_iso_op :
  @IsIsomorphism (C^op) a b h = @IsIsomorphism C b a h := eq_refl.

(*
2. The [Epic] ↔ pushout-square passage does NOT round-trip on the nose.
      [pushout_square_epic] rebuilds the cancellation field out of the
      mediator's [unique_property], so the recovered [Epic] is a different
      term even though [Epic] has primitive projections with eta.
      Stripped: "cannot unify pushout_square_epic f (epic_pushout_square f
      E) and E" — a conversion failure.

--------
2. [Epic] ↔ 推出方格通道并不能原样双向转换。
      [pushout_square_epic] 会根据中介者的 [unique_property] 重新构建取消字段，因此恢复的 [Epic] 即使 [Epic] 具有带 eta 的原始投影，也是一个不同的项。
      简化："无法统一 pushout_square_epic f (epic_pushout_square f E) 和 E" — 转换失败。
*)
Fail Definition neg_epi_roundtrip (E : Epic f) :
  pushout_square_epic f (epic_pushout_square f E) = E := eq_refl.

End ConversionNegatives.

Section SetsConversionNegatives.

Context {A B Q : SetoidObject}.
Context (f : A ~{Sets}~> B) (q1 q2 : B ~{Sets}~> Q).
Context (Hc : q1 ∘[Sets] f ≈ q2 ∘[Sets] f).

(*
3. The left triangle of the [Sets] cokernel pair is NOT a Leibniz
      equality of MORPHISMS, though it is one pointwise on the underlying
      functions (control above).  The composite rebuilds the
      [proper_morphism] certificate.
      Stripped: "cannot unify sets_ck_med f q1 q2 Hc ∘ ck_left f and q1" —
      a conversion failure.

--------
3. [Sets] 共核对的左三角形不是 MORPHISMS 的莱布尼茨等式，尽管在底层函数上它是逐点的（上方控制）。复合体重建了 [proper_morphism] 证书。删减后的信息：“无法统一 sets_ck_med f q1 q2 Hc ∘ ck_left f 和 q1”——转换失败。
*)
Fail Definition neg_sets_triangle :
  sets_ck_med f q1 q2 Hc ∘[Sets] ck_left f = q1 := eq_refl.

End SetsConversionNegatives.

(** ** FORMABILITY negatives / ** 可成形性缺点 *)

Section FormabilityNegatives.

Context {C : Category}.
Context {x y : C} (f : x ~> y).

(*
4. THE HEADER'S CENTRAL STRUCTURAL CLAIM.  Structure/Pushout.v's
      [IsPushout] is BUNDLED despite the [Is] prefix: it carries its apex
      as data and takes only the two span legs, so it cannot be applied to
      a GIVEN apex and a GIVEN pair of cocone legs.  That is why the
      epimorphism characterization — a statement about ONE square — was
      not expressible before [IsPushoutSquare], and why the issue's
      suggested spelling could not be used.
      Stripped: "Illegal application (Non-functional construction): the
      expression IsPushout f f of type Type cannot be applied to the term
      y" — a typing error, not a universe inconsistency.

--------
4. 页眉的核心结构声明。Structure/Pushout.v 的 [IsPushout] 是捆绑的，尽管有 [Is] 前缀：它将其顶点作为数据携带，并且只接受两个跨度边，因此它不能应用于给定的顶点和给定的余锥边。这就是为什么表态关于一个方格的满射表征在 [IsPushoutSquare] 之前无法表达，以及为什么无法使用该问题建议的拼写方式。简化为：“非法应用（非函数式构造）：类型为 Type 的表达式 IsPushout f f 不能应用于项 y”——这是一个类型错误，而不是宇宙不一致。
*)
Fail Check (IsPushout f f y id id).

End FormabilityNegatives.

(*
Negatives 5-9 measure a DONOR universe pin and attribute it PER DONOR
   rather than to the family as a whole.  The category below has its hom
   universe STRICTLY below its proof universe; the control section above
   shows such a category is perfectly formable and its hom-sets nameable,
   so the rejections are attributable to the named constants.

   Each of [Epic] (Theory/Morphisms.v), [Pullback] (Structure/Pullback.v),
   [IsPullback] (Theory/Morphisms/Stability.v) and [IsPushout]
   (Structure/Pushout.v) INDEPENDENTLY identifies hom with proof, and
   [IsPushoutSquare] inherits the identification — it introduces none of
   its own.  Every one was stripped and reports
   "universe inconsistency: Cannot enforce vp = vh because vh < vp",
   a genuine universe inconsistency and not a typing error (contrast
   negative 4, which IS a typing error).

--------
负例 5-9 测量的是 DONOR 宇宙针并将其属性按每个 DONOR 而不是整个家族进行分配。下面的类别其同态宇宙严格低于其证明宇宙；上面的控制部分显示这样一个类别是完全可构造的，并且其同态集可以命名，因此拒绝归因于命名的常量。

[Epic]（Theory/Morphisms.v）、[Pullback]（Structure/Pullback.v）、[IsPullback]（Theory/Morphisms/Stability.v）和 [IsPushout]（Structure/Pushout.v）各自独立地将 hom 与 proof 识别为同一，并且 [IsPushoutSquare] 继承了这种识别 — 它没有引入自己的。每一个都被剥离并报告“宇宙不一致：无法强制 vp = vh，因为 vh < vp”，这是一个真正的宇宙不一致，而不是类型错误（与负例 4 对比，负例 4 是类型错误）。
*)

Section UniverseNegatives.

Universes vo vh vp.
Constraint vh < vp.

Context (C : Category@{vo vh vp}).
Context (x y : C) (f : x ~> y).

(* 5. the [Epic] donor, Theory/Morphisms.v / 5. [Epic] 捐赠者，Theory/Morphisms.v *)
Fail Check (@Epic C x y f).

(* 6. the [Pullback] donor, Structure/Pullback.v / 6. [Pullback] 捐赠者，Structure/Pullback.v *)
Fail Check (@Pullback C x x y f f).

(* 7. the [IsPullback] donor, Theory/Morphisms/Stability.v / 7. [IsPullback] 捐赠者, Theory/Morphisms/Stability.v *)
Fail Check (@IsPullback C x x y f f x id id).

(* 8. the [IsPushout] donor, Structure/Pushout.v / 8. [IsPushout] 捐赠者，Structure/Pushout.v *)
Fail Check (@IsPushout C x y y f f).

(* 9. inherited by the pinned pushout square / 9. 由固定的推出平方继承 *)
Fail Check (@IsPushoutSquare C x y y f f y id id).

End UniverseNegatives.
