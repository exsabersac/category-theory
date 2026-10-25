Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Chain.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Chain.

Generalizable All Variables.

(** * Probe: strength boundaries of Sets cocompleteness / * 探测：集合余完备性的强度边界 *)

(*
Guard file for Instance/Sets/Cocomplete.v and Instance/Sets/Chain.v,
   in the Test/ProbeFunnyPoly.v convention.  The import list is the UNION
   of both targets, plus Instance/Sets/Complete.v for the duality
   negative.

   PROBE-HYGIENE WARNING, MEASURED DURING THE WORK AND RECORDED HERE SO
   IT IS NOT REDISCOVERED: writing the duality negative as
   [Sets_Complete (D^op) (F^op)] is a FALSE PASS.  Functor/Opposite.v
   opens [functor_scope], so [D^op] parses as [Opposite_Functor D] and
   the command fails with a NOTATION error -- "D has type Category while
   it is expected to have type ?C ⟶ ?D" -- rather than with the
   mathematics.  A [Fail] that succeeds for that reason measures
   nothing.  Both opposites are therefore spelled by NAME below.

   Every negative is paired with a positive control NAMING ITS OWN
   CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
   constants appearing in the NEGATIVES -- the wider check, re-run after
   each control was added.  MEASURED SCORE, counted rather than recalled:
   the three negatives name EIGHT distinct constants ([Sets_Complete],
   [Opposite], [Opposite_Functor], [Sets_colim_obj], [Sets_colim_sum],
   [Sets_colim_med], [Sets_colim_inj], [vertex_map]) and all EIGHT are
   guarded, 8/8.  An earlier revision of this file claimed "13/13", a
   figure matching no countable set here -- and it was claimed while
   [Opposite] was in fact unguarded and only two of the three negatives
   were shipped, so the number was wrong in both factors.

--------
Instance/Sets/Cocomplete.v 和 Instance/Sets/Chain.v 的守护文件，使用 Test/ProbeFunnyPoly.v 的约定。导入列表是两个目标的并集，再加上用于对偶负性的 Instance/Sets/Complete.v。

探针卫生警告，在工作过程中测量并记录在此，以免被重新发现：将双重性负写作 [Sets_Complete (D^op) (F^op)] 是一个错误通过。Functor/Opposite.v 打开 [functor_scope]，因此 [D^op] 解析为 [Opposite_Functor D]，并且命令因 NOTATION 错误而失败——“D 的类型是 Category，而期望的类型是 ?C ⟶ ?D”——而不是因为数学原因。出于这个原因成功的 [Fail] 什么也没有测量。因此，下面的两个对立项都是通过 NAME 拼写的。

每个阴性样本都与一个阳性对照配对，并为其命名自己的常量，并且通过在阴性样本中出现的常量上运行重命名模拟进行了配对验证——这是一个更广泛的检查，在每添加一个对照后重新运行。测量得分是计数而非回忆：三个阴性样本命名了八个不同的常量（[Sets_Complete]、[Opposite]、[Opposite_Functor]、[Sets_colim_obj]、[Sets_colim_sum]、[Sets_colim_med]、[Sets_colim_inj]、[vertex_map]），且所有八个常量都受到保护，8/8。本文件的早期版本声称“13/13”，该数字与此处可计数的集合不符——当时声称的同时，[Opposite]实际上没有受到保护，并且三个阴性样本中只有两个被发出，所以该数字在两个方面都是错误的。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** No duality shortcut from Sets_Complete

    [Colimit F := Limit (F^op)] is definitional, which makes it tempting
    to think completeness of [Sets] hands over cocompleteness.  It does
    not: [F^op] lands in [Sets^op], not [Sets], and what would give the
    colimit is [Complete (Sets^op)] -- which IS [Cocomplete Sets] again.
    This is a TYPING negative, not a conversion one.

--------
** 从 Sets_Complete 没有二元性捷径

[Colimit F := Limit (F^op)] 是定义性的，这让人很容易认为 [Sets] 的完备性会传递到余完备性。但事实并非如此：[F^op] 落在 [Sets^op]，而不是 [Sets]，而能给出余极限的是 [Complete (Sets^op)] —— 它又是 [Cocomplete Sets]。这是一个类型负面，而不是转换负面。
*)

Section DualityNegative.

Context (D : Category) (F : D ⟶ Sets).

Fail Check (Sets_Complete (Opposite D) (Opposite_Functor F)).

(*
Positive controls naming their own constants: completeness applies at
   the ORIGINAL diagram, and the colimit is a limit of the opposite
   functor -- so the refusal above is about which category the opposite
   functor lands in, not about the constants being unusable.

--------
正控制命名它们自己的常数：完整性适用于原始图，并且余极限是对偶函子（opposite functor）的极限——所以上面的拒绝是关于对偶函子落入哪个范畴，而不是关于常数不可用。
*)
Check (Sets_Complete D F).

Check (Sets_Colimit F).

(*
Control naming [Opposite_Functor] itself.  The rename simulation over
   the constants in the NEGATIVES found it named by no control -- it
   occurs only inside the Fail above -- so that negative would have gone
   vacuously green on a rename.  Recorded rather than quietly added.

--------
控制命名 [Opposite_Functor] 本身。对 NEGATIVES 中的常量进行重命名模拟时，发现它没有被任何控制命名——它只出现在上面的 Fail 中——所以该负值在重命名时本会徒然变为绿色。记录而不是悄悄添加。
*)
Check (Opposite_Functor F).

(*
Control naming [Opposite] -- the CATEGORY opposite -- itself.  The
   audit re-ran the simulation and found it named by no control: it too
   occurs only inside the Fail above, in the SAME expression, so the fix
   recorded just above had been applied to only one of that line's two
   opposites.  Renaming [Opposite] left this file compiling clean while
   the negative passed on a "reference not found" error rather than on
   the mathematics -- the very false-pass mode this header warns about.

--------
控制命名 [Opposite] —— 与之相对的 CATEGORY —— 自身。
审计重新运行了模拟，发现没有任何控制对其进行了命名：它也只出现在上面的 Fail 中，在同一个表达式中，因此刚刚记录的修复仅应用到该行的两个相对项中的一个。重命名 [Opposite] 后，该文件可以正常编译，而负测试则因“未找到引用”错误而未出现数学错误 —— 这正是该头文件所警告的错误通过模式。
*)
Check (Opposite D).

End DualityNegative.

(**
** The apex is not the coproduct on the nose

    The colimit apex and the indexed coproduct share a CARRIER but
    differ in [is_setoid] -- the apex carries the coarser generated
    relation.  That difference is the whole construction, so the
    negative and its control together say exactly what the quotient
    adds.

--------
** 顶点并不是字面上的余积

极限顶点和索引余积共享一个承载体，但在 [is_setoid] 上有所不同 —— 顶点携带了更粗的生成关系。这个差异就是整个构造，因此负态及其控制一起完全说明了商加上了什么。
*)

Section ApexNegative.

Context (D : Category) (F : D ⟶ Sets).

Fail Definition probe_apex_is_sum :
  Sets_colim_obj F = Sets_colim_sum F := eq_refl.

End ApexNegative.

(*
Positive controls naming Cocomplete.v's own constants: the carriers DO
   agree by eq_refl, and the apex equivalence IS the generated relation.

--------
阳性对照命名 Cocomplete.v 自己的常量：载体确实通过 eq_refl 同意，并且顶点等价就是生成的关系。
*)
Check Sets_colim_carrier_is_coproduct.
Check Sets_colim_equiv_is_rel.
Check Sets_colim_obj.
Check Sets_colim_sum.

(**
** Negative 3: the triangle as a Leibniz equality of WHOLE morphisms

    Conversion negative.  The triangle holds POINTWISE ([Sets_colim_triangle],
    an [Example] in Cocomplete.v), but the composite rebuilds a
    [proper_morphism] certificate, so the two whole morphisms do not
    convert.  Measured in Cocomplete.v's header since it was written and
    pinned NOWHERE until the audit found the gap.

--------
** 负面 3：作为整体态射的莱布尼茨等式的三角形

    转换为负面。三角形在点上成立（[Sets_colim_triangle]，Cocomplete.v 中的一个 [Example]），但是复合重建了一个 [proper_morphism] 证书，因此两个整体态射不能转换。自从 Cocomplete.v 的头文件编写以来一直被测量，并且在审计发现该漏洞之前没有固定在任何地方。
*)

Section TriangleNegative.

Context (D : Category) (F : D ⟶ Sets) (N : Cocone F) (d : obj[D]).

Fail Definition probe_triangle_whole_morphism :
  Sets_colim_med F N ∘ Sets_colim_inj F d = vertex_map[N] := eq_refl.

End TriangleNegative.

(*
Positive controls naming the negative's own constants.  [vertex_map] is
   guarded twice over: by this control, and because renaming it breaks the
   [vertex_map[N]] NOTATION into a syntax error, which [Fail] does not
   catch -- so that one would fail loudly even with no control at all.

--------
正向控制命名负向自身的常量。[vertex_map] 被双重保护：通过这个控制，并且因为重命名它会使 [vertex_map[N] 符号变成语法错误，而 [Fail] 不会检测到——所以即使没有任何控制，那一个也会明显失败。
*)
Check Sets_colim_med.
Check Sets_colim_inj.
Check @vertex_map.

(**
** Non-vacuity, guarded

    These are the two halves that keep the construction from being
    empty.  READ THE SCOPE: each is a fact about ONE shape, not a
    general non-collapse theorem, and both target headers say so.

--------
** 非空性，受保护的

    这两部分是防止构造为空的关键。请阅读范围：每一部分都是关于**一个形状**的事实，而不是一个一般的非塌陷定理，并且两个目标标题都说明了这一点。
*)

(*
The quotient does not collapse: at the two-object discrete shape the
   two fibres stay apart.

--------
商不会塌缩：在两个对象的离散形状上，两条纤维保持分离。
*)
Check two_fibres_not_collapsed.

Check two_fibres_not_equal_in_colimit.

Check two_disc_objects_distinct.

Check two_disc_hom_is_eq.

Check colim_rel_separates.

(*
The quotient does merge: at the omega shape, stages 0 and 1 are
   identified in the colimit while the coproduct keeps them apart.  A
   discrete shape has no connecting maps and so could not witness this.

--------
商确实会合并：在欧米茄形状下，第 0 阶段和第 1 阶段在余极限中被识别，而余积则将它们分开。离散形状没有连接映射，因此无法见证这一点。
*)
Check omega_stages_merged.

Check omega_stages_apart_in_coproduct.

(* The degenerate control, labelled as one in its own file. / 退化控制，在其自己的文件中标记为一。 *)
Check empty_shape_colim_empty.

(** ** The headline artifacts / ** 头条文物 *)

Check Sets_Cocomplete.

Check Sets_Omega_Colimit.

Check Sets_Chain_Colimit.

Check Sets_colim_triangle.
