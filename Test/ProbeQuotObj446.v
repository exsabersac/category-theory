Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(**
* Probe for Theory/Subobject/Quotient.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.7
    Definition 3, printed p. 126.  Issue #446.  The witnesses at Sets, Grp
    and FinSet have their own probe, Test/ProbeQuotObjWitnesses446.v; this
    file guards the general theory.

    The import list above is the target file's own import list,
    unabbreviated.  A short prefix is what makes a probe pass vacuously, so
    nothing is trimmed even where a require is redundant.

    Every statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read; a refutation that holds prints nothing under
    this repo's coqc, so a whole-file rc=0 would establish only THAT each
    command does not typecheck and never WHY.  Each negative is classified
    by the error TEXT, under THIS import list:

      CONVERSION  - "The term T has type X while it is expected to have
                    type Y (cannot unify A and B)".
      INSTANCE    - an implicit argument of class type that no instance in
                    scope resolves; the discriminator is the parenthetical
                    "(no type class instance found)".  A bare [Check]
                    TOLERATES such an open evar and succeeds, printing
                    "where ?H : [...]", so every missing-instance negative
                    is a [Definition], and the accepted [Check] is kept
                    beside it as the contrast.

    The instrument check comes first: a name that does not exist, refused
    for a reason unrelated to any boundary.  Every LIBRARY constant a
    negative names appears in a positive control outside any refutation
    command, so that a rename cannot leave a negative refused for
    reference-not-found and therefore vacuously green.

--------
* 探查 Theory/Subobject/Quotient.v

Mac Lane，《为从事数学工作的数学家而写的范畴论》，第二版，第V.7节 定义3，印刷第126页。问题#446。在Sets、Grp和FinSet中的证据者有他们自己的探针，Test/ProbeQuotObjWitnesses446.v；该文件维护一般理论。

上面的导入列表是目标文件自身的导入列表，未缩写。短前缀会使探针形式上通过，因此即使某个 require 是多余的，也不会被修剪。

下面声称被驳斥的每个陈述都已经在本文件的副本中被去掉了驳斥关键字，单独编译，并读取其完整错误；在本仓库的 coqc 下，一个成立的驳斥不会打印任何内容，因此整个文件的 rc=0 只会证明每条命令不能类型检查，但永远不会说明原因。每个否定都根据错误文本，在此导入列表下进行分类：

转换 - “术语 T 的类型是 X，而期望类型是 Y（无法统一 A 和 B）”。
实例 - 类类型的隐式参数，在作用域中没有实例可以解析；区分标志是括号内的“（未找到类型类实例）”。一个裸露的 [Check] 容忍这样的开放 evar 并成功，打印“where ?H : [...]”，所以每个缺失实例的负例都是 [Definition]，并且被接受的 [Check] 被保留在旁边作为对照。

仪器检查首先进行：一个不存在的名称，因为与任何边界无关的原因被拒绝。每个 LIBRARY 常量，一个负名称出现在任何反驳命令之外的正控制中，因此重命名不能因为未找到引用而留下负的拒绝，因此形式上为绿色。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check quot_obj_theory_446_no_such_constant.

(** ** Positive controls: every constant the negatives depend on / ** 阳性对照：每一个负对照所依赖的常数 *)

Check @QuotObj.
Check @SubObj.
Check @quot_cod.
Check @quot_epi.
Check @quot_le.
Check @quot_meet.
Check @quot_join.
Check @monic_op_iff_epic.
Check @Epic.
Check @Monic.
Check @Isomorphism.
Check @to.
Check @Cartesian.
Check @HasPushouts.
Check @HasImages.
Check @quot_equiv_iff_iso.
Check @quot_equiv_of_cod_iso.
Check @quot_le_unfold.
Check @quot_equiv_unfold.
Check @QuotObj_op_is_SubObj.

(** ** Readbacks that HOLD, at the strength stated / ** 按照所述强度保持的回读 *)

Section Readbacks.

Context {C : Category}.
Context {x : C}.

(*
F1: quotient objects of the opposite category ARE subobjects, on the
   nose, because C^op^op is C by reflexivity.

--------
F1：对偶范畴的商对象恰好是子对象，因为通过反身性，C^op^op 就是 C。
*)
Example p446t_op_is_sub : @QuotObj (C^op) x = @SubObj C x := eq_refl.

(*
F2: the covariant reading of the order is definitional -- q ≤ r when
   the epi of q FACTORS THROUGH the epi of r, q being the coarser.

--------
F2：序列的协变理解是定义性的 —— 当 q 的上射通过 r 的上射分解时，q ≤ r，且 q 是较粗的。
*)
Example p446t_le_unfold (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }
  := eq_refl.

(*
The accepted [Check] that the INSTANCE negative N5 is the contrast to:
   with no [HasPushouts C] in scope this succeeds, printing the open evar,
   which is exactly why N5 is a [Definition].

--------
接受的 [Check] 是 INSTANCE 负 N5 的对照：
   在没有 [HasPushouts C] 的情况下，这会成功，打印开放的 evar，
   这正是为什么 N5 是 [Definition]。
*)
Check (fun q r : QuotObj x => quot_meet q r).

End Readbacks.

(** ** Negatives / ** 负面 *)

Section Negatives.

Context {C : Category}.
Context {x y : C}.

(*
N2 -- CONVERSION.  Dropping the ^op on the left of F1: quotient objects
   of C are NOT subobjects of C.  "cannot unify QuotObj x and SubObj x".

--------
N2 -- 转换。在 F1 的左侧放弃 ^op：C 的商对象不是 C 的子对象。“无法统一 QuotObj x 和 SubObj x”.
*)
Fail Definition n2 : @QuotObj C x = @SubObj C x := eq_refl.

(*
N3 -- CONVERSION.  The setoid does not unfold covariantly on the nose:
   [SubObj_Setoid]'s witness at C^op is an isomorphism IN C^op, so the
   naive C-isomorphism spelling is refused, "cannot unify (q ≈ r) and
   ∃ i : quot_cod q ≅ quot_cod r, i ∘ quot_epi q ≈ quot_epi r".  The
   covariant characterization is therefore the LEMMA [quot_equiv_iff_iso]
   at ≈, while [quot_equiv_unfold] (the C^op-isomorphism spelling with the
   composition annotated) is the eq_refl.

--------
N3 -- 转换。集合类在表面上并不协变展开：
   [SubObj_Setoid] 在 C^op 上的证据是 C^op 中的一个同构，因此
   天真的 C-同构表示被拒绝，"无法统一 (q ≈ r) 和
   ∃ i : quot_cod q ≅ quot_cod r, i ∘ quot_epi q ≈ quot_epi r"。  因此协变的表征是 LEMMA [quot_equiv_iff_iso] 在 ≈ 处，而 [quot_equiv_unfold]（带组合注释的 C^op-同构表示）是 eq_refl。
*)
Fail Definition n3 (q r : QuotObj x) :
  (q ≈ r) = { i : quot_cod q ≅ quot_cod r & to i ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

(*
N4 -- CONVERSION.  The order direction: q ≤ r factors q THROUGH r and
   not the other way round.  "cannot unify" against the swapped mediator
   { k : quot_cod q ~> quot_cod r & k ∘ quot_epi q ≈ quot_epi r }.

--------
N4 -- 转换。顺序方向：q ≤ r 因子 q 通过 r，而不是反过来。对调换的中介者 { k : quot_cod q ~> quot_cod r & k ∘ quot_epi q ≈ quot_epi r }，“无法统一”。
*)
Fail Definition n4 (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod q ~> quot_cod r & k ∘ quot_epi q ≈ quot_epi r }
  := eq_refl.

(*
N5 -- INSTANCE, and it must be a [Definition].  The meet is conditional
   on pushouts: "Cannot infer the implicit parameter HP of quot_meet whose
   type is HasPushouts C (no type class instance found)".  The [Check] form
   above is accepted.

--------
N5 -- 实例，并且它必须是一个 [Definition]。会合是基于推卷的条件："无法推断 quot_meet 的隐式参数 HP，其类型为 HasPushouts C（未找到类型类实例）"。上面的 [Check] 形式是被接受的。
*)
Fail Definition n5 (q r : QuotObj x) : QuotObj x := quot_meet q r.

(*
N6 -- CONVERSION.  A direction swap of [monic_op_iff_epic]: its first
   projection goes from Monic in C^op to Epic in C, and the converse
   reading is refused, "cannot unify Epic f and Monic f" (printed with the
   short names in scope on both sides).

--------
N6 -- 转换。[monic_op_iff_epic] 的方向交换：它的第一个投影从 C^op 中的单射变为 C 中的满射，而相反的读法被拒绝，“无法统一满射 f 和单射 f”（在两边作用域内以简短名称打印）。
*)
Fail Definition n6 (f : x ~> y) : @Epic (C^op) y x f → @Monic C x y f :=
  fst (monic_op_iff_epic f).

End Negatives.

Section NoCoimages.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x : C}.

(*
N7 -- INSTANCE.  The join needs a supply of coimages: with products but
   no [HasCoimages C], "Cannot infer the implicit parameter HI of quot_join
   whose type is @HasCoimages C (no type class instance found)" -- which
   also shows that the [HasCoimages] NOTATION participates in class
   resolution.

--------
N7 -- 实例。连接需要提供协像：有乘积，但没有 [HasCoimages C]，“无法推断 quot_join 的隐式参数 HI，其类型为 @HasCoimages C（未找到类型类实例）”——这也表明 [HasCoimages] 符号在类解析中参与。
*)
Fail Definition n7 (q r : QuotObj x) : QuotObj x := quot_join q r.

End NoCoimages.
