Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Instance.Cat.Pullback.

Generalizable All Variables.

(* Boundary probe for Construction/Slice/Adjunction.v (issue #365). / 用于 Construction/Slice/Adjunction.v 的边界探针（问题 #365）。 *)

(*
This file exists for what an in-file [Fail] cannot do: an in-file
   negative is renamed in lockstep with the constant it guards, so it
   cannot detect a rename.  The [Require] list above is the target's own,
   verbatim, plus four additions that the target does not need:
   Construction/Comma.v and Construction/Opposite.v (both already in the
   target's transitive closure, named here for the route and orientation
   negatives below), Construction/Slice/Adjunction.v (the target itself)
   and Instance/Cat/Pullback.v (for the prior-art agreement checks; its
   own module closure is 39, and requiring it from the target would add
   14 modules to the target's 31 -- measured with coqdep, and the reason
   the target does not).  A short prefix of a target's imports is what
   makes a probe pass vacuously, so the mirroring is deliberate.

   TWELVE negatives of THREE KINDS, kept lexically apart, plus one
   scope-free instrument check (thirteen [Fail] commands in all).  Each was
   stripped ONE AT A TIME, with the others left intact, compiled alone,
   and its whole error read to confirm where it fires and what kind it
   is.  This repo's [coqc] emits nothing for a [Fail] that succeeds, so
   rc=0 with every [Fail] intact is the verification.

   Six FORMABILITY negatives end "universe inconsistency: Cannot enforce
   up = uh because uh < up".  Five CONVERSION negatives end "cannot
   unify" between two terms of ONE type.  The single TYPING negative
   ALSO ends "cannot unify", so the tail alone does NOT separate it: what
   separates it is that its unification mismatch is between two
   CATEGORIES -- the index arguments of the type former -- and not
   between two inhabitants of one type, with the body reporting one
   whole [Adjunction] type as found and another as expected.  The
   instrument check is itself a plain typing mismatch with no "cannot
   unify" at all.

--------
这个文件的存在是因为文件内的 [Fail] 无法做到的事情：文件内的负值会随着它所守护的常量同步重命名，所以它无法检测到重命名。上面提到的 [Require] 列表是目标自身的原样列表，另外加了四个目标不需要的条目：Construction/Comma.v 和 Construction/Opposite.v（两者都已在目标的传递闭包中，这里命名是为了下面的路线和方向负值）、Construction/Slice/Adjunction.v（目标本身）、以及 Instance/Cat/Pullback.v（用于现有协议检查；其自身的模块闭包为 39，如果从目标中引入会使目标的 31 个模块增加 14 个——用 coqdep 测量过，这也是目标不需要引入的原因）。目标导入的短前缀会让探测测试表面上通过，所以这种镜像是故意的。

三类十二个否定，保持词汇上分开，加上一个无作用域的工具检查（总共十三个 [Fail] 命令）。每一个都被单独剥离，其余保持完整，单独编译，并读取其整个错误以确认它触发的位置及其类型。这个仓库的 [coqc] 对于成功的 [Fail] 不会发出任何信息，因此在每个 [Fail] 保持完整的情况下 rc=0 就是验证。

六个 FORMABILITY 否定以“宇宙不一致：无法强制 up = uh 因为 uh < up”结束。五个 CONVERSION 否定以“无法统一”结束，发生在两项同为 ONE 类型的术语之间。唯一的 TYPING 否定也以“无法统一”结束，所以仅凭尾部不能将其分开：真正将其分开的是它的统一不匹配发生在两个 CATEGORY 之间——类型构造函数的索引参数——而不是在同一类型的两个元素之间，主体报告发现了一个完整的 [Adjunction] 类型，而另一种是预期类型。仪器检查本身只是一个普通的类型不匹配，根本没有“无法统一”。
*)

(** ** Instrument check: the harness reports a genuine rejection / ** 仪器检查：安全带报告了真实的拒绝 *)

Fail Check (1 = true).

(** ** Kind 1 — FORMABILITY: hom and proof universes cannot be split / ** 类型 1 — 可形成性：同类和证明宇宙不能被分割 *)

(*
Every headline constant of the target is stated over
   [C : Category@{u u0 u0}] -- hom IDENTIFIED with proof, by reuse of one
   level variable in the BINDER -- while the constraint blocks carry no
   equation at all, only bounds.  Reading the blocks alone reports "no
   identification" and is wrong.

   The identification is INHERITED, and FIVE donors each force it ALONE.
   Below, a category whose hom universe is declared STRICTLY BELOW its
   proof universe is formable, and so are its hom-sets and identities
   (the controls); every one of [Slice], [Coslice], [Cartesian],
   [IsTerminalObj] and [IsInitialObj] is rejected at those very levels,
   each with "Cannot enforce up = uh because uh < up", and so is the
   target's own [Coslice_Proj], which inherits it from [Coslice].
   Nothing in the target introduces the identification, and none of the
   five is claimed unavoidable.

--------
目标的每个头部常量都通过 [C : Category@{u u0 u0}] 声明为同态 IDENTIFIED 并附有证明，通过在 BINDER 中重用一个层变量实现——而约束块本身不携带任何方程，仅有边界。仅读取这些块会报告“无识别”，这是错误的。

该识别是继承的，每个五个捐赠者都单独强制它。下面是一个类别，其同态宇宙被声明严格低于其证明宇宙，它是可形成的，其同态集合和恒等式（控件）也是可形成的；[Slice]、[Coslice]、[Cartesian]、[IsTerminalObj] 和 [IsInitialObj] 的每一个在这些层次上都被拒绝，每个都显示“无法强制 up = uh 因为 uh < up”，目标自身的 [Coslice_Proj] 也被拒绝，它从 [Coslice] 继承了该识别。目标中没有任何内容引入该识别，且没有人声称这五个是不可避免的。
*)

Section UniverseBoundary.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : Cu).

(*
Controls: the category, its hom-sets and its identities all elaborate
   with the two levels declared strictly apart.

--------
控制：该范畴、它的同态集及其恒等元皆通过严格分开的两个层次详尽阐述。
*)
Check Cu.
Check (xu ~> yu).
Check (id[xu]).

(* Negative 1 (formability): the slice construction. / 负 1（可成型性）：切片结构。 *)
Fail Check (@Slice Cu xu).

(* Negative 2 (formability): the coslice construction. / 负 2（可形成性）：余切片结构。 *)
Fail Check (@Coslice Cu xu).

(*
Negative 3 (formability): the cartesian class -- hence also
   [Cocartesian], which is that class read at the opposite category.

--------
负3（可形成性）：笛卡尔类——因此也包括 [Cocartesian]，它是该类在对立范畴下的读取。
*)
Fail Check (@Cartesian Cu).

(* Negative 4 (formability): the object-level terminality predicate. / 负4（可形成性）：对象层级终结谓词。 *)
Fail Check (@IsTerminalObj Cu xu).

(* Negative 5 (formability): its initial dual. / 负 5（可成型性）：它的初始二重性。 *)
Fail Check (@IsInitialObj Cu xu).

(*
Negative 6 (formability): the target's own projection functor, which
   inherits the identification from [Coslice] and adds nothing.

--------
负6（可形成性）：目标自身的投射函子，它继承了来自 [Coslice] 的身份认同，并且没有添加任何东西。
*)
Fail Check (@Coslice_Proj Cu xu).

End UniverseBoundary.

(** ** Kind 2 — CONVERSION / ** 类型 2 — 转换 *)

Section Conversion.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context {CA : @Cartesian C}.
Context (a : C).

(*
Controls for negative 7: the unit of the delivered adjunction IS the
   right injection with one [id_left] residue in front of it, and that
   residue is exhibited literally rather than described.

--------
对负7的控制：所传递附加物的单位是带有一个 [id_left] 残基在前的右注入，并且该残基是以字面方式展示的，而不是被描述的。
*)
Example ctrl_unit_residue (c : C) :
  @unit (@Coslice C a) C (Coslice_Coprod a) (Coslice_Proj a)
    (Coslice_Projection_Adjunction a) c
    = id ∘ @coslice_projection_unit C CC a c := eq_refl.

Check @coslice_unit_strict.
Check @coslice_unit_is_inr.
Check @coslice_projection_unit.

(*
Negative 7 (conversion): the class-produced unit is NOT the bare
   injection on the nose.  [unit] is [⌊id⌋], and the forward transpose
   post-composes with [inr]; the identity of the coslice is carried by
   [id] of C, so what comes out is [id ∘ inr].  The [≈] form is the
   target's [coslice_unit_is_inr], one [id_left] away.

--------
负7（转换）：类生成的单元不是鼻子上的裸注射。[unit] 是 [⌊id⌋]，并且前向换位与 [inr] 后组合；余切片的同一性由 C 的 [id] 承载，所以输出的是 [id ∘ inr]。[≈] 形式是目标的 [coslice_unit_is_inr]，相差一个 [id_left]。
*)
Fail Example neg_unit_is_inr (c : C) :
  @unit (@Coslice C a) C (Coslice_Coprod a) (Coslice_Proj a)
    (Coslice_Projection_Adjunction a) c
    = @coslice_projection_unit C CC a c := eq_refl.

(*
Controls for negative 8: the slice counit carries the mirror-image
   residue, on the OTHER side.

--------
负8的控制：切片余单位携带镜像残基，在另一侧。
*)
Example ctrl_counit_residue (y : C) :
  @counit C (@Slice C a) (Slice_Proj a) (Slice_Prod a)
    (Slice_Projection_Adjunction a) y
    = @slice_projection_counit C CA a y ∘ id := eq_refl.

Check @slice_counit_strict.
Check @slice_counit_is_exl.
Check @slice_projection_counit.

(*
Negative 8 (conversion): the class-produced counit is NOT [exl] on the
   nose.  [counit] is [⌈id⌉], and the backward transpose pre-composes
   with the given slice arrow, which here is the identity of C.

--------
负 8（转换）：类生成的余单位在正点上不是 [exl]。[counit] 是 [⌈id⌉]，并且向后转置与给定的切片箭头预组合，这里的切片箭头是 C 的恒等映射。
*)
Fail Example neg_counit_is_exl (y : C) :
  @counit C (@Slice C a) (Slice_Proj a) (Slice_Prod a)
    (Slice_Projection_Adjunction a) y
    = @slice_projection_counit C CA a y := eq_refl.

End Conversion.

Section Orientation.

Context {C : Category}.
Context (a : C).

(*
The issue says the slice statement is "one [Opposite] transport away".
   It is not, on the nose.  The OBJECT types do agree definitionally --
   both are the arrows out of [a] -- which is what makes the negative
   below a statement about the hom EQUATIONS and not about the encoding
   at large.

--------
该问题指出切片语句是“离一个 [Opposite] 传输”。
   实际上并非如此。对象类型在定义上确实一致——
   两者都是 [a] 的箭头——这就是下面的否定
   是关于同态方程的声明，而不是关于整体编码的声明。
*)
Example ctrl_orientation_objects :
  obj[@Coslice C a] = obj[Opposite (@Slice (Opposite C) a)] := eq_refl.

Check @Coslice.
Check @Slice.
Check @Opposite.

(*
Negative 9 (conversion): [Coslice C a] is not [(Slice (C^op) a)^op].
   Unfolding, the opposite of the slice over C^op has homs
   [∃ f, f ∘ `2 x ≈ `2 y] where [Coslice] has [∃ f, `2 y ≈ f ∘ `2 x] --
   the same equation in the other ORIENTATION, hence a different type.
   Construction/Slice/Terminal.v already records exactly this,
   as its reason for proving [Coslice_Initial] directly rather than
   transporting [Slice_Terminal]; the target's Block B is built directly
   for the same reason, which is also what keeps [^op] out of every
   delivered slice-side type.

--------
负 9（转换）：[Coslice C a] 不是 [(Slice (C^op) a)^op]。
展开后，C^op 上切片的对偶有同态 [∃ f, f ∘ `2 x ≈ `2 y]，其中 [Coslice] 具有 [∃ f, `2 y ≈ f ∘ `2 x] —— 在另一种方向上的方程相同，因此类型不同。Construction/Slice/Terminal.v 已经准确记录了这一点，作为直接证明 [Coslice_Initial] 的理由，而不是传递 [Slice_Terminal]；目标的 Block B 也是出于同样的原因直接构建的，这也是使 [^op] 不出现在每一个已交付切片端类型中的原因。
*)
Fail Example neg_coslice_is_op_slice :
  @Coslice C a = Opposite (@Slice (Opposite C) a) := eq_refl.

End Orientation.

Section PriorArt.

Context {C : Category}.
Context (a : C).

(*
PRIOR ART.  The issue's Awodey section says of the slice domain
   functor that "the functor itself does not exist".  That is FALSE:
   Instance/Cat/Pullback.v [Slice_proj] and [Coslice_proj] are
   exactly this record, and Construction/Slice/Terminal.v's
   [Slice_Forget]/[Coslice_Forget] are its specialisations to a terminal
   and an initial object.  The target rebuilds it rather than requiring
   Instance/Cat/Pullback.v, whose module closure is far heavier; the
   agreement is measured HERE, where that file is already loaded.

   Both DATA fields agree on the nose, in both handednesses.

--------
现有技术。 Awodey 在本期刊中关于 slice 域函子的问题部分中说“该函子本身不存在”。这是错误的：Instance/Cat/Pullback.v 中的 [Slice_proj] 和 [Coslice_proj] 正是这个记录，而 Construction/Slice/Terminal.v 中的 [Slice_Forget]/[Coslice_Forget] 是其到终对象和初对象的特化。目标重新构建它，而不是依赖 Instance/Cat/Pullback.v，其模块闭包要重得多；一致性在此处衡量，该文件已被加载。

两个 DATA 字段在两种方向上都完全一致。
*)

Example ctrl_coslice_proj_fobj (x : @Coslice C a) :
  fobj[@Coslice_Proj C a] x = fobj[@Coslice_proj C a] x := eq_refl.

Example ctrl_coslice_proj_fmap (x y : @Coslice C a)
  (f : x ~{@Coslice C a}~> y) :
  fmap[@Coslice_Proj C a] f = fmap[@Coslice_proj C a] f := eq_refl.

Example ctrl_slice_proj_fobj (x : @Slice C a) :
  fobj[@Slice_Proj C a] x = fobj[@Slice_proj C a] x := eq_refl.

Example ctrl_slice_proj_fmap (x y : @Slice C a)
  (f : x ~{@Slice C a}~> y) :
  fmap[@Slice_Proj C a] f = fmap[@Slice_proj C a] f := eq_refl.

(*
Negative 10 (conversion): the WHOLE records are not equal.  [Functor]
   has five fields; the two data fields agree by the controls above, so
   the difference is confined to the three LAW fields, which are each
   file's own opaque [Program] obligations.

--------
负 10（转换）：整个记录不相等。[Functor] 有五个字段；根据上面的控件，两个数据字段一致，因此差异仅限于三个 LAW 字段，每个字段都是各自文件自身的不透明 [Program] 义务。
*)
Fail Example neg_coslice_proj_record :
  @Coslice_Proj C a = @Coslice_proj C a := eq_refl.

(*
THE ISSUE'S OWN SUGGESTED ROUTE, MEASURED.  Its "Current state" says
   the projection "through [Comma_Coslice] *is* the projection of the
   exercise" -- true as a statement about categories, and the transported
   functor does exist and typecheck ([p365_via_comma] below).  But
   [Comma_Coslice] (Construction/Slice.v) is a [Program Instance]
   whose [to] is written [{| fobj := _; fmap := _ |}], so BOTH data fields
   of the comparison functor are [Program] obligations; nothing about the
   transported functor reduces.  Not even its OBJECT action returns the
   first projection on the nose, which is why the target rebuilds the
   three-line record instead of transporting.

--------
该问题本身建议的路线，已测量。它的“当前状态”显示，投影“通过 [Comma_Coslice] *确实是*练习的投影”——作为关于范畴的陈述，这是正确的，并且传递的函子确实存在并且类型检查通过（见下方 [p365_via_comma]）。但是 [Comma_Coslice]（Construction/Slice.v）是一个 [Program Instance]，其 [to] 被写为 [{| fobj := _; fmap := _ |}]，因此比较函子的两个数据字段都是 [Program] 义务；传递的函子没有任何减少。甚至它的 OBJECT 动作也没有精确返回第一个投影，这就是为什么目标重建三行记录而不是进行传递的原因。
*)

Definition p365_via_comma : @Coslice C a ⟶ C :=
  comma_proj2 ◯ to (Comma_Coslice C a).

Check @p365_via_comma.
Check @comma_proj2.
Check @Comma_Coslice.

(*
Negative 12 (conversion): the transported functor's object action is
   not the first projection on the nose, where the target's
   [Coslice_Proj] has it definitionally (control above:
   [ctrl_coslice_proj_fobj]).

--------
负12（转换）：被传送的函子的对象作用在本质上不是第一个投影，其中目标的 [Coslice_Proj] 在定义上具有它（上方的控制：[ctrl_coslice_proj_fobj]）。
*)
Fail Example neg_via_comma_fobj (x : @Coslice C a) :
  fobj[p365_via_comma] x = `1 x := eq_refl.

End PriorArt.

(** ** Kind 3 — TYPING / ** 类型 3 — 输入 *)

Section Typing.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context (a : C).

(*
Control: the adjunction has the handedness the exercise asks for --
   the coproduct functor on the LEFT, the projection on the RIGHT.

--------
控制：伴随具有练习要求的方向 —— 左边是余积函子，右边是投影。
*)
Check (@Coslice_Projection_Adjunction C CC a
         : Coslice_Coprod a ⊣ Coslice_Proj a).

Check @Coslice_Coprod.
Check @Coslice_Projection_Adjunction.

(*
Negative 11 (typing): the other handedness is a different statement,
   and it is not merely unproved -- the ascription is rejected.

--------
负11（打字）：另一种手性是一个不同的陈述，且它不仅仅是未经证实——这种归因被拒绝了。
*)
Fail Check (@Coslice_Projection_Adjunction C CC a
              : Coslice_Proj a ⊣ Coslice_Coprod a).

End Typing.

(** ** Controls naming every remaining delivered constant / ** 控制命名每一个剩余的已传递常量 *)

Check @Cartesian.
(*
[Cocartesian] is a NOTATION (Structure/Cocartesian.v), not a
   constant, so [Check @Cocartesian.] does not parse -- it reports a
   missing [term] after '@Cocartesian'.  It is named instead by the
   [Context {CC : @Cocartesian C}] lines above, which are succeeding
   commands and serve as its control.

--------
[Cocartesian] 是一个符号（Structure/Cocartesian.v），而不是常量，所以 [Check @Cocartesian.] 无法解析——它会在 '@Cocartesian' 后报告缺少 [term]。它由上面的 [Context {CC : @Cocartesian C}] 行命名，这些行是后续命令，并作为它的控制。
*)
Check @IsTerminalObj.
Check @IsInitialObj.
Check @unit.
Check @counit.
Check @Coslice_proj.
Check @Slice_proj.
Check @Coslice_Proj.
Check @Slice_Proj.
Check @Slice_Prod.
Check @Slice_Projection_Adjunction.
Check @coslice_fmap_is_cover.
Check @slice_fmap_is_split.
Check @coslice_transpose.
Check @slice_transpose.
Check @coslice_adj.
Check @slice_adj.
Check @coslice_projection_counit.
Check @slice_projection_unit.
Check @coslice_counit_strict.
Check @coslice_counit_is_merge.
Check @slice_unit_strict.
Check @slice_unit_is_fork.
Check @slice_id_obj.
Check @coslice_id_obj.
Check @slice_id_IsTerminalObj.
Check @coslice_id_IsInitialObj.
Check @slice_left_adjoint_terminal.
Check @slice_terminal_left_adjoint.
Check @slice_terminal_left_adjoint_adj.
Check @slice_proj_left_adjoint_iff_terminal.
Check @coslice_right_adjoint_initial.
Check @coslice_initial_right_adjoint.
Check @coslice_initial_right_adjoint_adj.
Check @coslice_proj_right_adjoint_iff_initial.
Check @Sets_Coslice_Projection_Adjunction.
Check @Sets_Slice_Projection_Adjunction.
Check @sets_bipoint.
Check @sets_bipoint_l.
Check @sets_bipoint_r.
Check @sets_bipoint_distinct.
Check @sets_point.
Check @sets_bipoint_const.
Check @sets_bipoint_not_terminal.
Check @sets_bipoint_not_initial.
Check @sets_slice_proj_no_left_adjoint.
Check @sets_coslice_proj_no_right_adjoint.
Check @sets_slice_proj_left_adjoint_at_terminal.
Check @sets_coslice_proj_right_adjoint_at_initial.
Check @sets_coslice_transpose_computes.
Check @sets_slice_transpose_is_fork.
Check @sets_slice_transpose_computes.
Check @sets_coslice_unit_not_iso.
Check @slice_terminal_adj.
Check @coslice_initial_adj.
Check @coslice_adj_to.
Check @coslice_adj_from.
Check @slice_adj_to.
Check @slice_adj_from.
