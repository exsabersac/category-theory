Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Omega.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.InverseLimit.
Require Import Category.Instance.Rng.Zp.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.
Open Scope category_scope.

(**
* Boundary probes for Instance/Rng/Zp.v

    NINE refutation commands = a scope-free instrument check plus EIGHT
    negatives of THREE kinds, told apart by the error TEXT: four
    CONVERSION (negatives 1-4), two TYPING (negatives 5 and 7, whose
    errors carry no universe clause) and two FORMABILITY (negatives 6 and
    8, whose do).  Each is stripped one at a time in a copy of this WHOLE
    file and compiled alone.  Every constant a negative names is also
    named by a [Check] outside every refutation command, so a rename
    breaks this file at a control line rather than turning a guard
    vacuously green.

--------
* Instance/Rng/Zp.v 的边界探针

九个反驳命令 = 一个无域检查的工具加上八个三种类型的负例，通过错误文本区分：四个转换（负例 1-4），两个类型（负例 5 和 7，其错误不带宇宙条款）和两个可形成性（负例 6 和 8，其错误带宇宙条款）。每个负例会在本文件的副本中一次剥离并单独编译。每个负例所命名的常数也在每个反驳命令之外由 [Check] 命名，因此重命名会在控制行处破坏该文件，而不是使保护形式上变为绿色。
*)

(** ** Instrument: a refutation command must be able to fail / ** 工具：反驳命令必须能够失败 *)

Fail Check probe_zp409_no_such_name.

(** ** Guard block: every constant the negatives name, named outside them / ** Guard block: every constant the negatives name, named outside them / ** 保护块：每个常量都命名为负数，在它们之外命名 *)

Check @dsum.
Check @dadd.
Check @d7.
Check @d5.
Check @ResRing.
Check @ZComm.
Check @dpow.
Check @Int_Ring.
Check @zpd.
Check @zp_const.
Check @mraw.
Check @Zp_digits_iso.
Check @Zp.
Check @DigitSeq.
Check @Isomorphism.
Check @Rng.
Check @Sets.
Check @rig_setoid.
Check @carrier.
Check @mraw_1.
Check @RKills.
Check @ResIdeal.
Check @PrincipalIdeal.
(*
[ResTower] is named by negative 7 and nowhere else; without this
   line a rename of it would turn that guard vacuously green, which
   the rename simulation caught.

--------
[ResTower] 被命名为负 7，并且在其他地方没有命名；如果没有这一行，对它的重命名会使那个守卫虚无地变为绿色，而重命名模拟捕捉到了这一点。
*)
Check @ResTower.

(**
** Negative 1 (CONVERSION): the carry is real

    [Zp_digits_add] is an equation in [ResRing n], NOT at Leibniz equality
    of the partial sums: the carry out of position n is exactly the
    difference.  In base ten at n = 1 the digit-string sum of 7 and 5 has
    partial sum 2 while the integers sum to 12; at n = 2, where the carry
    has been absorbed, the two agree.

--------
** 负 1（转换）：进位是真实的

[Zp_digits_add] 是 [ResRing n] 中的一个方程，而不是部分和的莱布尼茨等式：位置 n 的进位正好是差值。在十进制下，当 n = 1 时，7 和 5 的位数字串和为 2，而整数和为 12；当 n = 2 时，进位已经被吸收，两者一致。
*)

Fail Example probe_carry_leibniz :
  dsum 10%Z (dadd 10%Z d7 d5) 1%nat
    = (dsum 10%Z d7 1%nat + dsum 10%Z d5 1%nat)%Z := eq_refl.

Example probe_carry_control_n1_lhs :
  dsum 10%Z (dadd 10%Z d7 d5) 1%nat = 2%Z := eq_refl.

Example probe_carry_control_n1_rhs :
  (dsum 10%Z d7 1%nat + dsum 10%Z d5 1%nat)%Z = 12%Z := eq_refl.

Example probe_carry_control_n2 :
  dsum 10%Z (dadd 10%Z d7 d5) 2%nat
    = (dsum 10%Z d7 2%nat + dsum 10%Z d5 2%nat)%Z := eq_refl.

(**
** Negative 2 (CONVERSION): the residue relation is coarser than [=]

    The quotient keeps the carrier of the base ring and coarsens only the
    setoid, so a residue equation is NOT an equation of integers.

--------
** 负 2（转换）：剩余类关系比 [=] 要粗。

商只保留基环的载体，并仅使集合等价关系变粗，所以剩余类方程不是整数方程。
*)

Fail Example probe_residue_leibniz :
  (2%Z : carrier (rig_setoid (ResRing ZComm 2%Z 1%nat))) = 0%Z := eq_refl.

(*
AN EARLIER REVISION of this control read [existT _ 1%Z eq_refl].  Since
   the PR "algebraic carriers are sets" (2026-09-17) a quotient ring's
   equality is the propositional TRUNCATION of ideal membership
   (Instance/Rng/Quotient.v's [rquot_rel]), so the witness is wrapped in
   [inhabits].  The negative above is unaffected -- what it pins is that the
   residue relation is coarser than [=], which is still true, and still for
   the same reason.

--------
这个控制的早期修订版本写作 [existT _ 1%Z eq_refl]。自从 PR “代数载体是集合” (2026-09-17) 以来，一个商环的相等性是理想成员资格的命题截断（Instance/Rng/Quotient.v 的 [rquot_rel]），因此见证被包装在 [inhabits] 中。上述否定不受影响——它确定的是剩余关系比 [=] 更粗，这仍然是真的，而且原因仍然相同。
*)
Example probe_residue_control :
  @equiv _ (rig_setoid (ResRing ZComm 2%Z 1%nat)) 2%Z 0%Z
  := inhabits (existT _ 1%Z eq_refl).

(**
** Negative 3 (CONVERSION): the normalisation in [zpd] is load-bearing

    Dividing the representative directly, without first reducing it modulo
    d^(n+1), gives the wrong digit at a negative representative: the
    units digit of −1 in base ten is 9, not −1.

--------
** 负3（转换）：[zpd]中的归一化是承重的

    直接除以代表而不先对其取模 d^(n+1)，会在负代表处得到错误的数字：十进制中−1的个位数字是9，而不是−1。
*)

Fail Example probe_zpd_without_mod :
  ((-1)%Z / (@dpow Int_Ring 10%Z 0%nat))%Z = 9%Z := eq_refl.

Example probe_zpd_without_mod_value :
  ((-1)%Z / (@dpow Int_Ring 10%Z 0%nat))%Z = (-1)%Z := eq_refl.

Example probe_zpd_control :
  zpd 10%Z (zp_const 10%Z (-1)%Z) 0%nat = 9%Z := eq_refl.

(**
** Negative 4 (CONVERSION): [mraw] is the convolution, not the
       pointwise product

--------
** 负4（转换）：[mraw] 是卷积，而不是逐点乘积
*)

Fail Example probe_mraw_pointwise (a b : nat -> Z) :
  mraw a b 1%nat = (a 1%nat * b 1%nat)%Z := eq_refl.

(**
** Negative 5 (TYPING): the bijection is in [Sets], not in [Rng]

    No ring structure is put on digit strings, so [DigitSeq p] is an
    object of [Sets] and not of [Rng]; the correspondence of the
    operations is [Zp_digits_add] and [Zp_digits_mul] instead.

--------
** 负 5（打字）：双射在 [Sets] 中，而不在 [Rng] 中

    数字字符串上没有放置环结构，因此 [DigitSeq p] 是 [Sets] 的对象，而不是 [Rng] 的对象；操作的对应关系是 [Zp_digits_add] 和 [Zp_digits_mul]。
*)

Fail Check (fun (p : Z) (Hp : (1 < p)%Z) =>
  (Zp_digits_iso p Hp : @Isomorphism Rng (Zp ZComm p) (DigitSeq p))).

Check (fun (p : Z) (Hp : (1 < p)%Z) =>
  (Zp_digits_iso p Hp
     : @Isomorphism Sets (rig_setoid (Zp ZComm p)) (DigitSeq p))).

(**
** Negatives 6-7: where the ring's three universes are identified

    Sections (A)-(B) do NOT identify the ambient ring's carrier, relation
    and proof universes: [PrincipalIdeal], [ResIdeal] and [ResRing] are
    all formable at a ring whose three levels are declared strictly apart.
    Everything from [res_kills] on -- the first constant to mention
    [Rng] -- carries the identification.  THE DONOR IS [Rng] ITSELF, NOT
    [RKills], and a first draft of this comment said otherwise:
    [Instance/Rng.v]'s [Rng := Ring] has [obj] at
    [RingObject@{u u u}], so [R : obj[Rng]] alone is refused at these
    levels with the IDENTICAL error and no [RKills] in the command
    (negative 8); and [RKills]'s own type mentions [R ~{Rng}~> K], so it
    cannot be tested apart from that -- negative 6's error fires at its
    [R] ARGUMENT, the already-refused-argument trap.  What the three
    controls below DO discriminate is that sections (A)-(B) are free of
    the identification; they attribute it to nothing.

    Read the two kinds apart: negative 8 is FORMABILITY (its error ends in
    a universe clause, "Cannot enforce rr = ro because ro < rr"), while
    negatives 6 and 7 are TYPING -- elaboration refuses the section's
    [RingObject]/[RingComm] instance where the all-equal one is wanted,
    with no universe clause at all.

    AN EARLIER REVISION of this paragraph assigned the FORMABILITY reading
    to negative 6 and the TYPING reading to negative 7 alone.  Re-measured
    at the PR "algebraic carriers are sets" (2026-09-17), by stripping each
    [Fail] in a copy of this whole file: negative 6 now reports

      The term "R" has type "RingObject@{rp ro rr}" while it is expected
      to have type "RingObject@{u u u}"

    -- one fresh universe repeated three times, printed under whatever name
    the enclosing module gives it -- with no universe clause, so it reads
    as TYPING and not as FORMABILITY;
    negative 7 reports the same shape at [RingComm]; and negative 8 still
    ends in "(universe inconsistency: Cannot enforce rr = ro because
    ro < rr)".  What each negative PINS is unchanged -- the identification
    is still [Rng]'s and still absent from sections (A)-(B) -- only the
    error kinds were misattributed.

--------
** 底片6-7：识别戒指的三个宇宙的地方

章节 (A)-(B) 并未识别环境环的载体、关系和证明宇宙：[PrincipalIdeal]、[ResIdeal] 和 [ResRing] 都可以在一个三个层次明确分开的环上形成。从 [res_kills] 开始——第一个提到 [Rng] 的常量——才带有识别。捐赠者是 [Rng] 本身，而不是 [RKills]，且这条注释的初稿曾说法不同：[Instance/Rng.v] 的 [Rng := Ring] 在 [RingObject@{u u u}] 上有 [obj]，因此单独的 [R : obj[Rng] 在这些层次上会因 IDENTICAL 错误而被拒绝，并且命令中没有 [RKills]（负 8）；而 [RKills] 自身的类型提到 [R ~{Rng}~> K]，因此无法脱离它进行测试——负 6 的错误会在其 [R] 参数处触发，即已被拒绝参数陷阱。下面的三个控件所区分的是章节 (A)-(B) 不具备这种识别；它们并未将识别归因于任何事物。

将这两类区分开：负 8 是可形成性（其错误以一个宇宙子句结束，“无法强制执行 rr = ro 因为 ro < rr”），而负 6 和 7 是类型化 —— 展开拒绝了该部分的 [RingObject]/[RingComm] 实例，而此处需要的是全相等的实例，并且根本没有宇宙子句。

这段话的早期修订将可成形性读数分配为负6，而打字读数则单独分配为负7。在 PR “代数承载器是集合”（2026-09-17）处重新测量，通过在该整个文件的副本中剥离每个 [Fail]：负6 现在报告

术语“R”的类型是“RingObject@{rp ro rr}”，而期望的类型是“RingObject@{u u u}”

——一个新宇宙重复三次，以任何名称印刷
    包围模块给出了它——没有宇宙子句，因此读为
    作为打字而非可形成性;
    负7报告[RingComm]时形状相同;负8仍然如此
    结尾为“（宇宙不一致：无法强制执行rr = ro，因为
    罗<RR）“。每个负面PIN码保持不变——识别
    仍然[Rng]，且在（A）-（B）节中仍然缺失——只有
    错误类型被错误归因。
*)

Section UniverseBoundary.

Universes ro rr rp.
Constraint ro < rr.
Constraint rr < rp.

(*
AN EARLIER REVISION wrote [RingObject@{ro rr rp}].  Since the PR
   "algebraic carriers are sets" (2026-09-17) the record's AUXILIARY universe
   moved from the third argument to the first -- the [PropEquiv] field puts
   [Set+1] in the record's sort -- so the three roles permuted from
   (carrier, proof, aux) to (aux, carrier, proof).  Each named universe keeps
   its original role; only the order changed.  The boundary this section pins
   is unmoved: [ro < rr < rp] still declares the three levels strictly
   apart.

--------
早期的修订写成了 [RingObject@{ro rr rp}]。由于 PR “代数承载体是集合”（2026-09-17），记录的辅助 (AUXILIARY) 宇宙从第三个参数移到了第一个——[PropEquiv] 字段将 [Set+1] 放入记录的排序中——因此三个角色从 (carrier, proof, aux) 调换为 (aux, carrier, proof)。每个命名的宇宙保持其原始角色；仅顺序发生了变化。本节固定的边界未动：[ro < rr < rp] 仍然严格声明三个层级彼此分离。
*)
Context (R : RingObject@{rp ro rr}) (Rc : RingComm R)
        (d : carrier (rig_setoid R)) (n : nat).

(* Controls: accepted at those very levels. / 控制：在那些级别上被接受。 *)
Check (PrincipalIdeal Rc d).
Check (ResIdeal Rc d n).
Check (ResRing Rc d n).

Fail Check (@RKills R (ResIdeal Rc d (S n)) (ResRing Rc d n)).

Fail Check (ResTower Rc d).

(*
Negative 8 (FORMABILITY): the donor, ISOLATED.  Neither [RKills] nor
   any constant of [Instance/Rng/Zp.v] occurs in this command -- mere
   objecthood in [Rng] is already refused, and this is the one negative of
   the three whose message ends in a universe clause.  An earlier revision
   said "with negative 6's error"; re-measured, negative 6's message is a
   plain instance mismatch and only this one carries "Cannot enforce
   rr = ro because ro < rr".

--------
负 8（可形成性）：供体，被孤立。 在此命令中既没有 [RKills] 也没有任何 [Instance/Rng/Zp.v] 的常量——仅在 [Rng] 中具有对象性已经被拒绝，而且这是三个负例中唯一一个其消息以宇宙子句结尾的。较早的版本说的是“带有负 6 的错误”；重新测量后，负 6 的消息是一个简单的实例不匹配，只有这个负例包含“无法强制执行 rr = ro 因为 ro < rr”.
*)
Fail Check (R : obj[Rng]).

End UniverseBoundary.
