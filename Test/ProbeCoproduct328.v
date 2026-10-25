Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Roster.

Generalizable All Variables.
Local Open Scope category_scope.

(** * Probe: strength boundaries of the Mon and Grph coproducts / * 探测：Mon 和 Grph 共积的强度边界 *)

(*
Guard file for Instance/Mon/Coproduct.v and
   Construction/Free/Quiver/Coproduct.v, in the Test/ProbeFunnyPoly.v
   convention.

   THE IMPORT LIST IS THE UNION OF THE TWO TARGETS' LISTS, plus
   Instance/Roster.v.  That last one is deliberate and is the ONLY place
   it appears: Instance/Mon/Coproduct.v does NOT require Roster, because
   Roster pulls in Instance/Top and hence the stdlib reals, and an
   algebra file depending on that would invert the layering.  The
   consequence is that the file states its results over
   [@Mon Sets Sets_Product_Monoidal] rather than over Roster's NAME for
   that term.  Those are the same term, and the [Mon_Sets] controls
   below are where that identification is machine-checked and GUARDED --
   it was previously verified only in a scratch probe that could not be
   preserved.

   Every negative is paired with a positive control NAMING ITS OWN
   CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
   constants appearing in the NEGATIVES -- the wider check, which found
   five unguarded negatives in an earlier probe file in this tree.

   All negatives here are CONVERSION negatives ([Fail Definition ...
   := eq_refl]); this file states no formability negative.  Each was
   stripped of its [Fail] once and the resulting message inspected.

--------
用于 Instance/Mon/Coproduct.v 和 Construction/Free/Quiver/Coproduct.v 的守护文件，遵循 Test/ProbeFunnyPoly.v 约定。

导入列表是两个目标列表的并集，再加上 Instance/Roster.v。最后一个是故意为之，并且是它出现的唯一地方：Instance/Mon/Coproduct.v 并不需要 Roster，因为 Roster 会引入 Instance/Top，从而引入标准库中的 real，而依赖于该文件的代数文件会颠倒层次结构。其结果是该文件在 [@Mon Sets Sets_Product_Monoidal] 上陈述其结果，而不是在 Roster 的 NAME 上陈述该项。这些是相同的项，下方的 [Mon_Sets] 控制是机器检查且受保护的该识别——之前仅在无法保存的临时探针中进行过验证。

每个阴性样本都与一个阳性对照配对，并为其命名自己的常量，并且通过重命名模拟对出现在阴性样本中的常量进行了配对验证——这是更广泛的检查，它在这个树的早期探测文件中发现了五个未受保护的阴性样本。

这里的所有否定都是转换否定（[Fail Definition ... := eq_refl]）；此文件声明没有可构成性否定。每一个都被剥除了它的 [Fail] 一次，并检查了生成的消息。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** The Mon_Sets name identification

    Instance/Mon/Coproduct.v is stated over [@Mon Sets
    Sets_Product_Monoidal]; Instance/Roster.v names that same term
    [Mon_Sets].  These controls are the machine-checked bridge.

--------
** Mon_Sets 名称识别

Instance/Mon/Coproduct.v 在 [@Mon Sets Sets_Product_Monoidal] 上声明；Instance/Roster.v 对同一术语 [Mon_Sets] 进行命名。这些控件是经过机器检查的桥梁。
*)

Definition probe_pos_mon_sets_is_the_same_term :
  Mon_Sets = @Mon Sets Sets_Product_Monoidal := eq_refl.

Check (_ : @Cocartesian Mon_Sets).

Check (Mon_Sets_Cocartesian).

Check (Mon_Sets_Initial).

(**
** Mon: beta and eta are not definitional at the morphism level

    The sharp pair is the first negative against
    [fp_beta_l_fun] (checked below): the underlying FUNCTIONS agree on the
    nose, so what fails is the [proper_morphism] certificate that
    [setoid_morphism_compose] rebuilds -- not the mathematics.

--------
** 星期一：在态射层面上，β 和 η 不是定义性的。

尖锐对是针对 [fp_beta_l_fun] 的第一个否定（如下所示检查）：底层函数在本质上是一致的，因此失败的是 [proper_morphism] 证书，而不是数学本身，而 [setoid_morphism_compose] 重新建立了该证书。
*)

Section MonNegatives.

Context (A B Q : @Mon Sets Sets_Product_Monoidal).
Context (f : A ~> Q) (g : B ~> Q).

Fail Definition probe_mon_beta_morphism :
  fp_merge A B Q f g ∘ fp_injl A B = f := eq_refl.

Fail Definition probe_mon_eta_morphism :
  fp_merge A B (FreeProd A B) (fp_injl A B) (fp_injr A B)
    = @id (@Mon Sets Sets_Product_Monoidal) (FreeProd A B) := eq_refl.

End MonNegatives.

(*
Control naming [id] itself.  The rename simulation over the
   constants appearing in the NEGATIVES found it named by no control --
   [@id] occurs once, inside the eta negative -- so that negative went
   vacuously green on a rename.  Recorded rather than quietly added.

--------
控制命名 [id] 本身。在出现在 NEGATIVES 中的常量上的重命名模拟发现它没有被任何控件命名 —— [@id] 出现一次，在 eta negative 内 —— 所以那个 negative 在重命名时空洞地变为绿色。被记录而不是悄悄添加。
*)
Check (fun (C : Category) (x : obj[C]) => @id C x).

(* Positive controls naming Instance/Mon/Coproduct.v's own constants. / 阳性对照命名 Instance/Mon/Coproduct.v 自身的常量。 *)
Check fp_beta_l_fun.
Check fp_beta_l_strict.
Check fp_merge_inl.
Check coprod_is_FreeProd.
Check fp_injl.
Check fp_injr.
Check FreeProd.
Check fp_merge.

(*
Non-degeneracy, named so the witness cannot silently go trivial:
   both injections are split monic for ARBITRARY factors, and over
   (nat,+) the two generators provably do not commute.

--------
非退化性，之所以这样命名，是为了确保证据不能默默地变得平凡：
   对任意因子，两者注入都是分裂单射，并且在 (nat,+) 上可以证明这两个生成元不交换。
*)
Check fp_injections_Monic.
Check fp_inl_injective.
Check fp_generators_do_not_commute.
Check fp_word_not_left.

(**
** Grph: the forgetful functor does NOT preserve coproducts on the
    nose

    Measured, not assumed.  Two independent causes, both located in
    Construction/Coproduct.v: it is a [Program Definition], so its [hom]
    field has an equation-passing match shape that does not convert
    under binders; and its [homset]'s [setoid_equiv] is a Qed-opaque
    obligation.  The SHARP measurement is the third negative -- [edgeset]
    fails at constructor arguments where [edges] SUCCEEDS at the very
    same arguments.

    THAT SHARP MEASUREMENT WAS CLAIMED HERE BEFORE IT WAS PINNED.  An
    earlier version of this header described it as "the third negative"
    when no [edgeset] negative existed anywhere in the file -- the
    measurement was real but GUARDED BY NOTHING, which is the exact
    distinction this file exists to enforce.  It is pinned below, with
    the [edges] control beside it so the contrast is visible.

--------
** Grph：这个遗忘函子在本质上不保持余积

经过测量，而非假设。两个独立的原因，都位于 Construction/Coproduct.v：它是一个 [Program Definition]，所以它的 [hom] 字段具有一个在绑定器下不会转换的方程传递匹配形状；并且它的 [homset] 的 [setoid_equiv] 是一个 Qed-opaque 义务。SHARP 测量是第三个负面因素——[edgeset] 在构造函数参数处失败，而 [edges] 在完全相同的参数下成功。

在被固定之前，这个尖锐的测量值已经在此处被声明。这个标题的早期版本将其描述为“第三个负值”，而文件中根本不存在任何 [edgeset] 负值——测量值是真实的，但没有受到任何保护，这正是这个文件存在的具体区别。它固定在下方，旁边是 [edges] 控制，以便对比清晰可见。
*)

Section QuiverNegatives.

Context (C D : Category).

Fail Definition probe_quiver_edges_strict :
  @edges (QuiverOfCat (C ∐ D))
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)) := eq_refl.

Fail Definition probe_quiver_record_strict :
  QuiverOfCat (C ∐ D)
    = QuiverCoprod (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

(*
THE SHARP ONE: [edgeset] fails at the SAME constructor arguments at
   which [edges] succeeds.  The control immediately below is what makes
   this a contrast rather than an isolated refusal.

--------
尖锐者：[edgeset] 在 [edges] 成功的相同构造函数参数下失败。下面的控制正是使这成为对比而非孤立拒绝的原因。
*)
Fail Definition probe_quiver_edgeset_ll (a b : obj[C]) :
  @edgeset (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edgeset (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

(*
Control naming [edgeset] itself, so the negative above cannot go
   vacuously green on a rename -- the [edges] control below names a
   different projection and does not cover it.

--------
控制名称 [edgeset] 本身，因此上述负数在重命名时不能无条件地变为绿色 —— 下面的 [edges] 控制命名了一个不同的投影，并且不涵盖它。
*)
Check (fun (G : Quiver) (x y : nodes) => @edgeset G x y).

Definition probe_pos_quiver_edges_ll (a b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

End QuiverNegatives.

(*
Positive controls naming Construction/Free/Quiver/Coproduct.v's own
   constants: the nodes and all four edge sets DO agree by eq_refl, and
   the isomorphism is what is delivered in place of the strict form.

--------
阳性对照命名 Construction/Free/Quiver/Coproduct.v 自身的常量：节点和所有四个边集通过 eq_refl 是一致的，而且同构是作为严格形式的替代提供的。
*)
(*
Control naming [edges] itself: the rename simulation over the
   constants in the NEGATIVES found it named by no control, so its
   negative would have gone vacuously green on a rename.  This line is
   the repair, recorded rather than quietly added.

--------
控制命名 [edges] 本身：对 NEGATIVES 中的常量进行重命名模拟时，发现没有控制对其进行命名，因此其负值在重命名时会自动变为绿色。这一行是修复，已记录，而不是悄悄添加。
*)
Check (fun (G : Quiver) => @edges G).

Check QuiverOfCat_Coproduct_nodes.
Check QuiverOfCat_Coproduct_edges_ll.
Check QuiverOfCat_Coproduct_edges_lr.
Check QuiverOfCat_Coproduct_iso.
Check QuiverCoprod.
Check QuiverOfCat.

(*
The two triangles hold at whole-record LEIBNIZ equality -- stronger
   than the Mon side, and worth guarding so a change is noticed.

--------
这两个三角形在全记录莱布尼茨等式上保持不变——比蒙边更强，并且值得守护，以便注意到变化。
*)
Check QuiverCopair_Inl.
Check QuiverCopair_Inr.

(*
Respectfulness IS proved here, unlike the sibling product's
   QuiverPair_unique, which the sibling discloses as unproved.

--------
尊重性在这里得到了证明，不像同系列产品 QuiverPair_unique，后者被同类产品披露为未经证明。
*)
Check QuiverCopair_respects.
Check QuiverCopair_unique.

(* The Cocartesian instance itself, and its derived vocabulary. / Cocartesian 实例本身及其派生词汇。 *)
Check QuiverCategory_Cocartesian.
Check Coprod_is_QuiverCoprod.

(*
Non-degeneracy: there is genuinely NO edge between the summands, and
   the two injections are not identified.

--------
非退化性：求和项之间确实没有边，并且两个注入映射没有被识别为相同。
*)
Check coprod_no_cross_edge.
Check injections_not_equivalent.
Check quiver_coprod_no_edge_lr.
