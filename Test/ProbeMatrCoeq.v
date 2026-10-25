Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Matr.Elimination.
Require Import Category.Instance.Matr.Coequalizer.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * Probe: strength boundaries of the matrix coequalizer / * 探测：矩阵余等化器的强度边界 *)

(*
Guard file for Instance/Matr/Elimination.v and
   Instance/Matr/Coequalizer.v, in the Test/ProbeFunnyPoly.v convention.

   THE IMPORT LIST ABOVE IS Coequalizer.v's OWN, VERBATIM AND IN ITS
   ORDER, AND THAT IS LOAD-BEARING RATHER THAN TIDINESS.  While drafting
   these negatives, two candidates PASSED for the wrong reason under a
   shortened import list: they failed at ELABORATION (a missing constant)
   instead of at UNIFICATION, so the [Fail] succeeded while measuring
   nothing at all.  A probe that cannot elaborate its own statement is
   not a probe.  Note in particular that [Coq.QArith.QArith] must come
   BEFORE [Category.Lib] -- QArith exports an [equiv] that shadows
   Lib/Setoid.v's, and with the other order every [Proper (equiv ==> ...)]
   in scope fails to elaborate.

   Every negative below is paired with a positive control NAMING ITS OWN
   CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
   constants appearing in the NEGATIVES -- not merely over those the
   controls happen to name, which is the narrower check that let three
   unguarded negatives ship in an earlier probe file in this tree.

   All SEVEN negatives here are CONVERSION negatives ([Fail Definition
   ... := eq_refl]); this file states no formability negative, so no
   lexical separation is needed.  Each was stripped of its [Fail] once
   and the resulting message inspected; every one reports a genuine
   "cannot unify".

--------
Instance/Matr/Elimination.v 和 Instance/Matr/Coequalizer.v 的保护文件，遵循 Test/ProbeFunnyPoly.v 的约定。

上述导入列表是 Coequalizer.v 文件自身的，逐字且按顺序，起的是承载作用而不是整齐美观。在起草这些否定测试时，有两个候选在缩短的导入列表下由于错误的原因通过：它们在展开（缺少常量）时失败，而不是在统一时失败，因此 [Fail] 成功了，但实际上没有测量任何东西。一个无法展开其自身声明的探针不是探针。特别注意 [Coq.QArith.QArith] 必须位于 [Category.Lib] 之前——QArith 导出了一个遮蔽 Lib/Setoid.v 的 [equiv]，并且在其他顺序下，作用域中的每个 [Proper (equiv ==> ...)] 都无法展开。

下面的每个阴性样本都与一个阳性对照配对，并为其命名了各自的常量，该配对通过对阴性样本中出现的常量进行重命名模拟进行了验证——而不仅仅是对对照恰好命名的常量进行验证，这是一种较窄的检查方法，曾导致三个未受保护的阴性样本在该树的早期探测文件中被释放。

这里的所有七个否定都是转换否定（[Fail Definition ... := eq_refl]）；该文件没有指出任何可形成性否定，因此不需要词汇分离。每一个都被剥去了它的 [Fail] 一次，并检查了生成的消息；每一个都报告了一个真正的“无法合一”.
*)

(**
** Instrument check

    A [Fail] that must itself fail, so a globally broken [Fail]
    vernacular would be caught here rather than silently greening the
    negatives below.  This is the INSTRUMENT, not one of the seven
    negatives.

--------
** 仪器检查

一个必须自身失败的 [Fail]，因此在此处会捕获一个全球性损坏的 [Fail] 术语，而不是在下方默默地将负数标记为绿色。这是仪器，而不是七个负数之一。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** The Qed-opaque decider

    THE SHARPEST MEASUREMENT IN THIS FILE, and it was found by a refuted
    probe rather than anticipated.  [Instance/Field.v]'s [F2_Field_dec]
 and [Q_Field_dec] are [Qed] lemmas.  They inhabit the
    decidability hypothesis perfectly well -- the engine is TOTAL and
    CORRECT when fed them -- but nothing REDUCES through an opaque
    constant, so the coequalizer object does not compute.  Elimination.v
    and Coequalizer.v therefore use transparent copies ([f2_dec], [q_dec],
    [Defined]) for every [eq_refl] witness.

    This is a fact about opacity, NOT about the mathematics: the negative
    and its control below differ ONLY in which decider is supplied.

--------
** Qed 不透明判定器

    本文件中最锐利的测量，它是通过一个被反驳的探针发现的，而不是预期的。[Instance/Field.v] 的 [F2_Field_dec] 和 [Q_Field_dec] 是 [Qed] 引理。它们完全符合可判定性假设——当提供给引擎时，引擎是完全的且正确的——但是没有任何东西能够通过一个不透明常量简化，因此等化子对象无法计算。因此，Elimination.v 和 Coequalizer.v 对每一个 [eq_refl] 证人使用透明副本 ([f2_dec]、[q_dec]、[Defined])。

    这是关于不透明性的事实，而不是数学问题：下面的负例及其控制仅在于提供的判定器不同。
*)

Fail Definition probe_qed_decider_blocks :
  matr_coeq_obj F2_Field F2_Field_dec coeq_f2_A coeq_f2_B = 1%nat
  := eq_refl.

Definition probe_pos_transparent_decider_computes :
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_B = 1%nat
  := eq_refl.

(**
** No normal form for the coequalizing map

    The next three are three faces of one fact: this development
    computes A coequalizing map, not a NORMALISED one, and [delta] is
    stuck under a free index.  Entrywise agreement holds; whole-function
    Leibniz equality does not.

--------
** 没有对等化映射的正规形式

接下来的三个是同一事实的三个方面：这个发展计算的是 A 对等化映射，而不是正规化映射，而且 [delta] 被困在一个自由索引下。按元素的一致性成立；整体函数的莱布尼茨相等性则不成立。
*)

Fail Definition probe_map_is_identity :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
    = mat_id F2_Field 2 := eq_refl.

Fail Definition probe_map_is_h :
  coeq_f2_map = coeq_f2_h := eq_refl.

Fail Definition probe_map_is_const :
  coeq_f2_map = ((fun _ _ => true) : 2%nat ~{Matr F2_Field}~> 1%nat)
  := eq_refl.

(*
Positive control naming Coequalizer.v's own agreement lemma: the two
   maps DO agree entrywise, so the refutations above are about
   whole-function equality and not about the maps differing in value.

--------
正向控制命名 Coequalizer.v 自己的协议引理：这两个映射在每个条目上确实一致，因此上面的反驳是关于整个函数的相等性，而不是关于映射在值上不同。
*)
Definition probe_pos_map_agrees_at :
  coeq_f2_map F1 F1 = coeq_f2_h F1 F1 := eq_refl.

(**
** The op-bridge is not a definitional identity of records

    Reduction.v (#326) proved abstractly that [IsCoequalizer] and
    [IsEqualizer (C^op)] are distinct record types though their fields
    are convertible.  This CONFIRMS that abstract negative at a CONCRETE
    category, which the abstract statement alone does not do.

--------
** 操作桥不是记录的定义性标识

Reduction.v (#326) 抽象地证明了 [IsCoequalizer] 和 [IsEqualizer (C^op)] 是不同的记录类型，尽管它们的字段可以互换。这证实了在具体范畴中抽象的否定，而单靠抽象陈述本身无法做到这一点。
*)

Fail Definition probe_op_record_identity :
  IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map
    = @IsEqualizer ((Matr F2_Field)^op) 2%nat 1%nat
        coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map := eq_refl.

(* Positive control naming the bridge constant itself. / 正对照命名桥本身的常数。 *)
Definition probe_pos_op_bridge :
  @IsEqualizer ((Matr F2_Field)^op) 2%nat 1%nat
    coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map
  := IsEqualizer_op_of_IsCoequalizer coeq_f2.

(** ** Elimination.v: the engine's own boundaries / ** Elimination.v：引擎自身的边界 *)

Section EliminationNegatives.

Context (K : FieldObject).
Context (a b : nat).
Context (A : Matrix K a b).

(*
The identity acts as a unit only up to [≈]; [mat_mul] does not
   reduce a Kronecker [delta] against a free matrix.

--------
该单位仅在 [≈] 范围内作为一个单位；[mat_mul] 不会降低针对自由矩阵的 Kronecker [delta]。
*)
Fail Definition probe_mat_id_l_strict :
  mat_mul K (mat_id K a) A = A := eq_refl.

Fail Definition probe_mat_sub_self_strict :
  mat_sub K A A = mat_zero K := eq_refl.

End EliminationNegatives.

(*
Positive controls naming Elimination.v's own constants, so a rename or
   a statement change in the engine breaks this file loudly.

--------
正向控制命名 Elimination.v 自身的常量，因此在引擎中重命名或更改语句会严重破坏此文件。
*)
Definition probe_pos_mat_id_l (K : FieldObject)
  (Kdec : forall a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b -> False))
  (a b : nat) (A : Matrix K a b) :
  mat_mul K (mat_id K a) A ≈ A := mat_mul_id_l K Kdec A.

(**
** Controls for constants that appear ONLY inside negatives

    The rename simulation over the constants occurring in the NEGATIVES
    (not merely those the controls happened to name) found FIVE that no
    control mentioned -- [F2_Field_dec], [matr_coeq_map], [IsCoequalizer],
    [mat_sub] and [mat_zero].  Renaming any of them left this file
    compiling and turned its negative vacuously green.  The controls
    below are the repair, and they are recorded here rather than quietly
    added because this is the THIRD probe file in this tree to ship with
    that same gap.

--------
** 仅在负数中出现的常量控制

对出现在负数中的常量进行重命名模拟（不仅仅是那些控制恰好命名的常量）发现有五个常量没有任何控制提及——[F2_Field_dec]、[matr_coeq_map]、[IsCoequalizer]、[mat_sub] 和 [mat_zero]。 重命名其中任何一个都不会影响该文件的编译，并会使其负数状态自动变为绿色。 下面的这些控制是修复措施，它们记录在此处而不是悄悄添加，是因为这是该树中第三个随同相同漏洞一起发布的探测文件。
*)

Check F2_Field_dec.

Check (matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_B).

Check (IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map).

Check (fun (K : FieldObject) (a b : nat) (A : Matrix K a b) =>
         mat_sub K A A).

Check (fun (K : FieldObject) (a b : nat) => @mat_zero K a b).

(**
** Positive controls for the headline artifacts

    These name the two principal constants directly, so that neither can
    be renamed or restated without this file failing.

--------
** 标题文物的阳性对照

    这些直接命名了两个主要常数，因此在不导致此文件失败的情况下，不能重命名或重新说明它们。
*)

Check (matr_IsCoequalizer F2_Field f2_dec coeq_f2_A coeq_f2_B).

Check (Matr_HasCoequalizers F2_Field f2_dec).

Check (left_null_basis F2_Field f2_dec).

Check (left_null_basis_diff F2_Field f2_dec).

(*
Non-degeneracy, named so the witness cannot silently become trivial:
   the coequalizing map is epic but NOT monic, so it is a proper
   quotient rather than an isomorphism in disguise.

--------
非退化性，之所以这样命名，是为了说明见证不能默默地变得平凡：协等化映射是本射的，但不是单射，因此它是一个真正的商，而不是伪装的同构。
*)

Check coeq_f2_map_epic.

Check coeq_f2_map_not_monic.

Check coeq_f2_obj_not_zero.

Check coeq_f2_obj_not_two.
