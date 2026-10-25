Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Powerset.Quantifier.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(**
* Probe for Instance/Powerset/Quantifier.v (issue #384)

    Every boundary that file's header MEASURES is pinned here, from
    OUTSIDE it: an in-file [Fail] renames in lockstep with the constant
    it guards and so cannot detect a rename.  The [Require] list above
    is the target's own, plus the target.

    SIX NEGATIVES OF THREE KINDS -- four CONVERSION, one TYPING, one
    FORMABILITY -- told apart by the error TEXT rather than by label,
    plus one scope-free instrument check.  Each was stripped of its
    [Fail] ONE AT A TIME, compiled alone, and its whole error read; the
    typing one reports a plain "has type ... while it is expected to
    have type" with NO "cannot unify" and no universe clause, the four
    conversion ones end in "cannot unify", and the formability one ends
    in "universe inconsistency: Cannot enforce pr = po".

      1 CONVERSION -- [GaloisFunctor_l] of the new connection is not
        [InverseImage f].  "cannot unify"; the two functor records have
        the same [fobj] and the same [fmap] (controls below) and differ
        only in their three opaque law fields, which is why the headline
        is built with [proset_adjunction_at] rather than with #380's
        [GaloisAdjunction].

      2 CONVERSION -- [proj_exists S] is not [Powerset_Prop_image] along
        the projection.  "cannot unify"; the [≈] form is the target's
        [proj_exists_is_image] and the pointwise disagreement is real,
        an [ex] against a [Powerset_squash] of a [sigT].

      3 CONVERSION -- [proj_forall S] is not [Powerset_Prop_dual] along
        the projection.  Same shape: the two quantify over different
        carriers.

      4 CONVERSION -- [Subsets 1] and [Props] are not the same category:
        their OBJECT types differ, an [equiv]-respecting predicate on the
        point against a bare [Prop].  So the target's
        [subsets_one_Props], which is an [≅[Cat]] and hence an
        EQUIVALENCE in this library, cannot be strengthened to an
        identity of categories, and the target's header says so.

    A NEGATIVE THAT DID NOT FIRE, RECORDED RATHER THAN REMOVED SILENTLY.
    The first cut of this probe carried, as negative 4, the refutation of
    Beck-Chevalley at WHOLE-SUBSET Leibniz equality, and it did not fire.
    The equality holds, the target now ships it at that grade
    ([beck_chevalley_exists]/[beck_chevalley_forall]), the probe carries
    it as a POSITIVE, and both headers record the reason.  The
    replacement negative 4 above is the [Subsets 1]-vs-[Props] one.

      5 TYPING -- the headline adjunction cannot be ascribed at the
        reversed handedness.  A plain "has type ... while it is expected
        to have type"; its tail does mention the two functors, so the
        kind is read off the whole message and not off the tail.

      6 FORMABILITY -- [Powerset_Prop_obj] does not accept a setoid whose
        carrier and relation universes are declared apart.  "Universe
        inconsistency"; the carrier and the setoid structure of that very
        argument ARE accepted at those levels, which is what makes the
        rejection attributable to [Powerset_Prop_obj] rather than to the
        argument.  It is probed FIRST, before [Powerset_Prop_dual], for
        the reason #340 records: a probe aimed at the derived constant
        would be rejected at its [Powerset_Prop_obj] argument and would
        measure nothing of its own.

--------
* 探查实例/幂集/量词.v（问题 #384）

该文件的头部的每一个边界 MEASURES 都固定在这里，从外部来看：文件内的 [Fail] 会与它所保护的常量同步重命名，因此无法检测重命名。上面的 [Require] 列表是目标自身的，加上目标。

三种类型的六个负例——四个转换，一个类型检查，一个可形成性——通过错误文本而不是标签来区分，再加上一个无作用域的工具检查。每个都被单独剥离了 [Fail]，一次一个，单独编译，然后读取其完整错误；类型检查的那个会报告一个简单的“具有类型...，而期望的类型是...”且没有“无法统一”也没有宇宙条款，四个转换的以“无法统一”结尾，而可形成性的那个以“宇宙不一致：无法强制 pr = po”结尾。

1 转换——新连接的 [GaloisFunctor_l] 不是 [InverseImage f]。“无法统一”；两个函子记录具有相同的 [fobj] 和相同的 [fmap]（以下控制），仅在其三个不透明的法字段上有所不同，这就是为什么标题是用 [proset_adjunction_at] 构建的，而不是用 #380 的 [GaloisAdjunction]。

2 转换 -- [proj_exists S] 沿投影线并不是 [Powerset_Prop_image]。“无法统一”；[≈] 形式是目标的 [proj_exists_is_image]，并且逐点的差异是真实的，一个 [ex] 对抗 [Powerset_squash] 的 [sigT]。

3 转换 -- [proj_forall S] 在投影上不是 [Powerset_Prop_dual]。形状相同：两者量化的载体不同。

4 转换 -- [Subsets 1] 和 [Props] 不属于同一类别：它们的对象类型不同，对于光秃的 [Prop] 上的点，[equiv] 尊重的谓词也是如此。因此，目标的 [subsets_one_Props]，它是一个 [≅[Cat]，因此在此库中是一个等价关系，不能被增强为类别的同一性，并且目标的标题已经说明了这一点。

未触发的负例，被记录而不是悄悄移除。
该探针的第一次剪辑作为负例 4，包含对 Beck-Chevalley 在整体-子集莱布尼茨等式上的反驳，但并未触发。
等式成立，目标现以该等级处理它（[beck_chevalley_exists]/[beck_chevalley_forall]），探针将其作为正例记录，并且两个标题都记录了原因。
上述替换的负例 4 是 [Subsets 1] 对比 [Props] 的版本。

5 类型 -- 标题附加不能归因于反转的手性。一个普通的“具有类型...，而预期具有类型”；它的尾部确实提到了两个函子，因此类型是从整个信息中读取的，而不是从尾部读取的。

6 可塑性 —— [Powerset_Prop_obj] 不接受载体和关系宇宙被单独声明的集合类。“宇宙不一致”；该参数的载体和集合结构在这些层次上是被接受的，这使得拒绝归因于 [Powerset_Prop_obj] 而不是该参数。根据 #340 记录的原因，它会首先被探测，在 [Powerset_Prop_dual] 之前：针对派生常数的探测会在其 [Powerset_Prop_obj] 参数处被拒绝，并且不会测量它自身的任何内容。
*)

(* ------------------------------------------------------------------------ *)
(** ** Instrument check / ** 仪表检查 *)

(*
[Fail] must be able to see a rejection at all.  Scope-free: no constant
   of the target occurs in it, so no rename can silence it.

--------
[Fail] 必须能够看到任何拒绝。无作用域：其中不包含目标的常量，因此重命名无法使其静默。
*)
Fail Check (probe_instrument_absent_384 : nat).

(* ------------------------------------------------------------------------ *)
(** ** Controls: every constant the negatives name, outside a [Fail] / ** 控制：每个常数由否定名称指定，在 [Fail] 之外 *)

Check @Powerset_Prop_dual.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_image.
Check @Powerset_Prop_preimage.
Check @DualImage.
Check @InverseImage.
Check @DirectImage.
Check @GaloisFunctor_l.
Check @GaloisFunctor_r.
Check @subset_le_preorder.
Check @preimage_dual_galois.
Check @substitution_forall_adjunction.
Check @exists_substitution_adjunction.
Check @image_preimage_adjunction.
Check @proj_exists.
Check @proj_forall.
Check @proj_fst.
Check @ProdSetoid.
Check @cylinder.
Check @cyl_reindex.
Check @quantifier_triple.
Check @forall_unit_incl.
Check @forall_counit_incl.
Check @proset_adjunction_at.
Check @gal_r_preserves_glb.
Check @gal_l_preserves_lub.
Check @carrier.
Check @is_setoid.
Check @subsets_one_Props.
Check @Delta_X.
Check @exists_X.
Check @forall_X.
Check @quant_one.
Check @quant_bang.
Check @exists_not_right_adjoint.
Check @forall_not_left_adjoint.
Check @dual_image_not_join_preserving.
Check @beck_chevalley_exists_mem.
Check @beck_chevalley_exists.

(* ------------------------------------------------------------------------ *)
(** ** (1) The two preimage functors are different RECORDS / ** (1) 这两个原像函子是不同的记录 *)

Section GaloisFunctorRecord.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* POSITIVE: the object actions agree on the nose ... / 积极：对象的动作完美一致…… *)
Example p384_fobj_agrees (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[GaloisFunctor_l (subset_le_preorder@{o} Y)
         (subset_le_preorder@{o} X) (preimage_dual_galois f)] T
    = fobj[InverseImage f] T := eq_refl.

(* ... and so do the arrow actions. / ... 箭头操作也是如此。 *)
Example p384_fmap_agrees (T T' : carrier (Powerset_Prop_obj@{o} Y))
  (h : subset_le T T') :
  @fmap _ _ (GaloisFunctor_l (subset_le_preorder@{o} Y)
               (subset_le_preorder@{o} X) (preimage_dual_galois f)) T T' h
    = @fmap _ _ (InverseImage f) T T' h := eq_refl.

(*
NEGATIVE 1 (CONVERSION).  The WHOLE records do not: the three law
   fields are separate opaque [Program] obligations.

--------
否定 1（转换）。整体记录不包括：三个法律字段是独立的不透明 [Program] 义务。
*)
Fail Example p384_functor_records_agree :
  GaloisFunctor_l (subset_le_preorder@{o} Y) (subset_le_preorder@{o} X)
    (preimage_dual_galois f)
  = InverseImage f := eq_refl.

(*
NEGATIVE 5 (TYPING).  The headline runs [InverseImage f ⊣ DualImage f]
   and cannot be ascribed the other way round.

--------
负 5（打字）。标题是 [InverseImage f ⊣ DualImage f]，不能反过来归类。
*)
Fail Example p384_reversed_handedness :
  DualImage f ⊣ InverseImage f := substitution_forall_adjunction f.

(* POSITIVE: the pinned existential leg IS #382's adjunction. / 积极：被固定的存在性腿是 #382 的附加。 *)
Example p384_exists_leg_is_donor :
  exists_substitution_adjunction f = image_preimage_adjunction f := eq_refl.

(* POSITIVE: the unit and the counit ARE Mac Lane's two inclusions. / 积极的：单位和余单位就是 Mac Lane 的两个包含。 *)
Example p384_unit_is_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  @unit _ _ (InverseImage f) (DualImage f)
    (substitution_forall_adjunction f) T = forall_unit_incl f T := eq_refl.

Example p384_counit_is_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  @counit _ _ (InverseImage f) (DualImage f)
    (substitution_forall_adjunction f) S = forall_counit_incl f S := eq_refl.

End GaloisFunctorRecord.

(* ------------------------------------------------------------------------ *)
(** ** (2), (3) Mac Lane's two operations against the general ones / ** (2)、(3) 麦克莱恩对一般运算的两种操作 *)

Section ProjectionGrades.

Universe o so u.
Constraint o < so.

Context (U V : SetoidObject@{o o}).
Context (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))).

(* NEGATIVE 2 (CONVERSION). / 负二（转换）。 *)
Fail Example p384_exists_is_image_strict :
  @proj_exists@{o so} U V S
    = Powerset_Prop_image@{o} (proj_fst@{o so} U V) S := eq_refl.

(* NEGATIVE 3 (CONVERSION). / 负三（转换）。 *)
Fail Example p384_forall_is_dual_strict :
  @proj_forall@{o so} U V S
    = Powerset_Prop_dual@{o} (proj_fst@{o so} U V) S := eq_refl.

(* POSITIVE: the [≈] forms hold, and are the target's. / 积极：[≈] 形态保持，并且是目标的。 *)
Check (proj_exists_is_image U V S).
Check (proj_forall_is_dual U V S).

(*
POSITIVE: the cylinder IS the inverse image along the projection, on
   the nose -- so the two negatives above are about [proj_exists] and
   [proj_forall] and not about the projection.

--------
积极：圆柱体是沿投影的逆像，在鼻子上——所以上面的两个否定是关于 [proj_exists] 和 [proj_forall] 的，而不是关于投影的。
*)
Example p384_cylinder_is_preimage
  (Xs : carrier (Powerset_Prop_obj@{o} U)) :
  @cylinder@{o so} U V Xs
    = Powerset_Prop_preimage@{o} (proj_fst@{o so} U V) Xs := eq_refl.

End ProjectionGrades.

(* ------------------------------------------------------------------------ *)
(** ** (4) Beck-Chevalley: pointwise yes, whole-subset no / ** (4) Beck-Chevalley：按点是的，整体子集否 *)

Section BeckGrades.

Universe o so.
Constraint o < so.

Context (U U' V : SetoidObject@{o o}).
Context (g : U' ~{Sets@{o so}}~> U).
Context (S : carrier (Powerset_Prop_obj@{o} (ProdSetoid@{o so} U V))).

(* POSITIVE: pointwise, at [eq_refl]. / 阳性：逐点，在 [eq_refl]。 *)
Example p384_beck_pointwise (x : carrier U') :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S) x
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) x := eq_refl.

(*
POSITIVE: and at the WHOLE SUBSET too, which is what the target
   ships.  This was measured, not assumed: a first draft of the probe
   pinned its refutation as a negative and that guard did not fire.

--------
积极：并且在整个子集中，这也是目标船只的情况。这是测量得到的，而不是假设的：探针的初稿将其反驳定为负面，并且那道防护没有发射。
*)
Example p384_beck_whole_subset :
  Powerset_Prop_preimage@{o} g (@proj_exists@{o so} U V S)
    = @proj_exists@{o so} U' V
        (Powerset_Prop_preimage@{o} (cyl_reindex V g) S) := eq_refl.

(* POSITIVE: the [≈] reading is the target's. / 积极：[≈] 的读数属于目标。 *)
Check (beck_chevalley_exists_equiv U U' V g S).
Check (beck_chevalley_exists U U' V g S).

End BeckGrades.

(* ------------------------------------------------------------------------ *)
(** ** (4) [Subsets 1] is EQUIVALENT to [Props], not isomorphic to it / ** (4) [Subsets 1] 等价于 [Props]，而不是与其同构 *)

Section OmegaGrades.

Universe o so u.
Constraint o < so.

(*
POSITIVE: the equivalence is the target's, and both round trips hold.
   The two CATEGORIES and their two object types are [Check]ed here as
   well, so that a rename of [Subsets] or of [Props] breaks this section
   at a control rather than turning the negative below vacuously green --
   before these four lines they occurred outside the [Fail] only in
   prose.

--------
正面：等价性属于目标，并且两次往返都成立。两个类别及其两个对象类型也在此处被[Check]处理，因此重命名[Subsets]或[Props]会在控制点中破坏该部分，而不是让下面的负面为空地变为绿色——在这四行之前，它们仅在[Fail]之外以散文形式出现。
*)
Check subsets_one_Props.
Check subsets_one_Props_round.
Check Props_subsets_one_round.
Check (Subsets@{o u} quant_one@{o so}).
Check Props@{o u}.
Check (obj[Subsets@{o u} quant_one@{o so}]).
Check (obj[Props@{o u}]).

(*
NEGATIVE 4 (CONVERSION).  The two categories are not the same object:
   an object of [Subsets 1] is an [equiv]-respecting predicate, an object
   of [Props] is a [Prop].  So the [≅[Cat]] the target ships -- which in
   this library IS equivalence -- cannot be strengthened to an identity,
   and the header says so.

--------
负 4（转换）。这两个类别不是同一个对象：[Subsets 1] 的对象是一个遵守 [equiv] 的谓词，[Props] 的对象是一个 [Prop]。因此，[≅[Cat]] 目标船舶——在这个库中是等价的——不能被加强为同一性，而且标题也说明了这一点。
*)
Fail Example p384_subsets_one_is_Props :
  obj[Subsets@{o u} quant_one@{o so}] = obj[Props@{o u}] := eq_refl.

End OmegaGrades.

(* ------------------------------------------------------------------------ *)
(** ** (6) The donors' universe identification / ** (6) 捐赠者的宇宙识别 *)

Section UniverseBoundary.

Universe po pr.
Constraint pr < po.

Context (A : SetoidObject@{po pr}).

(*
POSITIVE controls at the very same declared levels: the argument's
   carrier and its setoid structure are both fine.

--------
在完全相同的声明水平上的正向控制：论点的承载体及其集合结构都很好。
*)
Check (carrier A).
Check (is_setoid A).
Check (A : Type@{po}).

(*
NEGATIVE 6 (FORMABILITY).  [Powerset_Prop_obj@{o}] wants
   [SetoidObject@{o o}], one level for both.

--------
负 6（成型性）。[Powerset_Prop_obj@{o}] 想要 [SetoidObject@{o o}]，两者都要一个等级。
*)
Fail Check (Powerset_Prop_obj A).

End UniverseBoundary.

(* ------------------------------------------------------------------------ *)
(** ** Riehl's triple, and the truth-value comparison, exercised / ** Riehl 的三重，以及真值比较，已被运用 *)

Section RiehlChecks.

Universe o so u.
Constraint o < so.

Context (X : SetoidObject@{o o}).

Check (Delta_X X).
Check (exists_X X).
Check (forall_X X).
Check (riehl_exists_delta X).
Check (riehl_delta_forall X).
Check (riehl_adjoint_triple X).
Check (Delta_X_obj_mem X).

End RiehlChecks.

Check @subsets_one_to_Props.
Check @Props_to_subsets_one.
Check @subsets_one_Props_round.
Check @Props_subsets_one_round.
