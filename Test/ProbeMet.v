(* ========================================================================= *)
(* Machine-checked boundary probes for Instance/Met.v, Instance/Met/ / 针对 Instance/Met.v、Instance/Met/ 的机器检查边界探测          *)
(* Extended.v and Instance/Met/Completion.v. / Extended.v 和 Instance/Met/Completion.v。                                 *)
(*                                                                           *)
(* WHY THIS FILE EXISTS.  The three files above make several claims of the / WHY THIS FILE EXISTS.  The three files above make several claims of the / 为什么存在此文件。 上面的三个文件提出了若干声明    *)
(* form: this holds by conversion; and several of the form: this does NOT / form: this holds by conversion; and several of the form: this does NOT / 形式：这是通过转换保持的；而几种形式：这并不保持     *)
(* hold by conversion, only up to a proof.  A claim of the first kind is / 通过转换持有，仅限于证明。第一类的主张是      *)
(* guarded by an [eq_refl] in the file itself.  A claim of the second kind / 由文件本身中的 [eq_refl] 保护。第二类索赔    *)
(* is not guarded by anything unless the rejection is pinned, which is what / is not guarded by anything unless the rejection is pinned, which is what / 除非拒绝被固定，否则不会被任何东西保护，这就是   *)
(* this file does: MEASURED is not GUARDED, and a strictness boundary that / 此文件的作用：MEASURED 不是 GUARDED，并且有一个严格性边界，它    *)
(* nobody re-checks silently moves. / 没有人会重新检查悄悄移动的棋子。                                          *)
(*                                                                           *)
(* THE HYGIENE COST IS STATED, NOT HIDDEN.  Each use of the rejection / 卫生费用已说明，不隐瞒。每次使用拒绝         *)
(* vernacular is a hit for the [make todo] sweep (Makefile greps / [make todo] 扫描的方言命中（Makefile 搜索）            *)
(* case-insensitively over every .v file for a small set of trigger words, / case-insensitively over every .v file for a small set of trigger words, / 对每个 .v 文件以不区分大小写的方式搜索一小组触发词，    *)
(* one of which is that vernacular's own name).  Confining them here follows / one of which is that vernacular's own name).  Confining them here follows / 其中之一是该方言本身的名称）。将它们限制在这里是因为  *)
(* Test/Size.v, Test/Issue138.v and Test/ProbeFunnyPoly.v,77. / Test/Size.v，Test/Issue138.v 和 Test/ProbeFunnyPoly.v,77。   *)
(* This file contributes exactly THREE such hits, and the surrounding prose / This file contributes exactly THREE such hits, and the surrounding prose / 这个文件恰好贡献了三个这样的命中，以及周围的散文  *)
(* is worded to avoid the trigger words so the sweep's delta is exactly those / is worded to avoid the trigger words so the sweep's delta is exactly those / 措辞是为了避免触发词，因此扫掠的增量正好是那些 *)
(* three commands. / 三个命令。                                                           *)
(*                                                                           *)
(* WHAT THE VERNACULAR DOES AND DOES NOT SHOW.  It succeeds when the command / WHAT THE VERNACULAR DOES AND DOES NOT SHOW.  It succeeds when the command / 方言显示与未显示的内容。它在命令成功时起作用  *)
(* it wraps raises ANY error, and it does not report which one, so on its own / it wraps raises ANY error, and it does not report which one, so on its own / 它会捕获任何错误，但不会报告具体是哪一个，所以单独使用时 *)
(* it cannot tell a genuine non-convertibility from a typo or a scope slip. / it cannot tell a genuine non-convertibility from a typo or a scope slip. / 它无法将真正的不可转换性与打字错误或范围偏移区分开来。   *)
(* The probes below were therefore checked by hand in the way Test/Size.v / 因此，下面的探针按照 Test/Size.v 中的方式用手检查。     *)
(* prescribes: the wrapper was stripped, the bare command compiled, and the / 规定：包装被剥离，裸命令被编译，并且   *)
(* error read to confirm it is a unification error about the intended terms / error read to confirm it is a unification error about the intended terms / 错误读取以确认它是关于预期术语的统一错误   *)
(* and not something else.  Each is also paired with a POSITIVE CONTROL / 而不是其他的。每一个还配有一个阳性对照       *)
(* immediately above it — a closely related statement that DOES close by / immediately above it — a closely related statement that DOES close by / 就在它的正上方——一个密切相关的陈述，确实以……结尾      *)
(* conversion — so that a probe cannot pass merely because the surrounding / 转换——这样探针不能仅仅因为周围环境就通过    *)
(* vocabulary stopped elaborating. / 词汇停止了展开。                                           *)
(* ========================================================================= *)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Structure.UniversalProperty.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.
Require Import Category.Instance.Met.Extended.
Require Import Category.Instance.Met.Completion.

Generalizable All Variables.

Open Scope R_scope.

(* ===== BLOCK A — the vocabulary elaborates (instrument sanity check) ===== / ===== 块 A — 词汇详解（仪器健全性检查） ===== *)

(*
If these stopped type-checking, the rejections in Blocks B and C would
   pass for the wrong reason.

--------
如果这些停止类型检查，B 块和 C 块的拒绝将会因为错误的原因而通过。
*)
Check (Met : Category).
Check (CMet : Category).
Check (CMet_Incl : CMet ⟶ Met).
Check (R_Metric : MetricSpace).
Check (Harmonic : MetricSpace).
Check (fun X : MetricSpace => Completion X : MetricSpace).
Check (fun X : MetricSpace => eta X : Isometry X (Completion X)).
Check (fun X : MetricSpace =>
         Completion_AUniversalArrow X
           : AUniversalArrow (X : Met) CMet_Incl (Completion_CMet X)).
Check (TwoFar : ExtMetricSpace).

(* ===== BLOCK B — what IS definitional, and what is not, on the metric ===== / ===== B 块 — 在指标上什么是定义性的，什么不是 ===== *)

(*
POSITIVE CONTROL.  The distance of [R_Metric] reduces to the absolute
   difference; Instance/Met.v states this as an [Example] and it is repeated
   here so that Block B's rejection has a live neighbour.

--------
阳性对照。[R_Metric] 的距离减少到绝对差；Instance/Met.v 将其表述为 [Example]，并在此重复，以便 Block B 的拒绝有一个活跃的邻居。
*)
Example R_Metric_dist_is_abs (x y : R_Metric) : dist x y = Rabs (x - y) := eq_refl.

(*
POSITIVE CONTROL.  The carrier of the completion is the type of Cauchy
   sequences, definitionally.

--------
阳性对照。完成的载体从定义上来说是柯西序列的类型。
*)
Example Completion_carrier (X : MetricSpace) :
  met_carrier (Completion X) = CauchySeq_Object X := eq_refl.

(*
THE BOUNDARY.  The embedding preserves the distance, but NOT by
   conversion: [cdist] is the limit produced by [R_complete], so relating it
   to [dist a b] requires the uniqueness-of-limits argument that
   Instance/Met/Completion.v's [eta_dist] carries out.  Verified by hand:
   stripping the wrapper below reports that it cannot unify
   [dist (eta X a) (eta X b)] with [dist a b], which is the intended
   non-convertibility and not a typo or a scope slip.

--------
边界。嵌入保持了距离，但不是通过转换做到的：[cdist] 是由 [R_complete] 产生的极限，因此将其与 [dist a b] 关联需要 Instance/Met/Completion.v 中 [eta_dist] 执行的极限唯一性论证。手动验证：下面剥离包装器报告无法将 [dist (eta X a) (eta X b)] 与 [dist a b] 统一，这就是预期的不可转换性，而不是拼写错误或作用域错误。
*)
Fail Example eta_dist_is_definitional (X : MetricSpace) (a b : X) :
  dist (isometry_map (eta X) a) (isometry_map (eta X) b) = dist a b := eq_refl.

(*
... and here is the same statement holding, by proof.  Without this the
   rejection above would be consistent with the statement being false.

--------
... 这里同样的陈述通过证明成立。没有这一点，上述的拒绝将与该陈述为假的情况一致。
*)
Example eta_dist_holds_by_proof (X : MetricSpace) (a b : X) :
  dist (isometry_map (eta X) a) (isometry_map (eta X) b) = dist a b.
Proof. exact (isometry_dist (eta X) a b). Qed.

(* ===== BLOCK C — the extended/ordinary round trips are asymmetric ===== / ===== C 块 — 延长/普通往返行程是非对称的 ===== *)

(*
POSITIVE CONTROL, the strict direction.  Going from a metric space up to
   the extended world and back down along the canonical finiteness witness
   returns the distance on the nose.

--------
正向控制，严格的指导。从度量空间上升到扩展世界，再沿着规范有限性见证返回，距离会精确返回。
*)
Example ext_roundtrip_strict (X : MetricSpace) (x y : X) :
  dist (X := Metric_of_EFinite (ExtMetric_of_Metric X)
                               (ExtMetric_of_Metric_EFinite X)) x y
    = dist x y := eq_refl.

(*
THE BOUNDARY, the other direction.  Starting from an extended metric
   space and an ARBITRARY finiteness witness [Hfin], the value [efin] reads
   off is [`1 (Hfin x y)], and recovering [edist x y] from
   [RFin (`1 (Hfin x y))] needs [`2 (Hfin x y)] — a proof, not a
   conversion.  Verified by hand: stripping the wrapper below reports that
   it cannot unify [@edist (ExtMetric_of_Metric (Metric_of_EFinite E Hfin))
   x y] with [@edist E x y], which is the intended non-convertibility.

--------
边界，另一个方向。 从一个扩展度量空间和一个任意的有限性证明 [Hfin] 开始，读取的值 [efin] 是 [`1 (Hfin x y)]，而从 [RFin (`1 (Hfin x y))] 恢复 [edist x y] 需要 [`2 (Hfin x y)]——这是一个证明，而不是转换。 手工验证：剥去下面的包装显示它无法将 [@edist (ExtMetric_of_Metric (Metric_of_EFinite E Hfin)) x y] 与 [@edist E x y] 统一，这正是预期的不转换性。
*)
Fail Example ext_roundtrip_strict_other (E : ExtMetricSpace) (Hfin : EFinite E)
     (x y : E) :
  edist (X := ExtMetric_of_Metric (Metric_of_EFinite E Hfin)) x y = edist x y
    := eq_refl.

(* ... and the same statement holding, by proof. / ... 并且通过证明，同样的陈述成立。 *)
Example ext_roundtrip_other_by_proof (E : ExtMetricSpace) (Hfin : EFinite E)
        (x y : E) :
  edist (X := ExtMetric_of_Metric (Metric_of_EFinite E Hfin)) x y = edist x y.
Proof. exact (ExtMetric_of_Metric_roundtrip E Hfin x y). Qed.

(* ===== BLOCK D — a DONOR limitation, pinned so its repair is noticed ===== / ===== D区——一个供体限制，固定以便其修复被注意到 ===== *)

(*
Instance/Met/Completion.v's header records that the second generic
   uniqueness route — [univ_property_unique_up_to_unique_iso] reached through
   [UniversalArrowIsUniversalProperty] — could not be taken, and that the
   obstruction belongs to the bridge rather than to metric spaces.  This is
   the evidence for that claim, and it is a statement ABOUT THE DONOR, not
   about this development.

   The control is the identity functor on [Sets] — a trivial instance, but
   NOT the simplest one available: the bridge does elaborate at [_1], [_2]
   and [Cat], so what this probe pins is the rejection at the tree's LARGE
   concrete categories, not a blanket failure.  Verified by hand: stripping
   the wrapper below reports
   a universe inconsistency, of the form "Cannot enforce u = v because
   u < w <= v".  If the bridge's universes are ever repaired this probe
   starts complaining, which is the intended alarm — at that point
   Instance/Met/Completion.v's disclosure should be revisited and the second
   route taken.

--------
Instance/Met/Completion.v 的头部记录了第二个通用唯一性路径 —— 通过 [UniversalArrowIsUniversalProperty] 到达的 [univ_property_unique_up_to_unique_iso] —— 无法被采用，并且阻塞属于桥而不是度量空间。这就是该声明的证据，并且这是关于捐赠者的陈述，而不是关于此开发的陈述。

控制是 [Sets] 上的恒等函子——一个平凡的实例，但并不是可用的最简单的实例：桥接在 [_1]、[_2] 和 [Cat] 上有详细的演示，所以这个探针钉住的是树的大型具体范畴上的拒绝，而不是全面的失败。手动验证：剥离下面的封装会报告一个宇宙不一致，形式为“无法强制执行 u = v 因为 u < w <= v”。如果桥接的宇宙一旦被修复，这个探针就会开始发出警告，这就是预期的警报——到那时，应重新审视 Instance/Met/Completion.v 的披露并采取第二条路线。
*)
Fail Check (fun c : Sets => UniversalArrowIsUniversalProperty _ _ (Id[Sets]) c).

(*
POSITIVE CONTROL: the bridge's own statement elaborates, so the rejection
   above is about instantiating it and not about the name being absent.

--------
阳性对照：桥本身的陈述进行了阐述，所以上述拒绝是关于实例化它，而不是关于名称缺失。
*)
Check @UniversalArrowIsUniversalProperty.
Check @univ_property_unique_up_to_unique_iso.

(* ===== BLOCK E — the deferred functor really is obstruction-free ===== / ===== E 块 — 延迟函数对象确实是无阻塞的 ===== *)

(*
Instance/Met/Completion.v's header states that the completion functor and
   the adjunction [Completion ⊣ CMet_Incl] follow from the universal arrow
   with no further proof obligation, and that they are left out of the
   library surface by choice rather than by difficulty.  That is a claim
   about what elaborates, so it is checked here rather than asserted there.
   Nothing below is exported: these are local names in a test file, and the
   library gains no new constant from them.  CORRECTION (#370): the library
   now has them, as Instance/Met/Uniform.v's [CMet_Reflective_in_Met] and
   [completion_adj], built by the same two constructions; the two terms
   below stay as the check that nothing beyond the universal arrow is
   needed.

--------
Instance/Met/Completion.v 的头文件指出，completion 函子和伴随 [Completion ⊣ CMet_Incl] 都由通用箭头推导而来，无需进一步的证明义务，并且它们被排除在库界面之外是出于选择而非困难。 这是关于什么会被展开的声明，因此在这里检查而不是在那里断言。 以下内容没有导出：这些都是测试文件中的本地名称，库不会从中获得新的常量。 修正 (#370)：库现在拥有它们，作为 Instance/Met/Uniform.v 的 [CMet_Reflective_in_Met] 和 [completion_adj]，由相同的两个构造生成；下面的两个项保留为检查，确保除了通用箭头之外不需要其他内容。
*)

Definition probe_CompletionFunctor : Met ⟶ CMet :=
  LeftAdjointFunctorFromUniversalArrows CMet_Incl
    (fun X : Met => Completion_UniversalArrow X).

Definition probe_CompletionAdj : probe_CompletionFunctor ⊣ CMet_Incl :=
  AdjunctionFromUniversalArrows CMet_Incl
    (fun X : Met => Completion_UniversalArrow X).

(* ===== BLOCK F — the negative results are live, not vacuous ===== / ===== 块 F — 消极结果是存在的，不是空洞的 ===== *)

(*
The harmonic space really is incomplete, its completion really does have a
   point outside the image of the embedding, and the two-point space at
   infinite distance really is not an ordinary metric space.  These are
   [Check]s of already-proved statements: their value here is that they fix
   the STATEMENTS, so that a later weakening of any of them (to a vacuous
   hypothesis, say) shows up as a type error in this file.

--------
谐空间确实是不完全的，它的完备确实在嵌入的像之外有一个点，而且无限远处的两点空间确实不是普通的度量空间。这些都是已经证明的陈述的[Check]：它们在这里的价值在于它们固定了这些陈述，因此稍后对它们的任何削弱（例如变成一个无效假设）都会在此文件中显示为类型错误。
*)
Check (Harmonic_not_MComplete : MComplete Harmonic → False).
Check (Completion_Harmonic_adds_a_point
         : ∃ z : Completion Harmonic,
             ∀ k : Harmonic, isometry_map (eta Harmonic) k ≈ z → False).
Check (TwoFar_not_EFinite : EFinite TwoFar → False).
Check (TwoFar_not_a_metric_space : MetricPresentation TwoFar → False).

(* Mac Lane's parenthetical, and its categorical consequence. / 麦克莱恩的括号表达及其范畴结果。 *)
Check (fun (X Y : MetricSpace) (f : Isometry X Y) =>
         isometry_injective f
           : ∀ x y : X, isometry_map f x ≈ isometry_map f y → x ≈ y).
Check (fun (X Y : Met) (f : X ~> Y) => Met_all_Monic f : Monic f).
