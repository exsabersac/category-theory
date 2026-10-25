Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Span.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Two.
Require Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Fun.Closed.

Generalizable All Variables.

Open Scope category_scope.

(** * Probe: the measured boundaries of Structure/Limit/Finite.v / * 探针：结构/界限/有限.v 的测量边界 *)

(*
Companion to Structure/Limit/Finite.v and to the additions in
   Instance/Cones/Limit.v (Mac Lane, Categories for the Working
   Mathematician, 2nd ed., §V.2 Definition 1 and Corollary 1; Awodey §5.4
   and §5.6; Seven Sketches §6.2.4; Riehl §3.5 Theorem 3.5.17).  Everything
   those files claim at [eq_refl] is shipped there as an [Example]; what they
   cannot guard from inside are the REFUSALS their headers record and the
   universe boundaries a consumer meets.  Those are pinned here, from
   OUTSIDE the targets, because an in-file [Fail] renames in lockstep with
   the constant it guards and so cannot detect a rename.  The [FinSet],
   [Sets] and elementary-topos instantiations and the [Omega] refutation
   live here too, because they cost modules the targets should not carry.

   The negatives are of THREE kinds, told apart by the error TEXT — the
   kinds were read off the messages produced by stripping each [Fail] in
   turn, in a copy of this WHOLE file — plus one scope-free instrument
   check.

     N1  CONVERSION  [Initial (Cocones F)] and [Terminal (Cocones F)] are
                   different TYPES ([cannot unify]); the covariant
                   [Initial ((Cocones F)^op)] IS the latter, the control.
     N2  TYPING    The issue's literal passage [Initial (Cocones F) →
                   Colimit F]: the hypothesis has the wrong type for
                   [Colimit_Cocones] — a plain has-type mismatch with no
                   [cannot unify] clause and no universe clause.
     N3  CONVERSION  [Limit_Cones (Cones_Limit F L) = L] as whole [Limit]
                   records: the [uniqueness] field is rebuilt through
                   [one_unique]; the cone and every mediator agree at
                   [eq_refl] (controls).
     N4  CONVERSION  [Cones_Limit F (Limit_Cones T) = T] as whole
                   [Terminal] records: the unique arrow is re-paired (stdlib
                   [sigT] has no eta) and [one_unique] is rebuilt; the
                   terminal cone and the apex map of the unique arrow agree
                   at [eq_refl] (controls).
     N5  CONVERSION  A [FinitelyComplete C] ascribed at [Complete C]: the
                   message is a has-type mismatch whose [cannot unify]
                   clause compares the SECOND binders, [J ⟶ C] against
                   [FiniteCategory J] — the two Π-types differ in arity, and
                   the tree's convention classifies by the clause.
     N6  TYPING    [finitely_complete_from_generators] fed a
                   [HasCoequalizers] where it asks for [HasEqualizers]: a
                   plain has-type mismatch, no [cannot unify], no universe
                   clause.
     N7  UNIVERSE  A BARE clone of [EmptyDiagram] (no universe binders) is
                   refused at an ambient whose homs are declared strictly
                   above [Set] ("Cannot enforce Set = ch") while the
                   target's annotated [EmptyDiagram], [empty_cone],
                   [FinitelyComplete_Terminal] and the biconditional are all
                   accepted there — the pin the annotation lifts.
     N8  UNIVERSE  At that ambient a limit over [_2] ([Category@{u Set
                   Set}]) is refused ("Cannot enforce Set = ch") and so is
                   [FC _2 Two_FiniteCategory D2], firing at the [_2]
                   argument, while the diagram [_2 ⟶ Cu] is accepted and
                   [FC] at [Roof^op] and at [Parallel] — the free shapes —
                   is accepted: why the converse reads pullbacks at
                   [Roof^op] and the terminal object at [DiscreteCat False].
     N9  UNIVERSE  At a shape whose hom is declared strictly below its
                   proof universe, [x ~> y] and [id[x]] are accepted while
                   [ArrowIx] (FromProducts.v) is refused ALONE ("Cannot
                   enforce jp = jh") and [FiniteCategory] is refused at the
                   same argument with the same message — the donor of the
                   hom = proof identification in the record's binder; the
                   inherited refusal fires at an already-refused argument
                   and does not measure the record on its own.
     N10 CONVERSION  The terminal object recovered at [FinSet] from the
                   empty finite limit BY THE PULLBACK ROUTE (the witness
                   [FinSet_FinitelyComplete_pb]; the native route of
                   Instance/FinSet/Limit.v computes it) is not the numeral
                   [1] by conversion:
                   [lazy] leaves a [fin_countP] over a predicate testing
                   [unique_obj (FinSet_Pullbacks_obligation_2 …)], the
                   pullback UMP that [Program] closed opaquely, so the
                   derived equalizer's carrier is stuck; [terminal_unique]
                   gives the isomorphism (control).

   Guard coverage: every constant a negative names is also named outside
   every [Fail] (the guard block at the end, plus the controls beside each
   negative).  Rename simulation, each target constant a negative names
   renamed in ITS OWN FILE and the tree rebuilt: [FinitelyComplete],
   [finitely_complete_from_generators], [Two_FiniteCategory],
   [FiniteCategory], [FinitelyComplete_Terminal], [Colimit_Cocones] and
   [Cones_Limit] each break this file on a control line, never inside a
   [Fail]; [Limit_Cones] (pre-existing) breaks Structure/Limit/Initial.v
   first.  [Defined] flips: of Finite.v's nine, only [empty_cone] is
   load-bearing (its [Qed] form stops [FinitelyComplete_Terminal] in that
   file); Cones/Limit.v's [Cones_Limit] is load-bearing, its [Qed] form
   stopping [p417_round_cone] below.

--------
作为 Structure/Limit/Finite.v 的补充，以及 Instance/Cones/Limit.v 中新增内容的补充（Mac Lane，《为实际工作的数学家准备的范畴论》，第2版，第§V.2节 定义1及推论1；Awodey §5.4 和 §5.6；Seven Sketches §6.2.4；Riehl §3.5 定理3.5.17）。这些文件在 [eq_refl] 处声称的一切内容都会以 [Example] 的形式被包含；它们无法在内部保护的是其头文件记录的 REFUSALS 以及消费者所遇到的宇宙边界。这些内容在此处被固定，是从目标之外固定的，因为文件内的 [Fail] 会与其所保护的常量同步重命名，因此无法检测重命名。[FinSet]、[Sets] 以及 elementary-topos 的实例化和 [Omega] 的反驳也在此处，因为它们会让模块承担目标不应该有的开销。

消极情况有三种，通过错误文本加以区分——这些种类是通过在整个文件的副本中依次剥离每个 [Fail] 所产生的消息中读取的——外加一次无范围仪器检查。

N1 转换 [Initial (Cocones F)] 和 [Terminal (Cocones F)] 是不同的类型 ([cannot unify])；协变 [Initial ((Cocones F)^op)] 是后者，即控制。N2 类型 检查 问题的字面段落 [Initial (Cocones F) → Colimit F]：假设的 [Colimit_Cocones] 类型错误——一个普通类型不匹配，没有 [cannot unify] 条款，也没有宇宙条款。N3 转换 [Limit_Cones (Cones_Limit F L) = L] 作为整体 [Limit] 记录：[uniqueness] 字段通过 [one_unique] 重建；锥体和每个中介在 [eq_refl] 上一致（控制）。
N4 转换 [Cones_Limit F (Limit_Cones T) = T] 作为整体
                   [Terminal] 记录：唯一箭头重新配对（stdlib
                   [sigT] 没有 eta）且 [one_unique] 重建；
                   唯一箭头的末端锥和顶点映射在 [eq_refl] 处一致（控件）。
N5 转换 A [FinitelyComplete C] 在 [Complete C] 处归属：
                   消息是类型不匹配，其 [cannot unify] 子句比较第二个绑定器，[J ⟶ C] 对 [FiniteCategory J] — 两个 Π 类型在元数上不同，
                   树的约定按子句分类。
N6 类型 [finitely_complete_from_generators] 输入了 [HasCoequalizers] 而它要求 [HasEqualizers]：
                   一个普通类型不匹配，无 [cannot unify]，无宇宙子句。
N7 宇宙 一个 [EmptyDiagram] 的裸克隆（无宇宙绑定器）在 ambient 中被拒绝，该 ambient 的 homs 被严格声明在 [Set] 之上（“无法强制 Set = ch”），而目标的带注释 [EmptyDiagram]、[empty_cone]、[FinitelyComplete_Terminal] 以及双条件在该处都被接受——这是注释解除的限制。
N8 宇宙 在那个环境下，[_2]（[Category@{u Set Set}]）上的极限被拒绝（"无法强制 Set = ch"），[FC _2 Two_FiniteCategory D2] 也被拒绝，在 [_2] 参数上触发，而图 [_2 ⟶ Cu] 被接受，并且在 [Roof^op] 和 [Parallel] 的 [FC] —— 自由形状 —— 被接受：为什么反向读取在 [Roof^op] 的拉回和在 [DiscreteCat False] 的终对象。
N9 宇宙 在一个其 hom 被声明严格低于其证明宇宙的形状下，[x ~> y] 和 [id[x] 被接受，而 [ArrowIx]（FromProducts.v）单独被拒绝（"无法强制执行 jp = jh"），[FiniteCategory] 在相同的参数下也被拒绝，并显示相同的信息 — 这是记录绑定器中 hom = proof 身份的提供者；继承的拒绝在已经被拒绝的参数上触发，并不会单独评估记录。
N10 转换  从空的有限极限通过拉回路径在 [FinSet] 处恢复的终对象（见证 [FinSet_FinitelyComplete_pb]；Instance/FinSet/Limit.v 的本地路径计算它）不是通过转换得到的数字 [1]： [lazy] 在测试 [unique_obj (FinSet_Pullbacks_obligation_2 …)] 的谓词上留下了 [fin_countP]，拉回的 UMP 被 [Program] 不透明地关闭，因此导出的等化器的承载体被卡住；[terminal_unique] 给出了同构（控制）。

保护覆盖：每个常数的负名也在每个 [Fail]（末尾的保护块，以及每个负数旁的控制）之外被命名。重命名模拟，每个目标常数的负名在它自己的文件中被重命名，并重新构建树：[FinitelyComplete]、[finitely_complete_from_generators]、[Two_FiniteCategory]、[FiniteCategory]、[FinitelyComplete_Terminal]、[Colimit_Cocones] 和 [Cones_Limit]，每个在控制行上断开该文件，从不在 [Fail] 内断开；[Limit_Cones]（预先存在）首先断开 Structure/Limit/Initial.v。[Defined] 翻转：在 Finite.v 的九个中，只有 [empty_cone] 承重（其 [Qed] 形式阻止该文件中的 [FinitelyComplete_Terminal]）；Cones/Limit.v 的 [Cones_Limit] 承重，其 [Qed] 形式阻止下面的 [p417_round_cone]。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check probe417_nonexistent_name.

(** ** A: the cone-category reading (Instance/Cones/Limit.v) / ** A：圆锥范畴读法（Instance/Cones/Limit.v） *)

Section Cones.
  Context `(F : J ⟶ C).

  (* Control: the covariant spelling IS terminality in [Cocones F]. / 控制：协变拼写在 [Cocones F] 中就是终端性。 *)
  Example p417_initial_op_is_terminal :
    @Initial (Opposite (Cocones F)) = @Terminal (Cocones F) := eq_refl.

  (*
N1 CONVERSION: the issue's literal [Initial (Cocones F)] is a DIFFERENT
     type (terminality in [(Cocones F)^op]).

--------
N1 转换：该问题的字面 [Initial (Cocones F)] 是一种不同的类型（[(Cocones F)^op] 中的终端性）。
*)
  Fail Example p417_initial_is_not_terminal :
    @Initial (Cocones F) = @Terminal (Cocones F) := eq_refl.

  (*
N2 TYPING: the literal passage the issue asks for,
     [Initial (Cocones F) → Colimit F], is refused — the hypothesis has the
     WRONG type for [Colimit_Cocones], a plain has-type mismatch.

--------
N2 打字：问题所要求的字面段落，[Initial (Cocones F) → Colimit F]，被拒绝——假设对于 [Colimit_Cocones] 类型错误，是简单类型不匹配。
*)
  Fail Definition p417_colimit_of_initial (I : @Initial (Cocones F)) :
    Colimit F := Colimit_Cocones F I.

  Context (L : Limit F).

  (*
Controls: the round trip through [Cones F] returns the cone and every
     mediator on the nose.

--------
控制：通过 [Cones F] 的往返会返回锥体和鼻子上的每一个介体。
*)
  Example p417_round_cone :
    @limit_cone _ _ _ (@Limit_Cones _ _ F (Cones_Limit F L))
    = @limit_cone _ _ _ L := eq_refl.
  Example p417_round_med (N : Cone F) :
    unique_obj (@ump_limits _ _ _ (@Limit_Cones _ _ F (Cones_Limit F L)) N)
    = unique_obj (@ump_limits _ _ _ L N) := eq_refl.

  (* N3 CONVERSION: the whole [Limit] record is rebuilt. / N3转换：整个[Limit]记录已被重建。 *)
  Fail Example p417_round_limit_record :
    @Limit_Cones _ _ F (Cones_Limit F L) = L := eq_refl.

  Context (T : @Terminal (Cones F)).

  (*
Controls: the other round trip returns the terminal cone and the
     apex map of the unique arrow on the nose.

--------
控制：另一趟往返返回终端锥体和鼻子上独特箭头的顶点图。
*)
  Example p417_round_terminal_obj :
    @terminal_obj _ (Cones_Limit F (@Limit_Cones _ _ F T)) = @terminal_obj _ T
    := eq_refl.
  Example p417_round_one (N : Cone F) :
    `1 (@one _ (Cones_Limit F (@Limit_Cones _ _ F T)) N) = `1 (@one _ T N)
    := eq_refl.

  (* N4 CONVERSION: the whole [Terminal] record is rebuilt. / N4转换：整个[Terminal]记录已被重建。 *)
  Fail Example p417_round_terminal_record :
    Cones_Limit F (@Limit_Cones _ _ F T) = T := eq_refl.
End Cones.

(** ** B: finite completeness is not completeness (N5 CONVERSION, N6 TYPING) / ** B：有限完备性不是完备性（N5 转换，N6 类型） *)

Section NotComplete.
  Context {C : Category} (FC : @FinitelyComplete C).

  (*
N5 CONVERSION: a finitely complete category is not thereby complete —
     a has-type mismatch whose [cannot unify] clause compares the SECOND
     binders ([J ⟶ C] against [FiniteCategory J]), classified by the
     clause as the header table has it.

--------
N5 转换：一个有限完全范畴因此并不完全——a 类型不匹配，其 [cannot unify] 子句比较第二个绑定器（[J ⟶ C] 与 [FiniteCategory J]），由该子句按表头表格分类。
*)
  Fail Definition p417_fc_is_complete : @Complete C := FC.

  (* Control: the other direction is the target's own passage. / 控制：另一个方向是目标自身的通道。 *)
  Definition p417_complete_fc (HC : @Complete C) : @FinitelyComplete C :=
    Complete_FinitelyComplete HC.

  (*
N6 TYPING: the generator corollary fed coequalizers where it asks for
     equalizers.

--------
N6 打字：生成器推论在要求等化器的地方提供了共同等化器。
*)
  Fail Definition p417_wrong_generator (T : @Terminal C) (CP : @Cartesian C)
    (HCo : HasCoequalizers C) : @FinitelyComplete C :=
    finitely_complete_from_generators T CP HCo.
End NotComplete.

(** ** C: universes / ** C：宇宙 *)

(*
A bare clone of [EmptyDiagram]: the target's explicit binders are what
   keep the ambient category free of the literal [Set].

--------
[EmptyDiagram] 的一个裸克隆：目标的显式绑定器就是保持环境类别不被字面 [Set] 占用的原因。
*)
Definition EmptyDiagram_bare (C : Category) : EmptyShape ⟶ C.
Proof.
  unshelve refine (@Build_Functor EmptyShape C
    (fun x => False_rect _ x) (fun x y _ => False_rect _ x) _ _ _);
    intros; contradiction.
Defined.

Section UnivPin.
  Universes co ch.
  Constraint Set < ch.
  Context (Cu : Category@{co ch ch}).
  Context (FC : @FinitelyComplete Cu).

  (*
Controls: the shape-free constants and the free shapes elaborate at an
     ambient whose homs sit strictly above [Set].

--------
控制：无形常数和自由形状在一个其同态严格高于 [Set] 的环境中详细说明。
*)
  Check (@FinitelyComplete Cu).
  Check (FinitelyComplete_Terminal FC).
  Check (FinitelyComplete_HasPullbacks FC).
  Check (FinitelyComplete_Cartesian FC).
  Check (FinitelyComplete_HasEqualizers FC).
  Check (FinitelyComplete_iff_pullbacks_terminal Cu).
  Check (EmptyDiagram Cu).
  Check (@empty_cone Cu).
  Context (DR : Opposite Roof ⟶ Cu).
  Check (FC (Opposite Roof) Cospan_FiniteCategory DR).
  Context (DP : Parallel ⟶ Cu).
  Check (FC Parallel Parallel_FiniteCategory DP).

  (* N7 UNIVERSE: the bare clone pins the ambient at [Set]. / N7 宇宙：裸克隆在 [Set] 固定环境。 *)
  Fail Check (EmptyDiagram_bare Cu).

  (*
N8 UNIVERSE: [_2] is a [Category@{u Set Set}], so a limit over it — and
     hence [FC] at it — is refused at this ambient, though the diagram
     itself is accepted.

--------
N8 宇宙：[_2] 是一个 [Category@{u Set Set}]，因此对它的限制——以及因此在其上的 [FC]——在这种环境下是被拒绝的，尽管图表本身是被接受的。
*)
  Context (D2 : _2 ⟶ Cu).
  Check D2.
  Fail Check (Limit D2).
  Fail Check (FC _2 Two_FiniteCategory D2).
End UnivPin.

Section HomProof.
  Universes jo jh jp.
  Constraint jh < jp.
  Context (Jv : Category@{jo jh jp}).
  Context (x y : Jv) (f : x ~> y).
  Check f.
  Check (id[x]).
  (*
N9 UNIVERSE: [FiniteCategory] identifies the shape's hom and proof
     universes (through [ArrowIx]; measured).

--------
N9 宇宙：[FiniteCategory] 识别该形状的 hom 和证明宇宙（通过 [ArrowIx] 测量）。
*)
  Fail Check (@ArrowIx Jv).
  Fail Check (FiniteCategory Jv).
End HomProof.

(** ** D: witnesses / ** D：证人 *)

Definition FinSet_FinitelyComplete_pb : @FinitelyComplete FinSet :=
  finitely_complete_of_pullbacks_terminal FinSet_Pullbacks FinSet_Terminal.

Definition FinSet_FinitelyCocomplete : @FinitelyCocomplete FinSet :=
  finitely_cocomplete_of_pushouts_initial FinSet_HasPushouts FinSet_Initial.

Definition Sets_FinitelyComplete : @FinitelyComplete Sets :=
  finitely_complete_of_pullbacks_terminal Sets_HasPullbacks Sets_Terminal.

(*
The sentence Structure/Topos.v now carries: every elementary topos is
   finitely complete in the [Limit]-shaped sense.

--------
句子 Structure/Topos.v 现在包含：每个基本的拓扑都是在 [Limit] 形状意义下有限完备的。
*)
Definition topos_FinitelyComplete {C : Category} (T : ElementaryTopos C) :
  @FinitelyComplete C :=
  finitely_complete_of_pullbacks_terminal topos_pullbacks topos_terminal.

(*
N10 CONVERSION: the terminal object recovered from the empty finite limit
   at [FinSet] BY THE PULLBACK ROUTE does NOT compute to the numeral [1] —
   the chain runs through the chosen equalizer of
   [HasEqualizers_of_HasPullbacks_Terminal], whose object is opaque (see the
   diagnosis in the header).  The witness is named [_pb] since #415:
   Instance/FinSet/Limit.v's [FinSet_FinitelyComplete], over the native
   equalizer, DOES compute it — its
   [FinSet_FinitelyComplete_terminal_computes].

--------
N10 转换：从空的有限极限在 [FinSet] 通过拉回路径恢复的终对象并不会计算为数字 [1]——链条通过所选择的 [HasEqualizers_of_HasPullbacks_Terminal] 的等化器，其对象是不可见的（见头部的诊断）。该证明自 #415 起命名为 [_pb]：Instance/FinSet/Limit.v 中的 [FinSet_FinitelyComplete]，在本地等化器上确实可以计算它——它的 [FinSet_FinitelyComplete_terminal_computes]。
*)
Fail Example p417_finset_terminal_computes :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete_pb)
  = 1%nat := eq_refl.

(* Control: it IS the terminal object up to isomorphism, by uniqueness. / 控制：它是终对象，在同构下，由唯一性决定。 *)
Definition p417_finset_terminal_iso :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete_pb)
  ≅ @terminal_obj FinSet FinSet_Terminal :=
  terminal_unique (FinitelyComplete_Terminal FinSet_FinitelyComplete_pb)
                  FinSet_Terminal.

(*
The shape [Omega] (Instance/Omega.v) is NOT finite: its identity arrows
   would inject [nat] into [Fin.t n].

--------
形状 [Omega]（Instance/Omega.v）不是有限的：它的恒等箭头会将 [nat] 注入到 [Fin.t n] 中。
*)
Theorem Omega_not_FiniteCategory : FiniteCategory Omega -> False.
Proof.
  intros HJ.
  apply (fin_no_nat_injection (fun n => `1 (fc_cover HJ (@id Omega n)))).
  intros i j e.
  pose proof (hit_dom (`2 (fc_cover HJ (@id Omega i)))) as hi.
  pose proof (hit_dom (`2 (fc_cover HJ (@id Omega j)))) as hj.
  rewrite e in hi.
  exact (eq_trans (eq_sym hi) hj).
Qed.

(** ** Guards: every constant a negative names, outside every [Fail] / ** 守卫：每个常量都是负名，在每个 [Fail] 之外 *)

Check @Terminal.
Check @Cocones.
Check @Opposite.
Check @Colimit_Cocones.
Check @Colimit.
Check @Limit_Cones.
Check @Cones_Limit.
Check @Complete.
Check @FinitelyComplete.
Check @finitely_complete_from_generators.
Check @HasCoequalizers.
Check @Cartesian.
Check @EmptyDiagram_bare.
Check @EmptyDiagram.
Check @EmptyShape.
Check @Limit.
Check @Two_FiniteCategory.
Check @_2.
Check @ArrowIx.
Check @FiniteCategory.
Check nat.
