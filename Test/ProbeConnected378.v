Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Shapes.
Require Import Category.Theory.Skeleton.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Connected.Components.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Constant.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Instance.One.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Adjunction.FullFaithful.
Require Import Category.Adjunction.Diagonal.Connected.

Generalizable All Variables.

(**
* Boundary probe for Adjunction/Diagonal/Connected.v

    Every rejection the target's header records is pinned here, from
    OUTSIDE the target -- an in-file [Fail] renames in lockstep with the
    constant it guards and so cannot detect a rename.  The probe mirrors
    the target's whole [Require] list, plus Structure/Limit/Unique.v for
    negative 4; a short prefix is what makes a probe pass for the wrong
    reason.

    TEN [Fail] commands = 1 instrument check + 9 negatives of THREE
    kinds, kept lexically apart:

      - 3 CONVERSION (negatives 2, 4 and 10), each ending "cannot unify"
        between two terms of one type;
      - 2 TYPING (negatives 3 and 5), each a plain "has type ... while
        it is expected to have type" with NO "cannot unify" and NO
        universe clause.  Negative 3 is the sharper of the two and was
        measured rather than predicted: at an arbitrary choice of
        colimits the strict injection clause is not merely unprovable,
        it is NOT WELL-TYPED, the two sides having different codomains
        until the apex equation is supplied.  Negative 5 says the
        headline does not accept a bare family of colimits where the
        record is wanted;
      - 4 FORMABILITY (negatives 6-9), each ending "universe
        inconsistency: Cannot enforce ...".

    Each was stripped ONE AT A TIME, with the others left as [Fail],
    compiled alone, and its whole error read to confirm the kind and the
    command it fires at.

    Every constant a negative names also appears in a command OUTSIDE a
    [Fail], so a rename breaks the probe at a non-[Fail] line.  The
    universe sections carry the discriminating controls beside their
    negatives: [Ju ⟶ Cu] elaborates at hom levels declared strictly
    apart, so [Functor] is NOT a donor of either identification, and
    that is what makes the four rejections attributable.

--------
* 附加/对角/连通的边界探测器.v

目标的头记录中的每一次拒绝都固定在这里，从目标之外 —— 文件内部的 [Fail] 会随着它保护的常量同步重命名，因此无法检测到重命名。探针会镜像目标的整个 [Require] 列表，以及 Structure/Limit/Unique.v 用于负 4；短前缀是导致探针以错误原因通过的原因。

TEN [Fail] 命令 = 1 个仪器检查 + 9 个三种类型的阴性，按词汇上分开保存：

- 3 个转换（否定 2、4 和 10），每个以“不能统一”结束  
  两个同类型的项之间；  
- 2 个类型检查（否定 3 和 5），每个都是普通的“具有类型...但期望具有类型”，没有“不能统一”也没有宇宙条款。否定 3 是两个中较尖锐的，并且是测量得出的而非预测：在任意选择的余极下，严格的注入条款不仅不可证明，它的类型也不正确，直到提供顶点方程之前，双方具有不同的余域。否定 5 表示标题不接受裸的余极族，而是希望有记录；  
- 4 个可形成性（否定 6-9），每个以“宇宙不一致：无法强制执行...”结束。

每一个都被一个接一个地剥离，其余的保持为 [Fail]，单独编译，并读取其整个错误以确认类型以及它触发的命令。

每一个常量 a 负名称也出现在 [Fail] 外的命令中，因此重命名会在非 [Fail] 行中破坏探针。宇宙部分在它们的负面旁边携带区分控制：[Ju ⟶ Cu] 在严格分开的 hom 级别上详细说明，因此 [Functor] 不是任一识别的捐赠者，这就是使四个拒绝可归因的原因。
*)

(* ------------------------------------------------------------------ *)
(** ** Instrument check / ** 仪表检查 *)

Fail Check probe378_no_such_constant_anywhere.

(* ------------------------------------------------------------------ *)
(** ** Controls: every guarded constant named outside a [Fail] / ** 控件：每个在 [Fail] 外命名的受保护常量 *)

Check @diagonal_counit.
Check @diagonal_counit_strict.
Check @diagonal_counit_commutes.
Check @diagonal_counit_iso.
Check @diagonal_counit_Isomorphism.
Check @diagonal_counit_inverse.
Check @colim_const_inj_agree.
Check @colim_delta_nat.
Check @colim_diagonal_iso_Id.
Check @Diagonal_InjectiveOnObjects.
Check @diagonal_FFI.
Check @diagonal_RI.
Check @diagonal_fully_faithful_of_counit.
Check @ConstantColimits.
Check @cc_colim.
Check @cc_obj.
Check @cc_inj.
Check @constant_colimits_counit.
Check @colimit_is_lali_of_diagonal.
Check @colimit_lali_ffi.
Check @colimit_lali_ri.
Check @colim_diagonal_strict_Id.
Check @terminal_colimits.
Check @terminal_ConstantColimits.
Check @terminal_lali_of_diagonal.
Check @terminal_shape_connected.
Check @EvalAt.
Check @EvalAt_retracts.
Check @colimit_is_EvalAt.
Check @ordinal_ConstantColimits.
Check @ordinal_lali.
Check @two_ConstantColimits.
Check @two_lali.
Check @TwoGap.
Check @eval_not_left_adjoint.
Check @diagonal_limit_unit.
Check @diagonal_unit_commutes.
Check @lim_const_leg_agree.
Check @diagonal_unit_limit_iso.
Check @ConstantLimits.
Check @cl_limit.
Check @cl_obj.
Check @cl_leg.
Check @constant_limits_unit.
Check @diagonal_is_lari_of_limit.
Check @initial_limits.
Check @initial_ConstantLimits.
Check @initial_lari_of_limit.
Check @one_ConstantLimits.
Check @omega_ConstantLimits.
Check @omega_lari.
Check @two_discrete_counit_not_iso.
Check @two_discrete_no_ffi.
Check @two_discrete_no_lali.
Check @two_discrete_no_constant_colimits.
Check @two_discrete_objects_distinct.
Check @ordinal_two_not_degenerate.
Check @diagonal_counit_Isomorphism_to.
Check @lali_left_strict.
Check @lali_obj_strict.
Check @terminal_colimit_obj_strict.
Check @terminal_colimit_inj_strict.
Check @TwoGap_X.
Check @TwoGap_Y.
Check @lari_left_strict.
Check @lari_obj_strict.
Check @initial_limit_obj_strict.
Check @initial_limit_leg_strict.
Check @colim_diagonal_iso_Id_component.
Check @colim_diagonal_strict_Id_obj.

(* Donor constants the negatives below name. / 捐赠者确定下面名称的负数。 *)

Check @HasColimitsOfShape.
Check @colim_obj.
Check @colim_inj.
Check @LeftAdjointLeftInverse.
Check @colimit_unique_iso.
Check @const_IsAColimit.
Check @colim_acolimit.
Check @Diagonal.
Check @Two_Terminal.
Check @Fun.
Check @to.
Check @from.

(* ------------------------------------------------------------------ *)
(**
** (1) The unconditional strict clauses are REJECTED

    At an ARBITRARY choice of colimits the apex of the colimit of a
    constant diagram is the chosen one, and nothing reduces it to the
    constant -- which is exactly why [colimit_is_lali_of_diagonal]
    carries a hypothesis and section (A) of the target delivers only an
    isomorphism.

--------
** (1) 无条件严格条款被拒绝

在任意选择余极限时，常量图的余极限的顶点就是被选择的那个顶点，没有任何东西将其简化为常量——这正是为什么 [colimit_is_lali_of_diagonal] 带有假设，并且目标的部分 (A) 只提供一个同构。
*)

Section StrictClauses.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (P : ConstantColimits J C).

(* Negative 2 (CONVERSION). / 负 2（转换）。 *)
Fail Example probe_apex_strict (c : C) :
  colim_obj L Δ[J](c) = c := eq_refl.

(*
Control: with the record in hand the SAME equation is available, and
   under the terminal choice it holds by [eq_refl].

--------
控制：手中有记录时，相同的方程是可用的，并且在终端选择下，它由 [eq_refl] 保持。
*)
Definition probe_apex_control (c : C) : colim_obj (cc_colim P) Δ[J](c) = c
  := cc_obj P c.

Example probe_apex_terminal (T : @Terminal J) (c : C) :
  colim_obj (@terminal_colimits J C T) Δ[J](c) = c := eq_refl.

(*
Negative 3 (TYPING).  Measured, not predicted: at an arbitrary
   choice the strict injection clause is not even WELL-TYPED, the
   injection landing at [colim_obj L Δ[J](c)] where [id[c]] lands at
   [c].  Under the terminal choice the codomain reduces and the same
   statement is a passing control.

--------
负 3（类型检查）。测量的，而非预测的：在任意选择下，严格注入条件甚至不是良好类型的，注入落在 [colim_obj L Δ[J](c)]，而 [id[c]] 落在 [c]。根据终端选择，余域减少，同一陈述是一个通过的控制。
*)
Fail Example probe_inj_strict (c : C) (j : J) :
  colim_inj L Δ[J](c) j = id[c] := eq_refl.

Example probe_inj_terminal (T : @Terminal J) (c : C) (j : J) :
  colim_inj (@terminal_colimits J C T) Δ[J](c) j = id[c] := eq_refl.

(*
Negative 4 (CONVERSION): the counit and the leg of
   Structure/Limit/Unique.v's essential-uniqueness isomorphism are the
   same morphism up to [≈] -- both are mediators out of the chosen
   colimit into the constant cocone -- but they are DIFFERENT TERMS, so
   conversion rejects the identification.

--------
负 4（转换）：Structure/Limit/Unique.v 的 essential-uniqueness 同构的 counit 和 leg 是同态，在 [≈] 下是相同的——两者都是从所选余极限到恒定余锥的中介——但它们是不同的项，所以转换拒绝此识别。
*)
Fail Example probe_counit_is_unique_iso (c : C) :
  diagonal_counit L c
    = to (@colimit_unique_iso J C Δ[J](c) _ _
            (colim_acolimit L Δ[J](c)) (const_IsAColimit c K))
  := eq_refl.

(*
Control: the same statement at [≈] is what section (A) delivers, and
   the counit's own triangle is what proves it.

--------
控制：在 [≈] 的相同语句就是部分 (A) 提供的，而该单元自身的三角形就是证明它的东西。
*)
Definition probe_counit_control (c : C) (j : J) :
  diagonal_counit L c ∘ colim_inj L Δ[J](c) j ≈ id
  := diagonal_counit_commutes L c j.

(* Controls: both legs of the isomorphism read back on the nose. / 控制：同构的两条腿完全按原样回读。 *)
Example probe_to_strict (c : C) :
  to (diagonal_counit_Isomorphism L K c) = diagonal_counit L c := eq_refl.

Example probe_inverse_strict (c : C) :
  from (diagonal_counit_Isomorphism L K c)
    = colim_inj L Δ[J](c) (cn_obj K) := eq_refl.

End StrictClauses.

(* ------------------------------------------------------------------ *)
(**
** (2) The headline does not accept a bare family of colimits

    Negative 5 (TYPING).  [colimit_is_lali_of_diagonal] takes a point of
    the shape and a [ConstantColimits] record; feeding it the family
    alone is a plain type mismatch with no universe clause, which is the
    whole content of section 2 of the target's header.

--------
** (2) 标题不接受一个单独的余并列族

    负 5（类型错误）。[colimit_is_lali_of_diagonal] 接受一个形状的点和一个 [ConstantColimits] 记录；仅提供该族会导致纯类型不匹配且没有宇宙子句，这正是目标标题第2节的全部内容。
*)

Section Arity.

Context {J C : Category}.
Context (j0 : J).
Context (L : HasColimitsOfShape J C).
Context (P : ConstantColimits J C).

Fail Definition probe_lali_from_bare :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal j0 L.

(* Control: with the record it is exactly the headline. / 控制：有了记录，它正是标题。 *)
Definition probe_lali_control :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal j0 P.

Example probe_lali_left_strict :
  lali_left probe_lali_control = ColimitFunctor (cc_colim P) := eq_refl.

End Arity.

(* ------------------------------------------------------------------ *)
(**
** (3) Universes: the shape's and the ambient's hom levels coincide

    Negatives 6-8 (FORMABILITY).  With the two hom levels declared
    strictly apart, three donors are each rejected ALONE -- [Fun],
    [HasColimitsOfShape] and [Diagonal] -- while the functor type
    [Ju ⟶ Cu] elaborates at those very levels.  So [Functor] is not the
    cause, and the identification the target reports as [jh = ch] has
    three independent donors, none of them introduced here.

--------
** (3) 宇宙：形状的同伦等级与环境的同伦等级一致

    负数 6-8（可形成性）。当两个同伦等级明确分开时，三个供体各自单独被拒绝——[Fun]、[HasColimitsOfShape] 和 [Diagonal]——而函子类型 [Ju ⟶ Cu] 则在这些等级上展开。因此 [Functor] 不是原因，而目标报告的识别为 [jh = ch] 有三个独立供体，它们都不是在此引入的。
*)

Section ShapeAmbientHom.

Universes jo jh co ch.
Constraint jh < ch.

Context (Ju : Category@{jo jh jh}).
Context (Cu : Category@{co ch ch}).

(* Discriminating controls, accepted at the declared levels. / 在声明水平上接受的差别控制。 *)
Check (obj[Ju]).
Check (obj[Cu]).
Check (Ju ⟶ Cu).

(* Negative 6 (FORMABILITY): the functor category itself. / 负 6（可形成性）：函子范畴本身。 *)
Fail Check ([Ju, Cu]).

(* Negative 7 (FORMABILITY): the colimit hypothesis. / 负 7（可形成性）：余极限假设。 *)
Fail Check (HasColimitsOfShape Ju Cu).

(* Negative 8 (FORMABILITY): the diagonal. / 负8（可成型性）：对角线。 *)
Fail Check (@Diagonal Cu Ju).

End ShapeAmbientHom.

(* ------------------------------------------------------------------ *)
(**
** (4) Universes: hom and proof coincide in both categories

    Negative 9 (FORMABILITY).  [LeftAdjointLeftInverse] is rejected at a
    category whose hom and proof levels are declared apart, while
    [Au ⟶ Xu] is accepted there -- so this identification too is a
    donor's and not this development's.  [HasColimitsOfShape] and
    [Diagonal] are rejected at the same levels (measured, not pinned
    separately: they are already pinned above at the other
    identification, and one command cannot separate two).

    [ConstantColimits] is rejected there as well, but that says nothing
    of its own: [HasColimitsOfShape] is one of its fields, so it cannot
    be tested apart from a donor -- the trap Test/ProbeRingLattice340.v
    records for [MonoidObject].

--------
** (4) 宇宙：在两类中，hom 和 proof 一致

    否定 9（可形成性）。在某个 category 中，[LeftAdjointLeftInverse] 被拒绝，该 category 的 hom 和 proof 层次被声明为分开，而 [Au ⟶ Xu] 在那里被接受——因此这种识别也是捐赠者的，而不是本开发的。[HasColimitsOfShape] 和 [Diagonal] 在相同的层次被拒绝（测量的，而不是单独固定的：它们已经在另一个识别中固定了，且一个命令无法区分两个）。

    [ConstantColimits] 也在那里被拒绝，但这本身并没有说明任何问题：[HasColimitsOfShape] 是它的一个字段，因此不能在没有捐赠者的情况下进行测试——陷阱 Test/ProbeRingLattice340.v 为 [MonoidObject] 记录了信息。
*)

Section HomProof.

Universes ao ah ap xo xh xp.
Constraint ah < ap.

Context (Au : Category@{ao ah ap}).
Context (Xu : Category@{xo xh xp}).

Check (obj[Au]).
Check (Au ⟶ Xu).

Fail Check (@LeftAdjointLeftInverse Au Xu).

End HomProof.

(* ------------------------------------------------------------------ *)
(**
** (5) Readbacks the target's header claims, and the one it
       withdraws

--------
** (5) 重读目标的报头声明，以及它撤回的内容
*)

Example probe_eval_retracts {J C : Category} (j : J) (c : C) :
  fobj[@EvalAt J C j] Δ[J](c) = c := eq_refl.

Example probe_colimit_is_EvalAt {J C : Category} (T : @Terminal J)
  (F : [J, C]) :
  fobj[ColimitFunctor (@terminal_colimits J C T)] F
    = fobj[@EvalAt J C (@terminal_obj J T)] F := eq_refl.

(*
Negative 10 (CONVERSION).  The ARROW action of the same comparison
   does not convert: [ColimitFunctor]'s arrow action is the colimit
   mediator and [EvalAt]'s is the component, two different terms.  Only
   the object clause above is claimed.

--------
负10（转换）。同一比较的箭头动作不进行转换：[ColimitFunctor] 的箭头动作是余极限中介，[EvalAt] 的则是组成部分，这是两个不同的术语。上面的对象条款是唯一被主张的。
*)
Fail Example probe_colimit_is_EvalAt_arrow {J C : Category}
  (T : @Terminal J) (F G : [J, C]) (t : F ~{[J, C]}~> G) :
  fmap[ColimitFunctor (@terminal_colimits J C T)] t
    = fmap[@EvalAt J C (@terminal_obj J T)] t := eq_refl.

Example probe_two_lali_left (C : Category) :
  lali_left (two_lali C)
    = ColimitFunctor (@terminal_colimits _2 C Two_Terminal) := eq_refl.

Example probe_lari_left {J C : Category} (I : @Initial J) :
  lari_left (@initial_lari_of_limit J C I) = @Diagonal C J := eq_refl.
