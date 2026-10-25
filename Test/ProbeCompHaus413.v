(**
* Probe for Instance/Top/CompHaus.v and Construction/Subcategory/Creation.v
    (issue #413)

    Pins the measured boundaries of the compact-Hausdorff development: what
    is formable, what converts, and exactly where the classical arguments
    stop constructively.  Every refutation command below was stripped ONE
    AT A TIME in a copy of the whole file and compiled alone with its error
    read, so each refusal is of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 SORT/TYPING  the pairing into the truncated product is NOT shown
                     continuous by eliminating the squashed box datum into
                     the [Type]-valued [IsOpen Z]: the eliminator's motive
                     must be a [Prop] ("has type Type while it is expected
                     to have type Prop"); eliminating into [True] is
                     accepted (control).  N1 and N2 both say "universe
                     inconsistency"; they are told apart by "expected to
                     have type Prop" against "because o < …".
     N2 UNIVERSE     the other route to that continuity, a union indexed by
                     ALL boxes inside [W], is refused because the box datum
                     lives one universe above the space's points and
                     [open_union] indexes at the points' level; a union
                     indexed by the points themselves is accepted (control).
     N3 TYPING       [CompHaus_Forget] lands in [Sets], not in [Top] — a
                     plain has-type mismatch.
     N4 TYPING       [compact_hausdorff_bijection_iso] is NOT an isomorphism
                     without its decidability hypothesis: applied to the six
                     other arguments it still has a function type, refused
                     at [X ≅[Top] Y] ("has type … → X ≅ Y").

    POSITIVE, recorded because a survey predicted the opposite: the issue's
    pinned statement [CreatesLimit K CompHaus_Forget] IS formable, for a
    diagram out of any shape [J] — the forgetful functor lands in the [Sets]
    whose hom level is [Top]'s, so the limit-cone predicates apply on both
    sides.  What is not delivered is a PROOF of it (see the target's header).

    Readbacks at [eq_refl]: [CompHaus] IS [CompactHausdorffSpaces]; the
    inclusion's object map is the first projection; the truncated product's
    projections are [fst] and [snd] on points; the bijection isomorphism's
    forward map is [f] itself; the generic creation lemma's lift keeps the
    apex and the legs.  Non-vacuity: the per-open inverse lemma is applied
    at the one-point space with the identity bijection and the whole space
    as the decidable open.

    Guard coverage: every constant a negative names is also named outside a
    refutation command (the guard block at the end) — under the plain
    tokenization 31 identifiers inside, 29 also outside, the two exceptions
    exhaustively the instrument's absent name and the bound variable [z] of
    N1's lambda — so a renamed or removed constant breaks the build on a
    positive line rather than letting a refutation pass for the wrong
    reason.

--------
* 探查实例/顶层/CompHaus.v 和 构造/子类别/创建.v（问题 #413）

固定紧豪斯多夫发展测得的边界：什么是可形成的，什么会转换，以及经典论证在何处停止构造性地进行。下面的每个反驳命令都是在整份文件的副本中一次删除一个，并单独编译其错误读取的，所以每个拒绝的类型正如其标签所示。

编号：
     仪器 一个缺失的名称，被拒绝——反驳关键字
                     位于此文件中。N1 排序/打字  该配对进入截断的产品未显示
                     通过将压缩的框数据消除到连续的
                     [Type] 值 [IsOpen Z]：消除器的动机
                     必须是 [Prop]（“类型为 Type，而预期
                     类型为 Prop”）；消除到 [True] 被接受（控制）。N1 和 N2 都说“宇宙不一致”；它们通过“预期类型为 Prop”与“因为 o < …”区分。
N2 宇宙     另一种通向该连续性的方式，即由 [W] 内的所有盒子索引的联合，被拒绝，因为盒子数据位于空间点之上的一个宇宙，而 [open_union] 在点的层级进行索引；由点本身索引的联合被接受（控制）。 N3 类型     [CompHaus_Forget] 落入 [Sets]，而不是 [Top] — 简单类型不匹配。 N4 类型     [compact_hausdorff_bijection_iso] 在没有其可判定性假设的情况下不是同构：应用于其他六个参数时，它仍然具有函数类型，在 [X ≅[Top] Y] 被拒绝（“具有类型 … → X ≅ Y”）。

正面记录，因为一项调查预测了相反的情况：问题的固定语句 [CreatesLimit K CompHaus_Forget] 是可形成的，对于任意形状 [J] 的图表 —— 忘记函子落在 [Sets] 中，其同态层级是 [Top] 的，因此极限锥谓词在两边都适用。未提供的是其证明（见目标的标题）。

在 [eq_refl] 的回读：[CompHaus] 是 [CompactHausdorffSpaces]；包含的对象映射是第一个投影；截断积的投影在点上分别为 [fst] 和 [snd]；双射同构的前向映射是 [f] 本身；通用创建引理的提升保持顶点和边。非空性：在单点空间上应用每开逆引理，双射为恒等映射，整个空间作为可判定开集。

守卫覆盖：每个恒定的负名称也会在驳斥命令之外被命名（最后的守卫块）——在普通分词下，内部有 31 个标识符，外部也有 29 个，两个例外是乐器缺失的名称和 N1 的 lambda 的绑定变量 [z]——因此，重命名或删除常量会在正行上破坏构建，而不是因为错误的原因让驳斥通过。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Creation.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.CompHaus.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe413_absent_name.

(** ** A: the two walls in front of the product's universal property / ** A: 产品通用属性前的两面墙 *)

Section Fork.
Universe o o1.
Constraint o < o1.
Context (X Y Z : TopSpace@{o}) (f : Z ~{Top}~> X) (g : Z ~{Top}~> Y) (z0 : Z).

(* control: eliminating the squashed box datum into a Prop is accepted / 控制：将压扁的盒子数据消除到 Prop 中是被接受的 *)
Check (fun (W : sq_carrier X Y → Type@{o}) (HW : sq_open X Y W)
           (p : sq_carrier X Y) (w : W p) => (snd HW p w) True).

(* N1 TYPING *)
Fail Check (fun (W : sq_carrier X Y → Type@{o}) (HW : sq_open X Y W)
                (p : sq_carrier X Y) (w : W p) =>
              (snd HW p w) (IsOpen Z (fun z => W (sq_fork_map X Y f g z)))).

(* control: a union indexed by the points of Z is accepted / 控制：按 Z 点索引的并集被接受 *)
Check (@open_union Z (carrier (top_carrier Z))).

(* N2 UNIVERSE *)
Fail Check (@open_union Z (sq_boxdata X Y (fun _ => poly_unit)
                              (sq_fork_map X Y f g z0))).
End Fork.

(** ** B: the forgetful functor and the pinned creation statement / ** B：遗忘函子与固定创建声明 *)

(* POSITIVE: the issue's statement is formable / 积极：问题的陈述是可形成的 *)
Check (fun (J : Category) (K : J ⟶ CompHaus) =>
         @CreatesLimit J CompHaus _ K CompHaus_Forget).

(* control: creation by the inclusion, the delivered conditional / 控制：通过包含进行的创建，所传递的条件 *)
Check (fun (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
           (J : Category) (K : J ⟶ CompHaus) =>
         CompHaus_Incl_CreatesLimit closed K : CreatesLimit K CompHaus_Incl).

(* N3 TYPING *)
Fail Check (CompHaus_Forget : CompHaus ⟶ Top).

(** ** C: the bijection theorem needs its hypothesis / ** C：双射定理需要其假设 *)

Section Bij.
Context {X Y : TopSpace} (f : X ~{Top}~> Y)
        (g : SetoidMorphism (top_carrier Y) (top_carrier X))
        (Hfg : ∀ y : Y, continuous_map f (g y) ≈ y)
        (Hgf : ∀ x : X, g (continuous_map f x) ≈ x)
        (HX : IsCompact X) (HY : IsHausdorff Y)
        (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)).

(* control *)
Check (compact_hausdorff_bijection_iso f g Hfg Hgf HX HY dec : X ≅[Top] Y).

(* N4 TYPING *)
Fail Check (compact_hausdorff_bijection_iso f g Hfg Hgf HX HY : X ≅[Top] Y).

(* readback: the forward map is f itself / 回传：前向映射是 f 本身 *)
Example p413_iso_to :
  to (compact_hausdorff_bijection_iso f g Hfg Hgf HX HY dec) = f := eq_refl.
End Bij.

(* non-vacuity: the one-point space, the identity, the whole open / 非空性：一点空间、同一性、整体开放 *)
Definition p413_point_inverse_open :
  IsOpen Point_Top
    (fun y => (fun _ : Point_Top => poly_unit)
                (continuous_map (@id Top Point_Top) y)) :=
  inverse_open_of_decidable (X := Point_Top) (Y := Point_Top)
    (@id Top Point_Top) (continuous_map (@id Top Point_Top))
    (fun _ => reflexivity _) (fun _ => reflexivity _)
    Point_Compact Point_Hausdorff (fun _ => poly_unit) (open_whole _)
    (fun _ => inl ttt).

(** ** D: readbacks / ** D：复读 *)

Example p413_comphaus : CompHaus = CompactHausdorffSpaces := eq_refl.

Example p413_incl_obj (x : CompHaus) : fobj[CompHaus_Incl] x = `1 x := eq_refl.

Example p413_sq_fst (X Y : TopSpace) (p : sq_carrier X Y) :
  continuous_map (Top_sq_fst X Y) p = fst p := eq_refl.

Example p413_sq_snd (X Y : TopSpace) (p : sq_carrier X Y) :
  continuous_map (Top_sq_snd X Y) p = snd p := eq_refl.

Section LiftReadback.
Context {C : Category} (S : Subcategory C) (full : Full C S)
        (closed : ClosedUnderLimits S) {J : Category} (K : J ⟶ Sub C S)
        (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N).

Example p413_lift_apex :
  (`1 vertex_obj[creates_lift
                   (CreatesLimit := sub_CreatesLimit S full closed K) N HN])
  = vertex_obj[N] := eq_refl.

Example p413_lift_leg (x : J) :
  (`1 (cone_leg (creates_lift
                   (CreatesLimit := sub_CreatesLimit S full closed K) N HN) x))
  = cone_leg N x := eq_refl.
End LiftReadback.

(** ** Guard block / ** 防守格挡 *)

Check @CompHaus.
Check @CompHaus_Incl.
Check @CompHaus_Incl_Full.
Check @CompHaus_Incl_Faithful.
Check @CompHaus_Forget.
Check @CompHaus_Forget_Faithful.
Check @CompHaus_Incl_CreatesLimit.
Check @CompHaus_Complete_of.
Check @inverse_open_of_decidable.
Check @inverse_continuous_of_decidable.
Check @compact_hausdorff_bijection_iso.
Check @Top_sq_product.
Check @Top_sq_fst.
Check @Top_sq_snd.
Check @sq_carrier.
Check @sq_open.
Check @sq_boxdata.
Check @sq_fork_map.
Check @ClosedUnderLimits.
Check @sub_CreatesLimit.
Check @sub_CreatesAllLimits.
Check @sub_Complete.
Check @CreatesLimit.
Check @IsOpen.
Check @open_union.
Check @Top.
Check @Sets.
