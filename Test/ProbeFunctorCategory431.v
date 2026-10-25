(**
* Probe for Adjunction/FunctorCategory.v (issue #431)

    Pins the measured boundaries of the functor-category adjunctions and
    of Mac Lane's V.5 Remark 1 with negatives of three kinds, kept
    lexically apart: CONVERSION (N1: the square of left adjoints
    [postcompose F ◯ Δ] and [Δ ◯ F] is NOT an identity of functor records
    — the two [fmap] fields differ by a [fmap_id] — and holds only as the
    natural isomorphism [square_iso]; N5: the delivered adjunction's own
    [unit] accessor is the whiskered original at [≈] only, its [fmap_id]
    residue refusing the [eq_refl] form that the CONSTRUCTED
    [postcompose_unit] satisfies); TYPING (N2-N3: the two induced
    adjunctions have a direction — postcomposition keeps [F ⊣ G]'s,
    precomposition reverses it — and the opposite ascriptions are
    refused); UNIVERSE (N4: the functor category [[J, X]] identifies J's
    hom level with X's, Instance/Fun.v's [Fun] pin, so nothing in this
    development can hold at a shape whose hom level is below the
    target's).  The [eq_refl] readbacks are positive controls: the induced
    unit and counit are the whiskered originals ON THE NOSE, and the two
    functors [postcompose] / [precompose] are #318's [Postcompose] and
    Theory/Kan/Extension.v's [Induced] unchanged.  Each refutation was
    stripped one at a time in a copy of the whole file; the import list
    mirrors the target's.

--------
* 探测 Adjunction/FunctorCategory.v（问题 #431）

固定函子范畴伴随及麦克莱恩 V.5 注释 1 的测量界限，并用三种类型的否定表示，保持词汇上的分离：转换 (N1：左伴随 [postcompose F ◯ Δ] 和 [Δ ◯ F] 的平方 **不是** 函子记录的恒等 —— 两个 [fmap] 字段相差一个 [fmap_id] —— 仅在自然同构 [square_iso] 下成立；N5：所给出的伴随自身的 [unit] 存取器仅在 [≈] 处为原始的 whiskered，[fmap_id] 残余拒绝符合 CONSTRUCTED [postcompose_unit] 的 [eq_refl] 形式)；类型 (N2-N3：两个诱导的伴随具有方向性 —— 后组合保持 [F ⊣ G]，前组合则反向 —— 并且不接受相反的赋值)；宇宙 (N4：函子范畴 [[J, X]] 将 J 的同态层与 X 的同态层相识别，Instance/Fun.v 的 [Fun] 固定针，因此此开发中不可能在同态层低于目标的形态上成立)。
[eq_refl] 的回读是阳性对照：诱导的单位和余单位正好是带胡须的原始对象，两者完全匹配，并且两个函子 [postcompose] / [precompose] 是 #318 的 [Postcompose] 和 Theory/Kan/Extension.v 的 [Induced]，未做修改。每一次反驳都是在整个文件的副本中逐个剥离；导入列表与目标文件一致。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Construction.Postcompose.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.FunctorCategory.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe431_absent_name.

(** ** A: CONVERSION — the square of left adjoints is not strict / ** A：转换——左伴随的平方不是严格的 *)

Section SquareStrict.

Context {J X A : Category}.
Context (F : X ⟶ A).

(*
control: the square holds as a natural isomorphism with identity
   components

--------
控制：该方形作为具有恒等分量的自然同构保持不变
*)
Check (square_iso (J:=J) F
         : postcompose F ◯ @Diagonal X J ≅[Fun] @Diagonal A J ◯ F).
Example p431_square_component (x : X) (j : J) :
  transform[to (square_iso (J:=J) F)] x j = @id A (F x) := eq_refl.

(*
N1 CONVERSION: as functor records the two composites differ in their
   [fmap] field ([fmap[F] id] against [id])

--------
N1 转换：作为函子记录，两个复合体在它们的 [fmap] 字段（[fmap[F] id 对比 [id]）上有所不同
*)
Fail Example p431_square_not_strict :
  postcompose (J:=J) F ◯ @Diagonal X J = @Diagonal A J ◯ F := eq_refl.

End SquareStrict.

Section AccessorResidue.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

(* controls: the constructed unit on the nose, the adjunction's own at [≈] / 控制：位于鼻子的建构单位，[≈]上的附加组件自身 *)
Check (postcompose_unit_component (J:=J) Adj).
Check (postcompose_adjunction_unit (J:=J) Adj).

(*
N5 CONVERSION: the adjunction's own [unit] accessor carries a [fmap_id]
   residue over the whiskered original

--------
N5 转换：该附加体自身的 [unit] 访问器携带了一个 [fmap_id] 残余在带胡须的原件上
*)
Fail Example p431_adjunction_unit_not_definitional (S : J ⟶ X) (j : J) :
  transform[@Category.Theory.Adjunction.unit _ _ _ _
              (postcompose_adjunction (J:=J) Adj) S] j
    = @Category.Theory.Adjunction.unit _ _ F G Adj (S j) := eq_refl.

End AccessorResidue.

(** ** B: TYPING — each induced adjunction has one direction / ** B: 输入 — 每个引出附着都有一个方向 *)

Section PostDirection.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

(* control *)
Check (postcompose_adjunction (J:=J) Adj : postcompose F ⊣ postcompose G).

(* N2 TYPING: postcomposition keeps the direction of [F ⊣ G] / N2 打字：后组合保持 [F ⊣ G] 的方向 *)
Fail Check (postcompose_adjunction (J:=J) Adj : postcompose G ⊣ postcompose F).

End PostDirection.

Section PreDirection.

Context {C D E : Category}.
Context {F : C ⟶ D} {G : D ⟶ C}.
Context (Adj : F ⊣ G).

(* control *)
Check (precompose_adjunction (E:=E) Adj : precompose G ⊣ precompose F).

(* N3 TYPING: precomposition reverses it; [F^* ⊣ G^*] is refused / N3 打字：预组合会将其反转；[F^* ⊣ G^*] 被拒绝 *)
Fail Check (precompose_adjunction (E:=E) Adj : precompose F ⊣ precompose G).

End PreDirection.

(** ** C: UNIVERSE — the functor category identifies the hom levels / ** C: 宇宙 — 函子范畴识别同态层次 *)

Monomorphic Universe jo jh xo xh.
Monomorphic Constraint jh < xh.

Section HomLevels.

Context (Jw : Category@{jo jh jh}).
Context (Xw : Category@{xo xh xh}).

(* controls: the two categories form at distinct hom levels / 控制：这两类在不同的同源水平形成 *)
Check Jw.
Check Xw.

(*
N4 UNIVERSE: [[Jw, Xw]] needs [jh = xh] (Instance/Fun.v's [Fun]) — the
   pin every constant of the target inherits

--------
N4 宇宙：[[Jw, Xw]] 需要 [jh = xh]（实例/Fun.v 的 [Fun]）——目标继承的每个常量的引脚
*)
Fail Check ([Jw, Xw]).

End HomLevels.

(** ** D: readbacks / ** D：复读 *)

Section Readbacks.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).

Example p431_postcompose_is_Postcompose :
  postcompose (J:=J) F = Postcompose (D:=J) F := eq_refl.

Example p431_unit_is_whiskered_original (S : J ⟶ X) (j : J) :
  transform[transform[postcompose_unit Adj] S] j
    = @Category.Theory.Adjunction.unit _ _ F G Adj (S j) := eq_refl.

Example p431_counit_is_whiskered_original (T : J ⟶ A) (j : J) :
  transform[transform[postcompose_counit Adj] T] j
    = @Category.Theory.Adjunction.counit _ _ F G Adj (T j) := eq_refl.

End Readbacks.

Section Readbacks2.

Context {C D E : Category}.
Context {F : C ⟶ D} {G : D ⟶ C}.
Context (Adj : F ⊣ G).

Example p431_precompose_is_Induced :
  precompose (E:=E) F = @Induced C D F E := eq_refl.

Example p431_pre_unit_is_whiskered_original (S : C ⟶ E) (c : C) :
  transform[transform[precompose_unit (E:=E) Adj] S] c
    = fmap[S] (@Category.Theory.Adjunction.unit _ _ F G Adj c) := eq_refl.

End Readbacks2.

Section RemarkReadbacks.

Context {J X A : Category}.
Context {F : X ⟶ A} {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (LX : HasLimitsOfShape J X).
Context (LA : HasLimitsOfShape J A).

Check (Lim_commutes_right_adjoint Adj LX LA
         : LimitFunctor LX ◯ postcompose (J:=J) G ≈ G ◯ LimitFunctor LA).
Check (fun T : J ⟶ A =>
         lim_of_right_adjoint Adj LX LA T : lim_obj LX (G ◯ T) ≅ G (lim_obj LA T)).
Check (fun T : J ⟶ A => right_adjoint_carries_lim_counit Adj LA T).
Check (fun (T : J ⟶ A) (j : J) => @carried_leg_is_counit J X A G LA T j).

End RemarkReadbacks.

(** ** Guard block / ** 防守格挡 *)

Check @postcompose.
Check @precompose.
Check @postcompose_adjunction.
Check @precompose_adjunction.
Check @postcompose_unit.
Check @postcompose_counit.
Check @precompose_unit.
Check @square_iso.
Check @Lim_commutes_right_adjoint.
Check @lim_of_right_adjoint.
Check @right_adjoint_carries_lim_counit.
Check @Postcompose.
Check @Induced.
Check @Diagonal.
Check @Fun.
Check @Adjunction.
Check @Category.
Check @id.
Check @to.
Check @transform.
Check @fmap.
Check @Category.Theory.Adjunction.unit.
Check @Category.Theory.Adjunction.counit.
