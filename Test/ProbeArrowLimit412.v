Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Limit.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.One.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Probe: the measured boundaries of Construction/Arrow/Limit.v / * 探针：Construction/Arrow/Limit.v 的测量边界 *)

(*
Companion to Construction/Arrow/Limit.v (Mac Lane, Categories for the
   Working Mathematician, 2nd ed., §V.1 Exercise 3).  Everything that file
   claims at [eq_refl] is shipped there as an [Example]; what it cannot
   guard from inside are the REFUSALS its header records and the universe
   boundary a consumer meets.  Those are pinned here, from OUTSIDE the
   target, because an in-file [Fail] renames in lockstep with the constant
   it guards and so cannot detect a rename.  The concrete witness lives
   here too, because it costs three modules the target should not carry.

   FOUR negatives of THREE kinds — two CONVERSION, one TYPING, one
   UNIVERSE pinned by TWO [Fail] commands (the donor and the inherited
   refusal) — told apart by the error TEXT, plus one scope-free instrument
   check: five [Fail] commands beyond the instrument.  The kinds were read
   off the messages produced by stripping each [Fail] in turn, in a copy
   of this WHOLE file.

     N1  CONVERSION  [FCone comma_proj (comma_lift_cone K HT N HN)] is not
                   [N] as a whole RECORD, though its apex and every leg are
                   [N]'s on the nose (the two controls beside it): the
                   coherence field is a rebuilt proof and [≈] is
                   Type-valued.
     N2  CONVERSION  [Snd ◯ (comma_proj ◯ K)] is not [comma_proj2 ◯ K] as a
                   functor RECORD although both actions agree at [eq_refl]
                   (the two controls): [Compose]'s three law fields are
                   separate opaque obligations.  This is why the target
                   repackages [FCone Snd N] as [cod_cone N].  The same two
                   action controls are shipped for the [Fst]/[comma_proj1]
                   side, which the target's NOT DELIVERED paragraph cites.
     N3  TYPING    Supplying preservation on the DOMAIN side — a
                   [PreservesLimitCone (comma_proj1 ◯ K) S] — where the
                   theorem asks for [T] is a has-type mismatch between two
                   DIFFERENT types, with no universe clause; its trailing
                   [cannot unify] is on the two cone TYPES,
                   [Cone (comma_proj2 ◯ K)] against
                   [Cone (comma_proj1 ◯ K)], and not on two inhabitants of
                   one type, which is what separates it from N1 and N2.  The
                   correct hypothesis is the control.  Nothing is asked of
                   [S].
     N4  UNIVERSE  At a shape whose homs are declared strictly BELOW the
                   factors' homs, [Su ↓ Tu], the diagram [K] and a [Cone]
                   over it are ACCEPTED while the composite [comma_proj ◯ K]
                   is refused, firing at [K] with [Cannot enforce ch = jh]
                   — [Compose] is declared over three categories sharing
                   ONE hom-and-proof level.  [comma_proj_CreatesLimit] is
                   refused too, but NOT at that composite: it fires at its
                   shape argument [Ju], with [Cannot enforce jh = ah], its
                   own block equation [u0 = u6] met at an already-refused
                   argument (the #340 shape).  So the second [Fail] pins
                   the inherited boundary and does not independently
                   corroborate the [Compose] attribution, which rests on
                   the donor [Fail] alone.  The comma category is NOT a
                   donor: at [ah < bh] (the two factors' homs declared
                   apart) [Su ↓ Tu] is accepted, the control at the end.

   Every constant a negative names also appears in a [Check] outside every
   [Fail], so a rename breaks this file loudly instead of turning a [Fail]
   vacuously green.

--------
《Construction/Arrow/Limit.v》的伴随（Mac Lane，《为工作中的数学家而作的范畴论》，第2版，第V.1节 练习3）。该文件在 [eq_refl] 声明的一切内容都以 [Example] 的形式在此处提供；它无法从内部保护的是其头文件记录的 REFUSALS 以及使用者遇到的宇宙边界。这些在此被固定，因为它们来自目标之外的 OUTSIDE 文件，因为文件内的 [Fail] 会与它所保护的常量同步重命名，因此无法检测重命名。具体的实例也在这里，因为它会消耗目标不应携带的三个模块。

三种类型的四个否定——两个转换（CONVERSION），一个打字（TYPING），一个整体（UNIVERSE）通过两个[Fail]命令固定（捐赠者和继承的拒绝）——通过错误文本区分，加上一个无作用域的仪器检查：仪器之外的五个[Fail]命令。 这些类型是通过在该完整文件的副本中依次剥离每个[Fail]生成的消息中读取的。

N1 转换 [FCone comma_proj (comma_lift_cone K HT N HN)] 并非整体 RECORD 的 [N]，尽管它的顶端和每条分支都与 [N] 一致（旁边的两个控制）：相干域是重建的证明，[≈] 是类型值。N2 转换 [Snd ◯ (comma_proj ◯ K)] 并非作为函子 RECORD 的 [comma_proj2 ◯ K]，尽管两者操作在 [eq_refl]（两个控制）上相符：[Compose] 的三个法律域是独立的不透明义务。这就是目标将 [FCone Snd N] 重新打包为 [cod_cone N] 的原因。相同的两个操作控制用于 [Fst]/[comma_proj1] 端口，目标的“未交付”段落中提到。
N3  类型检查 在域(DOMAIN)端提供保存 — 一个 [PreservesLimitCone (comma_proj1 ◯ K) S] — 而定理要求 [T] 是一个类型不匹配的两个不同类型之间的问题，没有宇宙子句；它的尾随 [cannot unify] 位于两个锥形类型上，[Cone (comma_proj2 ◯ K)] 针对 [Cone (comma_proj1 ◯ K)]，而不是位于同一类型的两个元素上，这也是它与 N1 和 N2 的区别。正确的假设是控制。对 [S] 没有任何要求。
N4 宇宙 在一个其 Hom 被严格声明低于因子的 Hom 的形状上，[Su ↓ Tu]、图表 [K] 以及其上的 [Cone] 被接受，而复合 [comma_proj ◯ K] 被拒绝，在 [K] 以 [Cannot enforce ch = jh] 触发 —— [Compose] 被声明在三个共享一个 Hom-and-proof 级别的类别上。[comma_proj_CreatesLimit] 也被拒绝，但不是在那个复合上：它触发于其形状参数 [Ju]，使用 [Cannot enforce jh = ah]，其自身的区块方程 [u0 = u6] 在已被拒绝的参数（#340 形状）上被满足。
因此，第二个 [Fail] 固定了继承的边界，并没有独立证实 [Compose] 的归属，该归属仅依赖于捐赠者 [Fail]。逗号类别不是捐赠者：在 [ah < bh]（两个因素的同态单独声明）处，[Su ↓ Tu] 被接受，最后的控制。

每个常量负名称也出现在每个 [Fail] 之外的 [Check] 中，因此重命名会明显破坏此文件，而不是使 [Fail] 空洞地变为绿色。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check probe412_no_such_constant.

(** ** Guards *)

Check @comma_lift_cone.
Check @comma_lift_arrow.
Check @comma_proj_CreatesLimit.
Check @comma_proj.
Check @comma_proj1.
Check @comma_proj2.
Check @Comma.
Check @FCone.
Check @Cone.
Check @cone_leg.
Check @vertex_obj.
Check @Snd.
Check @Fst.
Check @Compose.
Check @PreservesLimitCone.
Check @IsLimitCone.
Check @Id_PreservesLimitCone.
Check @Arrow_Complete.

(** ** N1, N2: the records behind the on-the-nose readbacks / ** N1, N2：精确回读背后的记录 *)

Section Records.

Context {A B C : Category} {S : A ⟶ C} {T : B ⟶ C} {J : Category}.
Context (K : J ⟶ (S ↓ T)) (HT : PreservesLimitCone (comma_proj2 ◯ K) T).

(* Controls: the lift's image has [N]'s apex and legs on the nose. / 控制：电梯的图像在机头上有[N]的顶点和支腿。 *)
Example probe412_ctrl_apex (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  vertex_obj[FCone comma_proj (comma_lift_cone K HT N HN)] = vertex_obj[N]
  := eq_refl.

Example probe412_ctrl_leg (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N)
  (j : J) :
  cone_leg (FCone comma_proj (comma_lift_cone K HT N HN)) j = cone_leg N j
  := eq_refl.

(* N1: CONVERSION — the whole record is not. / N1: 转换 — 整个记录不是。 *)
Fail Example probe412_n1 (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  FCone comma_proj (comma_lift_cone K HT N HN) = N := eq_refl.

(* Controls: the two codomain-diagram functors agree on both actions. / 控制：两个余域图函子在两个作用上是一致的。 *)
Example probe412_ctrl_fobj :
  fobj[Snd ◯ (comma_proj ◯ K)] = fobj[comma_proj2 ◯ K] := eq_refl.

Example probe412_ctrl_fmap :
  @fmap _ _ (Snd ◯ (comma_proj ◯ K)) = @fmap _ _ (comma_proj2 ◯ K) := eq_refl.

(* N2: CONVERSION — not as records. / N2：转换——不是作为记录。 *)
Fail Example probe412_n2 : Snd ◯ (comma_proj ◯ K) = comma_proj2 ◯ K := eq_refl.

(*
Controls for the DOMAIN side, which the target's NOT DELIVERED paragraph
   cites: the two domain-diagram functors also agree on both actions.

--------
针对 DOMAIN 端的控制，目标未引用的段落指出：两个域图函子在两个动作上也一致。
*)
Example probe412_ctrl_fobj1 :
  fobj[Fst ◯ (comma_proj ◯ K)] = fobj[comma_proj1 ◯ K] := eq_refl.

Example probe412_ctrl_fmap1 :
  @fmap _ _ (Fst ◯ (comma_proj ◯ K)) = @fmap _ _ (comma_proj1 ◯ K) := eq_refl.

End Records.

(** ** N3: the hypothesis is on the codomain side / ** N3：假设在值域侧 *)

Section Handedness.

Context {A B C : Category} {S : A ⟶ C} {T : B ⟶ C} {J : Category}.
Context (K : J ⟶ (S ↓ T)).
Context (HT : PreservesLimitCone (comma_proj2 ◯ K) T).
Context (HS : PreservesLimitCone (comma_proj1 ◯ K) S).

(* Control. *)
Check (comma_proj_CreatesLimit K HT).

(* N3: TYPING. *)
Fail Check (comma_proj_CreatesLimit K HS).

End Handedness.

(**
** N4: the universe boundary, with the comma, the diagram and a cone as
       controls

--------
** N4：宇宙边界，带有逗号、图表和一个圆锥作为控制
*)

Section UniverseBoundary.

Universes jo jh ao ah co ch.
Constraint jh < ah.

Context (Ju : Category@{jo jh jh}).
Context (Au : Category@{ao ah ah}).
Context (Cu : Category@{co ch ch}).
Context (Su : Au ⟶ Cu) (Tu : Au ⟶ Cu).
Context (K : Ju ⟶ (Su ↓ Tu)).

(* Controls. / 控制。 *)
Check (Su ↓ Tu).
Check K.
Check (@Cone Ju (Su ↓ Tu) K).

(* N4: UNIVERSE — the donor. / N4：宇宙——捐赠者。 *)
Fail Check (comma_proj ◯ K).

(* Inherited: fires at the shape argument [Ju], [Cannot enforce jh = ah]. / 继承自：对形状参数 [Ju]、[Cannot enforce jh = ah] 触发。 *)
Fail Check (@comma_proj_CreatesLimit Au Au Cu Su Tu Ju K).

End UniverseBoundary.

(* The comma category itself keeps the two factors' hom levels apart. / 逗号范畴本身将两个因子的同态层级分开。 *)

Section CommaApart.

Universes ao ah bo bh co ch.
Constraint ah < bh.

Context (Au : Category@{ao ah ah}) (Bu : Category@{bo bh bh}).
Context (Cu : Category@{co ch ch}).
Context (Su : Au ⟶ Cu) (Tu : Bu ⟶ Cu).

Check (Su ↓ Tu).

End CommaApart.

(* No [Set] pin on the arrow-category statements. / 箭头类别语句上没有 [Set] 引脚。 *)

Section AboveSet.

Universes co ch.
Constraint Set < ch.

Context (Cu : Category@{co ch ch}).

Check (@Arrow Cu).
Check (@Arrow_Complete Cu).

End AboveSet.

(** ** The witness: the created arrow computes / ** 证人：被创造的箭在计算 *)

(*
Over [Coq] at the point shape [_1], the diagram constant at the arrow
   [negb].  Structure/Limit/Initial.v's [initial_cone] over [One_Initial]
   is limiting with its mediator definitionally the leg, so the created
   arrow reduces all the way.

--------
在点形状 [_1] 的 [Coq] 上，箭头 [negb] 的图示常数。结构/限制/初始.v 的 [initial_cone] 在 [One_Initial] 上有限，它的中介在定义上是腿，因此创建的箭头会一路减少。
*)

Program Definition NegK : _1 ⟶ @Arrow Coq := {|
  fobj := fun _ => ((bool, bool); negb);
  fmap := fun _ _ _ => ((id, id); _)
|}.

Definition NegN : Cone (comma_proj ◯ NegK) :=
  @initial_cone _1 (Coq ∏ Coq) One_Initial (comma_proj ◯ NegK).

Definition NegHN : IsLimitCone NegN :=
  @initial_IsLimitCone _1 (Coq ∏ Coq) One_Initial (comma_proj ◯ NegK).

Definition neg_created :=
  comma_lift_arrow NegK (Id_PreservesLimitCone _) NegN NegHN.

Example neg_created_is_negb : neg_created = negb := eq_refl.
Example neg_created_true : neg_created true = false := eq_refl.
Example neg_created_false : neg_created false = true := eq_refl.

Example neg_lift_apex :
  (`1 vertex_obj[comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN])
    = (bool, bool) := eq_refl.

Example neg_lift_leg :
  (`1 (cone_leg (comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN)
         ttt))
    = (id, id) := eq_refl.

(* The created cone is limiting, through the general theorem. / 通过一般定理，所创建的圆锥是有限制的。 *)
Definition neg_lift_limiting :
  IsLimitCone (comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN) :=
  creates_limiting (arrow_proj_creates_limits NegK) NegN NegHN.
