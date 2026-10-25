(*
The Grp layer's carriers are sets: what that moved, and what it refuses.

   Since the PR "algebraic carriers are sets" (2026-09-17) every [GrpObject]
   carries [grp_prop] (Instance/Grp.v), the property that its carrier's `≈`
   is logically equivalent to a [Prop]-valued relation.  Three relations in
   the Grp layer changed sort or shape as a result, and this file pins each
   one from both sides:

     [am_eq]      Instance/Grp/Pushout.v  -- the amalgam's congruence, now a
                  [Prop] INDUCTIVE;
     [quot_rel]   Instance/Grp/Quotient.v -- unchanged itself, but the
                  quotient group's `≈` is now its [inhabited] TRUNCATION
                  ([quot_equiv]);
     the free group's `≈` -- Instance/Grp/Free.v -- now the [inhabited]
                  truncation of the free groupoid's hom-equality ([fg_equiv]).

   Being in [Prop], each ELIMINATES ONLY INTO [Prop].  That is the whole
   content of the change, and it is what the negatives below pin.  The
   positive controls show what is NOT lost: every consumer reaches its
   [Type]-valued goal through the TARGET group's own [grp_prop], and the
   free-forgetful adjunction still types over an ARBITRARY object of [Sets].

   METHOD.  A [Fail Lemma <statement>] would be vacuous here: each statement
   is well formed whatever the relation's sort, and only the ELIMINATION is
   refused.  Each negative is therefore a [Fail Definition … :=
   ltac:(<tactic>)], carrying the proof.  Each was stripped once, in a copy
   of this WHOLE file, and the first error line is quoted beside it.

   The import list is the union of the three target files' own.

--------
Grp 层的载体是集合：它移动的，以及它拒绝的。

自从 PR “代数承载体是集合” (2026-09-17) 每个 [GrpObject] 承载 [grp_prop] (Instance/Grp.v) 以来，它的承载体的 `≈` 是与 [Prop] 值关系逻辑等价的性质。在 Grp 层的三个关系因此改变了类型或形状，这个文件固定了每一个关系的两个方面：

[am_eq]      实例/群/推导.v  -- 合并体的一致性，现在是一个
                  [Prop] 归纳;
     [quot_rel]   实例/群/商群.v -- 自身未改变，但商群的 `≈` 现在是其 [inhabited] 截断
                  ([quot_equiv]);
     自由群的 `≈` -- 实例/群/自由.v -- 现在是自由群族的同态相等的 [inhabited]
                  截断 ([fg_equiv])。

在 [Prop] 中，每一个只会消除到 [Prop]。这就是整个变更的内容，也是下面负面情况所显示的。正控制显示出什么不会丢失：每个消费者通过目标组自身的 [grp_prop] 达到其 [Type] 值的目标，而且自由遗忘的附加结构仍然可以对 [Sets] 的任意对象进行类型化。

方法。这里使用 [Fail Lemma <statement>] 是空洞的：无论关系的种类如何，每个语句都是良构的，只有消去被拒绝。因此，每个否定都是一个 [Fail Definition … := ltac:(<tactic>)]，携带证明。每个都被剥离一次，在这个整个文件的一个副本中，第一个错误行被引用在旁边。

导入列表是三个目标文件自身的导入列表的并集。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Free.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Instrument check: this file's [Fail] is a real one / ** 仪器检查：此文件的 [Fail] 是真正的 *)

(*
Scope-free: a statement that is simply ill-typed, so that a [Fail] which
   silently accepted everything would be caught here.

--------
无作用域：一个语句，它本身就是类型错误的，因此即使一个静默接受一切的 [Fail] 也会在这里被捕获。
*)
Fail Definition instrument_check : nat := true.

(* ------------------------------------------------------------------------ *)
(** ** (1) [am_eq] is a [Prop] inductive / ** (1) [am_eq] 是一种 [Prop] 感应式 *)

Section AmEq.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(*
NEGATIVE 1.  A bare elimination of [am_eq] into a [Type]-valued goal.
   Stripped in a copy of this whole file; first error line:

     Error: Cannot find the elimination combinator am_eq_rect, the
     elimination of the inductive definition am_eq on sort Type is probably
     not allowed.

   ([am_eq_ind] and [am_eq_sind] do exist; [am_eq_rect] and [am_eq_rec] do
   not, which is exactly what a [Prop] inductive gets.)

--------
负面 1. 将 [am_eq] 单纯消解为 [Type] 值的目标。
   在整个文件的副本中被剥离；第一行错误：

     错误：无法找到消解组合子 am_eq_rect，可能不允许对类型为 Type 的归纳定义 am_eq 进行消解。

   （[am_eq_ind] 和 [am_eq_sind] 确实存在；[am_eq_rect] 和 [am_eq_rec] 不存在，这正是 [Prop] 归纳所得到的结果。）
*)
Fail Definition am_eq_eliminates_into_Type
  (u v : AmTerm B C) (He : am_eq f g u v) : poly_unit :=
  ltac:(induction He).

(*
CONTROL 1a.  Two constructors of [am_eq] carry a [Type]-valued `≈`
   premise, and both are still accepted verbatim: a [Prop] inductive MAY
   store [Type]-valued data, it simply may not be eliminated into [Type].

--------
控制 1a。[am_eq] 的两个构造函数都携带一个 [Type] 值的 `≈` 前提，并且都仍然被逐字接受：一个 [Prop] 归纳可以存储 [Type] 值的数据，它只是不能被归约为 [Type]。
*)
Definition am_eq_stores_a_Type_premise (b b' : carrier B) (H : b ≈ b') :
  am_eq f g (am_l b) (am_l b') := ae_l_resp b b' H.

Definition am_eq_stores_a_Type_premise_r (c c' : carrier C) (H : c ≈ c') :
  am_eq f g (am_r c) (am_r c') := ae_r_resp c c' H.

(*
CONTROL 1b.  The relation IS the amalgam's own `≈`, and the amalgam's
   [grp_prop] reads it back on the nose in both directions.

--------
控制 1b。该关系是合并体自身的 `≈`，并且合并体的 [grp_prop] 在两个方向上都能精确地读回它。
*)
Definition am_eq_is_the_amalgam_equality (u v : AmTerm B C) :
  @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v = am_eq f g u v
  := eq_refl.

Definition am_eq_pequiv_to (u v : AmTerm B C)
  (H : @pequiv _ _ (grp_prop (AmalgamGrp f g)) u v) :
  @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v :=
  pequiv_to u v H.

Definition am_eq_pequiv_from (u v : AmTerm B C)
  (H : @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v) :
  @pequiv _ _ (grp_prop (AmalgamGrp f g)) u v :=
  pequiv_from u v H.

End AmEq.

(*
CONTROL 1c, APPLIED.  The one elimination of [am_eq] in the tree,
   [am_eval_respects], survives: it runs under the TARGET group's [pequiv]
   and comes back with [pequiv_to].  Here it is applied at the mediator.

--------
控制 1c，已应用。树中唯一被消除的 [am_eq]，[am_eval_respects] 存活：它在 TARGET 组的 [pequiv] 下运行，并带着 [pequiv_to] 返回。这里它在中介者处被应用。
*)
Definition am_med_applies
  {A B C : GrpObject} (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
  {Q : GrpObject} (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
  (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) :
  AmalgamGrp f g ~{Grp}~> Q :=
  am_med f g q1 q2 Hcomm.

(* ------------------------------------------------------------------------ *)
(** ** (2) [QuotientGrp]'s `≈` is the truncation of [quot_rel] / ** (2) [QuotientGrp] 的 `≈` 是 [quot_rel] 的截断 *)

Section Quot.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

(* The truncation, read back at [eq_refl]. / 截断，在 [eq_refl] 处回读。 *)
Definition quot_equiv_is_inhabited_quot_rel (a b : carrier G) :
  @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b
    = inhabited (quot_rel N a b) := eq_refl.

(*
NEGATIVE 2.  A [Type] destruct of a quotient equation: the witness is
   asked for in a [Type]-valued goal.  Stripped in a copy of this whole
   file; first error line:

     Error:
     Incorrect elimination in the inductive type "inhabited":
     the return type has sort "Type" while it should be SProp or Prop.

   [quot_rel N a b] is [sub_mem N (a * b⁻¹)], which stays [Type]-valued --
   its consumers READ THE WITNESS (Instance/Grp/Quotient/Isomorphism.v's
   [image_med]) -- so recovering it from the quotient's `≈` is exactly the
   elimination that is refused.

--------
否定 2. 一个 [Type] 商方程的构造：在 [Type] 值的目标中要求提供证人。通过复制整个文件去掉该要求；第一条错误行：

  错误：
  归纳类型 "inhabited" 中的消解不正确：返回类型为 "Type"，而它应当是 SProp 或 Prop。

  [quot_rel N a b] 是 [sub_mem N (a * b⁻¹)]，其保持 [Type] 值 —— 它的消费者读取证人（Instance/Grp/Quotient/Isomorphism.v 的 [image_med]） —— 因此从商的 `≈` 中恢复它正是被拒绝的消解。
*)
Fail Definition quot_equiv_yields_the_witness (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  quot_rel N a b := ltac:(destruct H).

(* CONTROL 2a.  The [inhabited] route in: one [constructor]. / 控制 2a。[inhabited] 路由输入：一个 [constructor]。 *)
Definition quot_equiv_of_witness (a b : carrier G) (H : quot_rel N a b) :
  @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b := inhabits H.

(* CONTROL 2b.  The [inhabited] route out, into a [Prop] goal. / 控制 2b。[inhabited] 路径出发，进入 [Prop] 目标。 *)
Definition quot_equiv_into_Prop (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  inhabited (quot_rel N a b) := H.

(*
CONTROL 2c.  And into a [Type] goal AT A GROUP, through that group's own
   [grp_prop] -- the repair every consumer of the quotient uses.  Applied:
   this is [quot_med]'s respectfulness obligation, in the shape
   Instance/Grp/Quotient.v carries it.

--------
控制 2c。并且进入一个 [Type] 目标的群体，通过该群体自己的 [grp_prop] —— 每个商的使用者都使用的修复方法。应用：这是 [quot_med] 的尊重义务，以 Instance/Grp/Quotient.v 的形式承载它。
*)
Definition quot_equiv_through_pequiv {K : GrpObject} (p : Kills N K)
  (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  grp_map (`1 p) a ≈ grp_map (`1 p) b.
Proof.
  apply (@pequiv_to _ _ (grp_prop K)).
  change (inhabited (quot_rel N a b)) in H.
  destruct H as [H].
  apply (@pequiv_from _ _ (grp_prop K)).
  exact (kills_descends N p a b H).
Defined.

(* CONTROL 2d, APPLIED.  The mediator itself still exists. / 控制 2d，已应用。调解器本身仍然存在。 *)
Definition quot_med_applies {K : GrpObject} (p : Kills N K) :
  QuotientGrp N ~{Grp}~> K := quot_med N p.

(*
CONTROL 2e.  [sub_mem] did NOT move: it is still [Type]-valued, and the
   subgroup's own membership still hands back a witness.

--------
CONTROL 2e。[sub_mem] 没有移动：它仍然是 [Type] 值，子组自身的成员资格仍然返回一个见证。
*)
Definition sub_mem_is_still_data (a : carrier G) (H : sub_mem N a) :
  sub_mem N a := H.

End Quot.

(* ------------------------------------------------------------------------ *)
(** ** (3) The free group's `≈` is a truncation too / ** (3) 自由群的 `≈` 也是一种截断 *)

Section Free.

Context (X : SetoidObject).

(* The truncation, read back at [eq_refl]. / 截断，在 [eq_refl] 处回读。 *)
Definition fg_equiv_is_inhabited_hom_equiv (a b : FGWord X) :
  @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b
    = inhabited (@equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b)
  := eq_refl.

(*
NEGATIVE 3.  A [Type] elimination out of the free group's equality: the
   free groupoid's hom-equality is [Construction/Quotient.v]'s [CongClosure],
   a [Type]-valued inductive, and recovering it from the truncation is
   refused.  Stripped in a copy of this whole file; first error line:

     Error:
     Incorrect elimination in the inductive type "inhabited":
     the return type has sort "Type" while it should be SProp or Prop.

--------
消极 3. 从自由群的等式中进行 [Type] 消元：自由群的同态等式是 [Construction/Quotient.v] 的 [CongClosure]，一个 [Type] 值的归纳类型，并且从截断中恢复它是被拒绝的。在此整个文件的副本中已剥离；第一条错误行：

错误：
在归纳类型“inhabited”中消元不正确：返回类型的排序为“Type”，而它应该是 SProp 或 Prop。
*)
Fail Definition free_equiv_yields_the_groupoid_equation (a b : FGWord X)
  (H : @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b) :
  @equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b
  := ltac:(destruct H).

(* CONTROL 3a.  The route in: one [inhabits]. / 控制 3a. 进入路线：一个 [inhabits]。 *)
Definition free_equiv_of_groupoid_equation (a b : FGWord X)
  (H : @equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b) :
  @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b := inhabits H.

(*
CONTROL 3b.  The route out, at a TARGET group, through [pequiv] -- which
   is how [free_grp_extend]'s respectfulness is proved.  Note what is NOT
   assumed: nothing about [X].  The witness comes from [H], which carries
   [grp_prop] as a field.

--------
控制 3b。在一个目标组中，通过 [pequiv] 的出路——这就是 [free_grp_extend] 的尊重性得到证明的方式。注意没有假设的内容：关于 [X] 的任何内容都没有。证人来自 [H]，它携带 [grp_prop] 作为一个字段。
*)
Definition free_equiv_through_pequiv {H : GrpObject}
  (h : X ~{Sets}~> Grp_Forget H) (a b : FGWord X)
  (Hab : @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b) :
  grp_map (free_grp_extend h) a ≈ grp_map (free_grp_extend h) b :=
  proper_morphism (grp_map (free_grp_extend h)) a b Hab.

End Free.

(*
CONTROL 3c, APPLIED AT AN ARBITRARY OBJECT OF [Sets].  The free-forgetful
   adjunction is still TOTAL: the free group is formed, and the universal
   arrow, the functor and the adjunction are named, at an arbitrary
   [X : Sets] with no [PropEquiv] hypothesis.  This is the control the plan's
   finding F1 asks for: the truncation did not restrict the domain.

--------
在 [Sets] 的任意对象上应用控制 3c。自由-遗忘伴随仍然是完全的：形成了自由群，并且在任意没有 [PropEquiv] 假设的 [X : Sets] 上命名了泛箭头、函子和伴随。这就是计划中查找 F1 所要求的控制：截断并未限制域。
*)
Definition free_group_is_total (X : Sets) : GrpObject := FreeGrpObject X.

Definition free_universal_arrow_is_total (X : Sets) :
  UniversalArrow X Grp_Forget := free_group_universal_arrow X.

Definition free_functor_is_total : Sets ⟶ Grp := FreeGrp.

Definition free_adjunction_is_total : FreeGrp ⊣ Grp_Forget :=
  free_group_adjunction.

Definition free_universal_is_total (X : Sets) :
  ∀ (H : GrpObject) (h : X ~{Sets}~> Grp_Forget H),
    ∃! g : FreeGrpObject X ~{Grp}~> H,
      h ≈ fmap[Grp_Forget] g ∘ fg_insert X :=
  free_group_universal X.

(* ------------------------------------------------------------------------ *)
(** ** (4) What did NOT move / ** (4) 什么没有动 *)

(*
[grp_coset_rel] (Instance/Grp/Epi.v) is deliberately NOT truncated -- the
   field constrains only the objects it is a field of, and
   [GrpCosetPower]'s witness comes from its CODOMAIN through
   [hom_PropEquiv].  Truncating it would have cost
   [transposition_decides_image] its strength.  That decision is guarded by
   two controls in Test/ProbeGrpQuotient.v's [Positive] section --
   [positive_grp_coset_rel_is_type_valued] and
   [positive_transposition_decides_image_full] -- and is not restated here;
   what this file records is that the three relations above are the only
   ones the Grp layer moved.

   CORRECTION, the same PR.  An earlier revision of the sentence above said
   "That development is probed by Test/ProbeGrpEpi*.v".  No such file has
   ever existed ([ls Test/ | grep -iE 'epi|coset|transpos|image'] matches
   nothing), so the strength claim was unguarded; the two controls named
   above were landed to close that gap.

--------
[grp_coset_rel]（Instance/Grp/Epi.v）故意未被截断——该字段仅约束它所在的对象，而[GrpCosetPower]的证据来自其通过[hom_PropEquiv]的余域。截断它将让[transposition_decides_image]失去其强度。这个决定由Test/ProbeGrpQuotient.v的[Positive]部分中的两个控件——[positive_grp_coset_rel_is_type_valued]和[positive_transposition_decides_image_full]——保护，并未在此重复；本文件记录的是上述三个关系是Grp层移动的唯一关系。

更正，同样的PR。上面句子的早期版本说“该开发由Test/ProbeGrpEpi*.v探测”。实际上从未存在过这样的文件（[ls Test/ | grep -iE 'epi|coset|transpos|image']不匹配任何东西），因此强度声明未受保护；上面提到的两个控件被引入以弥补该漏洞。
*)

(*
[Grp] is locally propositional, which is what lets the functor-of-points
   constructions of Structure/Group/Representable.v be applied at [Grp]
   itself with no manual hypothesis.

--------
[Grp] 是局部命题的，这使得 Structure/Group/Representable.v 的点函子构造能够直接在 [Grp] 本身上应用，而无需手动假设。
*)
Definition Grp_is_locally_propositional : LocallyPropositional Grp :=
  Grp_LocallyPropositional.

Definition grp_hom_setoid_is_propositional (G H : GrpObject) :
  PropEquiv (@GrpHom_Setoid G H) := GrpHom_PropEquiv.
