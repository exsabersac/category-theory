Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Equivalence.Adjoint.Compose.

Generalizable All Variables.

(*
Boundary probe for Theory/Equivalence/Adjoint/Compose.v (Mac Lane
   SIV.4 Exercise 2(b)).

   The negatives live here rather than in the target because an in-file
   negative renames in lockstep with the constant it guards and so
   cannot detect a rename.  The require list above mirrors the target's
   exactly.

   THIRTEEN negatives in THREE kinds, plus one scope-free instrument
   check.  Each was stripped ONE AT A TIME -- the others left in place
   -- and compiled alone, and its whole error message was read, and its
   line confirmed:

     CONVERSION (5, negatives 1-5): each reports "cannot unify" between
       two terms of a single type.  Negatives 1-3 separate the direct
       composite from the refinement route the catalog entry proposes;
       negatives 4-5 record that Mac Lane's whiskering formulas hold
       only at [~], so the two grades the target keeps apart are
       genuinely different.

     TYPING (3, negatives 6-8): a plain "has type X while it is
       expected to have type Y", with NO "cannot unify" and no universe
       clause -- the two sides do not inhabit a common type at all,
       because [Compose] of functors is neither associative on the nose
       nor strictly unital.  So the groupoid laws are not statable at
       the level of the class (6, 7), and neither is "the witness is an
       identity adjoint equivalence" (8).

     FORMABILITY (5, negatives 9-13): universe inconsistencies naming
       the declared levels.  Negative 9 isolates the IDENTITY FUNCTOR
       [Id] as a donor of the hom = proof identification ON ITS OWN --
       easy to miss, and it means a probe writing [Id[Cu]] into an
       [Adjunction] measures [Id] rather than [Adjunction]; negative 10
       shows [Adjunction] is a donor independently, probed at two
       arbitrary endofunctors so that no [Id] occurs in the command;
       negative 11 adds [AdjointEquivalence], which CANNOT be tested
       apart from [Adjunction], its first field being [F -| U], so 10
       and 11 are NOT independent; negative 12 is the target's own
       [AdjointEquivalence_Id], which has both donors in reach and
       isolates neither; and negative 13 locates the composite's
       identification of the three categories' hom universes at the
       mere presence of functors in BOTH directions, before any
       adjunction is formed.

   The controls beside them are what make the negatives measure
   something: [x ~> y], [id], an arbitrary endofunctor [Cu -> Cu],
   [IsIsomorphism] and the target's own four [IsIso_*] constants are all
   ACCEPTED at the very levels where the adjunction constants are
   rejected, so the rejection is about the adjunction vocabulary and not
   about the section's constraint.  Every constant a negative names is
   also named outside a [Fail] -- including the identity functor [Id],
   which a first cut named only INSIDE negative 9, so that renaming it
   left the negative silently green (found by audit; the guard below
   now breaks this file under that rename); rename simulation over the
   six TARGET constants the negatives name breaks this file at a guard
   line in all six cases.

--------
Theory/Equivalence/Adjoint/Compose.v 的边界探测（Mac Lane SIV.4 练习 2(b)）。

负数存在于这里而不是在目标中，因为文件内的负数会随着它所保护的常量同步重命名，因此无法检测重命名。上面的 require 列表与目标的完全一致。

十三个负数分为三种类型，再加一个无范围的仪器检查。每一个都被一次只剥离一个——其他的保持原位——并单独编译，读取其完整的错误信息，并确认其行数：

转换（5，否定 1-5）：每条都报告在单一类型的两个项之间“无法统一”。否定 1-3 将直接组合与目录条目提出的精化路径区分开来；否定 4-5 记录了 Mac Lane 的刷毛公式仅在 [~] 处成立，因此目标保留分开的两个等级确实是不同的。

输入（3，否定 6-8）：一个简单的“具有类型 X，而预期具有类型 Y”，没有“无法统一”且没有宇宙子句——因为函子 [Compose] 既不严格满足结合律，也不严格具有单位元素，所以两边根本不属于同一类型。因此，群类法则无法在类（6，7）层面陈述，“见证是一个恒等伴随等价”（8）也无法在该层面陈述。

可形成性（5，负项9-13）：宇宙不一致性命名宣告的层级。负项9将恒等函子 [Id] 隔离为同态的供体 = 证明识别自身——容易被忽略，这意味着一个探针将 [Id[Cu] 写入 [Adjunction] 时测量的是 [Id] 而不是 [Adjunction]；负项10显示 [Adjunction] 独立作为供体，在两个任意的自函子上被探测，因此命令中没有 [Id]；负项11添加了 [AdjointEquivalence]，它不能在没有 [Adjunction] 的情况下测试，其第一个字段是 [F -| U]，因此 10 和 11 并不是独立的；负项12是目标自身的 [AdjointEquivalence_Id]，它同时能访问两个供体，但没有隔离任何一个；负项13在任何伴随形成之前，仅通过函子在两个方向的存在，就定位了复合体对这三类同态宇宙的识别。

它们旁边的控制器是使负样本测量某些东西的原因：[x ~> y]、[id]、任意的端函子 [Cu -> Cu]、[IsIsomorphism] 以及目标自身的四个 [IsIso_*] 常量都在伴随常量被拒绝的级别上被接受，所以拒绝与伴随词汇相关，而不是与该部分的约束相关。每个负样本命名的常量在 [Fail] 之外也被命名——包括恒等函子 [Id]，第一个版本只在负样本 9 内部命名它，因此重命名它后负样本默默地变为绿色（通过审核发现；下面的保护现在在该重命名下会破坏此文件）；对负样本命名的六个目标常量进行重命名模拟，会在所有六种情况下在保护行处破坏此文件。
*)

(* Instrument check: a name that exists nowhere must be rejected. / 工具检查：一个不存在的名称必须被拒绝。 *)
Fail Check probe379_no_such_constant_anywhere.

(** ** Guards: every constant a negative names, named outside a [Fail] / ** 守卫：每个常量都是负面名称，在 [Fail] 外命名 *)

Check @AdjointEquivalence_Compose.
Check @AdjointEquivalence_Compose_via_equivalence.
Check @AdjointEquivalence_Compose_unit.
Check @AdjointEquivalence_Compose_counit.
Check @AdjointEquivalence_Compose_unit_transpose.
Check @AdjointEquivalence_Id.
Check @Id.
Check @adjoint_equivalence_compose_adj.
Check @assoc_left.
Check @assoc_right.
Check @indiscrete_square.
Check @indiscrete_swap.
Check @IsIso_id.
Check @IsIso_along.
Check @IsIso_comp.
Check @IsIso_fmap.
Check @adj_equivalence.
Check @Adjunction_Compose.
Check @unit.
Check @counit.
Check @AdjointEquivalence.
Check @Adjunction.
Check @Equivalence_to_AdjointEquivalence.
Check @EquivalenceOfCategories_Compose.
Check @AdjointEquivalence_to_Equivalence.
Check @AdjointEquivalence_swap.
Check IndT.
Check (Indiscrete bool).
Check @Erase.

(** ** Conversion negatives: the two routes are different / ** 转换否定：这两种路线是不同的 *)

Section Routes.

Context {C D E : Category}.
Context {F : C ⟶ D} {U : D ⟶ C}.
Context {F' : D ⟶ E} {U' : E ⟶ D}.
Context (A : AdjointEquivalence F U).
Context (B : AdjointEquivalence F' U').

(*
Positive control: both routes inhabit ONE type, so the negatives
   below are conversion questions and not typing ones.

--------
阳性对照：两条路线都属于同一种类型，因此下面的阴性问题是转换问题，而不是分型问题。
*)
Check (AdjointEquivalence_Compose A B
       : AdjointEquivalence (F' ◯ F) (U ◯ U')).
Check (AdjointEquivalence_Compose_via_equivalence A B
       : AdjointEquivalence (F' ◯ F) (U ◯ U')).

(*
Negative 1 (CONVERSION): the refinement route is not the direct
   composite, on the whole record.

--------
负1（转换）：精炼路线不是整个记录上的直接复合。
*)
Fail Example probe379_neg1 :
  AdjointEquivalence_Compose_via_equivalence A B
    = AdjointEquivalence_Compose A B := eq_refl.

(* Negative 2 (CONVERSION): nor on the underlying adjunction. / 负 2（转换）：也不在基础的伴随上。 *)
Fail Example probe379_neg2 :
  @adj_equivalence _ _ _ _ (AdjointEquivalence_Compose_via_equivalence A B)
    = @adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B) := eq_refl.

(*
Negative 3 (CONVERSION): nor on the unit components.  The direct
   route's unit DOES reduce -- that is the [eq_refl] control below,
   which is [AdjointEquivalence_Compose_unit_transpose] -- so the
   obstruction is on the refinement side.

--------
负3（转换）：在单元组件上也没有。直接路径的单元确实减少——即下面的 [eq_refl] 控制，它是 [AdjointEquivalence_Compose_unit_transpose]——所以阻碍在精炼端。
*)
Fail Example probe379_neg3 (x : C) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose_via_equivalence A B))
    x
  = @unit _ _ _ _
      (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x := eq_refl.

Example probe379_ctrl_direct_reduces (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    = to (@adj _ _ _ _ (@adj_equivalence _ _ _ _ A) x (U' (F' (F x))))
         (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x)) := eq_refl.

(*
Negative 4 (CONVERSION): Mac Lane's whiskering formula for the unit
   is [~] and not [eq_refl].  The [~] form is the target's
   [AdjointEquivalence_Compose_unit], reproduced as the control.

--------
负4（转换）：Mac Lane 的单位搓合公式是 [~]，而不是 [eq_refl]。[~] 形式是目标的 [AdjointEquivalence_Compose_unit]，作为控制复制。
*)
Fail Example probe379_neg4 (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    = fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x := eq_refl.

Example probe379_ctrl_unit_approx (x : C) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) x
    ≈ fmap[U] (@unit _ _ _ _ (@adj_equivalence _ _ _ _ B) (F x))
        ∘ @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  AdjointEquivalence_Compose_unit A B x.

(* Negative 5 (CONVERSION): the same for the counit. / 负五（转换）：对余单位也是如此。 *)
Fail Example probe379_neg5 (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) y
    = @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y))
  := eq_refl.

Example probe379_ctrl_counit_approx (y : E) :
  @counit _ _ _ _ (@adj_equivalence _ _ _ _ (AdjointEquivalence_Compose A B)) y
    ≈ @counit _ _ _ _ (@adj_equivalence _ _ _ _ B) y
        ∘ fmap[F'] (@counit _ _ _ _ (@adj_equivalence _ _ _ _ A) (U' y)) :=
  AdjointEquivalence_Compose_counit A B y.

End Routes.

(** ** Typing negatives: the groupoid laws are not statable at the class / ** 打负号：群oid定律无法在类上表述 *)

Section Laws.

Context {C1 C2 C3 C4 : Category}.
Context {F1 : C1 ⟶ C2} {U1 : C2 ⟶ C1}.
Context {F2 : C2 ⟶ C3} {U2 : C3 ⟶ C2}.
Context {F3 : C3 ⟶ C4} {U3 : C4 ⟶ C3}.
Context (A : AdjointEquivalence F1 U1).
Context (B : AdjointEquivalence F2 U2).
Context (G : AdjointEquivalence F3 U3).

(* Positive controls: each bracketing is formable, at ITS OWN type. / Positive controls: each bracketing is formable, at ITS OWN type. / 阳性对照：每个括号都是可成形的，在其自身类型下。 *)
Check (assoc_left A B G
       : AdjointEquivalence (F3 ◯ (F2 ◯ F1)) ((U1 ◯ U2) ◯ U3)).
Check (assoc_right A B G
       : AdjointEquivalence ((F3 ◯ F2) ◯ F1) (U1 ◯ (U2 ◯ U3))).

(*
Negative 6 (TYPING): the two bracketings do not inhabit a common
   type, so associativity is not statable at the level of the class.
   What IS statable, and holds by conversion, is the comparison of the
   units and counits -- the control below is the target's
   [AdjointEquivalence_Compose_assoc_unit].

--------
负 6（打字）：这两种括号化没有共同的类型，因此无法在类的层次上陈述结合性。可以陈述且通过转换成立的是单位和余单位的比较 —— 下面的控制是目标的 [AdjointEquivalence_Compose_assoc_unit]。
*)
Fail Check (assoc_left A B G = assoc_right A B G).

Example probe379_ctrl_assoc_unit (x : C1) :
  @unit _ _ _ _ (@adj_equivalence _ _ _ _ (assoc_left A B G)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ (assoc_right A B G)) x :=
  AdjointEquivalence_Compose_assoc_unit A B G x.

(* Negative 7 (TYPING): the same for the left identity law. / 负 7（输入）：左恒等律也是一样。 *)
Fail Check (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A = A).

Example probe379_ctrl_id_left_unit (x : C1) :
  @unit _ _ _ _
    (@adj_equivalence _ _ _ _
       (AdjointEquivalence_Compose (@AdjointEquivalence_Id C1) A)) x
    = @unit _ _ _ _ (@adj_equivalence _ _ _ _ A) x :=
  AdjointEquivalence_Compose_id_left_unit A x.

End Laws.

(*
Negative 8 (TYPING): the witness is likewise not of identity type --
   its two functors move an object, so it does not even have the TYPE of
   an identity adjoint equivalence.  Control: the object is moved.

--------
负 8（打字）：证人同样不是身份类型 —— 它的两个函子移动一个对象，因此它甚至没有身份伴随等价的类型。控制：对象被移动。
*)
Example probe379_ctrl_witness_moves :
  (IndT ◯ Erase (Indiscrete bool)) false = true := eq_refl.

Fail Check (indiscrete_square = @AdjointEquivalence_Id (Indiscrete bool)).

(**
** Formability negatives: where the universe identifications come
       from

--------
** 可成形性负面因素：宇宙识别来自何处
*)

Section HomIsProof.

Universes co ch cp.
Constraint ch < cp.
Context (Cu : Category@{co ch cp}).
Context (G H : Cu ⟶ Cu).
Context (x y : Cu).

(*
Controls, all accepted at these very levels: the category's homs and
   identity, a functor from the category to itself (so [Functor] is NOT
   a donor), the predicate [IsIsomorphism], and the target's own four
   [IsIso_*] constants, whose explicit universe binders keep hom and
   proof apart.

--------
控件，全部在这些级别上被接受：该范畴的同态和同一性，从该范畴到自身的函子（所以 [Functor] 不是捐赠者），谓词 [IsIsomorphism]，以及目标自身的四个 [IsIso_*] 常量，其显式的宇宙绑定器将同态和证明区分开。
*)
Check (x ~{Cu}~> y).
Check (@id Cu x).
Check (Cu ⟶ Cu).
Check (@IsIsomorphism Cu x y).
Check (@IsIso_id Cu x).
Check (@IsIso_along Cu x y).
Check (@IsIso_comp Cu x y).
Check (@IsIso_fmap Cu Cu G x y).

(*
Negative 9 (FORMABILITY): the IDENTITY FUNCTOR alone identifies hom
   with proof.
   This is worth isolating, because it means a probe that writes
   [Id[Cu]] into an [Adjunction] is testing [Id] and not [Adjunction].
   The control immediately above -- an arbitrary endofunctor of the same
   category, accepted -- is what separates the two.

--------
负 9（可形成性）：仅凭同一函子就能通过证明标识 hom。
这值得单独指出，因为它意味着写入 [Id[Cu] 到 [Adjunction] 的探针是在测试 [Id]，而不是 [Adjunction]。
上面的控制——同一范畴的任意自函子，被接受——就是区分两者的关键。
*)
Fail Check (@Id Cu).

(*
Negative 10 (FORMABILITY): [Adjunction] identifies hom with proof
   INDEPENDENTLY
   of that, probed here at two arbitrary endofunctors so that no [Id]
   occurs in the command.

--------
负10（可成形性）：[Adjunction] 独立地识别带有证明的同源物，与此无关，在这里探测两个任意的端函子，以确保命令中不会出现 [Id]。
*)
Fail Check (@Adjunction Cu Cu G H).

(*
Negative 11 (FORMABILITY): so does [AdjointEquivalence] -- but it
   CANNOT be
   tested apart from [Adjunction], its first field being [F -| U], so
   this is a second donor and NOT an independent cause.

--------
负11（可形成性）：[AdjointEquivalence]也是如此——但它无法单独测试，必须与[Adjunction]一起测试，其第一个字段是[F -| U]，所以这是第二个供体，而不是独立原因。
*)
Fail Check (@AdjointEquivalence Cu Cu G H).

(*
Negative 12 (FORMABILITY): the target's own identity adjoint
   equivalence inherits the identification.  It has at least the two
   sufficient donors above -- [Id] occurs in its statement and
   [Adjunction] in its field -- and this negative isolates neither.

--------
负 12（可成型性）：目标自身的身份伴随等价继承了识别。它至少有上面提到的两个充分供体——[Id] 出现在其声明中，[Adjunction] 出现在其字段中——并且这个负值没有孤立任何一个。
*)
Fail Check (@AdjointEquivalence_Id Cu).

End HomIsProof.

Section HomLevelsApart.

Universes ao ah bo bh.
Constraint ah < bh.
Context (Au : Category@{ao ah ah}).
Context (Bu : Category@{bo bh bh}).

(* Control: a functor in one direction is formable. / 控制：一个方向的函子是可形成的。 *)
Check (Au ⟶ Bu).

(*
Negative 13 (FORMABILITY): the mere presence of a functor in the
   OTHER direction
   forces the two hom universes to agree, before any adjunction is
   formed.  This is where the composite's [u0 = u2 = u4] comes from.

--------
负13（可形成性）：仅仅在相反方向上存在一个函子，就会迫使两个同构宇宙在形成任何连接之前达成一致。这就是复合体的 [u0 = u2 = u4] 来源的地方。
*)
Fail Check (Bu ⟶ Au).

End HomLevelsApart.
