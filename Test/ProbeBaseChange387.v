Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Slice.Pullback.
Require Import Category.Instance.Sets.Pullback.

Generalizable All Variables.

(** * Boundary probe for the base change adjunction Σ_f ⊣ f* / * 基变换伴随 Σ_f ⊣ f* 的边界探索 *)

(*
This file guards Construction/Slice/Pullback.v from OUTSIDE that
   module: a negative written inside a file is renamed in lockstep with
   the constant it guards and so cannot detect a rename, whereas a
   negative here breaks loudly.  The Require list is the target's own,
   extended by Instance/Sets/Pullback for the concrete section.

   What is pinned, and of which kind:

   (A) CONVERSION.  Two identifications that hold only up to ≈.  The
       class's counit carries a residual identity, so it is the pullback
       projection composed with [id] and not that projection; and the
       class's unit is the transpose of the slice identity, which is the
       mediator of the same cone as [bang_star_unit_mor] but produced
       from a different proof of the cone's square condition.  Each
       negative sits beside the strict statement that DOES hold, so what
       is measured is the residue and not the constant.

   (B) TYPING.  The reversed orientation is a different type, so the
       delivered adjunction cannot be ascribed at it.  This is a plain
       type mismatch, with no universe clause.

   (C) FORMABILITY.  [Base_Functor_Adjunction] is over a category whose
       hom and proof universes coincide -- an identification visible in
       its BINDER, [Category@{u u0 u0}], while its constraint block
       carries no equation at all.  Three donors are each rejected on
       their own at levels declared apart ([Slice], [Pullback],
       [Adjunction]); [Functor] is NOT one, and is the discriminating
       control.

   (D) The interesting measurement, and the reason the deleted stub in
       the target was wrong.  [Star_Functor f ⊣ Bang_Functor f] -- the
       orientation that stub proposed -- IS well typed: both functors
       have the shapes the class wants once the roles are swapped, so it
       is neither a formability nor a typing rejection.  It is a
       well-formed statement that is simply not true in general, and
       [reversed_orientation_refuted] compiles a counterexample: over
       Sets, along the unique morphism ∅ ~> 1, the unit such an
       adjunction would supply at the object (1; id) is a map 1 ~> ∅,
       because pulling anything back along ∅ ~> 1 lands in a setoid whose
       carrier is uninhabited (a sub-setoid of 1 × ∅, not the [sets_empty]
       declared below) while Σ leaves the underlying object alone.
       Evaluating it
       at the point produces an inhabitant of False.

   (E) The section hypothesis of the target is discharged at Sets from
       [Sets_HasPullbacks] (Instance/Sets/Pullback.v), and the transpose
       is exercised at a concrete morphism where it computes.

   The sections below run A, C, E, then B and D together, since the
   reversed orientation is refuted at a Sets witness and so has to come
   after E.

--------
这个文件保护 Construction/Slice/Pullback.v 不受模块外部影响：文件内部写的否定会随着它所保护的常量一起重命名，因此无法检测重命名，而这里的否定会大声报错。Require 列表是目标自身的，由 Instance/Sets/Pullback 扩展以适应具体部分。

什么被固定，以及是哪种类型：

(A) 转换。两个标识仅在≈范围内成立。类的余单位携带一个剩余标识，因此它是与 [id] 组成的拉回投影，而不是那个投影；类的单位是片标识的转置，它是与 [bang_star_unit_mor] 相同圆锥的中介，但由该圆锥平方条件的不同证明生成。每个负号位于严格成立的陈述旁边，因此测量的是残差而不是常数。

(B) 类型。反向取向是不同的类型，因此无法将传递的附加项归于它。这是一个纯粹的类型不匹配，没有宇宙条款。

(C) 可塑性。[Base_Functor_Adjunction] 是一个其 hom 和 proof 宇宙相吻合的范畴 —— 这一点在其 BINDER，[Category@{u u0 u0}] 中可见，而其约束块完全没有方程式。三个供体在各自单独被拒绝，其层级各自声明（[Slice]、[Pullback]、[Adjunction]）；[Functor] 不是其中之一，并且是区分控制。

(D) 有趣的测量，以及目标中被删除的存根错误的原因。[Star_Functor f ⊣ Bang_Functor f]——该存根提出的方向——类型良好：一旦角色交换，两个函子都具有类所需的形状，所以这既不是可形成性问题也不是类型拒绝问题。它是一个形式良好的语句，只是通常不成立，而 [reversed_orientation_refuted] 编译了一个反例：在集合上，沿着唯一的态射 ∅ ~> 1，这种伴随在对象 (1; id) 处提供的单位是一个映射 1 ~> ∅，因为沿着 ∅ ~> 1 拉回任何东西都会落入一个载体为空的集合等价类（1 × ∅ 的一个子集合等价类，而不是下面声明的 [sets_empty]），而 Σ 则保持底层对象不变。在该点上求值会产生 False 的一个实例。

(E) 目标的截面假设在 Sets 中从 [Sets_HasPullbacks] (Instance/Sets/Pullback.v) 被释放，并且在一个具体的态射上使用转置，其中它进行计算。

下面的部分依次是 A、C、E，然后是 B 和 D 一起，因为在 Sets 见证者处，反向的排列被驳回，因此必须在 E 之后出现。
*)

(* Instrument check: a name that cannot exist. / 仪器检查：一个不可能存在的名字。 *)
Fail Check probe_base_change_387_no_such_name.

(* ===================================================================== *)
(** ** (A) Conversion boundaries, over an abstract base category / ** (A) 转换边界，关于抽象基类         *)

Section Abstract.

Context `{C : Category}.
Context (pullbacks : ∀ (X Y Z : C) (f : Y ~> Z) (g : X ~> Z), Pullback f g).
Context `(f : a ~> b).

(*
Controls: every constant the negatives below name, outside any
   rejected command.

--------
控制：下面所列的每个常量，位于任何被拒绝的命令之外。
*)
Check @Bang_Functor.
Check @Star_Functor.
Check @Base_Functor_Adjunction.
Check @base_to_mor.
Check @bang_star_unit.
Check @bang_star_unit_mor.
Check @bang_star_counit.
Check @bang_star_counit_mor.
Check @unit.
Check @counit.
Check (Base_Functor_Adjunction pullbacks f).
Check (Bang_Functor f ⊣ Star_Functor pullbacks f).

(*
Control: the class's unit IS the transpose of the slice identity, on
   the nose.

--------
控制：这个类的单元格就是切片单位的转置，完全一样。
*)
Example ctrl_unit_strict (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (o; h))
  = base_to_mor pullbacks f (id[Bang_Functor f (o; h)]) := eq_refl.

(* Negative 1 (CONVERSION): against the named mediator it is only ≈. / 负 1（转换）：针对指定调解人的仅约为 ≈。 *)
Fail Example neg_unit_strict (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (o; h))
  = bang_star_unit_mor pullbacks f o h := eq_refl.

(* Control for negative 1: the ≈ statement does hold. / 对负一的控制：≈ 语句确实成立。 *)
Check (bang_star_unit_is_unit pullbacks f).

(*
Control: the class's counit is the projection with one residual
   identity, which is what ε := ⌈id⌉ produces.

--------
控制：该类的余单位是具有一个剩余恒等的投影，这就是 ε := ⌈id⌉ 所产生的。
*)
Example ctrl_counit_strict (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (p; k))
  = bang_star_counit_mor pullbacks f p k ∘ id := eq_refl.

(* Negative 2 (CONVERSION): the residue cannot be removed by conversion. / 负2（转换）：残留物无法通过转换去除。 *)
Fail Example neg_counit_strict (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (p; k))
  = bang_star_counit_mor pullbacks f p k := eq_refl.

(* Control for negative 2. / 控制负二。 *)
Check (bang_star_counit_is_counit pullbacks f).

(*
Negative 3 (CONVERSION): nor at the level of the whole slice
   morphism, where the commuting witnesses differ as well.

--------
负 3（转换）：也不是在整个片映射的层面上，其中交换的见证者也有所不同。
*)
Fail Example neg_counit_record (p : C) (k : p ~> b) :
  @counit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
    (p; k)
  = bang_star_counit pullbacks f p k := eq_refl.

(*
(D), first half: the reversed orientation is FORMABLE.  It is a
   statement, not a type error -- which is exactly why the deleted stub
   could be written down at all.

--------
(D)，前半部分：反向的方向是可形成的。这是一个陈述，而不是类型错误——这正是为什么可以把被删除的存根写出来。
*)
Check (Star_Functor pullbacks f ⊣ Bang_Functor f).

End Abstract.

(* ===================================================================== *)
(** ** (C) The universe identification, and its donors / ** (C) 宇宙识别及其捐赠者                   *)

Section Universes.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : Cu).

(* Controls at the very same declared levels. / 在完全相同的声明级别进行控制。 *)
Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@Functor Cu Cu).

(*
Controls naming, outside any rejected command, every constant the
   negatives below name -- without these a rename would leave those
   negatives green for the wrong reason.

--------
控制命名，在任何被拒绝的命令之外，对下面命名的每个常量进行控制——没有这些，重命名会因为错误的原因使这些负值显示为绿色。
*)
Check @Slice.
Check @Pullback.
Check @Adjunction.

(*
Negative 4 (FORMABILITY): the headline is not formable when hom and
   proof are declared apart.

--------
负4（可成形性）：当 hom 和 proof 被单独声明时，标题不可成形。
*)
Fail Check (@Base_Functor_Adjunction Cu).

(*
Negatives 5-7 (FORMABILITY): three donors, each rejected alone.
   [Functor] above is accepted at the same levels, so it is not one.

--------
负面 5-7（可形成性）：三个供体，每个单独被拒绝。
上面的 [Functor] 在相同水平上被接受，所以它不是其中之一。
*)
Fail Check (@Slice Cu xu).
Fail Check (@Pullback Cu).
Fail Check (@Adjunction Cu Cu).

End Universes.

(* ===================================================================== *)
(** ** (E) Discharging the hypothesis at Sets / ** (E) 在集合中解除假设                            *)

(*
Instance/Sets/Pullback.v's [Sets_HasPullbacks] supplies the target's
   section hypothesis directly; the issue's appended note that Sets has
   no pullback instance is stale.  This lives here rather than in the
   target because requiring Instance/Sets/Pullback there would take that
   file's transitive dependency closure from 27 modules to 44.

--------
Instance/Sets/Pullback.v 的 [Sets_HasPullbacks] 直接提供了目标的节假设；关于 Sets 没有 pullback 实例的附加说明已经过时。它放在这里而不是目标中，因为在目标中需要 Instance/Sets/Pullback 会将该文件的传递依赖闭包从 27 个模块增加到 44 个模块。
*)
Definition sets_pullbacks (X Y Z : Sets)
      (u : Y ~{Sets}~> Z) (v : X ~{Sets}~> Z) : Pullback u v :=
  @pullback Sets Sets_HasPullbacks _ _ _ u v.

Definition Sets_Base_Functor_Adjunction {a b : Sets} (f : a ~{Sets}~> b) :
  Bang_Functor f ⊣ Star_Functor sets_pullbacks f :=
  Base_Functor_Adjunction sets_pullbacks f.

Definition sets_one : Sets :=
  {| carrier := poly_unit; is_setoid := unit_setoid |}.

Definition sets_bool : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Program Definition sets_pick : sets_one ~{Sets}~> sets_bool := {|
  morphism := fun _ => true
|}.

Definition sets_x : @Slice Sets sets_one :=
  existT (fun o : obj[Sets] => o ~{Sets}~> sets_one) sets_one id.

Definition sets_y : @Slice Sets sets_bool :=
  existT (fun o : obj[Sets] => o ~{Sets}~> sets_bool) sets_bool id.

Program Definition sets_g :
  Bang_Functor sets_pick sets_x ~{@Slice Sets sets_bool}~> sets_y :=
  (sets_pick; _).

Definition sets_transpose :
  sets_x ~{@Slice Sets sets_one}~>
    Star_Functor sets_pullbacks sets_pick sets_y :=
  to (@adj (@Slice Sets sets_bool) (@Slice Sets sets_one)
        (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
        (Sets_Base_Functor_Adjunction sets_pick) sets_x sets_y) sets_g.

(*
The transpose COMPUTES: at the point of the singleton it is the pair
   ⟨the given morphism, the structure map⟩ inside the agreement
   sub-setoid of Instance/Sets/Pullback.v.

--------
转置计算：在单点处，它是对 ⟨给定的态射，结构映射⟩，位于 Instance/Sets/Pullback.v 的 agreement 子集合中。
*)
Example sets_transpose_fst :
  fst (`1 ((`1 sets_transpose) ttt)) = true := eq_refl.

Example sets_transpose_snd :
  snd (`1 ((`1 sets_transpose) ttt)) = ttt := eq_refl.

(*
And so does the backward transpose, which reads the first coordinate
   back off.

--------
反向转置也是如此，它会回退读取第一个坐标。
*)
Definition sets_untranspose :
  Bang_Functor sets_pick sets_x ~{@Slice Sets sets_bool}~> sets_y :=
  from (@adj (@Slice Sets sets_bool) (@Slice Sets sets_one)
          (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
          (Sets_Base_Functor_Adjunction sets_pick) sets_x sets_y)
       sets_transpose.

Example sets_untranspose_computes :
  (`1 sets_untranspose) ttt = true := eq_refl.

(*
Base change along the point [true] genuinely cuts the identity object
   over bool down to the fibre over true: every element of f* (bool; id)
   has [true] in its first coordinate.

--------
沿着点 [true] 的基变换真正地将身份对象在 bool 上切换到位于 true 上的纤维：f* (bool; id) 的每个元素在其第一个坐标上都有 [true]。
*)
Lemma sets_star_is_fibre
      (e : carrier (`1 (Star_Functor sets_pullbacks sets_pick sets_y))) :
  fst (`1 e) = true.
Proof. exact (`2 e). Qed.

Definition sets_fibre_pt :
  carrier (`1 (Star_Functor sets_pullbacks sets_pick sets_y)) :=
  ((true, ttt); eq_refl).

(*
The counit at (bool; id) is the pullback projection, and it computes
   on that element.

--------
在 (bool; id) 处的余单位是拉回投影，它在该元素上进行计算。
*)
Example sets_counit_computes :
  (`1 (@counit (@Slice Sets sets_bool) (@Slice Sets sets_one)
         (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
         (Sets_Base_Functor_Adjunction sets_pick) sets_y)) sets_fibre_pt
  = true := eq_refl.

(*
And so does the unit at (1; id), whose value is the comparison of the
   singleton into the pullback.

--------
位于 (1; id) 的单元也是如此，它的值是单元素对拉回的比较。
*)
Example sets_unit_computes :
  fst (`1 ((`1 (@unit (@Slice Sets sets_bool) (@Slice Sets sets_one)
                  (Bang_Functor sets_pick)
                  (Star_Functor sets_pullbacks sets_pick)
                  (Sets_Base_Functor_Adjunction sets_pick) sets_x)) ttt))
  = ttt := eq_refl.

(* ===================================================================== *)
(** ** (B) and (D) The reversed orientation / ** (B) 和 (D) 反向的方向                              *)

Definition sets_empty : Sets :=
  {| carrier := False; is_setoid := eq_Setoid False |}.

Program Definition sets_bang : sets_empty ~{Sets}~> sets_one := {|
  morphism := fun x => False_rect poly_unit x
|}.

(*
Negative 8 (TYPING): the delivered adjunction is not of the reversed
   type.  A plain mismatch -- no universe clause.

--------
负 8（输入中）：所提供的伴随不是反转类型。纯粹的不匹配——没有宇宙子句。
*)
Fail Definition neg_wrong_orientation :
  Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang :=
  Base_Functor_Adjunction sets_pullbacks sets_bang.

(* Control for negative 8: the delivered orientation. / 负8的控制：所提供的方向。 *)
Check (Base_Functor_Adjunction sets_pullbacks sets_bang).
Check (Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang).

Definition rev_x : @Slice Sets sets_one :=
  existT (fun o : obj[Sets] => o ~{Sets}~> sets_one) sets_one id.

(*
The stub's orientation is well typed and REFUTED: over Sets, along
   ∅ ~> 1, base change carries every object over 1 to the empty object,
   while Σ leaves the underlying object alone, so the unit at (1; id)
   would be a map from the singleton into the empty setoid.

--------
这个存根的方向类型良好并且已被反驳：在集合上，沿着 ∅ ~> 1，基变换将每个对象从 1 转移到空对象，而 Σ 保持底层对象不变，因此 (1; id) 处的单位将是从单例映射到空集合的映射。
*)
Theorem reversed_orientation_refuted :
  Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang → False.
Proof.
  intro A.
  pose proof (`1 (@unit (@Slice Sets sets_empty) (@Slice Sets sets_one)
                    (Star_Functor sets_pullbacks sets_bang)
                    (Bang_Functor sets_bang) A rev_x) ttt) as e.
  destruct e as [[u v] Hv].
  exact v.
Qed.
