Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Subcategory.Dense.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Skeleton.Separation.

Generalizable All Variables.

(** * Boundary probe for Construction/Subcategory/Dense.v (issue #375) / * 边界探针用于 Construction/Subcategory/Dense.v（问题 #375） *)

(*
Every boundary the target file's header states as measured is pinned
   here, from OUTSIDE that file: an in-file negative renames in lockstep
   with the constant it guards and so cannot detect a rename.  The
   [Require] list above mirrors the target's exactly, plus the target
   itself and the two modules the witnesses need.

   Five negatives of THREE kinds, kept lexically apart, plus one
   scope-free instrument check:

     CONVERSION  1  the [IsoDense] whole-record round trip does not
                    return -- stdlib [sigT] has no eta
     CONVERSION  2  the counit is not the fullness-lift of the chosen
                    isomorphism on the nose
     TYPING      3  [counit (dense_adj D) a = id[a]] is ill-typed: the two
                    endpoints are different objects of [Sub C S]
     TYPING      4  the reflection adjunction is not the [Reflective]
                    record
     FORMABILITY 5  [Subcategory] identifies its category's hom and proof
                    universes

   Negative 3 is the point of the whole file: Mac Lane's counit-is-the-
   identity depends on choosing a_0 = a for objects already in the
   subcategory, and with the choice supplied as one uniform function the
   representative of an object of the subcategory can be a DIFFERENT
   object.  The witness below is a full subcategory of [Indiscrete bool]
   containing BOTH points whose chosen representative for each point is
   the other point, and the two endpoints are proved distinct
   ([swap_objects_differ]).

   Each negative was stripped ONE AT A TIME, with the others left as
   [Fail], and the whole error read.  Negatives 1 and 2 end in "cannot
   unify"; negatives 3 and 4 report a plain "has type ... while it is
   expected to have type ...", with no "cannot unify" clause and no
   universe clause; negative 5 ends in "universe inconsistency: Cannot
   enforce cp = ch because ch < cp".

   Every constant a negative names also appears outside a [Fail], in a
   control below.  The controls were checked by rename simulation: each
   such constant was renamed throughout this file and the file then
   stopped compiling at a control rather than compiling with a vacuously
   green [Fail].

--------
目标文件的头部声明测量的每一个边界都在这里固定，从该文件的外部：文件内的负重命名与它所保护的常量同步，因此无法检测重命名。上面的 [Require] 列表完全镜像目标文件，加上目标文件本身以及见证者需要的两个模块。

三种类型的五个否定，按词汇分开，再加一个作用域自由的工具检查：

转换  1  [IsoDense] 全记录往返转换没有返回——stdlib [sigT] 没有估计时间
转换  2  共单位不是所选同构的满升的精确形式
类型检查  3  [counit (dense_adj D) a = id[a]] 类型不正确：两个端点是不同的 [Sub C S] 对象
类型检查  4  反射伴随不是 [Reflective] 记录
可形成性 5  [Subcategory] 识别其范畴的 Hom 和证明宇

负3是整个文件的重点：Mac Lane 的余单位是恒等式依赖于为子范畴中已经存在的对象选择 a_0 = a，并且如果使用作为统一函数提供的选择，子范畴中对象的代表可能是一个不同的对象。下面的例子是 [Indiscrete bool] 的一个满子范畴，包含两个点，其每个点的选定代表都是另一个点，并且两个端点被证明是不同的（[swap_objects_differ]）。

每个反例都是一次去掉一个，其余的保持为 [Fail]，然后读取整个错误。反例 1 和 2 以“cannot unify”结尾；反例 3 和 4 报告一个简单的“has type ... while it is expected to have type ...”，没有“cannot unify”条款，也没有 universe 条款；反例 5 以“universe inconsistency: Cannot enforce cp = ch because ch < cp”结尾。

每个常量的负命名也出现在 [Fail] 之外，在下面的一个控制中。这些控件通过重命名模拟进行了检查：每个这样的常量在整个文件中被重命名，然后该文件在一个控件处停止编译，而不是在 [Fail] 上以表面上绿色的方式编译。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
If this command ever succeeds, the [Fail] wrapper is not doing its job
   and every negative below is worthless.

--------
如果这个命令成功了，[Fail] 包装器就没有起作用，下面的每一个负面都是毫无意义的。
*)

Fail Check probe375_no_such_constant_anywhere.

Section Boundaries.

Context {C : Category}.
Context (S : Subcategory C).
Context (F : Subcategory.Full C S).
Context (D : IsoDense S).

(** ** Controls / ** 控制 *)

Check (Subcategory C).
Check (Sub C S).
Check (Incl C S).
Check (Incl_Faithful C S).
Check (Full_Implies_Full_Functor C S F).
Check (IsoDense S).
Check (iso_dense_ESO S D).
Check (ESO_iso_dense S (iso_dense_ESO S D)).
Check (dense_incl_equivalence S F D).
Check (dense_incl_adjoint_equivalence S F D).
Check (dense_reflector S F D).
Check (dense_adj S F D).
Check (dense_full_subcategory_reflective S F D : Reflective S).
Check (fun a : Sub C S => dense_counit_iso S F D a).
Check (fun a : Sub C S => dense_counit_Isomorphism S F D a).
Check (fun a : Sub C S =>
         @counit _ _ (dense_reflector S F D) (Incl C S)
           (dense_adj S F D) a).
Check (fun a : Sub C S => @id (Sub C S) a).
Check (reflector (dense_full_subcategory_reflective S F D)).
Check (reflective_adj (dense_full_subcategory_reflective S F D)).
Check (reflective_full (dense_full_subcategory_reflective S F D)).
Check (fun a : Sub C S => reflective_counit_iso
         (dense_full_subcategory_reflective S F D) a).

(** ** CONVERSION 1: the IsoDense round trip does not return / ** 转换 1：IsoDense 往返无法返回 *)

(*
The object components DO agree at [eq_refl] in both directions
   ([iso_dense_round_obj] and [ESO_iso_dense_obj] in the target), and the
   [EssentiallySurjective] whole record returns as well
   ([ESO_round_whole]), because that is a two-field class and Lib.v
   sets [Set Primitive Projections].  Stdlib [sigT] is not covered by
   that setting, so the [IsoDense] record does not.

--------
对象组件在 [eq_refl] 上在两个方向上都匹配（目标中的 [iso_dense_round_obj] 和 [ESO_iso_dense_obj]），并且整个 [EssentiallySurjective] 记录也会返回（[ESO_round_whole]），因为那是一个两字段类，并且 Lib.v 设置了 [Set Primitive Projections]。Stdlib [sigT] 不受该设置的影响，所以 [IsoDense] 记录不会返回。
*)

Fail Example probe_iso_dense_round :
  ESO_iso_dense S (iso_dense_ESO S D) = D := eq_refl.

(* The passing controls that locate the difference at the missing eta. / 确定缺失 η 处差异的通过控制。 *)

Example probe_iso_dense_round_obj (c : C) :
  `1 (ESO_iso_dense S (iso_dense_ESO S D) c) = `1 (D c) := eq_refl.

Example probe_ESO_round_whole (E : EssentiallySurjective (Incl C S)) :
  iso_dense_ESO S (ESO_iso_dense S E) = E := eq_refl.

(** ** CONVERSION 2: the counit does not reduce to the chosen iso / ** 转换 2：余单位不会化简为所选的同构 *)

(*
The counit ought to be the fullness-lift of [`2 (D (Incl C S a))], and
   that statement is true; but the route to it stops at [symmetry] on
   [Functor_Setoid] (Theory/Functor.v), whose [Equivalence] obligation
   is closed with [Qed], so the isomorphism family does not reduce.  The
   strict form is refuted here.  The control beside it names both sides of
   the refuted equation in a command that succeeds.

--------
余单位应该是 [`2 (D (Incl C S a))] 的全满提取，并且这一说法是正确的；但是通向它的路径在 [Functor_Setoid]（Theory/Functor.v）上的 [symmetry] 处停止，其 [Equivalence] 义务通过 [Qed] 被关闭，因此同构族不会化简。严格形式在这里被驳斥。旁边的控制命令在一个成功的命令中命名了被驳斥方程的两边。
*)

Fail Example probe_counit_is_chosen_iso (a : Sub C S) :
  fmap[Incl C S]
    (@counit _ _ (dense_reflector S F D) (Incl C S) (dense_adj S F D) a)
    = to (`2 (D (Incl C S a))) := eq_refl.

Check (fun a : Sub C S =>
         (fmap[Incl C S]
            (@counit _ _ (dense_reflector S F D) (Incl C S)
               (dense_adj S F D) a),
          to (`2 (D (Incl C S a))))).

(** ** TYPING 3: the counit is not the identity, and cannot be / ** 类型 3：余单位不是恒等映射，并且不能是 *)

(*
[counit ... a] runs [dense_reflector D (Incl C S a) ~> a].  Its source
   is the CHOSEN representative of [Incl C S a], which is a value of [D]
   and not [a].  The equation is therefore between morphisms of different
   types.  A witness where the two endpoints are provably distinct is the
   swap witness at the end of this file.

--------
[counit ... a] 运行 [dense_reflector D (Incl C S a) ~> a]。它的来源是 [Incl C S a] 的 CHOSEN 代表，该值属于 [D]，而不是 [a]。因此，该方程是在不同类型的态射之间。一个证明两个端点明显不同的证据是本文件末尾的交换证据。
*)

Fail Example probe_counit_id (a : Sub C S) :
  @counit _ _ (dense_reflector S F D) (Incl C S) (dense_adj S F D) a
    = @id (Sub C S) a := eq_refl.

(** ** TYPING 4: the adjunction is not the Reflective record / ** 输入4：附加不是反射记录 *)

Fail Check (dense_adj S F D : Reflective S).

End Boundaries.

(** ** FORMABILITY 5: [Subcategory] identifies hom with proof / ** 可塑性 5：[Subcategory] 识别带有证据的同质 *)

(*
Every constant of the target is over [Category@{u u0 u0}], and the
   identification is inherited rather than introduced: [Subcategory] alone
   already forces it, with the category's own hom-set and identity
   accepted at the very levels where [Subcategory] is rejected.  The
   identification sits in [Subcategory]'s BINDER; its constraint block is
   empty.  Only ONE such negative is pinned: [IsoDense] and [Reflective]
   both take a [Subcategory] argument, so neither can be tested apart from
   this donor.

--------
目标的每个常量都在 [Category@{u u0 u0}] 上，并且该同一性是继承的而非引入的：仅 [Subcategory] 就已经强制它，类别自身的 Hom 集和身份在 [Subcategory] 被拒绝的层次上被接受。该同一性位于 [Subcategory] 的 BINDER 中；其约束块为空。只有一个这样的负例被固定：[IsoDense] 和 [Reflective] 都接受 [Subcategory] 参数，因此除非有这个提供者，否则无法单独测试。
*)

Section UniverseProbe.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@homset Cu xu yu).

Fail Check (Subcategory Cu).

End UniverseProbe.

(** ** Witness (i): the skeleton of the indiscrete category on bool / ** 证人 (i)：bool上的不离散范畴的骨架 *)

(*
[Indiscrete_bool_Skeleton] (Theory/Skeleton/Separation.v) selects
   [true] alone out of the two points of [Indiscrete bool], so the
   reflection is genuinely non-inert at [false].

   RECORDED CORRECTION: an earlier revision added "Note the universe pin
   inherited from the witness: [Indiscrete@{u} : Type@{u} -> Category@{u
   Set Set}], so both readbacks below are about a category whose hom and
   proof universes are the literal [Set].  The general theorem carries no
   such pin."  There is no longer a pin to inherit: [Indiscrete] was
   annotated as [Indiscrete@{o h p} : Type@{o} -> Category@{o h p}] in the
   PR "algebraic carriers are sets" (2026-09-17),
   Instance/Discrete/Reconstruct.v.  The readbacks below are unchanged
   and still hold; what has gone is the caveat about the levels they hold
   at.

--------
[Indiscrete_bool_Skeleton]（Theory/Skeleton/Separation.v）从[Indiscrete bool]的两个点中只选择[true]，因此在[false]的反射实际上是非惯性的。

已记录的更正：之前的一个修订增加了“注意从见证继承的宇宙引脚：[Indiscrete@{u} : Type@{u} -> Category@{u Set Set}]，因此下面的两个读回都关于一个其 hom 和 proof 宇宙是字面 [Set] 的范畴。一般定理没有这样的引脚。” 现在不再有需要继承的引脚：[Indiscrete] 在 PR “代数载体是集合”（2026-09-17），Instance/Discrete/Reconstruct.v 中被标注为 [Indiscrete@{o h p} : Type@{o} -> Category@{o h p}]。下面的读回保持不变并仍然成立；消失的是关于它们成立的层级的警告。
*)

Definition probe_skel_refl :
  Reflective (skel_sub Indiscrete_bool_Skeleton) :=
  skeleton_reflective Indiscrete_bool_Skeleton.

Example probe_skel_true :
  fobj[reflector probe_skel_refl] true
    = skel_rep Indiscrete_bool_Skeleton true := eq_refl.

Example probe_skel_false :
  fobj[reflector probe_skel_refl] false
    = skel_rep Indiscrete_bool_Skeleton false := eq_refl.

(* The carrier of the reflection is [true] at BOTH points ... / 反射的载体在两个点都是 [true] ... *)

Example probe_skel_carrier_false :
  `1 (fobj[reflector probe_skel_refl] false) = true := eq_refl.

(* ... so at [false] the reflection moves the object: it is not inert. / ...所以在 [false] 中，反射会移动物体：它不是惯性的。 *)

Example probe_skel_not_inert :
  `1 (fobj[reflector probe_skel_refl] false) = false → False.
Proof. discriminate. Qed.

(** ** Witness (ii): a full subcategory on BOTH points, choosing the other / ** Witness (ii): a full subcategory on BOTH points, choosing the other / ** 见证者 (ii)：在两个点上的一个完整子范畴，选择另一个 *)

(*
Every object of [Indiscrete bool] lies in this subcategory, so the
   subcategory is the whole category and Mac Lane's "for objects a in A we
   can then choose a_0 = a" is available -- but it is a CHOICE, and the
   [IsoDense] datum below makes the other one, sending each point to its
   negation.  Since [Indiscrete bool] has exactly one morphism in each
   hom-set, that is still an iso-density witness.

--------
[Indiscrete bool] 的每个对象都属于这个子范畴，因此这个子范畴就是整个范畴，并且 Mac Lane 的“对于 A 中的对象 a，我们可以选择 a_0 = a”是可行的——但这是一种选择，而下面的 [IsoDense] 数据构成了另一种选择，将每个点映射为它的相反。由于 [Indiscrete bool] 在每个同态集中恰好有一个态射，这仍然是一个同构密度证明。
*)

Definition BothPoints : Subcategory (Indiscrete bool) :=
  @Build_Subcategory (Indiscrete bool)
    (fun _ => True)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition BothPoints_Full :
  Construction.Subcategory.Full (Indiscrete bool) BothPoints :=
  fun _ _ _ _ _ => I.

Definition swap_dense : IsoDense BothPoints :=
  fun c => ((negb c; I); Indiscrete_iso (negb c) c).

Definition swap_reflective : Reflective BothPoints :=
  dense_full_subcategory_reflective BothPoints BothPoints_Full swap_dense.

(* The reflector negates. / 反射器抵消。 *)

Example swap_reflector_true :
  `1 (fobj[reflector swap_reflective] true) = false := eq_refl.

Example swap_reflector_false :
  `1 (fobj[reflector swap_reflective] false) = true := eq_refl.

(*
The two endpoints of the counit at an object [a] are DIFFERENT objects
   of [Sub], which is what makes the identity form ill-typed rather than
   merely unproved.

--------
在对象 [a] 上，余单位的两个端点是 [Sub] 的不同对象，这正是使得恒等式形式类型不正确而不仅仅是未被证明的原因。
*)

Lemma swap_objects_differ (a : Sub (Indiscrete bool) BothPoints) :
  fobj[reflector swap_reflective] (Incl (Indiscrete bool) BothPoints a) = a
    → False.
Proof.
  destruct a as [b p]; destruct b; simpl; intro H;
  inversion H.
Qed.

(*
... hence the hypothesis that would strictify the counit -- that the
   chosen representative of an object already in the subcategory IS that
   object -- fails outright here.  Even where it holds it does not
   suffice, since the chosen isomorphism may be a non-identity
   automorphism; the target's header records that.

--------
... 因此，将余单位严格化的假设——即已经在子范畴中的对象的所选代表正是该对象——在这里完全失败。即使在成立的情况下，它也不足够，因为所选的同构可能是非恒等自同构；目标的头部记录了这一点。
*)

Lemma swap_not_self_dense :
  (∀ a : Sub (Indiscrete bool) BothPoints,
      `1 (swap_dense (Incl (Indiscrete bool) BothPoints a)) = a) → False.
Proof.
  intro H; exact (swap_objects_differ ((true; I)) (H (true; I))).
Qed.

(*
The counit at such an object is nevertheless an isomorphism, which is
   the form the proposition's third clause takes here.

--------
这样的对象上的余单位仍然是一个同构，这正是该命题第三条款在这里所采用的形式。
*)

Check (fun a : Sub (Indiscrete bool) BothPoints =>
         dense_counit_iso BothPoints BothPoints_Full swap_dense a).

Check (fun a : Sub (Indiscrete bool) BothPoints =>
         dense_counit_Isomorphism BothPoints BothPoints_Full swap_dense a).
