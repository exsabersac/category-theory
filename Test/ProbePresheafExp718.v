Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Closed.
Require Import Category.Instance.Two.

Open Scope category_scope.

Generalizable All Variables.

(** * Probe for issue #718 -- exponentials of presheaves / * 针对问题 #718 的探讨 —— 预层的指数 *)

(*
Every refutation command below was stripped ONE AT A TIME, compiled
   alone, and its WHOLE error read; the kind is read off the error TEXT.
   FORMABILITY = a "universe inconsistency: Cannot enforce ..." clause;
   CONVERSION = "cannot unify" between two terms of ONE type; TYPING = a
   plain "has type ... while it is expected to have type ..." with
   neither a cannot-unify nor a universe clause, or a bare
   "The type of this term is a product while it is expected to be ...".

   1 instrument check + 14 negatives:
     9 FORMABILITY  (1a, 1b, 1c, 1d, 2, 3, 4a, 4b, 4c)
     2 CONVERSION   (5, 6)
     3 TYPING       (7, 8, 9)

   The probe mirrors the target's FULL Require list -- a short prefix is
   what makes a negative pass for the wrong reason -- plus
   Instance/Fun/Closed.v and Instance/Two.v for the unconditional
   corollary, and Functor/Hom/Yoneda.v with
   Functor/Hom/Yoneda/Natural.v for the route measurement.  Note that a
   refutation command which does what it is supposed to do prints
   NOTHING, so each was stripped rather than trusted.

   GUARD COVERAGE, measured mechanically over the comment-stripped file:
   56 identifiers occur inside a refutation command and 49 of them also
   occur outside every one.  The seven exceptions are exhaustively the
   keyword [Fail] itself, the five [probe718_*] names DECLARED by a
   refutation command (which therefore never enter the environment), and
   the instrument's deliberately absent name.  No bound variable is among
   them.

   RENAME SIMULATION, 3/3.  Exactly three TARGET constants are named
   inside a refutation command -- [PshExp], [presheaf_exp_iso] and
   [Functor_Category_Closed] -- which is measured, not guessed: the same
   mechanical pass intersects the identifiers inside a refutation command
   with the 46 constants Instance/Fun/Exponential.v contributes and the
   four Instance/Fun/Closed.v gains, and returns those three.  Each was
   renamed in the TARGET ONLY -- whole-word, in both library files in
   place, their [.vo] rebuilt, and the files restored byte-exact
   afterwards -- and this file recompiled against the renamed library:
   every one broke at a [Check] line of the guard block below, and NONE
   inside a refutation command.  The guard
   block nevertheless names every constant of both library files that
   this probe could break on, not merely those three.

--------
下面的每个反驳命令都是一次去掉一个，单独编译，并完整读取其错误；错误类型是从错误文本中读取的。FORMABILITY = 一个“宇宙不一致：无法强制执行……”的条款；CONVERSION = 两个同一类型的项之间“无法统一”；TYPING = 一个普通的“具有类型……，而预期类型为……”，既没有无法统一也没有宇宙条款，或者一个简单的“该项的类型是一个乘积类型，而预期为……”的情况。

1 个仪器检查 + 14 个阴性：
     9 可成型性 (1a, 1b, 1c, 1d, 2, 3, 4a, 4b, 4c)
     2 转化 (5, 6)
     3 分型 (7, 8, 9)

该探针镜像目标的完整 Require 列表——短前缀会因为错误的原因而导致负通过——另外包括 Instance/Fun/Closed.v 和 Instance/Two.v 用于无条件推论，以及 Functor/Hom/Yoneda.v 和 Functor/Hom/Yoneda/Natural.v 用于路径测量。请注意，一个执行其预期操作的反驳命令不会打印任何内容，因此每个命令都被去掉，而不是被信任。

守卫覆盖率，通过对去掉注释的文件进行机械测量得出：
   56 个标识符出现在反驳命令中，其中 49 个也出现在每一个反驳命令之外。七个例外完全包括关键字 [Fail] 本身、反驳命令声明的五个 [probe718_*] 名称（因此它们从未进入环境）以及该工具故意缺少的名称。它们中没有绑定变量。

重命名模拟，3/3。在一个反驳命令中精确命名了三个TARGET常量——[PshExp]、[presheaf_exp_iso] 和 [Functor_Category_Closed]——这是经过测量的，而非猜测：相同的机械过程将反驳命令中的标识符与 Instance/Fun/Exponential.v 文件提供的46个常量以及 Instance/Fun/Closed.v 文件的新获得的四个常量相交，并返回这三个常量。每个常量仅在TARGET中被重命名——全字匹配，在两个库文件中原位修改，它们的 [.vo] 被重建，然后文件字节精确恢复——并且此文件针对重命名的库重新编译：每一个都在下面守护块的 [Check] 行出错，而没有一个出现在反驳命令中。然而，守护块仍然会命名该探测中可能出错的两个库文件的每个常量，而不仅仅是那三个。
*)

(* ------------------------------------------------------------------ *)
(** ** Instrument check / ** 仪表检查 *)

(*
A deliberately absent name.  If this were to succeed, the refutation
   commands below would be measuring nothing.

--------
一个故意缺失的名字。如果这成功了，下面的反驳命令将不会测量任何东西。
*)
Fail Check probe718_this_name_does_not_exist.

(* ------------------------------------------------------------------ *)
(** ** Guard controls -- every constant a negative names, named outside / ** 守卫控制——每个常量都是负名称，在外部命名 *)

Check @PshExp.
Check @PshExp_obj.
Check @PshExp_fmap.
Check @to_exp.
Check @to_exp_inner.
Check @from_exp.
Check @from_to_exp.
Check @to_from_exp.
Check @presheaf_exp_iso.
Check @to_exp_natural_X.
Check @from_exp_natural_X.
Check @Functor_Category_Closed.
Check @Functor_Category_Closed_cov.
Check @presheaf_terminal.
Check @presheaf_terminal_is_donor.
Check @exp_obj_is_display85.
Check @exponent_obj_is_PshExp.
Check @curry_is_to_exp.
Check @uncurry_is_from_exp.
Check @eval_is_at_identity.
Check @one_exp_iso.
Check @one_exp_to.
Check @one_exp_from.
Check @Psh2_Cart.
Check @Psh2_Closed.
Check @pq_point_distinct_unconditional.
Check @awodey_pointwise_not_exponential_unconditional.
Check @objectwise_candidate.
Check @PresheafP.
Check @PresheafQ.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Terminal.
Check @Sets_Cartesian.
Check @Sets_Closed.
Check @Sets_Terminal.
Check @Curried_CoHom.
Check @Yoneda_Lemma.
Check @yoneda_natural_pre.
Check @YoNatPre.
Check @Closed.
Check @exponent_obj.
Check @exp_iso.
Check @curry'.
Check @uncurry'.
Check @eval'.
Check @first.
Check @split.
Check @product_obj.
Check @Fun.
Check @Opposite.
Check @Functor.
Check @Sets.
Check @Terminal.
Check @_2.
Check @_1.

(* ------------------------------------------------------------------ *)
(** ** Positive controls the file's claims rest on / ** 积极控制文件所声称的内容 *)

(* The instance is found by typeclass resolution, at an arbitrary C. / 该实例是通过类型类解析在任意 C 处找到的。 *)
Definition probe718_resolves (C : Category) : @Closed ([C^op, Sets]) _ := _.

(* And so is the terminal object of the same category. / 同样，该范畴的终对象也是如此。 *)
Definition probe718_resolves_terminal (C : Category) :
  @Terminal ([C^op, Sets]) := _.

(*
Awodey display (8.5), restated from OUTSIDE the target so that a
   rename in the target breaks this file.

--------
Awodey 显示 (8.5)，从目标之外重新声明，因此目标中的重命名会破坏此文件。
*)
Example probe718_display85 {C : Category} (P Q : C^op ⟶ Sets) (c : C) :
  fobj[PshExp P Q] c
    = [[[C^op, Sets]]](
        @product_obj _ (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)
          (Curried_CoHom C c) P, Q )
  := eq_refl.

(* The class's data, read back from outside. / 从外部读取回来的类的数据。 *)
Example probe718_exponent {C : Category} (P Q : C^op ⟶ Sets) :
  @exponent_obj _ _ (Functor_Category_Closed C) P Q = PshExp P Q := eq_refl.

Example probe718_terminal (C : Category) :
  presheaf_terminal C = @Functor_Category_Terminal (C^op) Sets Sets_Terminal
  := eq_refl.

(*
Riehl's covariant reading is the same constant at the opposite
   category, on the nose.

--------
Riehl 的协变读数在相反类别上是相同的常数，恰好如此。
*)
Example probe718_cov (C : Category) :
  Functor_Category_Closed_cov C = Functor_Category_Closed (C^op) := eq_refl.

(*
WHY [first] AND NOT [split _ id]: in the pointwise-cartesian presheaf
   category the identity factor of [first] leaves NO [fmap[P] id]
   residue, so the second component of a pair passes through untouched
   and the first is precomposition on the nose.  Both close by [eq_refl].
   WHY it reduces is not isolated and no claim is made about it.

--------
为什么是 [first] 而不是 [split _ id]：在逐点笛卡尔预层范畴中，[first] 的恒等因子不会留下任何 [fmap[P] 剩余，所以一对的第二个分量直接通过而不受影响，第一个分量则是原样的前复合。两者都由 [eq_refl] 闭合。为什么它会归约并没有被单独讨论，也没有对此作出任何声明。
*)
Section FirstReduces.
Context {C : Category}.
Context (P : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).
Context (c c' : C) (h : c ~{C^op}~> c') (d : C^op).
Context (hp : fobj[@product_obj _ PshCart (Curried_CoHom C c') P] d).

Example probe718_first_snd :
  snd (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h) d hp) = snd hp
  := eq_refl.

Example probe718_first_fst :
  fst (@first _ PshCart _ _ P (fmap[Curried_CoHom C] h) d hp)
    = op h ∘ fst hp
  := eq_refl.
End FirstReduces.

(*
The two identifications that hold at [≈] and not at [eq_refl], stated
   from outside as the controls for negatives 5 and 6.

--------
在 [≈] 上成立而在 [eq_refl] 上不成立的两个识别，从外部表示为负数 5 和 6 的控制。
*)
Example probe718_eval_weak {C : Category} (P Q : C^op ⟶ Sets) (c : C)
  (gy : fobj[@product_obj _
               (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian)
               (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    ≈ (fst gy) c (id[c], snd gy)
  := eval_is_at_identity P Q c gy.

(*
The unconditional corollary of Instance/Fun/Closed.v, exercised from
   outside: the hypothesis that file's section F is stated over is now
   discharged by this issue's instance.

--------
Instance/Fun/Closed.v 的无条件推论，从外部使用：现在通过这个问题的实例，文件的 F 部分所陈述的假设已被解除。
*)
Check (awodey_pointwise_not_exponential_unconditional
         : @Isomorphism Sets
             ((@exponent_obj _ Psh2_Cart Psh2_Closed PresheafP PresheafQ) TwoY)
             objectwise_candidate -> False).
Check pq_point_distinct_unconditional.

(* ------------------------------------------------------------------ *)
(** ** The clone of the instance written WITHOUT universe binders / ** 未使用宇宙绑定器编写的实例克隆 *)

(*
Byte-for-byte the shipped body, with the [@{o h so +}] binder list,
   the [Category@{o h h}] annotation on C and the explicit [Sets@{h so}]
   all removed.  Measured, [About] under [Set Printing Universes]:

     probe718_closed_unannotated@{u u0} :
       forall C : Category@{u0 u0 u0}, Closed@{u u0 u}

   -- object, hom AND proof identified, where the shipped instance reads
   [forall C : Category@{o h h}, Closed@{so h u}] with block
   [h < so, h < u, o <= h, o <= so].  Negative 4c uses this clone.

--------
逐字节地运送的主体，带有 [@{o h so +}] 的绑定列表，
[Category@{o h h}] 在 C 上的注释，以及明确的 [Sets@{h so}]
均已移除。 测量得出，[About] 在 [Set Printing Universes] 下：

  probe718_closed_unannotated@{u u0} :
    forall C : Category@{u0 u0 u0}, Closed@{u u0 u}

-- 对象、hom 和证明已识别，其中运送的实例读取
[forall C : Category@{o h h}, Closed@{so h u}] with block
[h < so, h < u, o <= h, o <= so]。负 4c 使用此克隆。
*)
Program Definition probe718_closed_unannotated (C : Category) :
  @Closed ([C^op, Sets])
    (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian) := {|
  exponent_obj := fun P Q => PshExp P Q;
  exp_iso := fun X P Q => presheaf_exp_iso X P Q
|}.
Next Obligation.
  apply proper_morphism; split; simpl; [ | reflexivity ].
  assert (H : op (@id C x0) ∘ id ≈ @id C x0) by (unfold op; cat).
  etransitivity; [ exact (@fmap_respects _ _ x _ _ _ _ H c) | ].
  exact (@fmap_id _ _ x _ c).
Qed.

(* ------------------------------------------------------------------ *)
(** ** (1) The smallness bound: C's objects at or below Sets' carriers / ** (1) 小性界：C 中在或低于集合承载者的对象 *)

Section SmallC.
Universes coB chB oB soB.
Constraint oB < soB.
Constraint coB <= oB.
Context (Csm : Category@{coB chB chB}).
Context (Ps Qs : Csm^op ⟶ Sets@{oB soB}).

(*
CONTROL: with C's objects bounded by [Sets]' carrier universe, the
   display-(8.5) object IS an object of that same [Sets], and so are the
   functor, the isomorphism and the instance.

--------
控制：使用 C 的对象被 [Sets] 的承载宇宙所界定，显示-(8.5) 对象是同一个 [Sets] 的对象，函子、同构和实例也是如此。
*)
Check ([[[Csm^op, Sets@{oB soB}]]](Ps, Qs) : obj[Sets@{oB soB}]).
Check (PshExp Ps Qs).
Check (Functor_Category_Closed Csm).
End SmallC.

Section BigC.
Universes coA chA oA soA.
Constraint oA < soA.
Constraint oA < coA.
Context (Cbig : Category@{coA chA chA}).
Context (Xb Pb Qb : Cbig^op ⟶ Sets@{oA soA}).

(*
CONTROLS.  The presheaf category itself is perfectly formable at a C
   whose OBJECTS sit strictly ABOVE [Sets]' carrier universe -- so the
   bound the four negatives below pin is NOT the presheaf category's.
   Nor is it the terminal object's: [presheaf_terminal] ascribed at that
   very category is accepted.  (Why it is accepted -- the terminal
   presheaf is constant at [1] and so has no family indexed by C's
   objects in it -- is an explanation and not part of the measurement.)
   And [PshExp] READ ALONE is accepted too, landing in a LARGER [Sets]:
   measured, its printed result type is [Cbig^op ⟶ Sets@{u u0}] for
   fresh levels carrying [coA <= u].

--------
控制。预层范畴本身可以在一个 C 上完美形成，其对象严格位于 [Sets] 载体宇宙之上——因此下方针所绑定的四个负数**并不是**预层范畴的。它也不是终对象的：在该范畴上归属的 [presheaf_terminal] 是被接受的。（为什么它被接受——终预层在 [1] 上是恒定的，因此其内部没有由 C 的对象索引的族——这是一个解释，并不是测量的一部分。）并且单独读取的 [PshExp] 也是被接受的，会落入一个更大的 [Sets]：测量时，其打印结果类型是 [Cbig^op ⟶ Sets@{u u0}]，用于携带 [coA <= u] 的新层级。
*)
Check ([Cbig^op, Sets@{oA soA}]).
Check (presheaf_terminal Cbig : @Terminal ([Cbig^op, Sets@{oA soA}])).
Check (PshExp Pb Qb).

(*
NEGATIVE 1a (FORMABILITY).  The display-(8.5) object is not an object
   of that same [Sets].  The stripped error ends "(universe
   inconsistency: Cannot enforce ... = oA because oA < coA <= ...)", and
   the bound [coA <= ...] in the message is exactly [Transform]'s
   [Type@{max(o1,p2)}]: a set of natural transformations is a family
   indexed by C's objects.

--------
NEGATIVE 1a（可形成性）。显示的-(8.5)对象不是同一个[Sets]的对象。剥离的错误以“(宇宙不一致：无法强制 ... = oA 因为 oA < coA <= ...)”结束，消息中绑定的[coA <= ...]正是[Transform]的[Type@{max(o1,p2)}]：自然变换的集合是由C的对象索引的一个族。
*)
Fail Check ([[[Cbig^op, Sets@{oA soA}]]](Pb, Qb) : obj[Sets@{oA soA}]).

(*
NEGATIVE 1b (FORMABILITY).  This is the discriminating one against
   the third control: [PshExp] is accepted only because it may choose a
   BIGGER target: forced to land in the same [Sets] its arguments take
   values in, it is refused.

--------
NEGATIVE 1b（可成形性）。这是对第三个控制的区分：[PshExp] 之所以被接受，仅仅是因为它可能选择一个更大的目标：如果被迫降落在其参数取值的相同 [Sets] 中，它就会被拒绝。
*)
Fail Check (PshExp Pb Qb : Cbig^op ⟶ Sets@{oA soA}).

(*
NEGATIVE 1c (FORMABILITY).  [presheaf_exp_iso] is the constant that
   forces that collapse -- its statement puts the exponential on the
   right of a hom-setoid of the SAME presheaf category -- so it is
   refused here.

--------
负面 1c（可形成性）。[presheaf_exp_iso] 是强制该坍塌的常数——它的声明将指数放在同一预层范畴的同态集的右侧——因此在这里被拒绝。
*)
Fail Check (presheaf_exp_iso Xb Pb Qb).

(*
NEGATIVE 1d (FORMABILITY).  And so, therefore, is the headline.  This
   is Awodey's "for any small category C", as a measurement.

--------
负 1d（可形成性）。因此，标题也是如此。这是 Awodey 的“对于任何小范畴 C”，作为一种度量。
*)
Fail Check (Functor_Category_Closed Cbig).
End BigC.

(* ------------------------------------------------------------------ *)
(** ** (2)-(3) Hom = proof in the binder is the donors' doing / ** (2)-(3) Hom = 活页夹里的证明是捐赠者的作为 *)

Section HomBelowProof.
Universes coC chC cpC oC soC.
Constraint chC < cpC.
Constraint oC < soC.
Context (Cu : Category@{coC chC cpC}).

(*
CONTROLS accepted at levels where hom and proof are DECLARED APART:
   the hom type, an identity, and the bare functor type into [Sets].  So
   [Functor] is NOT a donor of [ch = cp].

--------
在 hom 和 proof 被声明分开的级别上接受的控制：
   hom 类型、一个恒等式，以及裸函数符号类型进入 [Sets]。因此
   [Functor] 不是 [ch = cp] 的捐赠者。
*)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => @id Cu x).
Check (@Functor Cu Sets@{oC soC}).

(*
NEGATIVE 2 (FORMABILITY).  [Opposite] forces [ch = cp] on its own; the
   stripped error ends "Cannot enforce cpC = chC because chC < cpC".

--------
负面 2（可成型性）。[Opposite] 强制 [ch = cp] 自行执行；去掉的错误以“无法强制 cpC = chC，因为 chC < cpC”结尾。
*)
Fail Check (Cu^op).

(*
NEGATIVE 3 (FORMABILITY).  So does [Fun], with NO [^op] anywhere in
   the command -- two INDEPENDENT donors, same error shape.

--------
负3（可形成性）。所以 [Fun] 也是如此，命令中没有 [^op] —— 两个独立的供体，相同的错误形态。
*)
Fail Check ([Cu, Sets@{oC soC}]).
End HomBelowProof.

(* ------------------------------------------------------------------ *)
(** ** (4) The route, and the load-bearing annotation / ** (4) 路线及承载标注 *)

Section Route.
Universes coD oD soD.
Constraint oD < soD.
Constraint coD < oD.
Context (Cr : Category@{coD oD oD}).
Context (Pr Qr Xr : Cr^op ⟶ Sets@{oD soD}).

(*
C's hom level MUST be pinned at [Sets]' carrier level for this section
   to measure anything: with it left free the Yoneda constants silently
   instantiate their own [Sets], and a refusal, when one surfaces at all,
   fires at some other pinned argument rather than at the lemma's
   category.  [Fun] pins it
   anyway, which is why the context above writes [Category@{coD oD oD}].

   CONTROLS, all accepted at a C whose OBJECTS sit strictly BELOW its
   homs: the presheaf category itself, the [*Pre] Yoneda functor (whose
   object universe is free), the display-(8.5) object, and every headline
   of the target, the covariant reading [Functor_Category_Closed_cov]
   included (it is annotated like the instance for exactly this
   reason).

--------
C 的同态层级必须固定在 [Sets] 的载体层级，以便本节能够测量任何内容：如果它保持自由，Yoneda 常数会默默地产生自己的 [Sets]，并且当某个拒绝出现时，它会在某个其他固定的参数上触发，而不是在引理的类别上。无论如何 [Fun] 都会固定它，这就是上文上下文写 [Category@{coD oD oD}] 的原因。

控制项，所有在其同态下对象严格低于 C 的情况均被接受：预层范畴本身，[*Pre] Yoneda 函子（其对象宇宙是自由的），显示-(8.5) 对象，以及目标的每一个标题，包括协变读法 [Functor_Category_Closed_cov]（它像实例一样被标注正是出于这个原因）。
*)
Check ([Cr^op, Sets@{oD soD}]).
Check (@YoNatPre Cr).
Check ([[[Cr^op, Sets@{oD soD}]]](Pr, Qr) : obj[Sets@{oD soD}]).
Check (PshExp Pr Qr).
Check (presheaf_exp_iso Xr Pr Qr).
Check (Functor_Category_Closed Cr).
Check (Functor_Category_Closed_cov Cr).

(*
NEGATIVE 4a, 4b (FORMABILITY).  [Yoneda_Lemma] is declared over
   [Category@{u0 u0 u0}] and is refused at that very C, with
   "Cannot enforce oD = coD because coD < oD".  [yoneda_natural_pre] is
   refused identically.  So a route through the Yoneda LEMMA would have
   narrowed the theorem, which is the measured content of the header's
   route paragraph.

--------
消极 4a、4b（可形成性）。[Yoneda_Lemma] 在 [Category@{u0 u0 u0}] 上被声明，并在那个 C 被拒绝，同时显示“无法强制 oD = coD，因为 coD < oD”。[yoneda_natural_pre] 以相同方式被拒绝。因此，通过 Yoneda 引理的路径本会缩小定理，这就是标题路径段所测量的内容。
*)
Fail Check (@Yoneda_Lemma Cr Pr).
Fail Check (yoneda_natural_pre Cr).

(*
NEGATIVE 4c (FORMABILITY).  The UNANNOTATED clone of the instance is
   refused here too, with the same message, where the shipped
   [Functor_Category_Closed Cr] above is accepted.  That is what makes
   the universe annotations load-bearing rather than decorative --
   jointly: measured one at a time out of tree, either the binder on C
   or the [Sets@{h so}] annotation alone keeps the object universe free,
   and only their joint absence collapses it (the target's header
   records both variants).

--------
负4c（可成形性）。实例的未加注释克隆在此也被拒绝，提示信息相同，而上述附带的[Functor_Category_Closed Cr]则被接受。这就是为什么宇宙注释是承重的而非装饰的原因——联合而言：从树外逐个测量，无论是C上的绑定器，还是单独的[Sets@{h so}]注释，都能保持对象宇宙的完整，只有当它们同时缺失时，宇宙才会崩塌（目标的头部记录了这两种变体）。
*)
Fail Check (probe718_closed_unannotated Cr).
End Route.

(* ------------------------------------------------------------------ *)
(** ** (5)-(6) The two conversion boundaries / ** (5)-(6) 这两个转换边界 *)

Section Conv.
Context {C : Category}.
Context (P Q : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(*
CONTROLS: the two spellings of Awodey's [y h × 1_P] both elaborate,
   and at the SAME type -- so the refusal below is about conversion and
   not about formability.

--------
控件：Awodey 的 [y h × 1_P] 两种拼写形式都很详细，并且在同一类型上——因此下面的拒绝是关于转换，而不是关于可形成性。
*)
Check (fun (c c' : C) (h : c ~{C^op}~> c') =>
         @first _ PshCart _ _ P (fmap[Curried_CoHom C] h)).
Check (fun (c c' : C) (h : c ~{C^op}~> c') =>
         @split _ PshCart _ _ _ _ (fmap[Curried_CoHom C] h)
           (@id ([C^op,Sets]) P)).

(*
NEGATIVE 5 (CONVERSION).  They are not the same term: the stripped
   error is "cannot unify" between two terms of one type.  The target
   uses [first], whose reduction the two [probe718_first_*] controls
   above pin.

--------
负 5（转换）。它们不是相同的术语：剥离后的错误是在一个类型的两个术语之间“无法统一”。目标使用 [first]，其简化被上面针脚处的两个 [probe718_first_*] 控制。
*)
Fail Definition probe718_first_is_split (c c' : C) (h : c ~{C^op}~> c') :
  @first _ PshCart _ _ P (fmap[Curried_CoHom C] h)
    = @split _ PshCart _ _ _ _ (fmap[Curried_CoHom C] h)
        (@id ([C^op,Sets]) P)
  := eq_refl.

(*
NEGATIVE 6 (CONVERSION).  Riehl's counit formula ev_c(γ,y) =
   γ_c(id_c,y) does NOT hold at [eq_refl]: [eval'] is [uncurry' id] and
   the identity of a functor category has component [fmap[−] id], so the
   value is γ_c(op id ∘ id, y) and the residue is one [id_left].  The
   [≈] form is [probe718_eval_weak] above.

--------
负 6（转换）。Riehl 的余单位公式 ev_c(γ,y) = γ_c(id_c,y) 在 [eq_refl] 处不成立：[eval'] 是 [uncurry' id]，且函子范畴的单位元的分量是 [fmap[−] id]，所以值为 γ_c(op id ∘ id, y)，余数是一个 [id_left]。[≈] 形式如上面的 [probe718_eval_weak]。
*)
Fail Example probe718_eval_strict (c : C)
  (gy : fobj[@product_obj _ PshCart (PshExp P Q) P] c) :
  (@eval' _ _ (Functor_Category_Closed C) P Q) c gy
    = (fst gy) c (id[c], snd gy)
  := eq_refl.
End Conv.

(* ------------------------------------------------------------------ *)
(** ** (7)-(9) Three typing boundaries / ** (7)-(9) 三个打字边界 *)

Section Typing.
Context {C : Category}.
Context (P Q X : C^op ⟶ Sets).
#[local] Notation PshCart :=
  (@Functor_Category_Cartesian (C^op) Sets Sets_Cartesian).

(* CONTROL: the exponential IS a presheaf. / 控制：指数是一个预层。 *)
Check (PshExp P Q : C^op ⟶ Sets).

(*
NEGATIVE 7 (TYPING).  It is not a COVARIANT functor: the stripped
   error is a plain "The term "PshExp P Q" has type "C^op ⟶ Sets" while
   it is expected to have type "C ⟶ Sets"", with no cannot-unify and no
   universe clause.  (The covariant reading of the THEOREM is
   [Functor_Category_Closed_cov], which is the instance at the opposite
   category, not this ascription.)

--------
负 7（打字）。它不是协变函子：剥离后的错误只是“术语‘PshExp P Q’的类型是‘C^op ⟶ Sets’，而预期类型是‘C ⟶ Sets’”，没有无法统一的情况，也没有宇宙条款。（定理的协变解释是 [Functor_Category_Closed_cov]，它是在对偶范畴上的实例，而不是这个类型注解。）
*)
Fail Definition probe718_psh_covariant : C ⟶ Sets := PshExp P Q.

(*
CONTROL: [exponent_obj y z] is z^y, so [PshExp P Q] is Q^P and the
   transposition names P as the factor and Q as the target.

--------
控制：[exponent_obj y z] 是 z^y，因此 [PshExp P Q] 是 Q^P，并且置换将 P 作为因子，Q 作为目标。
*)
Check (presheaf_exp_iso X P Q
         : @Isomorphism Sets
             ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
             ([[[C^op, Sets]]]( X, PshExp P Q ))).

(*
NEGATIVE 8 (TYPING).  The two arguments of [PshExp] are not
   interchangeable: ascribing the same isomorphism with [PshExp Q P] on
   the right is a plain has-type mismatch.

--------
负 8（输入）。[PshExp] 的两个参数不可互换：在右侧与 [PshExp Q P] 赋予相同同构是一种明确的类型不匹配。
*)
Fail Definition probe718_swapped :
  @Isomorphism Sets
    ([[[C^op, Sets]]]( @product_obj _ PshCart X P, Q ))
    ([[[C^op, Sets]]]( X, PshExp Q P ))
  := presheaf_exp_iso X P Q.

(*
NEGATIVE 9 (TYPING).  The objectwise assignment c |-> Q(c)^{P(c)} is a
   bare FAMILY of objects of [Sets] and not a presheaf: the stripped
   error is "The type of this term is a product while it is expected to
   be (C^op ⟶ Sets)".  READ THAT NARROWLY.  It pins the SHAPE of the
   objectwise data -- values with no action -- and is NOT a proof that no
   contravariant action on those values exists; Instance/Fun/Closed.v's
   header records that for the family at hand one does.  What refutes the
   objectwise formula is that file's
   [awodey_pointwise_not_exponential_unconditional], checked above, which
   shows the objectwise VALUE is already the wrong object.

--------
负面 9（类型）。对象级别的赋值 c |-> Q(c)^{P(c)} 是 [Sets] 的一个**裸**对象族，而不是预层：精简后的错误信息是“该项的类型是乘积类型，而期望的是 (C^op ⟶ Sets)”。严格理解这一点。它固定了对象级数据的形态——值但没有作用——并不能证明这些值上不存在逆变作用；Instance/Fun/Closed.v 的头部记录了该族确实存在这样的作用。反驳对象级公式的是该文件中的 [awodey_pointwise_not_exponential_unconditional]（上面已经检查过），它显示对象级的值已经是错误的对象。
*)
Fail Definition probe718_objectwise : C^op ⟶ Sets :=
  fun c => @exponent_obj Sets Sets_Cartesian Sets_Closed
             (fobj[P] c) (fobj[Q] c).
End Typing.
