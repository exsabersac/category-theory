Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Monad.Comparison.
Require Import Category.Comonad.Core.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rep.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Instance.Proset.Galois.FixedPoints.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Coq.Monoid.Free.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * Probe for Construction/Reflective/FixedPoints.v and its poset instance / * 探查 Construction/Reflective/FixedPoints.v 及其偏序集实例 *)

(*
This file states, from OUTSIDE both targets, every boundary those two
   files measure, so that a rename or a change of definition breaks a
   build rather than turning a guard silently green.  It mirrors the
   UNION of the two targets' [Require] lists (plus what the witnesses
   need); a short prefix would let a guard pass for the wrong reason.

   Contents: one scope-free instrument check, then negatives of THREE
   kinds kept lexically apart -- TYPING, CONVERSION and FORMABILITY --
   each with a control naming the same constants outside any guard, and
   finally the two concrete witnesses.

   The two witnesses are here rather than in the library files because
   Instance/Coq/Monoid/Free.v has a transitive closure of 67 modules
   (excluding itself), 44 of them outside the general file's 37, and the
   general theory needs none of it.

--------
该文件从两个目标的外部列出了这两个文件测量的每一个边界，以便重命名或更改定义会导致构建失败，而不是让守卫悄悄变绿。它反映了两个目标的 [Require] 列表的并集（加上证人所需的内容）；如果前缀过短，守卫可能会因为错误的原因而通过。

内容：一个无作用域的工具检查，然后是三种类型的否定——类型检查（TYPING）、转换（CONVERSION）和可形成性（FORMABILITY）——每种类型都有一个在任何守卫之外命名相同常量的控制，最后是两个具体的证人。

这两个证人在这里而不是在库文件中，是因为 Instance/Coq/Monoid/Free.v 有 67 个模块的传递闭包（不包括自身），其中 44 个模块在通用文件的 37 个之外，而通用理论不需要其中的任何内容。
*)

(** ** Instrument check / ** 仪表检查 *)

(*
A guard that must trigger for a trivial reason: the mechanism itself
   is working, and no [Require] above is needed for it.

--------
一个必须因微不足道的原因触发的守卫：机制本身在工作，并且不需要上述任何 [Require]。
*)
Fail Check probe386_instrument_no_such_constant.

(** ** Negatives of kind TYPING / ** 善良类型的消极面 *)

Section ProbeTyping.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(*
NEGATIVE 1 (TYPING).  The equivalence is between the two FIXED
   subcategories; it is not an equivalence carried by the original left
   adjoint.  The error is a plain "has type ... while it is expected to
   have type ...", with no unification clause.

--------
负 1（打字）。等价性存在于两个固定的子类别之间；它不是由原始左伴随携带的等价性。错误是一个简单的“类型是...，而预期类型是...”，没有统一子句。
*)
Fail Check (adjunction_fixed_point_equivalence A : EquivalenceOfCategories F).

(*
Controls: the term does elaborate at its own type, and [F] is a
   functor that [EquivalenceOfCategories] accepts as an argument.

--------
控件：该术语会在其自身类型上进行详细说明，而 [F] 是一个函子，[EquivalenceOfCategories] 接受其作为参数。
*)
Check (adjunction_fixed_point_equivalence A).
Check (fun (E : EquivalenceOfCategories F) => quasi_inverse).
Check (FixedL A).
Check (FixedR A).
Check (fixed_point_equivalence_swap A).
Check (fixed_AdjointEquivalence A).
Check (fixed_adjunction A).
Check (UnitFixed A).
Check (CounitFixed A).
Check (UnitFixed_Full A).
Check (CounitFixed_Full A).
Check (counit_iso_of_unit_iso A).
Check (unit_iso_of_counit_iso A).
Check (unit_fixed_iff_image A).
Check (counit_fixed_iff_image A).
Check (unit_iso_of_image A).
Check (counit_iso_of_image A).
Check (fixed_unit_inverse A).
Check (fixed_counit_inverse A).
Check (unit_fixed_reflective_of_idempotent A).
Check (counit_fixed_op_reflective_of_idempotent A).

End ProbeTyping.

Section ProbeTypingComonad.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Coreflective S).

(*
NEGATIVE 2 (TYPING).  The converse of [Idempotent_Coreflective] is NOT
   available as an [IdempotentComonad]: that class asks for an
   endofunctor presented as [W^op] for some [W : C ⟶ C], and the
   endofunctor a coreflection induces on C^op is [Incl ◯ reflector],
   which has no such presentation.  The error names the two classes
   directly.

--------
负数 2（键入）。[Idempotent_Coreflective] 的逆不可用作 [IdempotentComonad]：该类要求 endofunctor 以 [W^op] 的形式呈现用于某些 [W : C ⟶ C]，而 coreflection 在 C^op 上引起的 endofunctor 是 [Incl ◯ reflector]，它没有这样的呈现。错误直接给出了这两个类的名称。
*)
Fail Check (Reflective_IdempotentMonad R
              : IdempotentComonad
                  (Incl (C^op) (op_subcategory S) ◯ reflector R)
                  (Reflective_Monad R)).

(*
Control: in the op form the very same term typechecks, which is what
   [Coreflective_IdempotentMonad_op] delivers.

--------
控制：在操作形式中，相同的术语通过类型检查，这正是 [Coreflective_IdempotentMonad_op] 提供的功能。
*)
Check (Coreflective_IdempotentMonad_op R).
Check (Reflective_IdempotentMonad R).
Check (Reflective_Monad R).
Check @Incl.
Check @op_subcategory.
Check @reflector.
Check @sobj.
Check @IsIsomorphism.
Check @IdempotentComonad.
Check @Idempotent_Coreflective.
Check @WLocal_Subcategory.
Check @wlocal_obj_iff.
Check @wlocal_to_extract.
Check @extract_to_wlocal.

End ProbeTypingComonad.

(** ** Negatives of kind CONVERSION / ** 善意转化的消极面 *)

Section ProbeConversion.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(*
NEGATIVE 3 (CONVERSION).  The counit-fixed subcategory is not the
   opposite reading of the opposite adjunction's unit-fixed one: the two
   [sobj] fields carry [IsIsomorphism] in C and in C^op respectively, and
   those are different applications of the same class.  Only the
   underlying morphism agrees, which is [counit_fixed_op_strict].

--------
负向 3（转换）。余单位固定子范畴并不是对偶伴随的单位固定子范畴的对偶阅读：两个 [sobj] 域分别在 C 和 C^op 中承载 [IsIsomorphism]，而它们是同一类的不同应用。只有底层态射是相同的，即 [counit_fixed_op_strict]。
*)
Fail Example probe_counit_fixed_not_op :
  CounitFixed A = op_subcategory (UnitFixed (Opposite_Adjunction F U A))
  := eq_refl.

(*
Controls: the morphism identification that DOES hold, and the
   monad-side bridge, which holds on the whole record.

--------
控制：保持的同态识别，以及对整个记录都适用的单子端桥。
*)
Check (fun c : C =>
  eq_refl : @unit (D^op) (C^op) (U^op) (F^op) (Opposite_Adjunction F U A) c
              = @counit C D F U A c).
Check (eq_refl : UnitFixed A
                   = @MLocal_Subcategory D (U ◯ F)
                       (Adjunction_Induced_Monad A)).
Check (fun x : Sub D (UnitFixed A) =>
  eq_refl : `1 (@unit _ _ (FixedL A) (FixedR A) (fixed_adjunction A) x)
              = @unit C D F U A `1 x).
Check (fun y : Sub C (CounitFixed A) =>
  eq_refl : `1 (@counit _ _ (FixedL A) (FixedR A) (fixed_adjunction A) y)
              = @counit C D F U A `1 y).
Check (Opposite_Adjunction F U A).

End ProbeConversion.

Section ProbeConversionComonad.

Context {C : Category}.
Context {W : C ⟶ C}.
Context (H : @Comonad C W).

(*
NEGATIVE 4 (CONVERSION).  Membership in the colocal subcategory is
   invertibility read in C^op, and the covariant reading in C is a
   DIFFERENT type: the two inverse laws are exchanged.  That is why
   [wlocal_obj_iff] is a biconditional rather than an equation.

--------
负 4（转换）。在共定位子类中的成员资格是在 C^op 中以可逆性解读的，而在 C 中的协变解读是一种不同的类型：两个逆律被交换。这就是为什么 [wlocal_obj_iff] 是双条件而不是方程。
*)
Fail Example probe_wlocal_not_covariant (x : C) :
  sobj C (WLocal_Subcategory H) x = IsIsomorphism (@extract C W H x)
  := eq_refl.

(*
Controls: the op-side reading, which does hold on the nose, and the
   two passages.

--------
控制：操作侧读数，它确实贴合鼻子，以及两个通道。
*)
Check (fun x : C =>
  eq_refl : sobj C (WLocal_Subcategory H) x
              = @IsIsomorphism (C^op) x (W x) (@extract C W H x)).
Check (wlocal_to_extract H).
Check (extract_to_wlocal H).
Check (fun x : C => @extract C W H x).

End ProbeConversionComonad.

Section ProbeConversionGalois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

(*
NEGATIVE 5 (CONVERSION).  The bijection between the two sets of closed
   elements returns the underlying element on the nose only AFTER
   antisymmetry; the whole-sigma round trip is not even a conversion,
   the second component being a [Prop] with no proof irrelevance
   available.  This is what [closed_round_r] states instead.

--------
负5（转换）。两个闭合元素集合之间的双射只有在反对称性之后才会准确返回基础元素；整个 sigma 的往返甚至不是转换，第二个分量是一个 [Prop]，并且没有可用的证明无关性。这正是 [closed_round_r] 所陈述的内容。
*)
Fail Example probe_closed_sigma_round
  (p : ∃ a : A, GalClosed_r G a) :
  closed_l_to_r PA G (closed_r_to_l PB G p) = p := eq_refl.

(*
NEGATIVE 6 (CONVERSION).  Mac Lane's equation [p = RLp] is NOT a
   conversion: at a variable closed element the two sides are unrelated
   terms, and antisymmetry is what relates them.  This is the whole
   reason [closed_r_eq] carries an [Antisymmetric] hypothesis.

--------
负 6（转换）。Mac Lane 的方程 [p = RLp] 不是转换：在一个变量封闭的元素上，两边是无关的项，而反对称性将它们联系起来。这就是 [closed_r_eq] 带有 [Antisymmetric] 假设的全部原因。
*)
Fail Example probe_closed_not_definitional
  (a : A) (Hc : GalClosed_r G a) : gal_r G (gal_l G a) = a := eq_refl.

(*
Controls: the relatedness that DOES hold with no hypothesis, and the
   antisymmetric statement that supplies the equation.

--------
控制：在没有假设的情况下成立的相关性，以及提供方程的反对称陈述。
*)
Check (fun (a : A) (Hc : GalClosed_r G a) =>
  Hc : RA (gal_r G (gal_l G a)) a).
Check (gal_unit G PB).
Check (closed_r_eq PA PB G).
Check (closed_l_eq PA PB G).
Check (closed_r_iff_image_eq PA PB G).
Check (closed_l_iff_image_eq PA PB G).
Check (gal_lrl_eq PA PB G).
Check (gal_rlr_eq PA PB G).
Check (closed_r_to_l PB G).
Check (closed_l_to_r PA G).
Check (closed_round_r PA PB G).
Check (closed_round_l PA PB G).
Check (unit_fixed_iff_closed_r PA PB G).
Check (counit_fixed_iff_closed_l PA PB G).
Check (galois_fixed_point_equivalence PA PB G).
Check (galois_fixed_point_equivalence_swap PA PB G).
Check (GAdj PA PB G).

End ProbeConversionGalois.

(** ** Negatives of kind FORMABILITY / ** 亲和可塑性的缺点 *)

Section ProbeUniverses.

Universes uo uh up.
Constraint uh < up.

Context (Cu Du : Category@{uo uh up}).
Context (Fu : Du ⟶ Cu) (Uu : Cu ⟶ Du).

(*
Controls at the very same declared levels: the category's homs and its
   identities are formable, and so are functors in both directions.

--------
在完全相同的声明级别上进行控制：类别的同态及其同一性是可形成的，双向的函子也是如此。
*)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check Fu.
Check Uu.

(*
NEGATIVE 7 (FORMABILITY).  [Adjunction] identifies the hom universe
   with the proof universe.  This is inherited, not introduced by the
   targets (#367, #368 and #379 measure the same donor).

--------
否定 7（可形成性）。[Adjunction] 将同伦宇宙与证明宇宙等同。这是继承的，而不是由目标引入的（#367、#368 和 #379 测量的是同一捐赠者）。
*)
Fail Check (Fu ⊣ Uu).

(*
NEGATIVE 8 (FORMABILITY).  [Subcategory] does so independently, with
   no adjunction anywhere in the command.

--------
负 8（可成形性）。[Subcategory] 独立执行这一操作，在命令中的任何地方都没有附加。
*)
Fail Check (Subcategory Cu).

End ProbeUniverses.

(* Controls for the two donors, at levels where they ARE formable. / 两个供体的控制，在它们可形成的水平上。 *)
Section ProbeUniversesControl.

Universes vo vh.

Context (Cv Dv : Category@{vo vh vh}).
Context (Fv : Dv ⟶ Cv) (Uv : Cv ⟶ Dv).

Check (Fv ⊣ Uv).
Check (Subcategory Cv).
Check (fun (Av : Fv ⊣ Uv) => UnitFixed Av).
Check (fun (Av : Fv ⊣ Uv) => adjunction_fixed_point_equivalence Av).

End ProbeUniversesControl.

(** ** Witness: the free-monoid adjunction / ** 见证：自由幺半群对偶 *)

(*
Instance/Coq/Monoid/Free.v declares [MonCoq] and [UMon] as [#[local]]
   notations, which do not export; hence these two.

--------
Instance/Coq/Monoid/Free.v 将 [MonCoq] 和 [UMon] 声明为 [#[local] 符号，这些符号不会被导出；因此是这两个。
*)
Notation MonC := (@Mon Coq Coq_Monoidal).
Notation UMonC := (@Mon_Forget Coq Coq_Monoidal).

(* The unit at X carries [a] to the one-letter word [a :: nil]. / X 单元将 [a] 传递给单字母词 [a :: nil]。 *)
Example probe_free_unit_is_insert (X : Coq) (a : X) :
  @unit MonC Coq FreeMonoid UMonC free_monoid_adjunction X a
    = (a :: nil)%list := eq_refl.

(*
NO object of [Coq] is unit-fixed for this adjunction: a two-sided
   inverse [k] would give [k nil :: nil = nil].  So the unit-fixed
   subcategory of the free-monoid adjunction is EMPTY -- that is exactly
   what this states, and nothing is claimed about the counit-fixed one
   beyond the single object below.

--------
[Coq] 的对象没有为该伴随固定单元：一个双边逆 [k] 会给出 [k nil :: nil = nil]。因此，自由单子伴随的固定单元子范畴是空的——这正是这段话所陈述的，并且对于固定余单元的子范畴，除了下面的单个对象之外，没有其他的声明。
*)
Theorem free_monoid_unit_never_iso (X : Coq) :
  IsIsomorphism (@unit MonC Coq FreeMonoid UMonC free_monoid_adjunction X)
    → False.
Proof.
  intros [k Hr Hl].
  pose proof (Hr nil) as Hn.
  simpl in Hn.
  discriminate Hn.
Qed.

(*
The one-sided reading of "the fixed objects are the image of U" is
   therefore refuted: [list bool] IS [U (F bool)], so it lies in the
   image of the right adjoint, and yet the unit is not invertible there.
   The biconditional [unit_fixed_iff_image] escapes this because its
   right-hand side quantifies over COUNIT-FIXED objects.

--------
因此，对“固定对象是 U 的像”的片面解读被驳回：[list bool] 是 [U (F bool)]，所以它位于右伴随的像中，但单位在这里不是可逆的。双条件 [unit_fixed_iff_image] 逃脱了这个问题，因为它的右边对 COUNIT-固定对象进行量化。
*)
Example probe_list_is_U_of_F (X : Coq) :
  fobj[UMonC] (fobj[FreeMonoid] X) = list X := eq_refl.

Theorem probe_image_of_U_not_unit_fixed :
  IsIsomorphism
    (@unit MonC Coq FreeMonoid UMonC free_monoid_adjunction
       (fobj[UMonC] (fobj[FreeMonoid] bool)))
    → False.
Proof. exact (free_monoid_unit_never_iso (list bool)). Qed.

(*
The canonical comparison [eps (F x)] is not invertible here either, so
   [F eta] is not its inverse: Riehl's "F G F = F" reading is a
   statement about a Galois connection between POSETS and does not carry
   over to an arbitrary adjunction.  Whether some OTHER natural
   isomorphism [F ◯ U ◯ F ≈ F] exists at this adjunction is neither
   proved nor refuted here.

--------
在这里，规范比较 [eps (F x)] 也不可逆，因此 [F eta] 并不是它的逆：Riehl 的“F G F = F”解读是一个关于 POSETS 之间伽罗瓦对偶的陈述，并不能推广到任意的伴随对。是否在该伴随对中存在某个其他自然同构 [F ◯ U ◯ F ≈ F]，此处既没有证明也没有驳斥。
*)
(*
The object in question IS an [F]-image, which is what makes the next
   two computations a statement about the CANONICAL comparison.

--------
所讨论的对象确实是一个 [F] 图像，这也正是使接下来的两个计算成为关于标准比较声明的原因。
*)
Example probe_FreeMon_is_F_bool :
  FreeMon bool = fobj[FreeMonoid] bool := eq_refl.

Example probe_counit_of_two_words :
  `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
        (FreeMon bool)) (cons (@nil bool) nil)
    = @nil bool.
Proof.
  exact (free_monoid_counit_is_free_ext (FreeMon bool)
           (cons (@nil bool) nil)).
Qed.

Example probe_counit_of_empty_word :
  `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
        (FreeMon bool)) (@nil (list bool))
    = @nil bool.
Proof.
  exact (free_monoid_counit_is_free_ext (FreeMon bool)
           (@nil (list bool))).
Qed.

Theorem free_monoid_counit_not_iso :
  IsIsomorphism
    (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
       (FreeMon bool))
    → False.
Proof.
  intros [k Hr Hl].
  assert (Hinj : ∀ u v : list (list bool),
            `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
                  (FreeMon bool)) u
              = `1 (@counit MonC Coq FreeMonoid UMonC
                      free_monoid_adjunction (FreeMon bool)) v → u = v).
  { intros u v Huv.
    transitivity (`1 k
      (`1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
             (FreeMon bool)) u)).
    - symmetry; exact (Hl u).
    - rewrite Huv; exact (Hl v). }
  pose proof (Hinj (cons (@nil bool) nil) (@nil (list bool))) as Hc.
  rewrite probe_counit_of_two_words, probe_counit_of_empty_word in Hc.
  discriminate (Hc eq_refl).
Qed.

(*
The general theorem still applies there, with both fixed
   subcategories as they are: this is the control that the equivalence
   asks nothing of the adjunction.

--------
一般定理在那儿仍然适用，两者的固定子类保持不变：这是等价性对伴随关系不要求任何条件的控制。
*)
Check (adjunction_fixed_point_equivalence free_monoid_adjunction).

(** ** Witness: the identity adjunction, where every object is fixed / ** 证人：恒等伴随，其中每个对象都是固定的 *)

(*
The other extreme.  [adj_id]'s unit is [≈ id], so transporting
   invertibility of the identity along that equation makes every object
   of C unit-fixed, and dually.

--------
另一种极端。[adj_id] 的单位是 [≈ id]，因此沿着该方程传递恒等的可逆性会使 C 的每个对象都固定单位，反之亦然。
*)
Definition probe_id_unit_fixed {C : Category} (x : C) :
  sobj C (UnitFixed (@adj_id C)) x.
Proof.
  refine (fixed_IsIso_along (fixed_IsIso_of_iso (@iso_id C x)) _).
  symmetry; exact (@adj_id_unit C x).
Defined.

Definition probe_id_counit_fixed {C : Category} (x : C) :
  sobj C (CounitFixed (@adj_id C)) x.
Proof.
  refine (fixed_IsIso_along (fixed_IsIso_of_iso (@iso_id C x)) _).
  symmetry; exact (@adj_id_counit C x).
Defined.

Check (fun C : Category => adjunction_fixed_point_equivalence (@adj_id C)).

(** ** Witness: the shift connection on the naturals / ** 见证：自然音上的半音连接 *)

(*
The restricted left adjoint carries the fixed object 5 to 3, by
   computation, and 1 is not fixed.

--------
受限的左伴随通过计算将固定对象 5 映射到 3，而 1 不是固定的。
*)
Check nat_shift_five_closed.
Check nat_shift_five_fixed.
Check nat_shift_closed_r_iff.
Check nat_shift_closed_l_all.
Check nat_shift_two_one_not_closed.
Check nat_shift_gal_l_five.
Check nat_shift_FixedL_obj.
Check @image_preimage_image.
Check @preimage_image_preimage.
Check @image_closed_l.
Check @preimage_closed_r.
Check @group_action_fixed_point_equivalence.
