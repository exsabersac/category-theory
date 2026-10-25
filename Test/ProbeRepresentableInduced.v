(**
* Boundary probes for the induced-arrow theorem

    Companion to Functor/Representable.v and Functor/Representable/Functorial.v
    (issue #317; Mac Lane §III.2 Exercise 1, printed p. 62).  Those files make
    strength claims of two DIFFERENT kinds, and this file pins both.  **If the
    [Fail] commands below stop failing, this file breaks the build.**

    THE TWO KINDS ARE NOT THE SAME AND ARE NOT DESCRIBED WITH ONE WORD.

    (1) FORMABILITY.  [Yoneda_Full], [Yoneda_Faithful] and the [Yoneda_Embedding']
    assembled from them (Functor/Hom.v) are stated over
    [C : Category@{u u u}] — object, hom and proof universes IDENTIFIED — so
    nothing built over them applies to a category whose objects live strictly
    below its homs.  [repr_pair_iso] (Functor/Hom/Yoneda/Iso.v) consumes
    [Yoneda_Embedding'] and inherits the pin, and so does
    Functor/Representable/Functorial.v's [repr_pair_iso_from_is_induced] —
    whose printed BINDER shows [Category@{u u0 u0}] and whose CONSTRAINT BLOCK
    carries [u = u0].  The rejections in group (1) are UNIVERSE
    INCONSISTENCIES: the term is not formable at all, not merely
    non-convertible.

    The point of the group is that Functor/Representable.v does NOT inherit
    that pin, so the controls are as load-bearing as the negatives: the
    [Representable] class, [repr_induced], its uniqueness packaging, the
    tautological representation and the representing-object FUNCTOR are all
    formable at exactly the category the donors are rejected at.  That is the
    file's claim that the development escaped the donors' restriction, and
    that claim is what would break here if someone re-routed
    Functor/Representable.v through [Yoneda_Embedding'].

    The pin on the donors is an artifact of top-level minimization on an
    unannotated [(C : Category)] binder, not something inherent to Yoneda
    fullness or faithfulness: re-running those two proof scripts verbatim
    inside a section whose category is annotated [Category@{uo uh uh}]
    succeeds, and controls 7 and 8 are those two re-derivations performed
    here, so that negatives 1-3 are pinned as facts about the CONSTANTS.
    Nothing in this development repairs the donors.

    (2) CONVERSION.  Two claims of Leibniz equality are rejected because the
    two sides carry a different number of [fmap] applications, while the
    corresponding claims elsewhere DO hold on the nose.  These are
    [Fail Definition ... := eq_refl] and not [Fail Example ... : T.]: a failing
    type ascription would guard only the statement, whereas what is claimed is
    convertibility of the two terms.

    COUNTS.  Eight negatives — six in group (1) and two in group (2) — and
    twelve positive controls, which is not a one-to-one pairing: group (1)'s
    nine controls serve its six negatives jointly, and group (2)'s three
    controls are successes of exactly the [Fail Definition ... := eq_refl]
    shape its two negatives are rejections of.  Every negative is accompanied
    by at least one control that must SUCCEED.  The instrument itself was
    checked twice, once on a [Check] control and once on a
    [Definition ... := eq_refl] control — wrapping [Fail] around a succeeding
    command reports "The command has not failed!" and aborts compilation — and
    every negative was compiled once with the [Fail] stripped, to confirm the
    error is the intended one: six universe inconsistencies for group (1), of
    which five report "Cannot enforce uh = uo because uo < uh" naming the
    declared universes and the sixth (negative 4) reports "Cannot enforce
    uo = ..." while unifying the [Copresheaves] and [Fun] spellings of the
    functor category, and two "cannot unify" conversion errors for group (2).
    The import list is Functor/Representable/Functorial.v's own, in that
    file's order, plus both target files.

--------
* 诱导箭定理的边界探针

《Functor/Representable.v》和《Functor/Representable/Functorial.v》的伴随文件（问题 #317；Mac Lane 第 III.2 节练习 1，印刷页 62）。这些文件提出了两种不同类型的强度声明，而本文件固定了两者。**如果下面的 [Fail] 命令不再失败，本文件将导致构建失败。**

这两种类型不同，不可以用一个词来描述。

(1) 可构造性。[Yoneda_Full]、[Yoneda_Faithful] 及由它们组装的 [Yoneda_Embedding']（Functor/Hom.v）是在 [C : Category@{u u u}] —— 对象、Hom 和证明宇宙被识别 —— 上声明的，因此在它们之上构建的任何东西都不适用于对象严格低于其 Hom 的范畴。[repr_pair_iso]（Functor/Hom/Yoneda/Iso.v）使用 [Yoneda_Embedding'] 并继承了 pin，Functor/Representable/Functorial.v 的 [repr_pair_iso_from_is_induced] 也是如此 —— 它的打印 BINDER 显示 [Category@{u u0 u0}]，CONSTRAINT BLOCK 承载 [u = u0]。第 (1) 组中的拒绝是宇宙不一致：该项根本无法构造，而不仅仅是不可转换。

这个组的重点是 Functor/Representable.v 并没有继承那个固定引脚，所以控制像负极一样承重：[Representable] 类、[repr_induced]、它的唯一性封装、同义反复的表示以及表示对象 FUNCTOR 都可以在捐赠者被拒绝的恰好类别上形成。也就是说，这个文件声称开发突破了捐赠者的限制，而如果有人通过 [Yoneda_Embedding'] 重新路由 Functor/Representable.v，这个声称就会在此处失效。

捐赠者上的固定是未注释的 [(C : Category)] 绑定器上顶级最小化的产物，而不是 Yoneda 充满性或忠实性的固有属性：在注释了 [Category@{uo uh uh}] 的类别的部分中逐字重新运行那两个证明脚本是成功的，控件 7 和 8 是在此进行的那两个重新推导，因此负例 1-3 被固定为关于 CONSTANTS 的事实。在这个开发中没有任何东西修复捐赠者。

(2) 转换。两个莱布尼茨等式的声明被拒绝，因为两边应用了不同数量的 [fmap]，而在其他地方相应的声明确实完全成立。这些是 [Fail Definition ... := eq_refl] 而不是 [Fail Example ... : T.]：一个失败的类型归属只会保护声明，而所主张的是两个项的可转换性。

计数。八个阴性——第（1）组六个，第（2）组两个——以及十二个阳性对照，这不是一对一配对：第（1）组的九个对照共同服务于它的六个阴性，第（2）组的三个对照正好是 [Fail Definition ... := eq_refl] 形状，它们的两个阴性是被拒绝的。每个阴性都至少伴随一个必须成功的对照。
该仪器本身进行了两次检查，一次使用 [Check] 控制，另一次使用 [Definition ... := eq_refl] 控制——将 [Fail] 包裹在随后的命令周围会报告“该命令未失败！”并中止编译——每个负面情况都在去掉 [Fail] 后编译一次，以确认错误是预期的错误：组（1）存在六个宇宙不一致，其中五个报告“无法强制 uh = uo，因为 uo < uh”，指出声明的宇宙，第六个（负面 4）在统一 [Copresheaves] 和 [Fun] 的函子类别拼写时报告“无法强制 uo = ...”，组（2）有两个“无法统一”的转换错误。导入列表是 Functor/Representable/Functorial.v 自身的列表，按该文件中的顺序，加上两个目标文件。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Iso.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Representable.Functorial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(**
** (1) The donors' universe restriction, and the escape from it

    A category whose object universe is declared STRICTLY BELOW its hom
    universe.  The Yoneda donors do not reach it; the induced-arrow
    development does.

--------
** (1) 捐赠者的宇宙限制，以及从中逃逸

    一个范畴，其对象宇宙被声明严格低于其同构宇宙。Yoneda 捐赠者达不到它；诱导箭头的发展可以。
*)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(*
Control 1: the curried hom-functor itself is formable here — so what the
   negatives reject is the fullness/faithfulness packaging, not [Curried_Hom]
   and not the [[C, Sets]] target.

--------
控制 1：偏函数化的同函子本身在这里是可构造的——所以被否定的是否定的是完整性/忠实性封装，而不是 [Curried_Hom]，也不是 [[C, Sets] 目标。
*)
Check (Curried_Hom C).

(*
Control 2: so is the [Representable] class, which is what makes the
   restriction worth escaping — the class is more general than its donors.

--------
控制 2：[Representable] 类也是如此，这正是使得该限制值得逃避的原因——该类比它的捐赠者更通用。
*)
Check (fun F : C ⟶ Sets => Representable F).

(*
Controls 3-6: and so is the whole of Functor/Representable.v's
   development — the induced arrow, its uniqueness packaging, the
   isomorphism upgrade, and the tautological representation.

--------
控件 3-6：Functor/Representable.v 的整个开发过程也是如此——诱导箭头、其唯一性封装、同构升级以及自明表示。
*)
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (tau : K ⟹ K') => repr_induced R R' tau).
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (tau : K ⟹ K') => repr_induced_universal R R' tau).
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (i : K ≅[Fun] K') => repr_induced_iso R R' i).
Check (fun c : C => Hom_Representable c).

(* Negative 1: faithfulness of the Yoneda embedding is not formable here. / 负1：此处无法形成Yoneda嵌入的忠实性。 *)
Fail Check (Yoneda_Faithful C).

(* Negative 2: neither is fullness... / 负二：也不是充实… *)
Fail Check (Yoneda_Full C).

(*
...and negative 3, therefore neither is the packaged hom-bijection the
   issue suggested routing through.

--------
...以及负三，因此打包的同态双射都不是所建议通过的路径问题。
*)
Fail Check (fun c d : C => Yoneda_Embedding' C c d).

(*
Negative 4: the pin propagates to [repr_pair_iso], which consumes
   [Yoneda_Embedding'] — so it is the DONORS' restriction and not something
   Functor/Hom/Yoneda/Iso.v introduces.

--------
负4：引脚传播到[repr_pair_iso]，它消耗[Yoneda_Embedding'] —— 因此这是捐赠者的限制，而不是Functor/Hom/Yoneda/Iso.v引入的东西。
*)
Fail Check (fun (F : C ⟶ Sets) (c v : C)
                (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F) =>
              repr_pair_iso b1 b2).

(*
Negative 5: ...and thence to Functor/Representable/Functorial.v's
   cross-link, whose printed binder does NOT show the identification.

--------
负 5: ...然后到 Functor/Representable/Functorial.v 的交叉链接，其打印的绑定器未显示标识。
*)
Fail Check (repr_pair_iso_from_is_induced C).

(*
Negative 6 is negative 1 one application further in: the projection out of
   the instance is rejected too, for the same reason.  It earns its place by
   pairing with control 7, which inhabits the very same class at this very
   category — so what is rejected is the CONSTANT [Yoneda_Faithful], not the
   claim that [Curried_Hom C] is faithful here.

--------
负6 是向前应用负1 的一次：实例的投射也被拒绝，原因相同。它之所以存在，是因为它与控制7配对，而控制7正好属于这个类别的同一个类——所以被拒绝的是常量 [Yoneda_Faithful]，而不是声称 [Curried_Hom C] 在这里是可靠的。
*)
Fail Check (@fmap_inj _ _ (Curried_Hom C) (Yoneda_Faithful C)).

(*
Controls 7 and 8: the same two proof scripts, copied verbatim from
   Functor/Hom.v and run here, succeed.  This is what makes negatives
   1-3 a statement about minimization rather than about mathematics.

--------
控件 7 和 8：相同的两个证明脚本，从 Functor/Hom.v 中逐字复制并在此运行，都成功了。这就是使得否定 1-3 成为关于最小化而不是关于数学的陈述的原因。
*)
Definition probe_faithful_rederived : Functor.Faithful (Curried_Hom C).
Proof.
  constructor.
  intros c c' f g same.
  simpl in same.
  specialize same with c id. now rewrite 2 id_left in same.
Qed.

Definition probe_full_rederived : Functor.Full (Curried_Hom C).
Proof.
  unshelve econstructor; simpl in *.
  - exact (fun c d f => f c id).
  - abstract(intros x y [Ftrans Fnat ?] c f; simpl in *;
    unfold op;
    now rewrite Fnat, id_right).
Defined.

End ObjectsBelowHoms.

(*
Control 9, outside the section: the representing-object functor is formable
   over a category with the same strict separation.  It is stated separately
   because it needs the section's constraint discharged into its own binder.

--------
控制 9，在该节之外：表示对象函子可以在具有相同严格分离的范畴上形成。它单独说明是因为需要将该节的约束释放到它自己的绑定器中。
*)
Section FunctorBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

Check (ReprObjFunctor C).

End FunctorBelowHoms.

(** ** (2) The conversion boundaries / ** (2) 转换边界 *)

Section Conversion.

Context (C : Category).
Context {F : C ⟶ Sets}.
Context {c v : C}.
Context (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F).

(*
Control 10: the issue's suggested route and the route taken produce the SAME
   TERM — [repr_induced] IS the Yoneda transpose, by [eq_refl].

--------
控制 10：问题建议的路径和实际采取的路径产生相同的术语 — [repr_induced] 是由 [eq_refl] 给出的 Yoneda 转置。
*)
Definition probe_yoneda_transpose (K K' : C ⟶ Sets)
  (R : Representable K) (R' : Representable K') (tau : K ⟹ K') :
  @two_sided_inverse _ _ _ _
    (Yoneda_Embedding' C (@repr_obj _ _ R) (@repr_obj _ _ R'))
    (repr_transport R R' tau)
  = repr_induced R R' tau := eq_refl.

(*
Control 11: the isomorphism [univ_property_unique_up_to_unique_iso]
   produces IS [repr_pair_iso], on the nose.

--------
控制 11：同构 [univ_property_unique_up_to_unique_iso] 产生了 IS [repr_pair_iso]，完全一样。
*)
Definition probe_up_unique_obj (P : C → Type) (eqP : ∀ x, Setoid (P x))
  (H : IsUniversalProperty C P eqP) (x y : C) (t : P x) (s : P y) :
  unique_obj (univ_property_unique_up_to_unique_iso C P eqP H x y t s)
  = repr_pair_iso (to (repr_equivalence x) t) (to (repr_equivalence y) s)
  := eq_refl.

(*
Negative 7: but [repr_pair_iso]'s leg is NOT the induced arrow on the nose.
   [nat_id]'s component is [fmap[F] id] rather than [id]
   (Theory/Natural/Transformation.v), so the induced arrow carries one
   [fmap] application the leg does not, and the agreement is only [≈]
   ([repr_pair_iso_from_is_induced]).

--------
负7：但是[repr_pair_iso]的腿并不是鼻子上的诱导箭头。
[nat_id]的组件是[fmap[F] id]而不是[id]
（Theory/Natural/Transformation.v），所以诱导箭头携带一个[fmap]应用，而腿没有，并且一致性仅为[≈]
（[repr_pair_iso_from_is_induced]）。
*)
Fail Definition probe_pair_iso_strict :
  from (repr_pair_iso b1 b2)
  = repr_induced (repr_of_representation c b1)
                 (repr_of_representation v b2) nat_id := eq_refl.

End Conversion.

Section ConversionWitness.

Notation BNat := (Deloop Nat_Plus).

(*
Control 12: against the tautological representations the induced arrow
   computes on the nose.

--------
控制 12：针对同义反复表示，诱导箭头会准确地计算出来。
*)
Definition probe_wit_computes (n : nat) :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau n) = n := eq_refl.

(*
Negative 8: against [YoEvalAt_Representable] it does not, even
   componentwise — the Yoneda isomorphism's backward leg leaves an [∘ id],
   which over (ℕ, +) is an [n + 0].  The agreement is [≈]
   ([wit_ev_induced]).

--------
负 8：对于 [YoEvalAt_Representable] 并不成立，即使是按组件考虑——Yoneda 同构的反向部分留下了一个 [∘ id]，在 (ℕ, +) 上它是一个 [n + 0]。这个一致性是 [≈]（[wit_ev_induced]）。
*)
Fail Definition probe_wit_ev_strict (n : nat) (d : BNat) (g : ttt ~{BNat}~> d) :
  transform[repr_induced (YoEvalAt_Representable BNat ttt)
                         (YoEvalAt_Representable BNat ttt) (wit_ev_tau n)] d g
  = transform[wit_tau n] d g := eq_refl.

End ConversionWitness.
