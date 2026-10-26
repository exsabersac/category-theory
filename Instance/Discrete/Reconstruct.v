Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Discrete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

Import EqNotations.

(* * * Reconstructing a discrete category from its set of objects / * * 从其对象集合重建一个离散范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 Reference: Saunders Mac Lane, “Categories for the Working Mathematician”,
 2nd ed., §I.2, p. 11, construction 2: “A category is discrete
 when every arrow is an identity ... every set X may be regarded
 as a discrete category, and every discrete category is so
 determined by its set of objects.”
 Reference: Michael Hedberg, “A coherence theorem for Martin-Löf's type
 theory”, Journal of Functional Programming 8(4), 1998
 (decidable equality implies uniqueness of identity proofs).

 Both halves of Mac Lane's vocabulary are already in the library: the
 *construction* [DiscreteCat A] (Instance/Discrete.v) turns a type into a
 category, and the *predicate* [Discrete C] (Structure/Discrete.v) asserts
 that a category has only identity morphisms.  What was missing is the
 sentence that joins them — “every discrete category is so determined by its
 set of objects”, i.e. the reconstruction of [C] from [obj C].  This file
 supplies it.

 ** The comparison functor

 In one direction nothing is needed.  For any category [C] there is a functor

 [Discrete_Compare C : DiscreteCat (obj C) ⟶ C]

 which is the identity on objects and sends an equality proof [e : x = y] to
 the transported identity [rew e in id].  It is total, axiom-free, and
 requires no hypothesis on [C] whatever.  Given [Discrete C] it is moreover
 *full* ([Discrete_Compare_Full]): the [Discrete] witness of an arrow [f] is
 precisely a preimage of [f] under [fmap].  Since it is also bijective on
 objects (definitionally the identity), the whole of Mac Lane's claim reduces
 to one question: is this functor *faithful*?

 ** Why a hypothesis is unavoidable, and where it comes from

 [DiscreteCat A]'s hom-setoid is [Morphism_equality] — strict Rocq equality
 [eq] on the equality proofs themselves.  A functor *into* [DiscreteCat
 (obj C)] must therefore choose, for each arrow [f : x ~> y] of [C], one
 proof of [x = y], and its three laws ([fmap_respects], [fmap_id],
 [fmap_comp]) are then equations *between equality proofs*.

 [Discrete C] does not pin that choice down.  It hands back a witness
 [H : x = y] together with [f ≈ rew H in id], but the constraint is stated up
 to [≈] in [C]; two proofs [H H' : x = y] with [rew H in id ≈ rew H' in id]
 are not thereby equal.  Taking [f := id] shows the point concretely: the
 witness is some [H : x = x] with [id ≈ rew H in id], which does not force
 [H = eq_refl].  So the obstruction is a property of the *target's strict
 hom-setoid*, not an artifact of any particular proof — and that is a
 theorem, not an impression: [Discrete_DiscreteRigid_forces_UIP] below shows
 that if every [Discrete] category were [DiscreteRigid], uniqueness of
 identity proofs would hold for every type.

 ** The hypothesis actually taken: rigidity, not UIP

 The crude repair is to assume uniqueness of identity proofs on [obj C].
 This file assumes something strictly weaker and purely category-theoretic:

 [DiscreteRigid C]  ⟺  [Faithful (Discrete_Compare C)]

 — distinct proofs of [x = y] give [≈]-distinguishable transported
 identities.  The two readings are proved interchangeable
 ([DiscreteRigid_Faithful], [DiscreteRigid_elementary]).  UIP on [obj C]
 implies rigidity ([DiscreteRigid_UIP]), and decidable object equality
 implies UIP by Hedberg's theorem, taken from the standard library as
 [UIP_dec] ([DiscreteRigid_dec]) — the same axiom-free route already used by
 Construction/Grothendieck/Strict.v.

 Weakening UIP to rigidity is not cosmetic.  Every [DiscreteCat A] is rigid
 for *every* type [A], with no hypothesis at all ([DiscreteCat_Rigid]),
 because there the transported identity [rew H in id] *is* [H].  A
 UIP-phrased theorem would not apply to [DiscreteCat A] for an arbitrary [A];
 the rigid one does.

 ** Where the correspondence lives

 [Discrete_iso] is an isomorphism in [StrictCat], not merely in [Cat]: both
 functors are the identity on objects, and both round trips are strictly
 equal to the identity functor, so the on-the-nose statement is available and
 is the stronger one.  Landing in [Cat] instead does *not* buy back the
 hypothesis — the obstruction is in constructing the functor at all, not in
 comparing the two composites — so the [Cat] form ([Discrete_iso_Cat]) is
 recorded merely as a corollary through [strict_equiv_implies_fun_equiv].

 ** The iso-robust restatement

 Structure/Discrete.v carries an in-file caveat that phrasing discreteness
 through object *equality* is too strong, and the nLab notes the same: the
 equivalence-respecting reading asks instead that hom-setoids be
 subsingletons and every arrow be invertible.  That reading is
 [DiscreteUpToIso] below, and the outcome is a genuine negative result rather
 than the hoped-for equivalence:

 - [Discrete C] gives invertibility of every arrow with no hypothesis
 ([Discrete_invertible]), but the subsingleton half needs UIP on [obj C]
 ([Discrete_DiscreteUpToIso]).
 - For [DiscreteCat A] the restatement is *exactly* UIP on [A]
 ([DiscreteUpToIso_DiscreteCat]), whereas [Discrete (DiscreteCat A)] holds
 unconditionally ([DiscreteCat_Discrete]).  Consequently a general
 implication [Discrete C → DiscreteUpToIso C] would prove UIP for every
 type ([Discrete_DiscreteUpToIso_forces_UIP]), which is independent of
 Rocq's logic; it therefore cannot be established in-tree.
 - The converse implication is refuted outright: the indiscrete category on
 [bool] satisfies the restatement ([Indiscrete_DiscreteUpToIso]) yet
 [Discrete] of it is contradictory ([Indiscrete_bool_Discrete_absurd]).

 The reason is structural: subsingleton homs plus invertibility says [C] is
 *essentially* discrete — equivalent, given a choice of representatives, to
 the discrete category on its iso-classes — not isomorphic to
 [DiscreteCat (obj C)].  So the restatement is a different notion, and the
 two are INDEPENDENT in a precise sense proved below: the direction
 [DiscreteUpToIso → Discrete] is refuted outright by [Indiscrete bool],
 while the direction [Discrete → DiscreteUpToIso] is unprovable in bare
 Rocq — [Discrete_DiscreteUpToIso_forces_UIP] shows it entails UIP for
 every type — yet true under UIP ([Discrete_DiscreteUpToIso]).  Neither
 contains the other constructively; one inclusion holds exactly when UIP
 does.

 [Indiscrete] was introduced here as that separating witness.  It now has a
 second use: it is the non-skeletal half of the equivalence-invariance
 separation of Theory/Skeleton/Separation.v, where [Indiscrete bool] is
 equivalent to [1] yet not skeletal, and where its skeleton is exhibited on
 the nose as [1] ([Indiscrete_bool_skeleton_is_One]). 

 --------
 nLab: https://ncatlab.org/nlab/show/discrete+category
 参考文献：Saunders Mac Lane，《为在职数学家准备的范畴》，第二版，第I.2节，第11页，构造2：“当每个箭头都是恒等箭头时，一个范畴是离散的……每一个集合X都可以被看作一个离散范畴，每一个离散范畴都由它的对象集合唯一确定。”
 参考文献：Michael Hedberg，《Martin-Löf类型理论的一个相干性定理》，《函数式程序设计杂志》 8(4), 1998（可判定的等式意味着恒等证明的唯一性）。麦克莱恩词汇的两半已经在库中：*构造* [DiscreteCat A] (Instance/Discrete.v) 将一个类型变成一个范畴，而 *谓词* [Discrete C] (Structure/Discrete.v) 断言一个范畴只有恒等态射。缺少的是将它们连接起来的句子——“每个离散范畴由其对象集合唯一确定”，即从 [obj C] 重建 [C]。此文件提供了它。

 ** 比较函子

 在一个方向上不需要任何东西。对于任何范畴 [C]，都存在一个函子

 [Discrete_Compare C : DiscreteCat (obj C) ⟶ C]它是在对象上恒等的，并将等式证明 [e : x = y] 发送到传输的恒等 [rew e in id]。它是全体的、无公理的，并且不需要对 [C] 有任何假设。给定 [Discrete C]，它还*完全*（ZW11WZZ）：一个箭头 [f] 的 [Discrete] 证人恰好是 [f] 在 [fmap] 下的原像。由于它在对象上也是双射（定定义为恒等），Mac Lane 的整个主张简化为一个问题：这个函子是*忠实*的吗？

 ** 为什么假设是不可避免的，以及它来自何处[DiscreteCat A] 的同构集是 [Morphism_equality] ——严格的 Rocq 相等 [eq] 在平等证明自身上。因此，一个指向 [DiscreteCat (obj C)] 的函子必须为 [C] 的每一条箭头 [f : x ~> y] 选择一个 [x = y] 的证明，并且它的三个定律（[fmap_respects]、[fmap_id]、[fmap_comp]）随后就是 *平等证明之间* 的方程。[Discrete C] 并没有固定那个选择。它返回一个见证 [H : x = y] 与 [f ≈ rew H in id]，但约束只在 [≈] 中对 [C] 陈述；两个证明 [H H' : x = y] 与 [rew H in id ≈ rew H' in id] 因此并不相等。采取 [f := id] 可以具体展示这一点：见证是某个 [H : x = x] 与 [id ≈ rew H in id] 的组合，这并不强制 [H = eq_refl]。所以这个障碍是*目标的严格同态集*的一个性质，而不是任何特定证明的产物——这是一个定理，而不是印象：下面的 [Discrete_DiscreteRigid_forces_UIP] 显示，如果每个 [Discrete] 类别都是 [DiscreteRigid]，那么每个类型的身份证明的唯一性都将成立。

 ** 实际采纳的假设：刚性，而不是 UIP粗略的修复是假设  [obj C] 上的身份证明是唯一的。
 该文件假设一些严格较弱且纯粹范畴论的内容：

 [DiscreteRigid C]   ⟺   [Faithful (Discrete_Compare C)]

 —  [x = y] 的不同证明会给出 [≈] 可区分的传输身份。 两种解读被证明是可互换的（ [DiscreteRigid_Faithful] ,  [DiscreteRigid_elementary] ）。 [obj C] 上的 UIP 意味着刚性（ [DiscreteRigid_UIP] ），而可判定的对象相等性根据 Hedberg 定理意味着 UIP，该定理取自标准库为 [UIP_dec] （ [DiscreteRigid_dec] ）——与 Construction/Grothendieck/Strict.v 已经使用的无公理路线相同。将 UIP 弱化为刚性并非表面功夫。每个 [DiscreteCat A] 对于 *每个* 类型 [A] 都是刚性的，完全没有任何假设（[DiscreteCat_Rigid]），因为那里传输的恒等式 [rew H in id] *就是* [H]。用 UIP 表述的定理不会适用于任意 [A] 的 [DiscreteCat A]；而刚性版本会适用。

 ** 对应关系所在的位置[Discrete_iso] 是 [StrictCat] 中的一个同构，而不仅仅是在 [Cat] 中：两个函子在对象上都是恒等的，并且两个往返组合严格等于恒等函子，因此可以使用精确的说法，并且这种说法更强。降落到 [Cat] 中并不会“买回”假设——阻碍在于构造函子本身，而不是比较两个复合——因此 [Cat] 形式（[Discrete_iso_Cat]）仅通过 [strict_equiv_implies_fun_equiv] 作为推论记录。

 ** 同构稳健的重述Structure/Discrete.v 文件中有一个警告，说明通过对象*相等*来表述离散性要求过强，而 nLab 也有相同的说明：符合等价关系的解释则要求同态集（hom-setoids）是子单元集合，并且每个箭头都是可逆的。下面的 [DiscreteUpToIso] 就是这种解释，其结果是一个真正的负面结论，而不是希望得到的等价关系。- [Discrete C] 提供了在没有前提条件下每个箭头的可逆性（[Discrete_invertible]），但是子单例部分需要在 [obj C] 上使用 UIP（[Discrete_DiscreteUpToIso]）。
 - 对于 [DiscreteCat A]，其重述*正好*是 [A] 上的 UIP（[DiscreteUpToIso_DiscreteCat]），而 [Discrete (DiscreteCat A)] 无条件成立（[DiscreteCat_Discrete]）。因此，一般蕴含 [Discrete C → DiscreteUpToIso C] 将证明每种类型的 UIP（[Discrete_DiscreteUpToIso_forces_UIP]），这是 Rocq 的逻辑中独立的；因此它无法在树内建立。
 - 逆向蕴含被直接反驳：关于 [bool] 的离散范畴满足重述（[Indiscrete_DiscreteUpToIso]），然而它的 [Discrete] 是矛盾的（[Indiscrete_bool_Discrete_absurd]）。原因是结构性的：子单子态射加上可逆性表明 [C] 本质上是离散的——在选择代表的情况下，相当于其同构类上的离散范畴——并不与 [DiscreteCat (obj C)] 同构。因此，这种重新表述是一个不同的概念，而且两者在下面证明的精确意义上是独立的：[DiscreteUpToIso → Discrete] 的方向被 [Indiscrete bool] 直接驳斥，而 [Discrete → DiscreteUpToIso] 的方向在纯 Rocq 中不可证明——[Discrete_DiscreteUpToIso_forces_UIP] 显示它会蕴含所有类型的 UIP——但在 UIP 下为真（[Discrete_DiscreteUpToIso]）。在构造意义上，两者都不包含对方；只有在 UIP 存在时，一个包含关系才成立。[Indiscrete] 在这里被引入作为那个分离证人。它现在有了第二个用途：它是 Theory/Skeleton/Separation.v 中等价不变分离的非骨架部分，其中 [Indiscrete bool] 与 [1] 等价但不是骨架，其骨架在 [1]（[Indiscrete_bool_skeleton_is_One]）上直接展示。
*)

(*
 Why a separate file rather than extending Instance/Discrete.v, as the
 issue's work-plan suggested: NOT layering -- Instance/Discrete.v,
 Instance/Cat.v and Instance/StrictCat.v are independent siblings, and
 adding the imports there would create no cycle.  The reason is cost to
 consumers: Instance/Discrete.v is imported by Adjunction/GAFT.v,
 Adjunction/SAFT.v, Structure/Limit/Product.v and Theory/WeaklyInitial.v,
 and extending it would drag Instance/Cat, Instance/StrictCat and the
 Eqdep_dec development into all four of those dependency cones for the
 sake of theorems none of them consume. 

 --------
 为什么要使用一个单独的文件，而不是像问题的工作计划所建议的那样扩展 Instance/Discrete.v：不是分层——Instance/Discrete.v、Instance/Cat.v 和 Instance/StrictCat.v 是独立的同级文件，在那里添加导入不会创建循环。原因是对使用者的成本：Instance/Discrete.v 被 Adjunction/GAFT.v、Adjunction/SAFT.v、Structure/Limit/Product.v 和 Theory/WeaklyInitial.v 导入，扩展它会将 Instance/Cat、Instance/StrictCat 和 Eqdep_dec 的开发拉入这四个依赖锥中，而这些定理它们都不会使用。
*)

(** ** Transported identities / ** 转运身份 *)

(* Composing transported identities transports along the concatenated proof. / 组成传递的身份沿着串联的证明进行传递。 *)
Lemma rew_id_trans {C : Category} {x y z : C} (H : x = y) (H' : y = z) :
  rew H' in id ∘ rew H in id ≈ rew (eq_trans H H') in id.
Proof. destruct H, H'; cat. Qed.

(*
 A transported identity is invertible, its inverse being the identity
 transported along the reversed proof. 

 --------
 被传送的恒等式是可逆的，其逆就是沿着反向证明传送的恒等式。
*)
Lemma rew_id_iso_to {C : Category} {x y : C} (H : x = y) :
  rew (eq_sym H) in id ∘ rew H in id ≈ id.
Proof. destruct H; cat. Qed.

Lemma rew_id_iso_from {C : Category} {x y : C} (H : x = y) :
  rew H in id ∘ rew (eq_sym H) in id ≈ id.
Proof. destruct H; cat. Qed.

(** ** The comparison functor / ** 比较函数对象 *)

(*
 [DiscreteCat (obj C) ⟶ C]: the identity on objects, sending an equality
 proof to the identity transported along it.  The explicit universe binders
 force the discrete category to sit at [C]'s own universes, which is what the
 [StrictCat] statement below needs; [Program] is avoided here because its
 obligations cannot refer to named universes. 

 --------
 [DiscreteCat (obj C) ⟶ C]：对象上的恒等，发送一个等式证明到沿它传递的恒等。显式的宇宙绑定器迫使离散范畴位于 [C] 自身的宇宙中，这正是下面的 [StrictCat] 语句所需要的；这里避免使用 [Program]，因为它的义务不能引用命名的宇宙。
*)
Definition Discrete_Compare@{o h p} (C : Category@{o h p}) :
  DiscreteCat@{o h p} C ⟶ C.
Proof.
  unshelve refine (@Build_Functor@{o h p o h p} (DiscreteCat@{o h p} C) C
    (fun x : C => x)
    (fun (x y : C) (e : x = y) => rew [fun z : C => x ~{C}~> z] e in id)
    _ _ _).
  (* [≈] on the source is [eq]; [rew eq_refl in id] is [id] / 源上的 [≈] 是 [eq]；[rew eq_refl in id] 是 [id] *)
  - intros x y; proper; destruct X; reflexivity.
  - intros x; reflexivity.
  - intros x y z H H'; symmetry; apply rew_id_trans.
Defined.

(* The action on morphisms, in the [rew] shape used by Structure/Discrete.v. / 在 Structure/Discrete.v 中使用的 [rew] 形状上的态射作用。 *)
Lemma fmap_Discrete_Compare {C : Category} {x y : C} (e : x = y) :
  fmap[Discrete_Compare C] e ≈ rew e in id.
Proof. reflexivity. Qed.

(*
 Fullness is exactly the [Discrete] predicate: the witness it produces for an
 arrow [g] is a preimage of [g] under [fmap].  No further hypothesis. 

 --------
 满性恰好是 [Discrete] 谓词：它为箭头 [g] 所产生的见证是 [g] 在 [fmap] 下的原像。无需进一步假设。
*)
Program Definition Discrete_Compare_Full (C : Category) (D : Discrete C) :
  Full (Discrete_Compare C) := {|
  prefmap := fun x y g => `1 (D x y g)
|}.
Next Obligation. symmetry; exact (`2 (D x y g)). Qed.

(* * ** Rigidity: faithfulness of the comparison functor / * ** 稳定性：比较函子 的忠实性 *)

(*
 The reconstruction hypothesis: an equality proof is recoverable from the
 identity it transports.  Equivalently (see below) the comparison functor is
 faithful. 

 --------
 重建假设：一个等式证明可以从它传递的恒等式中恢复。同样（见下文）比较函子是忠实的。
*)
Definition DiscreteRigid (C : Category) : Type :=
  ∀ (x y : C) (H H' : x = y),
    fmap[Discrete_Compare C] H ≈ fmap[Discrete_Compare C] H' → H = H'.

(* The same condition spelled out without the functor. / 相同的条件，不使用函子表达。 *)
Lemma DiscreteRigid_elementary (C : Category) :
  DiscreteRigid C ↔
    (∀ (x y : C) (H H' : x = y),
       (rew H in id : x ~> y) ≈ rew H' in id → H = H').
Proof. split; intros r x y H H'; exact (r x y H H'). Qed.

(* And in the library's vocabulary. / 在图书馆的词汇中。 *)
Lemma DiscreteRigid_Faithful (C : Category) :
  DiscreteRigid C ↔ Faithful (Discrete_Compare C).
Proof.
  split; intro r.
  - constructor; intros x y f g e; exact (r x y f g e).
  - intros x y H H' e; exact (@fmap_inj _ _ _ r x y H H' e).
Qed.

(*
 Uniqueness of identity proofs on the objects is one sufficient condition:
 under it the hypothesis of rigidity is discarded outright. 

 --------
 对象上身份证明的唯一性是一个充分条件：在此条件下，刚性假设被完全舍弃。
*)
Definition DiscreteRigid_UIP (C : Category)
  (uip : ∀ (x y : C) (H H' : x = y), H = H') : DiscreteRigid C :=
  fun x y H H' _ => uip x y H H'.

(* Decidable object equality is another, through Hedberg's theorem. / 可判定的对象相等性是另一种，通过 Hedberg 定理。 *)
Definition DiscreteRigid_dec (C : Category)
  (dec : ∀ x y : C, {x = y} + {x <> y}) : DiscreteRigid C :=
  DiscreteRigid_UIP C (@UIP_dec (obj[C]) dec).

(*
 On a discrete category the comparison functor acts as the identity on
 morphisms, since there [rew H in id] reduces to [H] itself. 

 --------
 在离散范畴上，比对函子在态射上表现为恒等，因为这里  [rew H in id]  化简为  [H] 本身。
*)
Lemma DiscreteCat_rew_id {A : Type} {x y : A} (H : x = y) :
  fmap[Discrete_Compare (DiscreteCat A)] H = H.
Proof. destruct H; reflexivity. Qed.

(*
 Hence every [DiscreteCat A] is rigid, for every [A], with no hypothesis —
 the gain over phrasing the theorem with UIP. 

 --------
 因此，每一个 [DiscreteCat A] 都是刚性的，对于每一个 [A]，没有任何假设——相比用 UIP 表述定理的收益。
*)
Lemma DiscreteCat_Rigid (A : Type) : DiscreteRigid (DiscreteCat A).
Proof.
  intros x y H H' e.
  rewrite <- (DiscreteCat_rew_id H), <- (DiscreteCat_rew_id H').
  exact e.
Qed.

(* * ** The reconstruction functor and the correspondence / * ** 重建函子与对应关系 *)

Section Reconstruction.

Context {C : Category}.
Context (Dis : Discrete C).
Context (rigid : DiscreteRigid C).

(* The equality proof that [Discrete] attaches to an arrow. / [Discrete] 附加到箭头的等式证明。 *)
Definition disc_eq {x y : C} (f : x ~> y) : x = y := `1 (Dis x y f).

(* ... and its defining property, in comparison-functor form. / ... 以及它的定义性质，以比较函子形式。 *)
Lemma disc_eq_spec {x y : C} (f : x ~> y) :
  f ≈ fmap[Discrete_Compare C] (disc_eq f).
Proof. exact (`2 (Dis x y f)). Qed.

(*
 The reconstruction functor [C ⟶ DiscreteCat (obj C)]: the identity on
 objects, sending an arrow to its [Discrete] witness.  Each of the three
 functor laws is an equation between equality proofs, and each is discharged
 by rigidity from the corresponding law in [C]. 

 --------
 重构函子 [C ⟶ DiscreteCat (obj C)]：在对象上是恒等的，将一个箭头映射到其 [Discrete] 证明。三个函子律中的每一个都是等式证明之间的方程，每一个都由 [C] 中相应律的刚性来解除。
*)
Definition Discrete_Reconstruct : C ⟶ DiscreteCat C.
Proof using C Dis rigid.
  unshelve refine (@Build_Functor C (DiscreteCat C)
    (fun x : C => x) (fun (x y : C) (f : x ~> y) => disc_eq f) _ _ _).
  - intros x y; proper.
    apply rigid.
    now rewrite <- !disc_eq_spec.
  - intros x.
    apply rigid.
    rewrite <- disc_eq_spec.
    now rewrite fmap_id.
  - intros x y z f g.
    apply rigid.
    rewrite fmap_comp.
    now rewrite <- !disc_eq_spec.
Defined.

(*
 Mac Lane's “determined by its set of objects”, on the nose: reconstruction
 and comparison are mutually inverse in [StrictCat].  Both object maps are
 the identity, so both strict-equality witnesses are [eq_refl] and only the
 morphism coherence has content.  The [from ∘ to] coherence is exactly the
 [Discrete] witness property; the [to ∘ from] coherence is a further appeal
 to rigidity. 

 --------
 麦克莱恩的“由其对象集合决定”，恰到好处：在 [StrictCat] 中，重构与比较是相互逆的。两个对象映射都是同一映射，因此两个严格相等的证明都是 [eq_refl]，只有态射的相容性有内容。[from ∘ to] 的相容性正是 [Discrete] 的证明性质；[to ∘ from] 的相容性是对刚性的进一步调用。
*)
Definition Discrete_iso : C ≅[StrictCat] DiscreteCat C.
Proof using C Dis rigid.
  unshelve refine (@Build_Isomorphism StrictCat C (DiscreteCat C)
    Discrete_Reconstruct (Discrete_Compare C) _ _).
  - exists (fun _ => eq_refl).
    intros x y f; simpl.
    apply rigid.
    now rewrite <- disc_eq_spec.
  - exists (fun _ => eq_refl).
    intros x y f.
    symmetry; exact (disc_eq_spec f).
Defined.

(*
 The same correspondence read in [Cat], where functors are compared up to
 natural isomorphism.  This is strictly weaker and is recorded only for
 convenience: it does not relax the hypothesis. 

 --------
 相同的对应关系在 [Cat] 中被读取，其中函子被比较到自然同构。这严格来说更弱，仅为方便而记录：它并没有放宽假设。
*)
Definition Discrete_iso_Cat : C ≅[Cat] DiscreteCat C :=
  @Build_Isomorphism Cat C (DiscreteCat C)
    Discrete_Reconstruct (Discrete_Compare C)
    (strict_equiv_implies_fun_equiv _ _ (iso_to_from Discrete_iso))
    (strict_equiv_implies_fun_equiv _ _ (iso_from_to Discrete_iso)).

End Reconstruction.

(** ** The iso-robust restatement / ** 等方稳健重述 *)

(* Every arrow of a discrete category is invertible; no hypothesis needed. / 每一个离散范畴的箭头都是可逆的；不需要任何假设。 *)
Lemma Discrete_invertible (C : Category) (D : Discrete C)
  (x y : C) (f : x ~> y) :
  ∃ g : y ~> x, (f ∘ g ≈ id) ∧ (g ∘ f ≈ id).
Proof.
  destruct (D x y f) as [H Hf].
  exists (rew [fun z : C => y ~{C}~> z] (eq_sym H) in id).
  split; rewrite Hf.
  - apply rew_id_iso_from.
  - apply rew_id_iso_to.
Qed.

(*
 The equivalence-respecting reading of discreteness: hom-setoids are
 subsingletons and every arrow is invertible.  No object equality appears. 

 --------
 尊重等价性的离散性解读：同态集是单子集，每条箭头都是可逆的。没有出现对象相等。
*)
Definition DiscreteUpToIso (C : Category) : Type :=
  (∀ (x y : C) (f g : x ~> y), f ≈ g)
    ∧ (∀ (x y : C) (f : x ~> y), ∃ g : y ~> x, (f ∘ g ≈ id) ∧ (g ∘ f ≈ id)).

(*
 [Discrete] implies the restatement once the objects have UIP: the two
 witnesses attached to two parallel arrows are then the same proof. 

 --------
 [Discrete] 表示一旦对象具有 UIP 后的重述：连接到两条平行箭头的两个证人就是相同的证明。
*)
Theorem Discrete_DiscreteUpToIso (C : Category) (D : Discrete C)
  (uip : ∀ (x y : C) (H H' : x = y), H = H') : DiscreteUpToIso C.
Proof.
  split.
  - intros x y f g.
    destruct (D x y f) as [H Hf], (D x y g) as [H' Hg].
    rewrite Hf, Hg, (uip x y H H').
    reflexivity.
  - apply Discrete_invertible, D.
Qed.

(*
 For the constructed discrete categories the restatement is *exactly* UIP on
 the underlying type: its subsingleton clause is that statement verbatim,
 because the hom-setoid is strict equality of equality proofs.  Compare
 [DiscreteCat_Discrete], which holds with no hypothesis at all. 

 --------
 对于构造的离散范畴，重述就是在基础类型上*完全*的UIP：它的子单例条款就是逐字的该陈述，因为同构集合是等式证明的严格相等。比较 [DiscreteCat_Discrete]，它在没有任何假设的情况下成立。
*)
Theorem DiscreteUpToIso_DiscreteCat (A : Type) :
  DiscreteUpToIso (DiscreteCat A) ↔ (∀ (x y : A) (p q : x = y), p = q).
Proof.
  split.
  - intros [sub _] x y p q; exact (sub x y p q).
  - intros uip; split.
    + intros x y f g; exact (uip x y f g).
    + intros x y f.
      exists (eq_sym f).
      split; destruct f; reflexivity.
Qed.

(*
 Hence no general implication from [Discrete] to the restatement can be
 proven: it would decide UIP for every type, which Rocq's logic leaves open.
 This is the precise sense in which the restatement is *not* equivalent to
 the existing predicate. 

 --------
 因此，无法从 [Discrete] 推导出对重述的普遍结论：它将决定每种类型的 UIP，而 Rocq 的逻辑对此保持开放。这正是重述与现有谓词*不*等价的准确含义。
*)
Theorem Discrete_DiscreteUpToIso_forces_UIP
  (K : ∀ C : Category, Discrete C → DiscreteUpToIso C) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intro A.
  apply (fst (DiscreteUpToIso_DiscreteCat A)).
  apply K, DiscreteCat_Discrete.
Qed.

(* * ** The indiscrete category separates the two predicates / * ** 非离散类别区分了两个谓词 *)

(*
 One arrow between any two objects; the codiscrete/indiscrete right adjoint
 to the underlying-set functor, included here only as the separating
 witness. 

 --------
 在任意两个对象之间有一支箭头；底层集合函子（underlying-set functor）的共离散/不可离散右伴随，仅在此作为分离见证包含。
*)
(*
 The same reverse-mathematics argument for the PRIMARY hypothesis: if every
 [Discrete] category were [DiscreteRigid], UIP would hold for every type.
 The countermodel makes the premise of rigidity vacuous: objects [A],
 morphisms equality proofs, but the hom-setoid INDISCRETE, so that any two
 parallel arrows are equivalent.  Such a category is [Discrete] -- the
 morphism is its own witness -- while its rigidity is literally UIP on [A].
 Hence [DiscreteRigid] is a genuine extra hypothesis of [Discrete_iso], not
 a deficiency of its proof. 

 --------
 针对主要假设的相同逆数学论证：如果每个 [Discrete] 类别都是 [DiscreteRigid] ，那么 UIP 将适用于每种类型。反例模型使刚性前提变得无效：对象 [A] ，态射为相等证明，但同态集是离散的，因此任何两条平行箭头都是等价的。这样的类别是 [Discrete] ——其态射是其自身的见证——而其刚性在 [A] 上实际上就是 UIP。因此 [DiscreteRigid] 是 [Discrete_iso] 的一个真正的额外假设，而不是其证明的不足。
*)
Program Definition Blurry (A : Type) : Category := {|
  obj     := A;
  hom     := fun x y => x = y;
  homset  := fun x y => {| equiv := fun _ _ => True |};
  id      := fun x => eq_refl;
  compose := fun x y z (g : y = z) (f : x = y) => eq_trans f g
|}.

Lemma Blurry_Discrete (A : Type) : Discrete (Blurry A).
Proof. intros x y f. exists f. exact I. Qed.

Lemma Blurry_Rigid_is_UIP (A : Type) :
  DiscreteRigid (Blurry A) → ∀ (x y : A) (p q : x = y), p = q.
Proof. intros r x y p q. exact (r x y p q I). Qed.

Theorem Discrete_DiscreteRigid_forces_UIP
  (K : ∀ C : Category, Discrete C → DiscreteRigid C) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A. apply Blurry_Rigid_is_UIP. apply K, Blurry_Discrete.
Qed.

(*
 The binders are load-bearing, for the same reason as
 [DiscreteCat_Functor] (Instance/Discrete.v): declared bare, this
 minimized to [Indiscrete@{u} : Type@{u} → Category@{u Set Set}], pinning
 the hom and proof levels of the indiscrete category to [Set] and so
 pinning every limit taken over it.  The pin is INDEPENDENT of
 [DiscreteCat_Functor]'s — annotating that one does not touch this one,
 which is why Instance/Cat/Objects.v behaved differently
 while only one of the two donors was annotated.  (Both are annotated
 now, so both of those lines are plain [Check]s and both are accepted;
 an earlier revision of this sentence cited them,
 where they stood as [Fail Check]s before the PR “algebraic carriers
 are sets” (2026-09-17).)  The measured signature is

 Indiscrete@{o h p} : Type@{o} → Category@{o h p}
 ( * o h p |= h <= eq_ind.u0 / h <= Logic_lemmas.equality.u0
 / h <= eq_ind_r.u0 / h <= p * )

 — no literal [Set] anywhere, and [o] is now unconstrained.  [unit : Set]
 still inhabits the hom type, but cumulativity absorbs that silently: the
 constraint block records no lower bound on [h] at all. 

 --------
 这些绑定器是承重的，原因与 [DiscreteCat_Functor] (Instance/Discrete.v) 相同：声明为裸的，这被最小化为 [Indiscrete@{u} : Type@{u} → Category@{u Set Set}]，将非离散范畴的 hom 和证明级固定为 [Set]，因此固定了在其上取的每个极限。这个固定是独立于 [DiscreteCat_Functor] 的——注明一个不影响另一个，这就是为什么 Instance/Cat/Objects.v 的行为不同，而当时只有两个捐赠者中的一个被注解。（现在两者都已注解，所以这两行都是普通的 [Check] 并且都被接受；该句的早期版本引用了它们，在 PR “代数载体是集合” (2026-09-17) 之前，它们作为 [Fail Check] 出现。）测得的签名是Indiscrete@{o h p} : 类型@{o} → 范畴@{o h p}
 ( * o h p |= h <= eq_ind.u0 / h <= Logic_lemmas.equality.u0
 / h <= eq_ind_r.u0 / h <= p * )

 — 现在没有任何地方有字面意义的 [Set]，且 [o] 现在不受约束。[unit : Set] 仍然存在于同态类型中，但累积性会默默吸收它：约束块完全没有记录 [h] 的下界。
*)
Program Definition Indiscrete@{o h p} (A : Type@{o}) : Category@{o h p} := {|
  obj     := A;
  hom     := fun _ _ => unit;
  homset  := fun x y => Morphism_equality@{o h p} x y;
  id      := fun _ => tt;
  compose := fun _ _ _ _ _ => tt
|}.
(*
 All category laws are equations in [unit] and are discharged by the default
 obligation tactic. 

 --------
 所有范畴律都是 [unit] 中的方程，并且通过默认义务策略来解除。
*)

(* It satisfies the restatement for every [A]: [unit] is a subsingleton and [tt] inverts [tt]. / 它满足对每个 [A] 的重述：[unit] 是一个子单例，并且 [tt] 反转 [tt]。 *)
Lemma Indiscrete_DiscreteUpToIso (A : Type) : DiscreteUpToIso (Indiscrete A).
Proof.
  split.
  - intros x y f g; now destruct f, g.
  - intros x y f; exists tt; split; reflexivity.
Qed.

(*
 But on [bool] it is not [Discrete]: the arrow [tt : true ~> false] would
 have to produce a proof of [true = false].  So the restatement does not
 imply the existing predicate either — the two are incomparable. 

 --------
 但是在 [bool] 上，它不是 [Discrete]：箭头 [tt : true ~> false] 必须产生 [true = false] 的证明。因此，这个重述也不意味着现有的谓词——两者是不可比较的。
*)
Lemma Indiscrete_bool_Discrete_absurd : Discrete (Indiscrete bool) → False.
Proof. intro D; destruct (D true false tt) as [H _]; discriminate. Qed.
