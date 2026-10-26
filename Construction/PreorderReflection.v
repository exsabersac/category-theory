(*
   * * The preorder reflection of a category

   Every category has an underlying preorder on objects: [x ≤ y] whenever
   some morphism [x ~> y] exists.  Passing to it discards the identity of the
   witnessing morphism and keeps only its existence.  The construction that
   performs that erasure while staying inside [Cat] is built here: the same
   objects, with all parallel morphisms identified.  The result is THIN -- at
   most one morphism between any two objects -- and thin categories are
   exactly preorders, as recorded at Theory/Category.v and
   Instance/Proset.v.  See https://ncatlab.org/nlab/show/thin+category.

   NOT THE POSETAL REFLECTION.  These must not be conflated, and the
   difference is exactly which data is discarded.  The nLab's posetal
   reflection (https://ncatlab.org/nlab/show/posetal+reflection) quotients
   OBJECTS by mutual relatedness -- [a ≃ b] when [a ≤ b] and [b ≤ a] -- and
   exhibits posets as reflective in preorders.  [PreorderReflect] does the
   opposite: [preorder_reflect_obj] below proves objects are untouched
   DEFINITIONALLY, and only morphisms are identified.  This construction is
   the category-level ANALOGUE of the posetal reflection, which is how
   jwiegley/category-theory#803 words it; the object-identifying construction
   is a separate obligation that remains open.

   WHY “REFLECTION” IS EARNED HERE.  Not by citation, but by the universal
   property proved below: [ThinLift] shows every functor into a thin category
   factors through [Reflect] uniquely ([ThinLift_proj], [ThinLift_unique]).
   That makes [PreorderReflect C] THE universal thin quotient of [C], rather
   than merely a quotient that happens to be thin.  The full reflective
   adjunction with the inclusion of preorders into [Cat] is a stronger
   statement and is NOT proved here (see SCOPE).

   WHY IT MATTERS HERE.  A diagram commutes exactly when it factors through
   the preorder reflection of its indexing category.  That is the packaging
   Fong and Spivak give for commutativity in Seven Sketches in
   Compositionality §3.3.4, the footnote to Definition 3.51; it is the
   reading that makes
   “commutes” a statement about the SHAPE rather than about any one figure:
   once parallel morphisms of the shape are identified, a functor out of the
   quotient cannot distinguish two parallel paths, so it cannot help but
   commute.  Theory/Diagram.v proves both directions.

   Cited by location only: the Fong-Spivak text was not consulted while
   writing this file, matching the disclosure in Theory/Diagram.v.

   HOW IT IS BUILT.  Nothing new is required.  Construction/Quotient.v already
   quotients a category by a hom-congruence -- [HomCongruence],
   [Quotient], [QuotientProj], and the universal property
   [QuotientLift] with [QuotientLift_proj] and
   [QuotientLift_unique].  The preorder reflection is that quotient at
   the TOTAL congruence, the relation relating every pair of parallel
   morphisms.  All FOUR congruence fields -- [cong_incl], [cong_sym],
   [cong_trans], [cong_comp] -- are immediate, since the relation is
   constantly [True].  (Reflexivity is not a field: it is the derived
   [cong_refl] at Construction/Quotient.v.)  Before this file the only in-tree [HomCongruence]
   instances were the PROP and coloured-PROP term congruences.

   NOT [hom_preorder].  Theory/Category.v declares
   [hom_preorder : PreOrder (@hom C)], but that is a different thing and is
   not the reflection: being a [CRelationClasses.PreOrder] on [hom] it is
   [Type]-valued, so it REMEMBERS which morphism witnesses the relation --
   exactly the information the reflection is meant to discard.  Its header
   does not use the phrase “Type-valued”; what it records is that reflexivity
   is witnessed by [id] and transitivity by composition, which is the same
   fact stated constructively.

   SCOPE.  jwiegley/category-theory#803 lists SEVEN work items.  This file
   supplies item 1 (the total hom-congruence and the quotient), plus the
   universal property below.  The remaining SIX are NOT built here and nothing
   below depends on them: the truncated object preorder
   [c ≤ c' := inhabited (c ~> c')] and its comparison with [PreorderReflect]
   (item 2); functoriality of [PreorderReflect] on [Cat] (3); the reflective
   adjunction with the inclusion of preorders (4); Exercise 3.21, the
   reflection of [FreeOnQuiver G] as a reachability preorder (5); Exercise
   3.22, the reflection of the loop category (6); and Remark 3.23's two-sided
   [HomRel] containment (7).

   NAMES.  #803's plan names the module [Construction/PreorderReflection.v]
   and the constant [PreorderReflect]; those two are taken from it so that
   issue lands here cleanly.  [TotalRel], [preorder_reflect_thin], [Reflect],
   [Thin] and [ThinLift] are this file's own coinages, not the plan's. 

   --------
   * * 一个范畴的预序反射

   每个范畴在对象上都有一个基本的预序：只要存在某个态射。通过这个过程，会舍弃见证态射的具体身份，仅保留其存在性。在此构建了一个在保持在原范畴内部的同时进行这种删除的构造：使用相同的对象，并将所有平行态射识别。结果是THIN —— 任意两个对象之间最多只有一个态射 —— 而薄范畴正好就是预序，如在 Theory/Category.v 和 Instance/Proset.v 中记录的那样。见不是序集合反射。这些不能混为一谈，区别正好在于丢弃哪些数据。nLab 的序集合反射（https://ncatlab.org/nlab/show/posetal+reflection) 通过相互关联将对象取商 -- [a ≃ b] 当 [a ≤ b] 和 [b ≤ a] -- 并将序集合作为在预序中反射的形式。[PreorderReflect] 做了相反的事情：[preorder_reflect_obj] 下面证明对象在定义上不受影响，并且只识别态射。这个构造是序集合反射的范畴级类比，这正是 jwiegley/category-theory#803 的表达；识别对象的构造是一个独立的任务，仍然没有解决。为什么这里称之为“反射”。不是通过引用，而是通过下面证明的普遍性质：[ThinLift] 显示，每一个进入薄范畴的函子都唯一地经过 [Reflect] 因式分解（[ThinLift_proj]，[ThinLift_unique]）。这使得 [PreorderReflect C] 成为 [C] 的普遍薄商，而不仅仅是恰好是薄的商。与将偏序集合包含入 [Cat] 的包含函子形成的完全反射伴随是一个更强的陈述，并且在这里未被证明（参见 SCOPE）。为什么这很重要。在这里，当一个图通过其索引类别的预序反射因子化时，该图才严格可换。也就是说，这就是 Fong 和 Spivak 在《组合性七个素描》第 3.3.4 节及定义 3.51 的脚注中给出的关于可换性的封装；这是使“可换”成为关于形状而非关于任何单一图形的陈述的理解：一旦形状的平行态射被识别出来，一个来自商的函子就无法区分两条平行路径，因此它必然可换。Theory/Diagram.v 证明了两个方向。 仅按位置引用：在编写此文件时未查阅 Fong-Spivak 文本，这与 Theory/Diagram.v 中的说明相符。如何构建。无需任何新内容。Construction/Quotient.v 已经根据一个同态合同对一个范畴进行了商化 -- [HomCongruence], [Quotient], [QuotientProj]，以及具有 [QuotientLift_proj] 和 [QuotientLift_unique] 的普遍性质 [QuotientLift]。预序反射就是在总合同（TOTAL congruence）下的那个商化，该关系将每对平行态射都关联起来。所有四个合同字段 -- [cong_incl], [cong_sym], [cong_trans], [cong_comp] -- 都是直接的，因为该关系恒为 [True]。（自反性不是一个字段：它是在 Construction/Quotient.v 中推导得到的 [cong_refl]。）在此文件之前，唯一的树内 [HomCongruence] 实例是 PROP 和带颜色的 PROP 项合同。不是 [hom_preorder]。Theory/Category.v 声明了 [hom_preorder : PreOrder (@hom C)]，但那是不同的东西，并不是反射：作为 [CRelationClasses.PreOrder] 在 [hom] 上，它是 [Type] 值的，因此它记住了哪个态射证明了该关系——正是反射要舍弃的信息。它的头部没有使用“类型值”这个短语；它记录的是自反性由 [id] 证明，传递性由复合证明，这与构造性陈述的事实相同。范围。jwiegley/category-theory#803 列出了七个工作项。此文件提供了第 1 项（全同态余类和商），以及下面的范畴论性质。剩下的六项没有在此构建，下面的内容也不依赖它们：截断对象预序 [c ≤ c' := inhabited (c ~> c')] 及其与 [PreorderReflect] 的比较（第 2 项）； [PreorderReflect] 在 [Cat] 上的函子性（第 3 项）；预序包含的反射伴随（第 4 项）；练习 3.21，将 [FreeOnQuiver G] 反射为可达性预序（第 5 项）；练习 3.22，将循环范畴反射（第 6 项）；以及备注 3.23 的双向 [HomRel] 含入（第 7 项）。名称。#803 的计划将模块命名为 [Construction/PreorderReflection.v]，并将常量命名为 [PreorderReflect]；这两个名称是取自计划的，以便问题能干净地落在这里。[TotalRel]、[preorder_reflect_thin]、[Reflect]、[Thin] 和 [ThinLift] 是该文件自己的创作，而不是计划中的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.

Generalizable All Variables.

(** ** The total hom-congruence / ** 总同余 *)

(*
   * The relation relating ALL parallel morphisms.  Note this is a relation on
   each hom, not on objects: it never relates morphisms of different type. 

   --------
   * 涉及所有平行态射的关系。请注意，这是对每个同态（hom）的关系，而不是对对象的关系：它从不关联不同类型的态射。
*)
Definition TotalRel (C : Category) : HomRel C := fun _ _ _ _ => True.

(*
   * Every congruence field is immediate: the relation is constantly [True], so
   inclusion of [≈], symmetry, transitivity, and compatibility with
   composition all hold by [I].  (Reflexivity is derived, not a field.) 

   --------
   * 每一个合同域都是即时的：该关系恒为 [True]，因此包含 [≈]、对称性、传递性以及与组合的兼容性都通过 [I] 得以成立。（自反性是推导出来的，而不是一个域。）
*)
#[export] Instance TotalRel_Congruence (C : Category) :
  @HomCongruence C (TotalRel C).
Proof. constructor; intros; exact I. Defined.

(** ** The reflection / ** 反射 *)

(*
   * Same objects as [C]; parallel morphisms all identified. 

   --------
   * 与 [C] 相同的对象；所有平行态射都已被识别。
*)
Definition PreorderReflect (C : Category) : Category :=
  Quotient C (TotalRel C).

(*
   * The defining property: the result is thin.  Thin is exactly “is a
   preorder” (Theory/Category.v), so this is the sense in which
   [PreorderReflect C] is a preorder rather than merely a category. 

   --------
   * 定义性质：结果是薄的。 薄正是“是一个预序”（Theory/Category.v），因此在这种意义上，[PreorderReflect C] 是一个预序，而不仅仅是一个范畴。
*)
Lemma preorder_reflect_thin (C : Category) (x y : PreorderReflect C)
      (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(*
   * Objects are untouched -- definitionally, not merely up to iso. 

   --------
   * 对象保持不变——从定义上讲，而不仅仅是到同构。
*)
Lemma preorder_reflect_obj (C : Category) :
  obj[PreorderReflect C] = obj[C].
Proof. reflexivity. Qed.

(*
   * The reflection map, identity on objects and on morphisms; only the
   hom-setoid coarsens. 

   --------
   * 反射映射，在对象和态射上都是恒等的；只有态射集等价关系被粗化。
*)
Definition Reflect (C : Category) : C ⟶ PreorderReflect C :=
  @QuotientProj C (TotalRel C) _.

(* * ** The universal property: the universal thin quotient / * ** 通用性质：通用薄商 *)

(*
   * A category is THIN when any two parallel morphisms agree.  By
   Theory/Category.v that is exactly “is a preorder”. 

   --------
   * 当任意两个平行态射相等时，一个范畴是稀薄的。根据 Theory/Category.v，这正是“是一个预序”的定义。
*)
Definition Thin (D : Category) : Type :=
  ∀ (x y : D) (f g : x ~> y), f ≈ g.

(*
   * [PreorderReflect C] is thin -- [preorder_reflect_thin] repackaged to the
   predicate, so it can be handed to [ThinLift]. 

   --------
   * [PreorderReflect C] 很瘦 -- [preorder_reflect_thin] 被重新打包到谓词中，因此它可以交给 [ThinLift]。
*)
Definition PreorderReflect_Thin (C : Category) : Thin (PreorderReflect C) :=
  fun _ _ _ _ => I.

Section Universal.

Context {C D : Category}.
Context (HD : Thin D).
Context (F : C ⟶ D).

(*
   * Every functor into a thin category factors through the reflection.  The
   hypothesis [QuotientLift] needs -- that [F] identifies related morphisms --
   is discharged by thinness of the target alone, with no condition on [F]. 

   --------
   * 每个进入薄范畴的范畴函子都可以通过反射因式分解。假设 [QuotientLift] 需要 -- 即 [F] 识别相关的态射 -- 这一点仅由目标范畴的薄性解决，而对 [F] 没有任何条件。
*)
Definition ThinLift : PreorderReflect C ⟶ D :=
  @QuotientLift C (TotalRel C) _ D F (fun x y f g _ => HD _ _ _ _).

(** The factorization reproduces [F] on the nose. / 分解精确再现了 [F]。 *)
Lemma ThinLift_proj {x y : C} (f : x ~> y) :
  fmap[ThinLift] (fmap[Reflect C] f) = fmap[F] f.
Proof. reflexivity. Qed.

(*
   * ...and it is the only such functor -- in a form STRONGER than the usual
   uniqueness clause, so read the hypotheses carefully.  No agreement between
   [G] and [F] after the reflection is assumed; object agreement [Hobj] alone
   (needed anyway for the statement to typecheck, since [hom_cast] transports
   along it) already pins [G] on every hom.  The proof is [apply HD] and uses
   nothing else, which is exactly the content: a thin target leaves no room
   for two functors with the same object action to differ, so a fortiori none
   for two different factorizations of [F]. 

   --------
   * ...并且它是唯一这样的函子——形式比通常的唯一性条款更强，所以请仔细阅读假设。在反射之后没有假设 [G] 与 [F] 之间的协作；对象协作 [Hobj] 本身（无论如何为了语句类型检查的需要，因为 [hom_cast] 沿它进行传输）已经确定了每个 hom 上的 [G]。证明是 [apply HD]，并且不使用其他任何东西，这正是其内容：一个稀薄的目标不会留下两种具有相同对象作用的函子不同的空间，因此更不可能存在 [F] 的两种不同分解形式。
*)
Lemma ThinLift_unique (G : PreorderReflect C ⟶ D)
      (Hobj : ∀ x : C, fobj[G] x = fobj[F] x)
      {x y : C} (f : x ~{PreorderReflect C}~> y) :
  hom_cast (Hobj x) (Hobj y) (fmap[G] f) ≈ fmap[ThinLift] f.
Proof. apply HD. Qed.

End Universal.

(*
   * So [PreorderReflect C] is THE universal thin quotient of [C], not merely a
   quotient that happens to be thin.  This is what earns the word
   “reflection” here; the full reflective adjunction with the inclusion of
   preorders into [Cat] is stronger and is item 4 of #803. 

   --------
   * 所以 [PreorderReflect C] 是 [C] 的普遍薄商，而不仅仅是恰好是薄的商。这就是这里使用“反射”一词的原因；与将序理论包含到 [Cat] 中的完全反射伴随更强，并且是 #803 的第 4 条。
*)
