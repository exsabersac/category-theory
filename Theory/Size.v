(**
* Size vocabulary: small, locally small, and the arrows-with-dom-cod packaging

    Mac Lane fixes ZFC plus one universe [U] and calls a set, a function, or a
    category SMALL when it lies in [U] (Categories for the Working
    Mathematician, 2nd ed., §I.6, printed pp. 22-24).  Awodey Definition 1.11
    says a category is small when its objects [C0] and its arrows [C1] are both
    sets, and Definition 1.12 calls it LOCALLY SMALL when each [Hom(X,Y)] is a
    set.  Riehl Definition 1.1.6 says the same with “a set's worth of arrows”,
    and Definition 1.1.7 the same for local smallness.

    This library takes a different foundational route, and docs/SIZE.md sets
    the two side by side in full.  The short version: there is no universe
    object, no membership, and no size axiom.  [Class Category@{o h p}]
    (Theory/Category.v) is universe-POLYMORPHIC, so every category already
    carries its own three levels, and the work Mac Lane's [U] does is done by
    the elaborator's constraint solver.  That is why self-membership is a
    universe inconsistency rather than a paradox to be excluded by axiom
    (Instance/Cat.v).

    WHAT THIS FILE ADDS, AND WHY IT IS NOT REDUNDANT.  The discipline above is
    enforced but was UNSTATABLE: before this file `Small`, `IsSmall` and
    `LocallySmall` had no declaration anywhere in the tree, so smallness could
    be neither a hypothesis nor a conclusion -- it could only be chosen at a
    definition site by instantiating universes.  Theory/Lawvere/Sets.v
    records the consequence in passing (“the library has no smallness
    machinery”).  The predicates below are that missing vocabulary.

    THE DESIGN, AND THE ONE THING THAT MAKES IT WORK.  A category is small
    RELATIVE TO A PAIR OF LEVELS when its objects and each of its hom-setoids
    are matched by copies at those levels.  All the content sits in the strict
    constraints [uo < o] and [uh < h]: without them one could discharge
    [Small C] for every [C] by handing back [obj[C]] and [hom] themselves, and
    the predicate would be vacuously true.  With them that discharge is a
    universe inconsistency -- Test/Size.v exhibits exactly that, since
    demonstrating it needs the rejection vernacular, which this file avoids so
    that the [make todo] sweep sees no new hit from here.

    OBJECTS USE [=], HOMS USE [≈].  Objects carry no setoid in this library, so
    a bijection of object types is Leibniz; that matches Instance/StrictCat.v's
    treatment.  Morphisms do carry setoids, and CLAUDE.md's standing rule is
    that [=] is never used on them, so the hom half is a SETOID ISOMORPHISM.
    This is not a stylistic choice: stating the hom round trip with [=] is also
    REJECTED, because the [eq] lemmas it drags in impose constraints
    ([h <= eq_ind.u0]) that a declared universe binder cannot mention.

    A TWO-SIDED SITUATION, RECORDED AS SUCH.  What the library PROVIDES is
    stronger than the books' convention: [Class Category]'s [homset] field
    (Theory/Category.v) gives every category hom-setoids at a fixed level
    [h], so local smallness holds by construction and a non-locally-small
    category is not expressible.  [locally_small_ambient] below records that as
    a lemma rather than as prose, which is what makes the observation checkable.
    What the library LACKED is the predicate needed to state the distinction at
    all, and that is what [LocallySmall] supplies.  Accordingly [LocallySmall]
    is stated with a NON-STRICT [uh <= h], so that the ambient instance exists;
    [Small] is stated with strict constraints, so that it has content.  Both
    readings are deliberate and neither is an oversight.

    The books are cited BY LOCATION only.  Their printed text was not consulted
    while writing this file; the locations record where each definition is
    stated, and the Coq below stands on its own.  The attributions follow issue
    jwiegley/category-theory#253, which supplies them.

--------
* 大小词汇：小、局部小，以及带 dom-cod 的箭头包装

    Mac Lane 固定 ZFC 加一个宇宙 [U]，当集合、函数或范畴落在 [U] 内时称为小
    （Categories for the Working Mathematician, 2nd ed., §I.6, printed pp. 22-24）。
    Awodey Definition 1.11 称范畴小当其对象 [C0] 与箭头 [C1] 都是集合，Definition 1.12
    称局部小当每个 [Hom(X,Y)] 是集合。Riehl Definition 1.1.6 以「一集合份量的箭头」说同样的话，
    Definition 1.1.7 对局部小同理。

    本库取不同基础路线，docs/SIZE.md 把两者完整并置。简短版：没有宇宙对象、没有成员关系、
    没有大小公理。[Class Category@{o h p}]（Theory/Category.v）是宇宙*多态*的，故每个范畴
    已携带各自三个层级，Mac Lane 的 [U] 所做的工作由 elaborator 的约束求解器完成。这正是
    自成员是宇宙不一致而非要用公理排除的悖论的原因（Instance/Cat.v）。

    本文件添加什么，以及为何不冗余。上述纪律被强制但曾*不可陈述*：此前文件树中任何地方
    都没有 `Small`、`IsSmall`、`LocallySmall` 的声明，故小性既不能作假设也不能作结论——
    只能在定义点通过实例化宇宙来选择。Theory/Lawvere/Sets.v 顺便记录后果（「库没有小性机制」）。
    下文谓词即那缺失的词汇。

    设计，以及使之成立的一件事。范畴相对一对层级是小的，当其对象与每个 hom-setoid 在那些
    层级有匹配副本。全部内容在严格约束 [uo < o] 与 [uh < h]：没有它们，对每个 [C] 都可把
    [obj[C]] 与 [hom] 自身交回以消解 [Small C]，谓词将空虚为真。有了它们，该消解是宇宙不一致——
    Test/Size.v 恰展示这一点，因演示需要拒绝方言，本文件避免之，使 [make todo] 扫描不见新命中。

    对象用 [=]，hom 用 [≈]。对象在本库无 setoid，故对象类型的双射是 Leibniz；与
    Instance/StrictCat.v 的处理一致。态射有 setoid，且 CLAUDE.md 的常设规则是从不在其上用 [=]，
    故 hom 半边是 setoid 同构。这不是风格选择：用 [=] 陈述 hom 往返也会被*拒绝*，因它拖入的
    [eq] 引理施加声明宇宙绑定无法提及的约束（[h <= eq_ind.u0]）。

    双边局面，按原样记录。库*提供*的比书中约定更强：[Class Category] 的 [homset] 字段
    （Theory/Category.v）给每个范畴固定层级 [h] 的 hom-setoid，故局部小性由构造成立，
    非局部小范畴不可表达。下文 [locally_small_ambient] 把它记为引理而非散文，使观察可检查。
    库*缺少*的是陈述该区分所需的谓词，这正是 [LocallySmall] 所提供。因此 [LocallySmall]
    以非严格 [uh <= h] 陈述，使环境实例存在；[Small] 以严格约束陈述，使之有内容。两种读法
    都是刻意的，都不是疏忽。

    书目仅按位置引用。撰写本文件时未查阅印刷正文；位置记录各定义在何处陈述，下文 Coq
    自立。归属依 issue jwiegley/category-theory#253 所供。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.One.

Generalizable All Variables.

(** ** A level-polymorphic identity type for objects / ** 一种对象的等级多态同一类型 *)

(**
Objects carry no setoid in this library, so an object bijection has to be
    stated with an identity type.  Stdlib [eq] cannot be used HERE, and the
    reason is a genuine portability constraint rather than a preference: on
    Coq 8.19 and 8.20 [eq] is pinned to a global universe, so mentioning it
    inside a definition that DECLARES its own universe binder yields
    “Universe constraints are not implied by the ones declared: o <= eq.u0”,
    which a binder has no syntax to discharge.  Rocq 9.1 made [eq] polymorphic
    and accepts the same text, so this breaks only on the older toolchains --
    exactly the kind of divergence the three-version build exists to catch.

    Two details, since both are easy to state too broadly.  First, the trigger
    is not merely declaring a universe binder: [Definition d@{u} (A : Type@{u})
    (x : A) : x = x := eq_refl] SUCCEEDS on 8.19 and 8.20.  What breaks is a
    binder carrying an explicit constraint clause -- both [@{u | }] and
    [@{u v | u <= v}] are rejected.  Second, [ObjEq] is used in the two
    [arrow_quiver_*] lemmas below as well, which carry no binder at all; it is
    used there for uniformity with the [ArrowQuiver] fields they are about, not
    from necessity.

    [ObjEq] follows the [poly_unit@{u}] idiom at Lib/Setoid.v.

--------
在这个库中，对象不携带集合结构，因此对象双射必须使用标识类型来说明。Stdlib [eq] 不能在此使用，其原因是一个真正的可移植性限制，而不是偏好问题：在 Coq 8.19 和 8.20 中，[eq] 被固定到一个全局宇宙，因此在一个声明自身宇宙绑定器的定义中引用它会产生“宇宙约束没有被声明的约束所暗含：o <= eq.u0”，而绑定器没有语法来解决这个问题。Rocq 9.1 使 [eq] 成为多态的，并接受相同的文本，所以这种问题仅在旧版本工具链中出现——这正是三版本构建存在的目的之一，用于捕捉这种类型的差异。

两个细节，因为这两点都很容易概括说明。首先，触发器不仅仅是声明一个宇宙绑定器：[Definition d@{u} (A : Type@{u}) (x : A) : x = x := eq_refl] 在 8.19 和 8.20 上是成功的。出问题的是带有显式约束条款的绑定器——[@{u | }] 和 [@{u v | u <= v}] 都被拒绝。其次，[ObjEq] 在下面的两个 [arrow_quiver_*] 引理中也有使用，这两个引理根本没有绑定器；它在这里的使用是为了与它们有关的 [ArrowQuiver] 字段保持一致性，而非出于必要性。

[ObjEq] 遵循 Lib/Setoid.v 中的 [poly_unit@{u}] 习惯用法。
*)
Inductive ObjEq@{u} {A : Type@{u}} : A → A → Type@{u} :=
  obj_refl : ∀ a : A, ObjEq a a.

Arguments obj_refl {A} a.


(** ** Local smallness / ** 局部小 *)

(**
Awodey Definition 1.12 / Riehl Definition 1.1.7: only a set's worth of
    morphisms between any two objects.  “A set's worth” is read as: matched by
    a setoid at level [uh].

    [uh <= h] is deliberately NON-STRICT, so that [locally_small_ambient] below
    can witness the predicate at a category's own hom level.  Instantiating it
    at a strictly smaller [uh] is the reading with content.

--------
Awodey 定义 1.12 / Riehl 定义 1.1.7：在任意两个对象之间只有一组的态射。“一组的”被理解为：由位于 [uh] 级别的集合带匹配。

[uh <= h] 是故意非严格的，因此下面的 [locally_small_ambient] 可以在一个范畴自身的 Hom 级别见证谓词。在严格较小的 [uh] 上实例化它是具有实际内容的理解。
*)
Class LocallySmall@{o h p uh up | h <= p, uh <= up, uh <= h}
      (C : Category@{o h p}) := {
  ls_hom     : ∀ (x y : C), Type@{uh};
  ls_setoid  : ∀ x y, Setoid@{uh up} (ls_hom x y);

  ls_to      : ∀ {x y}, ls_hom x y → (x ~> y);
  ls_from    : ∀ {x y}, (x ~> y) → ls_hom x y;

  (*
Respectfulness is stated directly rather than through [Proper]: the
     relation spans both hom types, so a [Proper] instance lands at
     max(h,uh) and cannot be a field constrained to [Type@{uh}].

--------
尊重是直接陈述的，而不是通过 [Proper]：该关系跨越两种同类类型，因此 [Proper] 实例位于 max(h,uh)，不能是受 [Type@{uh}] 约束的字段。
*)
  ls_to_resp : ∀ {x y} (u v : ls_hom x y),
                 @Setoid.equiv _ (ls_setoid x y) u v → ls_to u ≈ ls_to v;

  (*
[ls_from] must respect [≈] too.  Without this field the structure is only
     a section/retraction pair and NOT a setoid isomorphism: [ls_from] could
     send [≈]-equal morphisms to unrelated small representatives, and no such
     field is derivable from the others.  A countermodel exists -- a category
     whose hom-setoid relates everything, resized by a small setoid that
     relates nothing, satisfies every other field.

--------
[ls_from] 也必须尊重 [≈]。没有这个字段，该结构只是一个节/收缩对，而不是一个集合同构：[ls_from] 可能将 [≈] 相等的态射发送到无关的小代表，并且不能从其他字段推导出这样的字段。存在一个反例模型——一个同态集合将一切联系起来的范畴，通过一个不联系任何事物的小集合重新调整大小，满足其他所有字段。
*)
  ls_from_resp : ∀ {x y} (f g : x ~> y),
                 f ≈ g → @Setoid.equiv _ (ls_setoid x y) (ls_from f) (ls_from g);

  ls_to_from : ∀ {x y} (f : x ~> y), ls_to (ls_from f) ≈ f;
  ls_from_to : ∀ {x y} (u : ls_hom x y),
                 @Setoid.equiv _ (ls_setoid x y) (ls_from (ls_to u)) u
}.

(**
EVERY category is locally small at its own hom level, by the identity
    resizing.  This is Riehl's “each of these is locally small” (Definition
    1.1.7 and the discussion after Example 1.1.3) turned into a lemma.

    Note precisely what it does and does not say.  It is not that local
    smallness is a theorem of category theory -- it is that [Class Category]
    BUILDS IT IN, by giving [homset] at a fixed level.  So in this library the
    book's distinction between “small” and “merely locally small” collapses on
    the locally-small side: the predicate is universally satisfiable at the
    ambient level, and only acquires content strictly below it.

--------
每一个范畴在其自身的同态层次上都是局部小的，通过恒等重置。这就是Riehl的“每一个都是局部小的”（定义1.1.7以及例子1.1.3之后的讨论）转换成的引理。

要准确注意它说的和没说的内容。它并不是说局部小性是范畴论的一个定理——而是说[Class Category]通过在固定层次上提供[homset]将其内建。因此，在这个库中，书中“小的”和“仅仅局部小的”之间的区分在局部小方面消失了：该谓词在环境层次上是普遍可满足的，并且只有在其下层才具有实际意义。
*)
Definition locally_small_ambient@{o h p | h <= p} (C : Category@{o h p})
  : LocallySmall@{o h p h p} C :=
  @Build_LocallySmall@{o h p h p} C
    (fun x y => (x ~> y))
    (@homset C)
    (fun _ _ f => f)
    (fun _ _ f => f)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H)
    (fun x y f => reflexivity f)
    (fun x y u => reflexivity u).

(** ** Smallness / ** 小 *)

(**
Awodey Definition 1.11 / Riehl Definition 1.1.6: the objects and the arrows
    are both sets.  Here BOTH constraints are strict, and that is the whole
    content of the definition.

--------
Awodey 定义 1.11 / Riehl 定义 1.1.6：对象和箭头都是集合。这里两个约束都是严格的，这就是定义的全部内容。
*)
Class Small@{o h p uo uh up | h <= p, uh <= up, uo < o, uh < h}
      (C : Category@{o h p}) := {
  small_locally     :: LocallySmall@{o h p uh up} C;

  small_ob          : Type@{uo};
  small_ob_to       : small_ob → obj[C];
  small_ob_from     : obj[C] → small_ob;
  small_ob_to_from  : ∀ x, ObjEq (small_ob_to (small_ob_from x)) x;
  small_ob_from_to  : ∀ a, ObjEq (small_ob_from (small_ob_to a)) a
}.

(**
“Every small category is locally small” (Awodey, the note after Definition
    1.12; Riehl, likewise).  Here it is a projection -- which is the honest
    form, since smallness was DEFINED to include the hom condition.

--------
“每个小范畴都是局部小的”（Awodey，在定义1.12之后的注释；Riehl，同样）。这里它是一个投影——这是诚实的形式，因为小性被定义为包括Hom条件。
*)
Definition small_locally_small@{o h p uo uh up
    | h <= p, uh <= up, uo < o, uh < h}
  (C : Category@{o h p}) (S : Small@{o h p uo uh up} C)
  : LocallySmall@{o h p uh up} C := small_locally.

(**
A TYPE is small at level [w] when it is in bijection, up to [ObjEq], with
    a type at that level.  This is the object half of [Small] with the
    category dropped: the same four fields [small_ob], [small_ob_to],
    [small_ob_from], and the two round trips, stated of a bare [Type@{u}].

    WHY IT IS SEPARATE FROM [Small].  [Small] is a property of a CATEGORY and
    bundles the hom condition with the object condition; what the adjoint
    functor theorems need of a solution set is neither -- the index of a
    [SolutionSet] is a bare [Type], with no category structure on it at all
    (Adjunction/SpanningArrow.v says so of its own index).  So the
    object half is factored out here and consumed, with no hom condition
    anywhere, by Adjunction/GAFT/Resize.v.

    THE TWO BINDERS ARE THE POINT.  [w] is the level of the small carrier and
    [u] the level of the type being resized; they are UNRELATED, which is
    what makes a use of this record a resizing rather than an identity.
    Measured, [About] under [Set Printing Universes]:

      SmallType@{w u} : Type@{u} → Type@{max(w+1,u)}
      (* w u |= *)

--------
当某个类型在与该级别的类型之间存在双射（到 [ObjEq] 为止）时，它在 [w] 级别上是小的。这是 [Small] 的对象部分，去掉了范畴：相同的四个字段 [small_ob]、[small_ob_to]、[small_ob_from]，以及两个往返操作，都是针对一个裸 [Type@{u}] 来描述的。

为什么它与[Small]是分开的。[Small]是一个范畴的属性，并且将同源条件与对象条件捆绑在一起；而伴随定理所需要的解集既不是这两者——[SolutionSet]的指数只是一个纯粹的[Type]，完全没有任何范畴结构（Adjunction/SpanningArrow.v在其自身的指数中如此说明）。因此，对象部分在这里被分解并消费掉，而没有任何同源条件，由Adjunction/GAFT/Resize.v处理。

这两个绑定器是关键。[w] 是小型载体的级别，而 [u] 是正在调整大小的类型的级别；它们彼此无关，这就是使使用此记录成为调整大小而不是恒等的原因。测量时，[About] 位于 [Set Printing Universes] 之下：

SmallType@{w u} : Type@{u} → Type@{max(w+1,u)}
      (* w u |= *)                               <-- empty constraint block

    [ObjEq] (above) rather than [eq] for the round trips, for the reason the
    [ObjEq] header gives and [Small] already relies on: object equality in
    this library is a [Type]-valued identity that survives the universe
    polymorphism, and [eq] at [Type@{u}] would pin the level.

    PRIOR ART.  This is the shape the HoTT literature writes [IsSmall] or
    “essentially small” (Coq-HoTT's [IsSmall@{i j} X := { Y : Type@{i} & Y
    <~> X }], Basics/Equivalences and Universes/Smallness), with the
    equivalence replaced by an [ObjEq] round trip because this library is
    axiom-free and has no univalence.  The consequence is that [SmallType] is
    DATA, not a property: two resizings of the same type need not agree, and
    nothing here truncates.  Structure/Complete.v's SIZE NOTE, item 4, is the
    statement of why the library wants it. *)
Record SmallType@{w u} (A : Type@{u}) : Type@{max(w+1,u)} := {
  st_carrier : Type@{w};
  st_to      : st_carrier → A;
  st_from    : A → st_carrier;
  st_to_from : ∀ a : A, ObjEq@{u} (st_to (st_from a)) a;
  st_from_to : ∀ s : st_carrier, ObjEq@{w} (st_from (st_to s)) s
}.

Arguments st_carrier {A} _.
Arguments st_to {A} _ _.
Arguments st_from {A} _ _.
Arguments st_to_from {A} _ _.
Arguments st_from_to {A} _ _.

(**
A setoid whose equivalence is constantly [True]: any two elements agree.
    Used below for the one-element small hom, mirroring the device at
    Construction/Sq.v and Instance/Proset.v.  Kept [#[local]] for the
    reason Construction/Sq.v gives for its own copy: applied to a
    data-carrying type it would silently identify everything, so it must not
    leak into the library interface.

--------
一个等价总是 [True] 的集体：任何两个元素都相等。下面用于单元素小同态，类似于 Construction/Sq.v 和 Instance/Proset.v 中的装置。保留 [#[local] 的原因与 Construction/Sq.v 为其自身副本给出的理由相同：应用于携带数据的类型时，它会悄无声息地将所有东西视为相同，所以它不能泄露到库接口中。
*)
#[local] Definition True_setoid@{u p} (A : Type@{u}) : Setoid@{u p} A :=
  {| Setoid.equiv    := fun _ _ => True
   ; setoid_equiv    :=
       {| Equivalence_Reflexive  := fun _ => I
        ; Equivalence_Symmetric  := fun _ _ _ => I
        ; Equivalence_Transitive := fun _ _ _ _ _ => I |} |}.

(**
The terminal category is small: one object and one arrow, so [poly_unit] at
    the lower levels serves as the small copy.

    Every proof term is given EXPLICITLY rather than by [destruct] or [Program].
    That is not fastidiousness: the [destruct] route elaborates through
    [eq_ind], whose global universe ([eq_ind.u0]) a declared universe binder
    cannot mention, so the definition is rejected with “Universe constraints are
    not implied by the ones declared”.

    The hom half is split out with an explicit type ascription because a nested
    record literal leaves the class parameter [C] unresolved.

--------
终端范畴是小的：一个对象和一条箭头，因此在较低层中 [poly_unit] 作为小副本使用。

每个证明项都是明确给出的，而不是通过 [destruct] 或 [Program]。那并非挑剔：[destruct] 的路径会经过 [eq_ind] 展开，而 [eq_ind] 的全局宇宙（[eq_ind.u0]）是一个已声明的宇宙绑定器不能提及的，因此该定义会被拒绝并显示“宇宙约束不被已声明的约束所隐含”。

同态的一半被拆出来并进行了显式的类型指定，因为嵌套记录文本会使类参数 [C] 无法解析。
*)
(*
No explicit universe binder here, deliberately, and the hom half is INLINED
   rather than named separately.  Two distinct obstacles force this shape:

   - [_1]'s hom-setoid is [Morphism_equality], a [Program Definition] whose own
     obligations carry constraints on [eq]'s global universes ([eq_ind.u0]).  A
     declared binder cannot mention those, so declaring one makes the witness
     un-typecheckable.
   - Naming the hom half separately makes Coq solve its constraints in
     isolation, where it collapses [uh] to [h]; the result then cannot be used
     at the strict [uh < h] that [Small] demands.  Inlining lets both halves be
     solved together.

   Nothing is given up.  The STRICTNESS lives in the class, so any inhabitant
   of [Small] satisfies [uo < o] and [uh < h] by [Small]'s own constraints --
   which is exactly why this witness is evidence that those constraints are
   satisfiable rather than merely restrictive.

--------
这里没有显式的宇宙绑定器，这是故意的，并且 hom 部分是内联的，而不是单独命名的。两个不同的障碍迫使这种形状出现：

- [_1] 的同态集合是 [Morphism_equality]，一个 [Program Definition]，其自身的义务对 [eq] 的全局宇宙 ([eq_ind.u0]) 施加了约束。一个声明的绑定器不能提及这些，所以声明一个会使见证无法类型检查。
- 分开命名同态的一半会使 Coq 独立解决其约束，在那里它将 [uh] 压缩为 [h]；结果随后无法在 [Small] 所要求的严格 [uh < h] 下使用。内联则允许两半一起解决。

没有任何东西被放弃。严格性存在于类中，因此 [Small] 的任何成员都会通过 [Small] 自身的约束满足 [uo < o] 和 [uh < h] —— 这正是为什么这个见证是这些约束可满足而不仅仅是限制性的证据。
*)
Definition One_Small : Small _1 :=
  @Build_Small _1
    (@Build_LocallySmall _1
       (fun _ _ => poly_unit)
       (fun _ _ => True_setoid poly_unit)
       (fun _ _ _ => ttt)
       (fun _ _ _ => ttt)
       (fun _ _ _ _ _ => eq_refl)
       (fun _ _ _ _ _ => I)
       (fun _ _ f => match f with ttt => eq_refl end)
       (fun _ _ _ => I))
    poly_unit
    (fun _ => ttt)
    (fun _ => ttt)
    (fun x => match x with ttt => obj_refl ttt end)
    (fun a => match a with ttt => obj_refl ttt end).

(** ** Riehl's arrows-with-domain-and-codomain packaging / ** Riehl 的带有定义域和陪域的箭头打包 *)

(**
Riehl Remark 1.1.2 (used again at Definition 1.1.6) packages a category as
    a set of objects, a set of morphisms, and functions [dom], [cod], [id],
    with [dom] and [cod] retracting [id].

    The tree's [Quiver] (Construction/Free/Quiver.v) is the INDEXED
    presentation -- [edges : nodes → nodes → Type] -- in which [dom] and [cod]
    are carried by the indexing rather than by functions, and it has no
    identity selection at all, so it supplies neither half of Riehl's
    retraction.  A “reflexive quiver” appears nowhere in the tree.

    Both presentations are given below, because the difference is exactly where
    the retraction laws live.  In the UNINDEXED form they are genuine equations
    that a candidate must satisfy; in the INDEXED form they are definitional,
    since an identity edge at [x] has source and target [x] by typing.  That is
    worth having on record: it is a case where the library's formulation makes
    a book axiom disappear rather than proving it.

--------
Riehl 注释 1.1.2（在定义 1.1.6 中再次使用）将一个范畴打包为一个对象集合、一组态射，以及函数 [dom]、[cod]、[id]，其中 [dom] 和 [cod] 收缩 [id]。

树的 [Quiver]（Construction/Free/Quiver.v）是索引的
    [edges : nodes → nodes → Type]——在其中[dom]和[cod]
    由索引而非函数承载，且
    根本没有恒等选择，因此它既不提供里尔的一半
    收回。“反射箭袋”在树中没有出现。

两种表述都列在下面，因为区别正好在于撤回法则所在的位置。在非索引形式中，它们是真正的方程，一个候选对象必须满足；在索引形式中，它们是定义性的，因为在 [x] 处的恒等边根据类型规定具有源和目标 [x]。这值得记录：这是一个例子，其中库的表述使得书中的公理消失，而不是证明它。
*)

(** The unindexed packaging, as Riehl states it. / 正如Riehl所说的未索引包装。 *)
Record ArrowQuiver@{u} := {
  aq_ob      : Type@{u};
  aq_mor     : Type@{u};
  aq_dom     : aq_mor → aq_ob;
  aq_cod     : aq_mor → aq_ob;
  aq_id      : aq_ob → aq_mor;
  aq_dom_id  : ∀ x, ObjEq (aq_dom (aq_id x)) x;
  aq_cod_id  : ∀ x, ObjEq (aq_cod (aq_id x)) x
}.

(**
The total arrow collection of a category: Awodey's [C1], Riehl's “a set's
    worth of arrows”.  Note it bundles the endpoints, so its level is at least
    that of the objects -- which is why Awodey's Definition 1.11 needs BOTH
    halves and not just the hom condition.

--------
一个范畴的箭头总集合：Awodey 的 [C1]，Riehl 的“一个集合所对应的箭头”。注意它把端点捆绑在一起，所以它的层次至少与对象的层次相同——这就是为什么 Awodey 的定义 1.11 需要两部分，而不仅仅是同态条件。
*)
(**
The total arrow collection of a category: Awodey's [C1], Riehl's “a set's
    worth of arrows”.  Note it BUNDLES the endpoints, so its level is at least
    that of the objects -- which is exactly why Awodey's Definition 1.11 needs
    both halves rather than the hom condition alone.  An [ArrowQuiver] keeps
    objects and arrows in ONE universe, the way a set-theoretic presentation
    keeps them both sets; universes are left to inference here, since
    [sigT]'s projections carry global constraints ([Projections.u0]) that a
    declared binder cannot mention, and no strictness is wanted at this
    point anyway.

--------
一个范畴的箭头总集合：Awodey 的 [C1]，Riehl 的“一组箭头的集合”。注意它捆绑了端点，因此其层次至少与对象的层次一样 —— 这正是 Awodey 的定义 1.11 需要两部分而不仅仅是同态条件的原因。一个 [ArrowQuiver] 把对象和箭头保存在一个宇宙中，就像集合论表示法把它们都作为集合一样；这里的宇宙留待推断，因为 [sigT] 的投影带有全局约束（[Projections.u0]），一个声明的绑定器不能提到，并且此时也不希望有严格性。
*)
Definition TotalMor (C : Category) : Type :=
  { x : obj[C] & { y : obj[C] & x ~{C}~> y }}.

(**
A category packages as an [ArrowQuiver], and both retraction laws hold
    by [obj_refl] -- the identity arrow at [x] is stored with [x] as both of
    its endpoints, so [aq_dom] and [aq_cod] project it back definitionally.

    Proof terms are explicit rather than left to [Program]: see the note on
    [One_Small] above for why the [eq]-lemma route is not available under a
    declared universe binder.

    SCOPE.  Leaving universes to inference here has one consequence worth
    stating rather than leaving to be discovered: it forces [p] equal to [h],
    so this applies to every category whose hom-setoid proofs sit at the hom
    level -- which is every category in the tree, since inference unifies them
    at each use site -- but NOT to a hypothetical [C : Category@{o h p}] with
    strictly [h < p], which the class permits.  [locally_small_ambient] carries
    no such restriction.

--------
一个范畴被打包为 [ArrowQuiver]，并且通过 [obj_refl] 保持两个回撤定律 —— 在 [x] 的恒等箭头与 [x] 一起存储，作为它的两个端点，因此 [aq_dom] 和 [aq_cod] 定义性地将其投射回去。

证明项是明确的，而不是留给 [Program]：参见上文关于 [One_Small] 的注释，了解为什么在声明的宇宙绑定器下无法使用 [eq]-引理路径。

范围。将宇宙留给推断在这里有一个值得说明的后果，而不是留待发现：它强制 [p] 等于 [h]，因此这适用于每一个其同构集合证明位于同构级别的范畴——也就是树中每一个范畴，因为推断在每个使用点统一了它们——但不适用于一个假设的严格为 [h < p] 的 [C : Category@{o h p}]，而类允许这种情况。[locally_small_ambient] 不受这种限制。
*)
Definition ArrowQuiverOfCat (C : Category) : ArrowQuiver :=
  {| aq_ob     := obj[C]
   ; aq_mor    := TotalMor C
   ; aq_dom    := fun m => projT1 m
   ; aq_cod    := fun m => projT1 (projT2 m)
   ; aq_id     := fun x => existT _ x (existT _ x (@id C x))
   ; aq_dom_id := fun x => obj_refl x
   ; aq_cod_id := fun x => obj_refl x |}.

(**
The two retraction laws, stated separately so the file records that in this
    presentation they are DEFINITIONAL rather than assumed -- the point of
    giving both packagings.

--------
这两条收回法则是分别陈述的，以便文件记录在此陈述中它们是定义性的，而不是假定的——给出这两种表述的目的就在于此。
*)
Lemma arrow_quiver_dom_id (C : Category) (x : obj[C]) :
  ObjEq (aq_dom (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x.
Proof. exact (obj_refl x). Qed.

Lemma arrow_quiver_cod_id (C : Category) (x : obj[C]) :
  ObjEq (aq_cod (ArrowQuiverOfCat C) (aq_id (ArrowQuiverOfCat C) x)) x.
Proof. exact (obj_refl x). Qed.
