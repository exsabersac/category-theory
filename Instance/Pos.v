(*
   * * Pos, the category of posets and monotone maps

   Awodey §1.4 (Categories of structured sets): posets with monotone maps
   form a category, the identity being monotone and monotone maps being
   closed under composition.  The book is cited BY LOCATION only; its printed
   text was not consulted while writing this file, and the locations follow
   issue jwiegley/category-theory#641.

   TWO DIFFERENT THINGS CALLED "POSET AS A CATEGORY", and this file is the
   second.  Instance/Poset.v turns ONE poset into a thin category, whose
   objects are the elements and whose homs are the order relation.  This file
   builds the category whose OBJECTS ARE POSETS and whose morphisms are the
   monotone maps between them -- the structured-sets reading, in the same
   spirit as Instance/CMon.v's [CMon].  Neither subsumes the other, and #641
   is explicit that it wants this one.

   WHY Instance/Poset.v CANNOT BE REUSED.  Its [Poset] (shifted by
   this commit's own two-line edit to that file's header) reads
   [Definition Poset ... := Proset P], DISCARDING the antisymmetry argument,
   which never appears in the body.  So a [Poset] VALUE is literally a
   [Proset] value: antisymmetry is not recoverable from it, and a category of
   posets cannot be carved out of [Cat] by selecting such values.  The
   structure has to be bundled, which is what [PosetObject] does.

   A FIELD Instance/Poset.v DOES NOT HAVE: [pos_le_respects], requiring the
   order to be compatible with the carrier's own [≈].  State its status
   accurately: it is an OBJECT WELL-FORMEDNESS condition, not a lemma anything
   below consumes.  Composition of monotone maps is proved from
   [SetoidMorphism]'s [proper_morphism] alone, and the file still compiles
   with [pos_le_respects] deleted.  It is kept because an order that
   distinguished [≈]-equal elements would not deserve the name, and because
   Instance/CMon.v carries [cmon_plus_respects] in exactly this slot -- not
   because any proof here needs it.

   Antisymmetry is likewise stated at the SETOID level
   ([pos_antisym : le x y -> le y x -> x ≈ y]) rather than with Leibniz [eq];
   that is the honest reading of "partial order" over setoid carriers.  It is
   what makes this the category of POSETS -- [Pos] compiles as a category
   without it -- and it is a disclosed deviation from Awodey's set-level
   statement.

   SCOPE.  #641's work item 2 offers an "alternative": realize [Pos] as a full
   subcategory of [Cat] on "the skeletal thin categories [Poset P]".  That is
   NOT taken, and the honest reason is the one the issue itself gives -- it
   calls the direct construction "likely simpler and the recommended
   principal artifact".

   Be precise about what is and is not an obstacle here, because it is easy to
   overstate.  The subcategory ITSELF is constructible in a few lines:
   Construction/Subcategory.v's [sobj : C -> Type] takes an arbitrary
   [Type]-valued predicate, so "thin and skeletal" can be selected directly
   with no equality on [Category] values anywhere.  Nor does "skeletal thin"
   misdescribe its family: skeletality is exactly what antisymmetry buys (as
   Instance/Poset.v says), and it strictly excludes preorders -- the
   two-element indiscrete preorder is thin and NOT skeletal.

   What is genuinely deferred is the AGREEMENT: showing the subcategory
   presentation matches [Pos] means recovering the carrier setoid and the
   order from a skeletal thin category, which is real work and is not
   attempted here.  ([thin] and [skeletal] also have no in-tree predicate
   today, but that is a "nobody wrote it yet" fact, not a viability
   argument.)

   A comparison in the other direction is cheap and IS provided:
   [PosetAsCategory] sends a poset to its thin category and
   [MonotoneAsFunctor] sends a monotone map to the induced functor, which is
   the honest formal link between the two readings. 

   --------
   * * Pos，偏序集与单调映射的范畴

   Awodey §1.4（结构化集合的范畴）：具有单调映射的偏序集构成一个范畴，恒等映射是单调的，并且单调映射在复合下是封闭的。该书仅按位置引用；在编写此文件时未查阅其印刷文本，引用的位置遵循问题 jwiegley/category-theory#641。有两种不同的东西都称为“作为范畴的偏序集”，这个文件是第二种。Instance/Poset.v 将一个偏序集变成一个稀薄范畴，其对象是元素，其态射是序关系。这个文件构建了一个范畴，其对象是偏序集，其态射是它们之间的单调映射——结构化集合的视角，同 Instance/CMon.v 中 [CMon] 的精神。两者并不包含对方，并且 #641 明确表示需要这个。为什么 Instance/Poset.v 不能被重用。它的 [Poset]（被这个提交自己对该文件头部的两行编辑移动）变为 [Definition Poset ... := Proset P]，舍弃了反对称性论证，而该论证从未出现在正文中。所以一个 [Poset] 值字面上就是一个 [Proset] 值：无法从中恢复反对称性，并且无法通过选择此类值从 [Cat] 中划分出一个偏序集的范畴。该结构必须被打包，这就是 [PosetObject] 所做的事情。A FIELD 实例/Poset.v 没有:  [pos_le_respects] ，需要顺序与载体自身的 [≈] 兼容。准确地陈述其状态：它是一个对象良构性条件，而不是下面任何内容使用的引理。单调映射的组合仅从 [SetoidMorphism] 的 [proper_morphism] 中证明，而且即使删除 [pos_le_respects] 文件仍能编译。保留它是因为一个区分 [≈] 相等元素的顺序不配称这个名字，并且因为 Instance/CMon.v 在正是这个位置上携带 [cmon_plus_respects] ——而不是因为这里的任何证明需要它。反对称性同样在集合等价类（SETOID）层面陈述（[pos_antisym : le x y -> le y x -> x ≈ y]），而不是用莱布尼茨（[eq]）；也就是说，这是对集合等价类载体上“偏序”的诚实解读。这也是使其成为偏序集合（POSETS）范畴的原因——[Pos] 在没有它的情况下可以编译为范畴——并且这是对 Awodey 集合层次陈述的一个披露的偏离。

   范围。#641 的工作项 2 提供了一个“替代方案”：将 [Pos] 实现为 [Cat] 的一个完全子范畴，作用于“骨架薄范畴 [Poset P]”。这一方案没有被采纳，而其诚实的理由就是该问题本身给出的理由——它称直接构造“可能更简单，并且是推荐的主要成果”。要精确说明这里什么是障碍，什么不是，因为很容易夸大。子类别本身可以用几行代码构造：Construction/Subcategory.v 的 [sobj : C -> Type] 接受任意 [Type] 值的谓词，因此“薄且骨架状”可以直接选择，而不需要在任何地方对 [Category] 值使用等式。‘骨架状薄’也没有误描其族：骨架性正是反对称性所带来的（如 Instance/Poset.v 所述），并且它严格排除了前序——两个元素的不可分前序是薄的，但不是骨架状。真正被推迟的是协议：显示子类别的表示匹配 [Pos] 意味着从一个骨架稀疏类别中恢复载体集合和顺序，这是实际工作，这里并未尝试。（[thin] 和 [skeletal] 今天也没有树内谓词，但这是“还没人写它”的事实，而不是可行性论证。）

   反方向的比较是简单的，并且提供了：[PosetAsCategory] 将一个偏序集发送到其稀疏类别，[MonotoneAsFunctor] 将一个单调映射发送到诱导函子，这是真实形式上两种理解之间的联系。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.

Generalizable All Variables.

(** ** Objects *)

(*
   * A poset over a setoid carrier: a relation that respects [≈], is reflexive
   and transitive, and is antisymmetric UP TO [≈]. 

   --------
   * 集合载体上的偏序集：一种关系，它遵循 [≈]，是自反的和传递的，并且在 [≈] 下是反对称的。
*)
Record PosetObject := {
  pos_setoid :> SetoidObject;

  pos_le : carrier pos_setoid → carrier pos_setoid → Prop;

  pos_le_respects : Proper (equiv ==> equiv ==> iff) pos_le;

  pos_refl    : ∀ x, pos_le x x;
  pos_trans   : ∀ x y z, pos_le x y → pos_le y z → pos_le x z;
  pos_antisym : ∀ x y, pos_le x y → pos_le y x → x ≈ y
}.

#[export] Existing Instance pos_le_respects.

(** ** Morphisms / **态射 *)

(*
   * A monotone map: a setoid morphism preserving the order.  Respect for [≈]
   comes from [SetoidMorphism]; monotonicity is the added field. 

   --------
   * 单调映射：保持顺序的集合模态态射。对 [≈] 的尊重来自 [SetoidMorphism]；单调性是额外的字段。
*)
Record MonoHom (P Q : PosetObject) := {
  mono_fn :> SetoidMorphism (pos_setoid P) (pos_setoid Q);
  mono_le : ∀ x y, pos_le P x y → pos_le Q (mono_fn x) (mono_fn y)
}.

Arguments mono_fn {P Q} _.
Arguments mono_le {P Q} _ _ _ _.

#[local] Obligation Tactic := idtac.

(*
   * Monotone maps are compared pointwise up to the codomain's [≈], as in
   Instance/CMon.v and Instance/Sets.v -- never by Leibniz equality. 

   --------
   * 单调映射在值域的 [≈] 下逐点比较，如 Instance/CMon.v 和 Instance/Sets.v 中所示——从不使用 Leibniz 相等比较。
*)
#[export]
Program Instance MonoHom_Setoid {P Q : PosetObject} : Setoid (MonoHom P Q) := {|
  equiv := fun f g => ∀ a, mono_fn f a ≈ mono_fn g a
|}.
Next Obligation.
  intros P Q. constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (mono_fn g a); [apply Hfg|apply Hgh].
Qed.

(*
   * Awodey's two closure facts: the identity is monotone, and composites of
   monotone maps are monotone.  Both are the [Next Obligation]s below, so they
   are proved rather than assumed. 

   --------
   * Awodey 关于闭包的两个事实：恒等映射是单调的，单调映射的复合也是单调的。两者都是下面的 [Next Obligation]，因此它们是被证明的，而不是被假设的。
*)
Program Definition mono_hom_id {P : PosetObject} : MonoHom P P := {|
  mono_fn := setoid_morphism_id
|}.
Next Obligation. intros P x y H; exact H. Qed.

Program Definition mono_hom_compose {P Q R : PosetObject}
        (g : MonoHom Q R) (f : MonoHom P Q) : MonoHom P R := {|
  mono_fn := setoid_morphism_compose (mono_fn g) (mono_fn f)
|}.
Next Obligation.
  intros P Q R g f x y H; simpl.
  apply (mono_le g), (mono_le f); exact H.
Qed.

Program Instance mono_hom_compose_respects {P Q R : PosetObject} :
  Proper (equiv ==> equiv ==> equiv) (@mono_hom_compose P Q R).
Next Obligation.
  intros P Q R g g' Hg f f' Hf a; simpl.
  transitivity (mono_fn g (mono_fn f' a)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category / ** 类别 *)

Program Definition Pos : Category := {|
  obj     := PosetObject;
  hom     := MonoHom;
  homset  := @MonoHom_Setoid;
  id      := @mono_hom_id;
  compose := @mono_hom_compose;
  compose_respects := @mono_hom_compose_respects
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(** The underlying-set functor, forgetting the order. / 基础集合函子，忽略顺序。 *)
Program Definition Pos_Forget : Pos ⟶ Sets := {|
  fobj := fun P => pos_setoid P;
  fmap := fun _ _ f => mono_fn f
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

(* * ** The link between the two readings / * ** 两次读数之间的联系 *)

(*
   * Every poset yields a thin category -- Instance/Proset.v's construction
   applied to its order.  This is the formal bridge between "a poset viewed as
   a category" and "the category of posets", and it is what #641's work item 2
   was reaching for; taken in this direction it needs no equality on
   [Category] values and no [thin]/[skeletal] vocabulary. 

   --------
   * 每个偏序集都会产生一个薄范畴——Instance/Proset.v 的构造应用到其序上。这是“将偏序集视为范畴”和“偏序集的范畴”之间的正式桥梁，这也是 #641 的工作项 2 所涉及的；沿着这个方向不需要对 [Category] 值进行相等性，也不需要 [thin] / [skeletal] 词汇。
*)
(*
 [RelationClasses.PreOrder] qualified explicitly: unqualified [PreOrder]
 resolves to the [crelation] version from Category.Lib, while [Proset] wants
 the stdlib [Prop]-valued one.  Importing Coq.Classes.Equivalence to
 disambiguate is NOT an option -- it shadows the library's own [equiv]. 

 --------
 [RelationClasses.PreOrder] 明确限定：未限定的 [PreOrder] 解析为 Category.Lib 的 [crelation] 版本，而 [Proset] 想要 stdlib 的 [Prop] 值版本。导入 Coq.Classes.Equivalence 来消除歧义不是一个选项——它会遮蔽库自身的 [equiv] 。
*)
Definition pos_preorder (P : PosetObject)
  : RelationClasses.PreOrder (pos_le P).
Proof.
  constructor.
  - exact (pos_refl P).
  - intros x y z f g; exact (pos_trans P x y z f g).
Defined.

Definition PosetAsCategory (P : PosetObject) : Category :=
  Proset (pos_preorder P).

(*
   * A monotone map induces a functor between the thin categories: on objects it
   is the map, on morphisms it is monotonicity, and every law is an equation
   between parallel morphisms in a thin target, hence free. 

   --------
   * 单调映射在薄范畴之间引入了一个函子：在对象上它就是映射，在态射上它表现为单调性，并且每条定律都是薄目标中平行态射之间的方程，因此是自由的。
*)
Program Definition MonotoneAsFunctor {P Q : PosetObject} (f : MonoHom P Q)
  : PosetAsCategory P ⟶ PosetAsCategory Q := {|
  fobj := fun x => mono_fn f x;
  fmap := fun x y h => mono_le f x y h
|}.
(*
 The file sets [Obligation Tactic := idtac] above, so these are discharged
 explicitly rather than silently.  All three are equations between parallel
 morphisms in a thin target, hence [I]. 

 --------
 该文件在上方设置了 [Obligation Tactic := idtac]，因此这些是被显式释放的，而不是默默释放的。所有三个都是薄目标中平行态射之间的方程，因此 [I]。
*)
Next Obligation. intros P Q f x y g h Hgh; exact I. Qed.
Next Obligation. intros P Q f x; exact I. Qed.
Next Obligation. intros P Q f x y z g h; exact I. Qed.

(** Sanity: the induced functor's object action IS the underlying map. / 理智：所诱导的函子在对象上的作用就是底层映射。 *)
Example monotone_functor_fobj {P Q : PosetObject} (f : MonoHom P Q)
  (x : carrier (pos_setoid P)) :
  fobj[MonotoneAsFunctor f] x = mono_fn f x := eq_refl.
