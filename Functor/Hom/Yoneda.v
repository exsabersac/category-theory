Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The Yoneda lemma and the Yoneda embedding.  / * 米田引理和米田嵌入。*)

(*
nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   For a presheaf F : C^op ⟶ Sets and an object A, the Yoneda lemma is the
   bijection between natural transformations out of the representable
   [Hom ─,A] and elements of F A:

       Nat([Hom ─,A], F) ≅ F A.

   Here the left-hand side is written [Presheaves [Hom ─,A] F]: the Category
   [Presheaves] = [C^op, Sets] coerces (via [Curried_Hom]) to a functor whose
   value on the pair ([Hom ─,A], F) is the hom-setoid of natural transformations
   [Hom ─,A] ⟹ F, so [≅] is an isomorphism in Sets. The forward map [to] is
   evaluation at the identity, η ↦ η_A id_A; its inverse [from] sends y ∈ F A to
   the transformation whose component at x carries φ : x ~> A to fmap[F] φ y.
   [Covariant_Yoneda_Lemma] is the dual for a copresheaf F : C ⟶ Sets and the
   covariant representable [Hom A,─].

   WHAT THIS FILE PROVES AND WHERE NATURALITY LIVES. The two instances below
   are per-pair: for each F and each A they give an isomorphism of setoids,
   with F a section parameter and A universally quantified. They do not by
   themselves say that the family is natural in A or in F — a family of
   isomorphisms is strictly weaker than an isomorphism of functors, and this
   library carries counterexamples separating the two
   (Instance/Ab/Character/NonNatural.v, Instance/FdVect/NonNatural.v). The
   naturality clause of Mac Lane §III.2 Lemma 2, Awodey §8.3 Lemma 8.2 and
   Riehl §2.2 Theorem 2.2.4 — “natural in both A and F” — is
   Functor/Hom/Yoneda/Natural.v's [yoneda_natural], an isomorphism of
   bifunctors [C, Sets] ∏ C ⟶ Sets whose components are literally
   [Covariant_Yoneda_Lemma] below; the presheaf orientation is
   [yoneda_natural_pre] there, and [Yoneda_Lemma_derived] there records that
   [Yoneda_Lemma] is [Covariant_Yoneda_Lemma] at C^op up to conversion, the
   derivation these two separately-discharged instances do not perform. Note
   that those results are stated over a category whose object, hom and proof
   universes are identified, a restriction inherited from the two instances
   below and measured in Test/ProbeYonedaNatural.v.

   Specialising F to a representable recovers the Yoneda embedding as a fully
   faithful functor (see [Yoneda_Full] and [Yoneda_Faithful] in Functor/Hom.v):
   on hom-setoids it gives Nat([Hom ─,A], [Hom ─,B]) ≅ (A ~> B), realised below
   as [Yoneda_Embedding] and its covariant counterpart.

   The intuition: since the only thing knowable about a functor is its ability
   to map objects and morphisms, any object `F x` through which we map a
   morphism `x ~> A` to obtain an element of `F A` *must* be determined by `F A`
   obtained directly, since the functor has no way of introducing additional
   meaning.

   A benefit of the lemma is that we can displace any source object `a` (from
   an arbitrary category `C`) into an object in the category of Sets -- i.e.,
   the hom-set whose domain or codomain is `a` -- allowing us to handle it
   using the structure of sets. This has the benefit of making many proofs
   easier, which become more difficult when restricted to the fully abstract
   nature of `C`. 

--------
nLab：https://ncatlab.org/nlab/show/Yoneda+lemma
 维基百科：https://en.wikipedia.org/wiki/Yoneda_lemma

对于预束 F : C^op ⟶ 集合和对象 A，米田引理是
 可表示的自然变换之间的双射
 [Hom ─,A] 和 F A 的元素：

Nat([Hom ─,A], F) ≅ F A。

这里左边写的是[Presheaves [Hom ─,A] F]：类别
 [Presheaves] = [C^op, Sets] 强制（通过 [Curried_Hom]）到一个函子，其
 对 ([Hom ─,A], F) 的值是自然变换的 hom-setoid
 [Hom ─,A] ⟹ F，所以 [≅] 是集合中的同构。 [to] 的正向映射是
 身份评估， η ↦ η_A id_A; 其逆 [from] 将 y ∈ F A 发送至
 x 处的分量带有 φ 的变换： x ~> A 到 fmap[F] φ y。 
[Covariant_Yoneda_Lemma] 是双轴 F : C ⟶ 套件和
 协变可表示 [Hom A,─]。

该文件证明了什么以及自然存在的地方。 下面两个实例
 是每对：对于每个 F 和每个 A，它们给出 setoid 的同构，
 其中 F 是截面参数，A 是通用量化的。 他们不通过
 他们自己说这个家庭是 A 或 F 中的自然家庭——a family of
 同构比函子的同构严格弱，并且这个
 图书馆提供了将两者分开的反例
 （实例/Ab/字符/NonNatural.v、实例/FdVect/NonNatural.v）。
的
 Mac Lane §III.2 引理 2、Awodey §8.3 引理 8.2 的自然性子句和
 Riehl §2.2 定理 2.2.4 —“A 和 F 都是自然的” — 是
 Functor/Hom/Yoneda/Natural.v 的 [yoneda_natural]，同构
 bifunctors [C, Sets] ∏ C ⟶ 其组件按字面意思表示的集合
 [Covariant_Yoneda_Lemma]以下； 预束方向为
 [yoneda_natural_pre] 和 [Yoneda_Lemma_derived] 记录了
 [Yoneda_Lemma] 是 [Covariant_Yoneda_Lemma] 在 C^op 上转换，
 这两个单独放电的实例不执行推导。 注意事项
 这些结果是在一个类别中陈述的，该类别的对象、名称和证明
 宇宙被识别，从两个实例继承的限制
 如下并在 Test/ProbeYonedaNatural.v 中测量。

将 F 专门化为可表示的将 Yoneda 嵌入恢复为完全
 忠实函子（请参阅 Functor/Hom.v 中的 [Yoneda_Full] 和 [Yoneda_Faithful]）：
 在 hom-setoids 上，它给出 Nat([Hom ─,A], [Hom ─,B]) ≅ (A ~> B)，如下实现
 作为 [Yoneda_Embedding] 及其协变版本。

直觉：因为关于函子唯一可知的就是它的能力
 映射对象和态射，我们通过它映射 a 的任何对象“F x”
 态射 `x ~> A` 以获得 `FA` 的元素 *必须* 由 `FA` 确定
 直接获得，因为函子无法引入额外的
 意义。

引理的一个好处是我们可以替换任何源对象“a”（来自
 任意类别“C”）转换为集合类别中的对象 - 即，
 其域或辅域为“a”的 hom-set——允许我们处理它
 使用集合的结构。 这样做的好处是可以做很多证明
 更容易，当仅限于完全抽象时变得更困难
 ‘C’的性质。 
*)

(* Where the lemma comes from, and what follows from it

   Memoir: Yoshiki Kinoshita, categories mailing list, 23 April 1996,
           https://mta.ca/~cat-dist/catlist/1999/yoneda
   Text:   Emily Riehl, “Category Theory in Context”, Dover 2016, §2.2

   The lemma entered mathematics by conversation rather than by
   publication.  Kinoshita's memorial post records the circumstances:
   Saunders Mac Lane, anxious to learn from Nobuo Yoneda during a visit to
   Paris — dated to 1954 by Mac Lane's later account — interviewed him in
   a café at the Gare du Nord, and the interview continued on Yoneda's
   train until its departure.  Mac Lane learned the result there and later
   baptized it, publishing his own brief telling (Mac Lane, “The Yoneda
   lemma”, Mathematica Japonica 47, 1998) beside Kinoshita's obituary; the
   French nickname “le lemme de la Gare du Nord” survives (Wikipedia).
   Its first appearance in print is in Grothendieck's descent seminar
   (Grothendieck, “Technique de descente et théorèmes d'existence en
   géométrie algébriques”, Séminaire Bourbaki 1960; Riehl, §2.2, footnote
   9) — the same functor-of-points program that studies a scheme through
   the presheaf it represents, and that rests on this lemma for its
   faithfulness.

   Riehl calls the result “arguably the most important result in category
   theory”, and its weight is carried by a chain of corollaries.  Full
   faithfulness of the embedding ([Yoneda_Full] and [Yoneda_Faithful] in
   Functor/Hom.v) yields that [Hom ─,A] ≅ [Hom ─,B] exactly when A ≅ B —
   stated and proved, with the data-level bijection, as
   Functor/Hom/Yoneda/Iso.v's [iso_iff_representably_iso] and
   [representable_iso_setoid].  An object is determined, up to isomorphism, by the totality of maps
   into it — probes by the other objects of the category suffice to
   distinguish it (nLab, Corollary II).  Tai-Danae Bradley states the
   perspective as slogans: mathematical objects are completely determined
   by their relationships to other objects, so the properties of an
   object matter more than any particular presentation of it (Bradley,
   “The Yoneda Perspective”, 2017).  Two classical specializations.  At a
   one-object category, full faithfulness of the covariant embedding is
   Cayley's theorem — every group embeds into a permutation group (Riehl,
   Corollary 2.2.11) — and Construction/Cayley.v builds the Cayley
   representation of an arbitrary category on
   [Covariant_Yoneda_Embedding] below.  And every row operation defined
   uniformly on matrices with n rows is left multiplication by a fixed
   matrix, found by applying the operation to the identity matrix —
   evaluation at the identity being precisely the forward map of the
   lemma (Riehl, Corollary 2.2.10); no longer only prose: this is
   Instance/Matr/Yoneda.v's [row_operations_are_left_multiplication],
   derived from [Yoneda_Embedding] below over the matrix category of
   Instance/Matr.v.

   Within the library the lemma is the engine of representability.
   Structure/UniversalProperty.v consumes [Yoneda_Lemma] and
   Functor/Hom.v's [Yoneda_Embedding'] to identify universal properties
   with representations and to conclude that universal objects are unique
   up to unique isomorphism, a program continued for limits and universal
   arrows in Structure/UniversalProperty/Limit.v and
   Structure/UniversalProperty/Universal/Arrow.v.  The end/coend form of
   the lemma — the ninja Yoneda reductions of Theory/Coend/Yoneda.v —
   drives the Day convolution unitors of Construction/Day.v, and the
   profunctor unit laws of Construction/Profunctor/Laws.v perform the
   same co-Yoneda collapse inline.

   The computational reading is genuine, and this library carries it out.
   In programming terms the lemma says that f a ≅ ∀ r, (a → r) → f r for
   any functor f: a machine that accepts a handler a → r and uniformly
   produces an f r can only operate by holding an f a and mapping the
   handler over it, since it has no other means of manufacturing results
   (Piponi, “Reverse Engineering Machines with the Yoneda Lemma”, 2006,
   which calls the lemma “the hardest trivial thing in mathematics”).  At
   the identity functor this reads ∀ r, (a → r) → r ≅ a: a value is
   interchangeable with its continuation-passing form (Milewski, “The
   Yoneda Lemma”, 2015).  Because the handler is an accumulating
   parameter, the encoding fuses successive uses of fmap into one — the
   optimization shipped as Data.Functor.Yoneda in the kan-extensions
   package (Kmett, “Free Monads for Less, Part 2: Yoneda”, 2011) — and
   difference lists are the same idea one categorical level down, the
   Cayley representation of the list monoid (Rivas and Jaskelioff,
   “Notions of Computation as Monoids”, 2014).  Theory/Coq/Functor.v
   realizes the encoding as [Yoneda] with [Yoneda_Functor], a functor in
   its argument whether or not F is one, and Theory/Coq/Applicative.v and
   Theory/Coq/Monad.v transport the Applicative and Monad structures
   across the isomorphism Yoneda F ≅ F.  There is a coda: on the advice
   of his thesis advisor Shokiti Iyanaga, Yoneda spent much of his career
   in computing, serving on the ALGOL 68 committee and teaching
   information science at the University of Tokyo (Kinoshita, 1996) — the
   man behind the lemma worked in the field where its
   continuation-passing reading now lives. *)

#[export]
Program Instance Yoneda_Lemma `(C : Category) `(F : C^op ⟶ Sets) :
  ∀ A : C, Presheaves [Hom ─,A] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi : A ~{ C^op }~> x =>
                     @fmap (C^op) Sets F A x phi y |} |} |}
}.
Next Obligation.
  (* [transform] preserves morphism equivalences.  / [transform] 保留态射等价。*)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X.
Qed.
Next Obligation.
  (* The action of [transform] is natural.  / [transform] 的作用是自然的。*)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  (* The action of [transform] is natural (symmetric).  / [transform] 的作用是自然的（对称的）。*)
  autounfold.
  destruct F; simpl in *.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences.  / [from] 保留态射等价。*)
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category.  / [from] 的结果遵循函子类别的定律。*)
  autounfold; simpl.
  destruct F; simpl in *.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences.  / [from] 的结果保留了态射等价性。*)
  autounfold.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  rewrite naturality.
  apply transform; cat.
Qed.

#[export]
Program Instance Covariant_Yoneda_Lemma `(C : Category) `(F : C ⟶ Sets) :
  ∀ A : C, Copresheaves [Hom A,─] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi : A ~{ C }~> x =>
                     @fmap C Sets F A x phi y |} |} |}
}.
Next Obligation.
  (* [transform] preserves morphism equivalences.  / [transform] 保留态射等价。*)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X.
Qed.
Next Obligation.
  (* The action of [transform] is natural.  / [transform] 的作用是自然的。*)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  (* The action of [transform] is natural (symmetric).  / [transform] 的作用是自然的（对称的）。*)
  autounfold.
  destruct F; simpl in *.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences.  / [from] 保留态射等价。*)
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category.  / [from] 的结果遵循函子类别的定律。*)
  autounfold; simpl.
  destruct F; simpl in *.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences.  / [from] 的结果保留了态射等价性。*)
  autounfold.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  rewrite naturality.
  apply transform; cat.
Qed.

#[export]
Program Instance Yoneda_Embedding `(C : Category) :
  ∀ A B : C, Presheaves [Hom ─,A] [Hom ─,B] ≊ A ~> B.
Next Obligation. morphism. Defined.
Next Obligation.
  morphism.
  - intros.
    transform; simpl.
    + intros.
      construct.
      * exact (X ∘ X0).
      * proper.
    + simpl; cat.
    + simpl; cat.
  - proper.
Defined.
Next Obligation.
  destruct x; simpl in *.
  rewrite naturality.
  apply proper_morphism; cat.
Qed.

#[export]
Program Instance Covariant_Yoneda_Embedding `(C : Category) :
  ∀ A B : C, Copresheaves [Hom B,─] [Hom A,─] ≊ A ~> B.
Next Obligation. morphism. Defined.
Next Obligation.
  morphism.
  - intros.
    transform; simpl.
    + intros.
      construct.
      * exact (X0 ∘ X).
      * proper.
    + simpl; cat.
    + simpl; cat.
  - proper.
Defined.
Next Obligation.
  destruct x; simpl in *.
  rewrite naturality.
  apply proper_morphism; cat.
Qed.
