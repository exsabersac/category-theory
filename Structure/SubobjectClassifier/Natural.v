Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * The subobject classifier classifies NATURALLY / * * 子对象分类器自然地进行分类 *)

(*
 nLab: https://ncatlab.org/nlab/show/subobject+classifier
 nLab: https://ncatlab.org/nlab/show/representable+functor

 A subobject classifier is usually introduced object by object: for each
 x, the subobjects of x correspond to the morphisms x ⟶ Ω.  Awodey makes
 the point (Category Theory, §5.3 Example 5.14, printed pp. 104-106) that
 the correspondence is not merely a bijection at each object but is
 NATURAL in the object, and that naturality is a strictly stronger
 statement than an object-wise bijection.  Naturality is what says that
 substitution — pulling a subobject back along a morphism — is computed
 on characteristic maps by composition.  This file states and proves that
 upgrade, for an arbitrary [SubobjectClassifier] in an arbitrary category
 with a terminal object and chosen pullbacks:

 [Sub_classifier_natural : Sub ≅[[C^op, Sets]] [Hom ─,Ω]].

 ATTRIBUTION, and what was and was not consulted.  The section-and-page
 coordinates above, and the one-line summary of what that passage
 contains, are reproduced from the catalogue entry of the issue this file
 answers (jwiegley/category-theory#311, item awodey:5.3:example14).  The
 printed text was not consulted while writing the file, so every
 statement here about its content is the issue's characterization rather
 than a reading of the book.  The mathematics stands on its own proofs.

 THE NATURALITY SQUARE, WRITTEN OUT, because a reader should not have to
 unfold four definitions to see what is being claimed.  Fix f : y ~> x in
 C — an arrow x ~> y of [C^op], which is the index category of both
 presheaves.  The square is

 Sub x  --- char --->  C(x, Ω)
 |                      |
 sub_reindex f            (─) ∘ f
 |                      |
 v                      v
 Sub y  --- char --->  C(y, Ω)

 and its commutativity is exactly

 [char_reindex] :  char (f* s)  ≈  (char s) ∘ f,

 "the characteristic map of a pulled-back subobject is the characteristic
 map composed with the substitution".  That is the whole content of the
 upgrade; everything else in this file is packaging.

 WHAT IS DELIVERED, AND AT WHICH STRENGTH.

 (1) [char_reindex] — the substitution law above, for an arbitrary
 classifier.  It is proved from the two round trips already in
 Structure/SubobjectClassifier.v ([classifier_char_roundtrip],
 [classifier_pullback_roundtrip]) together with
 Theory/Subobject/Functor.v's [sub_reindex_comp], which is itself
 the pullback pasting lemma.  So the categorical input is exactly
 "pasting two pullback squares gives a pullback square", which is
 the argument Awodey's example runs.

 (2) [classifier_char_transform] and [classifier_pullback_transform] —
 the two natural transformations, and
 [Sub_classifier_natural] — the isomorphism in the functor
 category [[C^op, Sets]].

 (3) THE UPGRADE IS AN UPGRADE, NOT A PARALLEL CONSTRUCTION, and that
 is machine-checked rather than asserted: the components of the
 natural isomorphism ARE the legs of the pre-existing per-object
 [classifier_classifies], by [eq_refl]
 ([classifier_natural_component_to], [..._from], and the two
 [..._computes] readings).  Nothing is rebuilt; what is added is
 the naturality proof the per-object statement could not carry.

 (4) [Sub_Representable] — [Sub : C^op ⟶ Sets] is a representable
 presheaf, represented by Ω.  This is the Yoneda reading of the
 same fact, and it is the reason the upgrade is worth having: a
 family of bijections is not a representation, and a natural
 family is.

 WHAT IS NOT DELIVERED, STATED PLAINLY.  This file does NOT prove that
 naturality is strictly stronger than an object-wise bijection.  That is
 a general fact about families of isomorphisms, not a fact about
 classifiers, and the tree already carries witnesses for it that are not
 reproved here: Instance/Ab/Character/NonNatural.v's [sigma_not_natural]
 and Instance/FdVect/NonNatural.v's [sigma_family_not_natural] each
 exhibit a family of isomorphisms, one at every object, whose naturality
 is refuted at a single square.  Those are cited, not restated.  Nor is
 any new classifier constructed here; the file is stated over the class
 and instantiated downstream. 

 --------
 nLab:  https://ncatlab.org/nlab/show/subobject+classifier 
 nLab:  https://ncatlab.org/nlab/show/representable+functor 

 子对象分类器通常是逐个对象引入的：对于每一个 x，x 的子对象对应于态射 x ⟶ Ω。Awodey 在《范畴论》第5.3节示例5.14（印刷页 104-106）中指出，这种对应不仅仅是每个对象处的双射，而是在对象上是自然的，并且自然性是一个比对象逐个双射更严格的陈述。自然性说明了替换——沿着态射将子对象拉回——可以通过组合在特征映射上计算。该文档陈述并证明了这种升级，对任意范畴中带终对象和选定拉回的任意 [SubobjectClassifier] 的情形适用：

 [Sub_classifier_natural : Sub ≅[[C^op, Sets] ]  [Hom ─,Ω]]。归属，以及咨询过和未咨询过的内容。上述的章节和页码坐标，以及该段落内容的一行摘要，摘自本文件所回应的议题的目录条目（jwiegley/category-theory#311，条目 awodey:5.3:example14）。撰写本文件时未参考印刷文本，因此此处关于其内容的每一陈述均为该议题的描述，而非对书籍的阅读。数学内容凭其自身证明成立。

 自然性方格，完整写出，因为读者不应需要展开四个定义才能理解所主张的内容。固定 f : y ~> x 在 C — 一条来自 [C^op] 的箭头 x ~> y，这个是两个预层的指标范畴。该方格为Sub x  --- char --->  C(x, Ω)
 |                      |
 sub_reindex f            (─) ∘ f
 |                      |
 v                      v
 Sub y  --- char --->  C(y, Ω)

 它的交换性正是

 [char_reindex]  :  char (f* s)  ≈  (char s) ∘ f,

 “一个被拉回的子对象的特征映射就是与替换组合的特征映射”。这就是升级的全部内容；该文件中的其他内容都是包装。

 提供了什么，以及以何种强度。(1)  [char_reindex] — 上述对于任意分类器的代入律。它通过 Structure/SubobjectClassifier.v 中已有的两个往返证明（[classifier_char_roundtrip], [classifier_pullback_roundtrip]），以及 Theory/Subobject/Functor.v 中的 [sub_reindex_comp]（它本身就是拉回粘合引理）证明。所以范畴论输入正好是“粘合两个拉回方格得到一个拉回方格”，这正是 Awodey 的例子所展示的论证方法。

 (2)  [classifier_char_transform] 和 [classifier_pullback_transform] — 两个自然变换，以及 [Sub_classifier_natural] — 函子范畴 [[C^op, Sets] 中的同构。(3) 升级就是升级，而不是平行构造，这一点是机器检查的，而不是断言的：自然同构的组成部分就是预先存在的每对象 [classifier_classifies] 的两个分支，由 [eq_refl] ([classifier_natural_component_to]、[..._from] 以及两个 [..._computes] 读数) 确定。没有任何重建；添加的是每对象声明无法承载的自然性证明。

 (4) [Sub_Representable] — [Sub : C^op ⟶ Sets] 是一个可表征的预层，由 Ω 表征。这是同一事实的 Yoneda 解读，也是升级值得拥有的原因：一族双射不是表征，而自然族才是。没有交付的内容，直白地说明。这份文件并不能证明自然性严格强于对象层面的双射。这是关于同构族的一般事实，而不是关于分类器的事实，且树状结构中已经有它的证明证据，这里没有重新证明：Instance/Ab/Character/NonNatural.v 的 [sigma_not_natural] 和 Instance/FdVect/NonNatural.v 的 [sigma_family_not_natural] 分别展示了一族同构，在每个对象上都有一个同构，它们的自然性在单个方形上被驳斥。这些已被引用，而非重新陈述。这里也没有构建任何新的分类器；该文件是针对该类声明的，并在下游被实例化。
*)

Section ClassifierNatural.

Context {C : Category}.
Context `{HT : @Terminal C}.
Context `{HP : @HasPullbacks C}.
Context `{HS : @SubobjectClassifier C HT}.

(* ------------------------------------------------------------------------ *)
(** ** The substitution law / ** 代换律 *)

(*
 The characteristic morphism of a subobject, with the mono and its
 monicity read off the record rather than passed separately.  This is the
 [to] leg of [classifier_classifies] as a plain function; the [eq_refl]
 below records that naming it changed nothing. 

 --------
 子对象的特征态射，其单射及其单性从记录中读取，而不是单独传递。这是 [to] 在 [classifier_classifies] 中作为普通函数的一条腿；下面的 [eq_refl] 记录了命名它并没有改变任何东西。
*)
Definition char_sub {x : C} (s : SubObj x) : x ~> Ω :=
  char (sub_mono s) (sub_is_monic s).

Example char_sub_is_classifier_to {x : C} (s : SubObj x) :
  char_sub s = to (classifier_classifies x) s := eq_refl.

(* [char_respects] is stated on the three components; a subobject is its own triple, so the passage is a [destruct]. / [char_respects] 在三个组成部分上有所说明；一个子对象就是它自己的三元组，所以这个段落是一个 [destruct]。 *)
Lemma char_sub_respects {x : C} (s s' : SubObj x) :
  s ≈ s' → char_sub s ≈ char_sub s'.
Proof. destruct s, s'; apply char_respects. Qed.

(*
 THE NATURALITY SQUARE.  Pulling a subobject back along f and then
 classifying is classifying and then precomposing with f.

 The proof is the round trip in both directions.  Reindexing truth along
 [char_sub s ∘ f] is, by the pasting lemma [sub_reindex_comp], reindexing
 along [char_sub s] and then along f; the first of those recovers s by
 [classifier_pullback_roundtrip], so the whole thing is [sub_reindex f s].
 Classifying both sides and using [classifier_char_roundtrip] on the
 right-hand one concludes. 

 --------
 自然性方形。沿着 f 拉回一个子对象，然后进行分类，相当于先进行分类再与 f 进行前作合成。

 证明是双向的循环往返。在 [char_sub s ∘ f] 上重新索引真值，根据粘贴引理 [sub_reindex_comp]，相当于先沿着 [char_sub s] 重索引，然后再沿着 f 重索引；其中第一个通过 [classifier_pullback_roundtrip] 恢复 s，所以整个过程是 [sub_reindex f s]。对两边进行分类并在右边使用 [classifier_char_roundtrip] 即可得出结论。
*)
Lemma char_reindex {x y : C} (f : y ~> x) (s : SubObj x) :
  char_sub (sub_reindex f s) ≈ char_sub s ∘ f.
Proof.
  transitivity (char_sub (sub_reindex (char_sub s ∘ f) truth_subobject)).
  - apply char_sub_respects.
    symmetry.
    transitivity (sub_reindex f (sub_reindex (char_sub s) truth_subobject)).
    + apply sub_reindex_comp.
    + apply sub_reindex_respects, classifier_pullback_roundtrip.
  - apply classifier_char_roundtrip.
Qed.

(*
 The companion square for the inverse leg: reindexing along f the
 pullback of truth along h is the pullback of truth along h ∘ f.  This is
 [sub_reindex_comp] read backwards, and it is stated separately only
 because the transformation below needs it in this orientation. 

 --------
 逆边的伴随方块：沿 f 对真理的回拉是沿 h 的回拉的复合 h ∘ f。这是 [sub_reindex_comp] 反向读，并且单独陈述它只是因为下面的变换需要它以这种方向。
*)
Lemma reindex_char {x y : C} (f : y ~> x) (h : x ~> Ω) :
  sub_reindex f (sub_reindex h truth_subobject)
    ≈ sub_reindex (h ∘ f) truth_subobject.
Proof. symmetry; apply sub_reindex_comp. Qed.

(*
 TWO MORE ORIENTATIONS, STATED AS LEMMAS FOR A MECHANICAL REASON worth
 recording once here rather than at each use.  By the time a [Program]
 obligation of the isomorphism below is reached, its [simpl] has unfolded
 the subobject equivalence into the underlying sigma, so the [symmetry]
 and [transitivity] TACTICS have no relation left to turn — they report
 "Cannot find a relation to rewrite".  Stated as lemmas, where the goal
 is still the folded [≈], both go through in one line, and the
 obligations then close by [apply], which converts. 

 --------
 另外两个方向，作为引理陈述出于机械原因值得在此记录一次，而不是在每次使用时记录。当达到下面同构的 [Program] 义务时，其 [simpl] 已经将子对象等价展开到基础 sigma，因此 [symmetry] 和 [transitivity] 策略没有剩余的关系可转换——它们会报告“找不到可重写的关系”。作为引理陈述时，当目标仍然是折叠的 [≈] 时，它们都可以一行完成，并且义务随后通过 [apply] 关闭，该操作会进行转换。
*)

Lemma sub_reindex_id_sym {x : C} (s : SubObj x) : s ≈ sub_reindex id s.
Proof. symmetry; apply sub_reindex_id. Qed.

Lemma classifier_pullback_roundtrip_id {x : C} (s : SubObj x) :
  sub_reindex (char_sub s) truth_subobject ≈ sub_reindex id s.
Proof.
  transitivity s.
  - apply classifier_pullback_roundtrip.
  - apply sub_reindex_id_sym.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The two natural transformations / * ** 这两个自然变换 *)

(*
 Both components are taken verbatim from [classifier_classifies], so what
 the two definitions add is precisely the naturality field. 

 --------
 这两个组件都是从 [classifier_classifies] 原文逐字取来的，因此这两个定义所增加的正是自然性字段。
*)

(*
 The [@]-spellings below are forced and worth a note: [classifier_classifies]
 takes its category as an IMPLICIT argument inferred from the type of its
 object, and the objects here arrive as [obj[C^op]].  Left to itself the
 elaborator instantiates the donor at [C^op] and then cannot match
 [@SubObj (C^op) x] against [carrier (fobj[Sub] x)].  Pinning C is the
 whole fix; nothing about the mathematics changes. 

 --------
 下面的 [@] 拼写是强制性的，值得注意：[classifier_classifies] 将其类别作为从其对象类型推断出的隐式参数，这里的对象是以 [obj[C^op] 形式出现的。单靠自己，展开器会在 [C^op] 处实例化捐赠者，然后无法将 [@SubObj (C^op) x] 与 [carrier (fobj[Sub] x)] 匹配。固定 C 是整个解决办法；数学本身没有任何变化。
*)

Program Definition classifier_char_transform :
  @Transform (C^op) Sets (@Sub C HP) (@Curried_CoHom C Ω) := {|
  transform := fun x : C => to (@classifier_classifies C HT HP HS x)
|}.
Next Obligation. simpl; intros; symmetry; apply (@char_reindex x y f). Qed.
Next Obligation. simpl; intros; apply (@char_reindex x y f). Qed.

Program Definition classifier_pullback_transform :
  @Transform (C^op) Sets (@Curried_CoHom C Ω) (@Sub C HP) := {|
  transform := fun x : C => from (@classifier_classifies C HT HP HS x)
|}.
Next Obligation. simpl; intros; apply (@reindex_char x y f). Qed.
(* The symmetric orientation, applied in [sub_reindex_comp]'s own direction for the reason given above. / 对称取向，按照上述原因应用于[sub_reindex_comp]自身的方向。 *)
Next Obligation.
  simpl; intros; rename x0 into h.
  exact (sub_reindex_comp h f truth_subobject).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Awodey's clause: the correspondence is natural / * ** Awodey的条款：对应关系是自然的 *)

Program Definition Sub_classifier_natural :
  @Isomorphism ([(C^op), Sets]) (@Sub C HP) (@Curried_CoHom C Ω) := {|
  to   := classifier_char_transform ;
  from := classifier_pullback_transform
|}.
Next Obligation.
  simpl; intros.
  transitivity x0.
  - apply classifier_char_roundtrip.
  - symmetry; apply id_right.
Qed.
Next Obligation. simpl; intros; apply classifier_pullback_roundtrip_id. Qed.

(*
 THE UPGRADE IS THE PRE-EXISTING BIJECTION, machine-checked.  Both legs
 are the corresponding legs of [classifier_classifies] at Leibniz [=] —
 the convertibility exception, flagged as such — so no reader has to take
 on trust that this is the same correspondence rather than a second one
 that happens to agree. 

 --------
 升级是预先存在的双射，经过机器验证。两条腿都是Leibniz [=]中[classifier_classifies]的对应腿——可转换性例外，被标记为如此——因此没有读者必须盲目信任这是相同的对应关系，而不是恰好一致的第二个对应关系。
*)
Example classifier_natural_component_to (x : C) :
  transform (to Sub_classifier_natural) x = to (classifier_classifies x)
  := eq_refl.

Example classifier_natural_component_from (x : C) :
  transform (from Sub_classifier_natural) x = from (classifier_classifies x)
  := eq_refl.

Example classifier_natural_to_computes (x : C) (s : SubObj x) :
  transform (to Sub_classifier_natural) x s = char_sub s := eq_refl.

Example classifier_natural_from_computes (x : C) (h : x ~> Ω) :
  transform (from Sub_classifier_natural) x h
    = sub_reindex h truth_subobject := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The Yoneda reading / ** 读Yoneda *)

(*
 Naturality is exactly what turns the family of bijections into a
 representation, so the upgrade has an immediate payoff: [Sub] is a
 representable presheaf and Ω is a representing object.  [Representable]
 is Functor/Representable.v's class, whose [represented] field is a
 natural isomorphism [Hom(A, ─) ≅ F] — read here at [C^op], where
 [Hom ─,Ω] is that hom-functor. 

 --------
 自然性恰恰是将一族双射变成表示的原因，因此这一升级立即有了回报：[Sub] 是一个可表示的预层对象，而 Ω 是一个表示对象。[Representable] 是 Functor/Representable.v 的类，其 [represented] 字段是一个自然同构 [Hom(A, ─) ≅ F]——在此处 [C^op] 阅读，其中 [Hom ─,Ω] 是那个 Hom 函子。
*)
(*
 [Representable]'s [represented] field is spelled with the COVARIANT
 [Curried_Hom] of the index category, here [@Curried_Hom (C^op) Ω]; the
 contravariant spelling used above is that same term by [Definition]
 ([Curried_CoHom C := Curried_Hom C^op]), recorded here by [eq_refl].
 The isomorphism is nevertheless built by [exact] rather than supplied as
 a record field, because the elaborator does not unfold [Curried_CoHom]
 while unifying a field's expected type. 

 --------
 [Representable] 的 [represented] 字段是用索引范畴的协变 [Curried_Hom] 拼写的，这里是 [@Curried_Hom (C^op) Ω]；上面使用的逆变拼写是通过 [Definition] 的相同项（[Curried_CoHom C := Curried_Hom C^op]），在这里由 [eq_refl] 记录。然而，该同构仍由 [exact] 构建，而不是作为记录字段提供，因为在统一字段的期望类型时，阐释器不会展开 [Curried_CoHom]。
*)
Example CoHom_is_Hom_op : @Curried_CoHom C Ω = @Curried_Hom (C^op) Ω := eq_refl.

Definition Sub_Representable : Representable (@Sub C HP) :=
  @Build_Representable (C^op) (@Sub C HP) (@Ω C HT HS)
    (iso_sym Sub_classifier_natural).

Example Sub_repr_obj :
  @repr_obj (C^op) (@Sub C HP) Sub_Representable = @Ω C HT HS := eq_refl.

End ClassifierNatural.
