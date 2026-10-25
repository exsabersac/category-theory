Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(*
   * * The finite setoids inside [Sets]: a worked full-subcategory example 

   --------
   * * [Sets] 中的有限集合类：一个完整子范畴的实际示例
*)

(*
 nLab:      https://ncatlab.org/nlab/show/FinSet
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_finite_sets
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, Springer 1998, §I.3, printed pp. 14-15
 Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,
 Remark 1.5.8, printed p. 33

 Mac Lane's §I.3 example of a full subcategory is the finite sets inside
 Set, with all functions between them.  This file is that example over
 Instance/Sets.v's setoids, assembled from Construction/Subcategory.v:
 [FinSets] selects objects by a finiteness witness and retains EVERY
 morphism of [Sets] between selected objects, so its inclusion is full
 ([FinSets_Full_Functor]) as well as faithful ([FinSets_Faithful]).

 Finiteness, over setoids.  A setoid counts as finite here when some list of
 its carrier exhausts it UP TO `≈` ([FiniteSetoid] via [mem_upto]).  The
 list need not be duplicate-free and the carrier needs no decidable
 equality.  This is the reading forced by the setoid discipline: the ambient
 `≈` is what "the same element" means, so exhaustion must be stated with
 respect to it, not with respect to Coq's `=` on the carrier.

 This is deliberately the cheap witness, sufficient for a full-subcategory
 example and nothing more.  Mac Lane's §I.4 skeleton construction — the
 equivalence between finite sets and finite ordinals, catalog item
 `maclane:I.4:construction4`, filed as issue #238 — is the place where a
 canonical choice of representative for each finite cardinality belongs;
 Instance/FinSet.v already carries the skeletal side of that story.  Nothing
 here depends on either, and no skeleton is constructed below.

 What is exhibited, and what is not
 ----------------------------------

 [FinSets_Incl] is a FULLY FAITHFUL functor into [Sets] whose objects are
 finite setoids.  It is NOT claimed to be injective on objects.  An object
 of [Sub] is a setoid PAIRED WITH a chosen witness, so one setoid can be
 presented with two different enumerations and yield two objects with the
 same image under the inclusion; [FinSets_bool] and [FinSets_bool_dup]
 below do exactly that, and [FinSets_bool_same_image] records that their
 images agree on the nose.  Those two objects ARE provably distinct, and the
 first commit of this file had this backwards: it said deciding the
 question would need proof irrelevance for the [sobj] component.  Proof
 irrelevance would be needed to prove them EQUAL.  Distinctness is
 immediate, with no axiom, because [FiniteSetoid] carries its enumeration
 as DATA and the length of that enumeration separates them —
 [FinSets_bool_distinct] below.  They are nonetheless isomorphic in the
 subcategory ([FinSets_bool_iso]), which is the point: the inclusion is
 fully faithful without being injective on objects.  (Correction due to an
 audit of the first commit.)  Nothing in
 the [Subcategory] record of Construction/Subcategory.v forces [sobj] to be
 subsingleton-valued, so this is a feature of the apparatus rather than of
 finiteness.

 Terminology, accordingly: "subcategory" in this file always names the
 [Subcategory] RECORD of Construction/Subcategory.v — the selection data —
 and never asserts that [FinSets_Incl] is injective on objects.  The functor
 is described as fully faithful, which is what is proved of it.

 Non-vacuity.  Statements about an inclusion are content-free if the
 hom-setoids involved are trivial, and faithfulness in particular is an
 injectivity claim that would then say nothing.  [FinSets_two_arrows] below
 exhibits two parallel morphisms of the subcategory — the identity and the
 negation of the two-element setoid — and shows them DISTINCT in the
 subcategory's own hom-setoid.  [FinSets_negb_Monic] then puts
 Theory/Functor.v's [faithful_reflects_monic] to work on that morphism. 

 --------
 nLab:       https://ncatlab.org/nlab/show/FinSet
 维基百科:  https://en.wikipedia.org/wiki/Category_of_finite_sets
 书籍:      Mac Lane, 《工作数学家的范畴论》, 第2版, GTM 5, Springer 1998, §I.3, 印刷页 14-15
 书籍:      Riehl, 《语境中的范畴论》, Dover 2016, §1.5, 注释 1.5.8, 印刷页 33

 Mac Lane §I.3 关于满子范畴的例子是集合 Set 内的有限集，以及它们之间的所有函数。这个文件是基于 Instance/Sets.v 的集值对象（setoids），从 Construction/Subcategory.v 组装而成的这个例子：
 [FinSets]  通过有限性证明选择对象，并保留 [Sets] 中所选对象之间的每一个态射，因此它的包含（inclusion）是满的 ([FinSets_Full_Functor]) 以及忠实的 ([FinSets_Faithful])。有限性，在集合等价类上。当某个承载集合的列表能穷尽该集合到 `≈`（通过 [mem_upto] 到 [FiniteSetoid]）时，这里的集合等价类就被认为是有限的。该列表不需要无重复，并且承载集合不需要有可判定的等式。这是集合等价类规范所强制的解读：环境中的 `≈` 是“相同元素”的意义，因此穷尽必须以它为准，而不是以 Coq 在承载集合上的 `=` 为准。这是故意选择的廉价示例，足以作为一个完整子范畴的示例，仅此而已。Mac Lane 的 §I.4 骨架构造——有限集合与有限序数之间的等价关系，目录项 `maclane:I.4:construction4`，作为问题 #238 提出——是为每个有限基数选择规范代表的地方；Instance/FinSet.v 已经包含了这一故事的骨架部分。这里没有依赖于任何一个，也没有在下面构造任何骨架。

 展示了什么，以及没有展示什么
 ----------------------------------[FinSets_Incl] 是一个完全忠实的函子，其值域为 [Sets]，后者的对象是有限等价集合。并没有声称它在对象上是单射的。[Sub] 的一个对象是一个与一个选定证据配对的等价集合，因此一个等价集合可以用两种不同的枚举方式表示，并在包含函子的作用下得到两个具有相同像的对象；下面的 [FinSets_bool] 和 [FinSets_bool_dup] 就是这样做的，而 [FinSets_bool_same_image] 记录了它们的像完全一致。这两个对象是可以被证明不同的，而这个文件的首次提交恰恰反转了这一点：它说明要决定这个问题，需要 [sobj] 组件的证明无关性。证明无关性是用来证明它们相等所需要的。区分性是直接的，无需公理，因为 [FiniteSetoid] 将其枚举作为数据，并且该枚举的长度将它们区分开来——见下文 [FinSets_bool_distinct]。尽管如此，它们在子范畴 ([FinSets_bool_iso]) 中仍然是同构的，这就是重点：包含函子是完全忠实的，但在对象上并非单射。（由于第一次提交的审计而做出的更正。）Construction/Subcategory.v 的 [Subcategory] 记录中没有任何内容强制 [sobj] 具有子单值性质，因此这是装置的特性，而非有限性所决定的。术语，因此：在此文件中，“subcategory”总是指 Construction/Subcategory.v 的 [Subcategory] 记录——选择数据——并且从不断言 [FinSets_Incl] 在对象上是单射。该函子被描述为完全忠实，这是对它所证明的内容。

 非空性。如果涉及的同态集合是平凡的，那么关于包含的陈述就是没有实质内容的，尤其是忠实性是一个单射性声明，这在此情况下将毫无意义。下面的 [FinSets_two_arrows] 展示了子类的两个平行态射——恒等态射和二元素集合的取反——并在子类自身的同态集合中显示它们是不同的。然后 [FinSets_negb_Monic] 将 Theory/Functor.v 的 [faithful_reflects_monic] 应用于该态射。
*)

(** ** Finiteness of a setoid / ** 集合的有限性 *)

(*
 Membership up to the ambient `≈` rather than up to `=`; `∨` is
 Category.Lib's `sum`, so this is `Type`-valued and can be eliminated into
 `Type`. 

 --------
 成员资格高达环境的 `≈`，而不是高达 `=`；`∨` 是 Category.Lib 的 `sum`，所以这是 `Type` 值，可以被消除为 `Type`。
*)
Fixpoint mem_upto {X : SetoidObject} (a : carrier X)
         (l : list (carrier X)) : Type :=
  match l with
  | nil       => False
  | cons b l' => (a ≈ b) ∨ mem_upto a l'
  end.

(*
 A setoid is finite when some list of its carrier exhausts it up to `≈`. 

 --------
 当其承载集合的某个列表在 `≈` 范围内穷尽它时，集合等价类是有限的。
*)
Definition FiniteSetoid (X : SetoidObject) : Type :=
  { l : list (carrier X) & ∀ a : carrier X, mem_upto a l }.

(* * ** The subcategory of finite setoids / * ** 有限集合范畴的子类别 *)

(*
 [shom] ignores its morphism argument: every [Sets]-morphism between finite
 setoids is retained.  That is what makes the subcategory full, and it also
 makes the two closure conditions immediate. 

 --------
 [shom] 忽略它的态射参数：每一个 [Sets] 态射在有限集合类之间都被保留。这就是使得子范畴是满的原因，同时也使得两个闭合条件显而易见。
*)
Definition FinSets : Subcategory Sets :=
  @Build_Subcategory Sets FiniteSetoid
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition FinSetsCat : Category := Sub Sets FinSets.

Definition FinSets_Incl : FinSetsCat ⟶ Sets := Incl Sets FinSets.

(* Full as data, hence full as a functor. / 作为数据是满的，因此作为函子也是满的。 *)
Definition FinSets_Full : Subcategory.Full Sets FinSets :=
  fun _ _ _ _ _ => I.

Definition FinSets_Full_Functor : Functor.Full FinSets_Incl :=
  Full_Implies_Full_Functor Sets FinSets FinSets_Full.

(*
 Faithful by the generic argument of Construction/Subcategory.v, which is
 where the observation that it holds for every subcategory now lives. 

 --------
 由 Construction/Subcategory.v 的通用论证所证明的忠实性，其中对每个子类都成立的观察现在就存在于此。
*)
Definition FinSets_Faithful : Functor.Faithful FinSets_Incl :=
  Incl_Faithful Sets FinSets.

(*
 [shom] here does not inspect its morphism argument, so it is trivially
 closed under `≈`, and the converse bridge applies: fullness of the
 inclusion returns fullness of the data.  This instantiates the hypothesis
 that Construction/Subcategory.v has to assume, showing it is a real
 condition met by the standard shape of full subcategory and not an
 unreachable one. 

 --------
 [shom] 在这里不检查其态射参数，因此它在 `≈` 下显然是封闭的，并且适用逆向桥接：包含的充足性返回数据的充足性。这验证了 Construction/Subcategory.v 必须假设的假设，显示它是由完整子范畴的标准形态满足的真实条件，而不是一个无法达到的条件。
*)
Definition FinSets_ShomRespects : ShomRespects Sets FinSets :=
  fun _ _ _ _ _ _ _ _ => I.

Definition FinSets_Full_roundtrip : Subcategory.Full Sets FinSets :=
  Full_Functor_Implies_Full Sets FinSets
    FinSets_ShomRespects FinSets_Full_Functor.

(*
   * ** Two objects over the same setoid, and two distinct parallel arrows 

   --------
   * ** 在同一集合上的两个对象，以及两个不同的平行箭头
*)

(*
 The two-element setoid of Theory/Concrete.v is finite: `true` and `false`
 exhaust it. 

 --------
 Theory/Concrete.v 的二元集合体是有限的：`true` 和 `false` 穷举了它。
*)
Definition bool_finite : FiniteSetoid bool_setoid_object.
Proof.
  exists (cons true (cons false nil)).
  intro a; destruct a; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
Defined.

(*
 A second, deliberately redundant enumeration of the very same setoid. 

 --------
 对完全相同的集合进行第二次故意冗余的枚举。
*)
Definition bool_finite_dup : FiniteSetoid bool_setoid_object.
Proof.
  exists (cons true (cons false (cons true nil))).
  intro a; destruct a; simpl.
  - left; reflexivity.
  - right; left; reflexivity.
Defined.

Definition FinSets_bool : FinSetsCat := (bool_setoid_object; bool_finite).

Definition FinSets_bool_dup : FinSetsCat :=
  (bool_setoid_object; bool_finite_dup).

(*
 The two objects have the same image under the inclusion.  This statement is
 deliberately `=` and not `≈`: it compares OBJECTS of [Sets], for which the
 library supplies no hom-setoid to weaken to, and the two images are the same
 object literally, so [reflexivity] closes it.  The setoid discipline applies
 to morphisms, and every morphism-level claim in this file uses `≈`. 

 --------
 在包含下，这两个对象具有相同的像。这个陈述特意是 `=` 而不是 `≈`：它比较的是 [Sets] 的对象，对于这些对象，库没有提供可弱化的同态集合，而这两个像在字面上是相同的对象，所以 [reflexivity] 将其关闭。同态集合的规则适用于态射，并且该文件中的每个态射级别的声明都使用了 `≈`。
*)
Lemma FinSets_bool_same_image :
  FinSets_Incl FinSets_bool = FinSets_Incl FinSets_bool_dup.
Proof. reflexivity. Qed.

(*
 They are isomorphic in the subcategory, by the identity of [Sets] in both
 directions: the two enumerations differ, the underlying setoid does not. 

 --------
 它们在子范畴中是同构的，由  [Sets] 在两个方向上的恒等：两个枚举不同，基础集合结构不变。
*)
Program Definition FinSets_bool_iso :
  FinSets_bool ≅[FinSetsCat] FinSets_bool_dup := {|
  to   := (id; I);
  from := (id; I)
|}.

(*
 Negation, as a morphism of the subcategory: the underlying [Sets]-morphism
 paired with the trivial [shom] witness. 

 --------
 否定，作为子范畴的态射：与平凡的 [shom] 证据配对的基础 [Sets] 态射。
*)
Definition FinSets_negb : FinSets_bool ~{FinSetsCat}~> FinSets_bool :=
  (Sets_negb; I).

(*
 Non-vacuity.  [Sub]'s `≈` is `≈` of first projections, so distinctness of
 these two parallel morphisms of the subcategory reduces to distinctness of
 `id` and `negb` in [Sets] — Theory/Concrete.v's [Sets_two_arrows].  Stated
 with `→ False` because hom-equivalence here is `Type`-valued, so `¬`, which
 forces `Prop`, does not apply. 

 --------
 非空性。[Sub] 的 `≈` 是第一投影的 `≈`，因此子范畴中这两个平行态射的不同性归结为 [Sets] 中 `id` 和 `negb` 的不同性——Theory/Concrete.v 的 [Sets_two_arrows]。使用 `→ False` 表述，因为这里的同构等价是 `Type` 值的，所以 `¬`，这会强制 `Prop`，不适用。
*)
Lemma FinSets_two_arrows :
  @id FinSetsCat FinSets_bool ≈ FinSets_negb → False.
Proof.
  intro Heq.
  exact (Sets_two_arrows Heq).
Qed.

(*
 [faithful_reflects_monic] on this example.  Negation is injective, hence
 monic in [Sets] by Instance/Sets.v's [injectivity_is_monic]; the inclusion
 is faithful; so negation is monic in the subcategory as well.  The
 conclusion is not content-free: monicity cancels over every hom-setoid into
 [FinSets_bool], and at least one of them — the endo-hom-setoid, taking the
 source to be [FinSets_bool] itself — has the two distinct elements exhibited
 by [FinSets_two_arrows]. 

 --------
 在这个例子中，否定是单射，因此根据 Instance/Sets.v 的 [injectivity_is_monic]，它在 [Sets] 中是单态的；包含映射是忠实的；所以否定在子范畴中也是单态的。结论不是无内容的：单态性在每个到 [FinSets_bool] 的同态集合上可以消去，并且至少有一个 —— 将源视为 [FinSets_bool] 本身的端同态集合 —— 具有由 [FinSets_two_arrows] 表现的两个不同元素。
*)
Lemma FinSets_negb_Monic : Monic FinSets_negb.
Proof.
  apply (faithful_reflects_monic FinSets_Incl).
  apply (fst (injectivity_is_monic Sets_negb)).
  intros a b Hab; destruct a, b; simpl in *;
    solve [ reflexivity | discriminate ].
Qed.

(*
 The separating measurement promised in the header: the length of the
 chosen enumeration.  This is well-typed with no proof irrelevance, no
 UIP and no axiom — the enumeration is data, not a proof. 

 --------
 标题中承诺的分离测量：所选枚举的长度。这在类型上是正确的，不需要证明的无关性、无UIP（唯一标识原理）且不依赖公理——枚举是数据，而不是证明。
*)
Definition enum_len (s : FinSetsCat) : nat := length (projT1 (projT2 s)).

(*
 So the two objects over the same setoid are genuinely different objects,
 even though the inclusion sends them to the same object of [Sets] and
 they are isomorphic in the subcategory. 

 --------
 所以在相同的集合上，这两个对象实际上是不同的对象，尽管包含映射将它们发送到 [Sets] 的同一个对象，并且它们在子范畴中是同构的。
*)
Theorem FinSets_bool_distinct : FinSets_bool = FinSets_bool_dup → False.
Proof.
  intro Heq.
  assert (H : enum_len FinSets_bool = enum_len FinSets_bool_dup)
    by (rewrite Heq; reflexivity).
  simpl in H; discriminate.
Qed.
