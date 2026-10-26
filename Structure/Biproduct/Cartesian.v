Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* * * Biproducts give both a cartesian and a cocartesian structure / * * 双积既提供笛卡尔结构又提供余笛卡尔结构 *)

(*
 nLab:      https://ncatlab.org/nlab/show/biproduct
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct
 Book:      Mac Lane, “Categories for the Working Mathematician”
 (2nd ed.), §III.3, book p. 63 (maclane:III.3:remark1)

 Mac Lane's §III.3 roster of concrete coproducts opens with the direct
 sum: in Ab, in R-Mod, and (the semiadditive phenomenon in its purest
 form) in the category of commutative monoids, the coproduct of two
 objects is carried by the SAME object as their product.  This file is
 the piece of vocabulary that observation needs and that the tree did
 not have.

 [Structure/Biproduct.v] already packages “x ⊕ y is at once a product
 and a coproduct” as a record, with both universal properties stated in
 the ∃!-form: [bi_is_product] and [bi_is_coproduct].  What it does not
 do is hand the result back in the vocabulary the rest of the library
 speaks.  Products and coproducts are consumed through
 [Structure/Cartesian.v]'s [Cartesian] class and
 [Structure/Cocartesian.v]'s [Cocartesian] notation — [x × y], [f △ g],
 [exl]/[exr]; [x + y], [f ▽ g], [inl]/[inr] — and neither was reachable
 from a biproduct.  The two definitions below close that gap once and
 for all:

 [biproduct_Cartesian]   : HasBiproducts C → @Cartesian C
 [biproduct_Cocartesian] : HasBiproducts C → @Cocartesian C

 Both are pure repackagings.  [bi_pair]/[bi_copair] supply the two
 mediators, [bi_pair_respects]/[bi_copair_respects] the two
 respectfulness fields, and the single ∃! clause of the biproduct record
 supplies both halves of [ump_products] — its existence half gives the
 two computation rules and its uniqueness half gives the converse.  No
 new mathematical content is introduced; what is introduced is a name.

 WHAT IS PROVED, AND AT WHAT STRENGTH.  The three identifications below
 the definitions hold at LEIBNIZ EQUALITY by [eq_refl], not merely up to
 [≈] or up to isomorphism:

 [biproduct_product_obj]   : x × y IS [biproduct_obj (biproduct x y)]
 [biproduct_coprod_obj]    : x + y IS the same object
 [biproduct_prod_is_coprod]: x × y IS x + y

 The last is the sentence “in a category with biproducts the binary
 product and the binary coproduct are the same object” as a machine
 checked conversion rather than as prose or as a constructed
 isomorphism.  The mediators and the injections likewise return on the
 nose ([biproduct_fork_is_pair], [biproduct_merge_is_copair],
 [biproduct_exl_is_bi_exl] and its three siblings), so a consumer may
 move between the two vocabularies by conversion alone.

 THE ROUND TRIP AGAINST Structure/Semiadditive.v.  The converse passage
 already existed: [cartesian_biproduct] and [cartesian_has_biproducts]
 (Structure/Semiadditive.v) turn a preadditive category with
 binary products into one with biproducts.  Composing it with this
 file's [biproduct_Cartesian] returns the original biproduct OBJECT by
 [eq_refl] ([biproduct_roundtrip_obj]) and the original projections by
 [eq_refl] too ([biproduct_roundtrip_exl], [biproduct_roundtrip_exr]).
 It does NOT return the original record: the INJECTIONS are rebuilt as
 the forks [id △ 0] and [0 △ id], which are only [≈]-equal to the
 originals (proved, as [biproduct_roundtrip_inl] and
 [biproduct_roundtrip_inr]), and the law and universal-property fields
 are rebuilt from scratch.  Both strict failures are pinned as
 conversion negatives in Test/ProbeCoproduct.v rather than left as
 assertions.

 AN ENGINEERING FINDING, AND WHY NEITHER DEFINITION IS AN [Instance].
 Registering [biproduct_Cartesian] for typeclass resolution would close
 a resolution cycle with Structure/Semiadditive.v's converse:
 [Cartesian C] would be solved from [HasBiproducts C], which
 [cartesian_has_biproducts] solves from [Cartesian C] and
 [Preadditive C].  Both are plain [Definition]s here and there for that
 reason, and the concrete categories downstream register their own
 [Cartesian]/[Cocartesian] instances directly, so resolution never sees
 the generic bridge at all.

 UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  Both definitions read
 [biproduct_Cartesian@{u u0} : ∀ {C : Category@{u u0 u0}} …], so the
 category's HOM and PROOF universes are IDENTIFIED, not merely bounded.
 That is INHERITED from [Cartesian], not introduced here:
 [Cartesian@{u u0}] itself takes a [Category@{u u0 u0}], and that link
 is real.  But read the CAUSE precisely, because an earlier draft of
 this header got it wrong: it said the identification “is already
 present at Structure/Terminal.v's [Terminal]”, implying [Terminal] is
 the source.  An audit REFUTED that as causal — a one-field class
 [{ t1 : obj }] declared over an unannotated [Context `{C : Category}]
 with no [Terminal] and no [Cartesian] anywhere in scope comes out at
 [Category@{u u0 u0}] just the same.  The source is universe
 MINIMIZATION of the unannotated generalized binder, which every class
 in this hierarchy shares.  Nor does any of this content REQUIRE the
 identification: the same field shape re-elaborates as
 [Category@{uo uh up}] when the levels are declared apart, so what is
 really present is a bound that minimization collapses.  Negatives 6
 and 7 record that the EXISTING constants [Cartesian] and [Terminal]
 cannot be applied at separated levels — which is true and worth
 pinning — but they establish sharing, not causation.  Nothing else
 is pinned: the object universe
 stays free, and the only other constraints are the two bounds
 [u0 <= projections.u0] and [u0 <= projections.u1] coming from the
 [∃!] in the biproduct record.

 WHAT IS NOT DELIVERED.  No terminal or initial object is claimed from
 the biproduct structure — a zero object is already assumed, so both
 exist, but they are not bundled into the produced structures (the
 [Cartesian] class carries no terminal object, matching
 Instance/Grp.v's [Grp_Cartesian]).  Nothing is said about biproducts of
 families or about additivity; [Structure/Semiadditive.v] owns the
 enrichment story and is only consumed here, never extended.  And no
 claim is made that a category with binary products and binary
 coproducts on a common carrier must have biproducts: the four
 interaction laws are genuine extra data, and the converse is
 Structure/Semiadditive.v's [bicartesian_preadditive], stated there
 under its own hypotheses. 

 --------
 nLab：       https://ncatlab.org/nlab/show/biproduct
 Wikipedia：  https://en.wikipedia.org/wiki/Coproduct
 书籍：      Mac Lane，《为工作中的数学家而写的范畴论》
 （第2版），§III.3，第63页（maclane:III.3:remark1）

 Mac Lane的§III.3具体余积列表以直和开头：在Ab类中、在R-模类中，以及（其纯粹形式下的半加性现象）在交换幺半群类中，两个对象的余积由它们的积所承载的相同对象构成。该文件是此观察所需的词汇部分，而树中没有这个。[Structure/Biproduct.v] 已经将“x ⊕ y 同时是积与余积”作为记录打包，并以 ∃!-形式陈述了两个普遍性性质：[bi_is_product] 和 [bi_is_coproduct]。它所没有做的是用库的其余部分所使用的词汇返回结果。积和余积是通过 [Structure/Cartesian.v] 的 [Cartesian] 类和 [Structure/Cocartesian.v] 的 [Cocartesian] 符号来使用的——[x × y]、[f △ g]、[exl] / [exr]；[x + y]、[f ▽ g]、[inl] / [inr]——而且从双积中无法访问它们。以下两个定义一劳永逸地弥补了这一空白：

 [biproduct_Cartesian]    : HasBiproducts C → @Cartesian C
 [biproduct_Cocartesian]  : HasBiproducts C → @Cocartesian C两者都是纯粹的重新包装。[bi_pair] / [bi_copair] 提供了两个中介，[bi_pair_respects] / [bi_copair_respects] 提供了两个敬意场，而双产物记录的唯一 ∃! 条款提供 [ump_products] 的两半——它的存在性一半给出两个计算规则，它的唯一性一半给出逆命题。没有引入新的数学内容；引入的只是一个名称。

 什么被证明，以及以何种强度。定义下的三个对应关系通过 [eq_refl] 在 Leibniz 等价下成立，而不仅仅是到 [≈] 或同构意义下：

 [biproduct_product_obj] : x × y 是 [biproduct_obj (biproduct x y)]
 [biproduct_coprod_obj] : x + y 是同一对象
 [biproduct_prod_is_coprod] : x × y 是 x + y最后一句是“在具有积与余积的范畴中，二元积和二元余积是同一个对象”，作为机器检查的转换，而不是作为散文或构造的同构。中介对象和注入同样精确返回（[biproduct_fork_is_pair], [biproduct_merge_is_copair], [biproduct_exl_is_bi_exl]及其三个兄弟），因此使用者可以仅通过转换在这两种词汇之间切换。关于 Structure/Semiadditive.v 的往返转换。相反的过程已经存在：[cartesian_biproduct] 和 [cartesian_has_biproducts]（Structure/Semiadditive.v）将具有二元积的前加性范畴转换为具有二元和的范畴。将其与本文件中的 [biproduct_Cartesian] 组合，将返回原始的二元和对象（OBJECT）通过 [eq_refl]（[biproduct_roundtrip_obj]）以及原始投影通过 [eq_refl]（[biproduct_roundtrip_exl], [biproduct_roundtrip_exr]）。它不会返回原始记录：INJECTIONS 被重建为叉 [id △ 0] 和 [0 △ id]，这些仅与原始对象 [≈] 相等（已证明，如 [biproduct_roundtrip_inl] 和 [biproduct_roundtrip_inr]），并且法则和普适性质字段是从头重建的。两个严格失败被固定为 Test/ProbeCoproduct.v 中的转换否定，而不是作为断言保留。一个工程发现，以及为什么这两个定义都不是 [Instance]。将 [biproduct_Cartesian] 注册用于类型类解析将会关闭与 Structure/Semiadditive.v 的逆向解析循环：[Cartesian C] 将通过 [HasBiproducts C] 解决，而 [cartesian_has_biproducts] 则通过 [Cartesian C] 和 [Preadditive C] 解决。基于这个原因，这里那里两者都只是普通的 [Definition]，并且下游的具体范畴会直接注册它们自己的 [Cartesian] / [Cocartesian] 实例，因此解析从未看到通用桥梁。宇宙，用约束块衡量。两个定义都读取 [biproduct_Cartesian@{u u0} : ∀ {C : Category@{u u0 u0}} …]，因此该类别的 HOM 和 PROOF 宇宙是同一的，而不仅仅是有界。这是从 [Cartesian] 继承的，并非在此引入：[Cartesian@{u u0}] 本身接受一个 [Category@{u u0 u0}]，并且该链接是真实的。但要精确阅读原因，因为该标题的早期草稿写错了：它说这个同一性“已经存在于 Structure/Terminal.v 的 [Terminal]”，暗示 [Terminal] 是源头。一项审计反驳了这作为因果关系——一个字段类 [{ t1 : obj }] 声明在未标注的 [Context `{C : Category}] 上，在任何作用域中没有 [Terminal] 也没有 [Cartesian]，结果仍然变为 [Category@{u u0 u0}]。源头是对未标注的广义绑定器的宇宙最小化，而该层次结构中的每个类都共享这一点。这些内容也不需要进行识别：当各级别分别声明时，相同的字段形状会重新表示为 [Category@{uo uh up}]，因此实际存在的是最小化会折叠的界限。负数 6 和 7 记录了现有常量 [Cartesian] 和 [Terminal] 不能在分离的级别上应用——这是事实且值得记录——但它们确立的是共享，而非因果关系。没有其他内容被固定：对象宇宙保持自由，唯一的其他约束是来自双积记录中的 [∃!] 的两个界限 [u0 <= projections.u0] 和 [u0 <= projections.u1]。未提供的内容。没有从余积结构中声明终对象或初对象——零对象已经被假定，所以两者都存在，但它们没有被打包到生成的结构中（[Cartesian] 类不包含终对象，与 Instance/Grp.v 的 [Grp_Cartesian] 相匹配）。关于族的余积或加法性没有任何说明；[Structure/Semiadditive.v] 拥有增强（enrichment）内容，仅在这里使用，从未扩展。而且，没有声称在共用载体上具有二元积和二元余积的范畴必须具有余积：四条交互律是真正的额外数据，其逆命题是 Structure/Semiadditive.v 的 [bicartesian_preadditive]，在那里根据自身假设陈述。
*)

Section BiproductCartesian.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{B : @HasBiproducts C Z}.

(** ** The cartesian structure / ** 笛卡尔结构 *)

(* The product-side mediator, named so the [Cartesian] record below can be built as a literal rather than through [Program] obligations whose order is an elaboration detail. / 产品方中介，因此下面名为 [Cartesian] 的记录可以作为字面值来构建，而不是通过 [Program] 义务来构建，其顺序是一个具体化的细节。 *)
Definition biproduct_fork {x y z : C} (f : x ~> y) (g : x ~> z) :
  x ~> biproduct_obj (biproduct y z) :=
  bi_pair (biproduct y z) f g.

Lemma biproduct_fork_respects (x y z : C) :
  Proper (equiv ==> equiv ==> equiv) (@biproduct_fork x y z).
Proof. apply bi_pair_respects. Qed.

(*
 The universal property: existence gives the two computation rules,
 uniqueness gives the converse. 

 --------
 泛性质：存在性给出两个计算规则，唯一性给出逆命题。
*)
Lemma biproduct_ump {x y z : C} (f : x ~> y) (g : x ~> z)
      (h : x ~> biproduct_obj (biproduct y z)) :
  h ≈ biproduct_fork f g
    ↔ (bi_exl (biproduct y z) ∘ h ≈ f)
    ∧ (bi_exr (biproduct y z) ∘ h ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + rewrite Hh.
      apply bi_exl_pair.
    + rewrite Hh.
      apply bi_exr_pair.
  - intros [Hl Hr].
    symmetry.
    now apply bi_pair_unique.
Qed.

(*
 The chosen biproduct object, its two projections and the product-side
 mediator [bi_pair] assemble into a [Cartesian] structure directly. 

 --------
 所选的双积对象、它的两个投影以及积侧中介 [bi_pair] 直接组装成一个 [Cartesian] 结构。
*)
Definition biproduct_Cartesian : @Cartesian C := {|
  product_obj := fun x y => biproduct_obj (biproduct x y);
  fork := @biproduct_fork;
  exl := fun x y => bi_exl (biproduct x y);
  exr := fun x y => bi_exr (biproduct x y);
  fork_respects := biproduct_fork_respects;
  ump_products := @biproduct_ump
|}.

(** ** The cocartesian structure / ** 余笛卡尔结构 *)

(*
 Dually — and this is the half Mac Lane's roster is about — the SAME
 object with the two injections and the copairing [bi_copair] is a
 cocartesian structure.  Recall that [Cocartesian C] is notation for
 [@Cartesian (C^op)] (Structure/Cocartesian.v), so the field names
 below are the product ones read in the opposite category: [product_obj]
 is the coproduct x + y, [exl]/[exr] are [inl]/[inr], [fork] is the
 copairing ▽, and [ump_products] arrives with its composition order
 flipped, reading [h ∘ inl ≈ f] and [h ∘ inr ≈ g] in C. 

 --------
 双重地——这就是 Mac Lane 的列表中一半内容所涉及的——具有两个注入和副配对 [bi_copair] 的同一对象是一个余笛卡尔结构。请记住，[Cocartesian C] 是 [@Cartesian (C^op)]（Structure/Cocartesian.v）的符号表示，因此下面的字段名是以对偶范畴读取的乘积项：[product_obj] 是余积 x + y，[exl] / [exr] 是 [inl] / [inr]，[fork] 是副配对 ▽，[ump_products] 的组合顺序被翻转，读取 [h ∘ inl ≈ f] 和 [h ∘ inr ≈ g] 在 C 中。
*)
Definition biproduct_merge {x y z : C} (f : y ~> x) (g : z ~> x) :
  biproduct_obj (biproduct y z) ~> x :=
  bi_copair (biproduct y z) f g.

Lemma biproduct_merge_respects (x y z : C) :
  Proper (equiv ==> equiv ==> equiv) (@biproduct_merge x y z).
Proof. apply bi_copair_respects. Qed.

Lemma biproduct_coump {x y z : C} (f : y ~> x) (g : z ~> x)
      (h : biproduct_obj (biproduct y z) ~> x) :
  h ≈ biproduct_merge f g
    ↔ (h ∘ bi_inl (biproduct y z) ≈ f)
    ∧ (h ∘ bi_inr (biproduct y z) ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + rewrite Hh.
      apply bi_copair_inl.
    + rewrite Hh.
      apply bi_copair_inr.
  - intros [Hl Hr].
    symmetry.
    now apply bi_copair_unique.
Qed.

(*
 TWO ELABORATION HAZARDS, both met and both worth recording.

 (1) A [{| … |}] literal ascribed to [@Cocartesian C] is checked field by
 field before the ascription has forced the implicit category, and
 [product_obj]'s type [obj → obj → obj] unifies that category with [C] on
 sight — [obj[C^op]] and [obj[C]] being definitionally equal but not
 syntactically so.  Every later field is then checked at [C], and [fork]
 fails with its arrows pointing the wrong way.  Naming the constructor
 and its category, [@Build_Cartesian (C^op) …], fixes the orientation.

 (2) With the orientation fixed, the OPPOSITE hazard appears in
 [product_obj]'s body: [biproduct_obj] and [biproduct] have their
 category implicit ([Arguments biproduct_obj {C Z x y} _] and
 [Arguments biproduct {C Z _} x y]), so writing them unannotated at an
 expected result type of [obj[C^op]] resolves them AT [C^op], and the
 [fork] field is then checked against a different family of biproducts
 from the one [biproduct_merge] was built over.  The two are printed
 identically — [biproduct_obj (biproduct y z)] either way — so the error
 message is unreadable.  Spelling [@biproduct_obj C Z] and
 [@biproduct C Z B] out is what pins the family. 

 --------
 两个展开危险，都遇到了，都值得记录。

 (1) 一个归属于 [@Cocartesian C] 的 [{| … |}] 文字在归属强制隐式类别之前，会逐字段检查，并且 [product_obj] 的类型 [obj → obj → obj] 会立刻与 [C] 统一该类别——[obj[C^op] ] 和 [obj[C] ] 在定义上相等，但在语法上不相等。随后每个字段都会在 [C] 处进行检查，而 [fork] 失败，其箭头指向错误的方向。命名构造器及其类别 [@Build_Cartesian (C^op) …] 可以修正方向。(2) 当方向固定时，[product_obj] 的主体中出现了相反的危险：[biproduct_obj] 和 [biproduct] 它们的类别是隐含的（[Arguments biproduct_obj {C Z x y} _] 和 [Arguments biproduct {C Z _} x y]），因此在预期结果类型为 [obj[C^op] 时未标注地编写它们会在 [C^op] 处解析它们，然后 [fork] 字段会与 [biproduct_merge] 所构建的双产物族不同的族进行检查。这两者打印出来是相同的——无论哪种方式都是 [biproduct_obj (biproduct y z)]——所以错误信息是无法读取的。拼写出 [@biproduct_obj C Z] 和 [@biproduct C Z B] 是固定该族的方式。
*)
Definition biproduct_Cocartesian : @Cocartesian C :=
  @Build_Cartesian (C^op)
    (fun x y => @biproduct_obj C Z x y (@biproduct C Z B x y))
    (@biproduct_merge)
    (fun x y => @bi_inl C Z x y (@biproduct C Z B x y))
    (fun x y => @bi_inr C Z x y (@biproduct C Z B x y))
    biproduct_merge_respects
    (@biproduct_coump).

(** ** Strict identifications / ** 严格识别 *)

(* The product object IS the biproduct object, on the nose. / 产品对象正是副产品对象，完全如此。 *)
Example biproduct_product_obj (x y : C) :
  @product_obj C biproduct_Cartesian x y = biproduct_obj (biproduct x y) :=
  eq_refl.

(* And so is the coproduct object. / 余积对象也是如此。 *)
Example biproduct_coprod_obj (x y : C) :
  @Coprod C biproduct_Cocartesian x y = biproduct_obj (biproduct x y) :=
  eq_refl.

(*
 Hence the binary product and the binary coproduct are the SAME object
 — the defining feature of a biproduct, as a conversion rather than as
 prose or as a constructed isomorphism. 

 --------
 因此，二元积和二元余积是相同的对象——作为二重积的定义特征，它是一种转换，而不是以散文形式或作为构造的同构。
*)
Example biproduct_prod_is_coprod (x y : C) :
  @product_obj C biproduct_Cartesian x y
    = @Coprod C biproduct_Cocartesian x y :=
  eq_refl.

(* The two mediators are the biproduct's own, definitionally. / 根据定义，这两个介质本身就是副产品的。 *)
Example biproduct_fork_is_pair {x y z : C} (f : x ~> y) (g : x ~> z) :
  @fork C biproduct_Cartesian x y z f g = bi_pair (biproduct y z) f g :=
  eq_refl.

Example biproduct_merge_is_copair {x y z : C} (f : y ~> x) (g : z ~> x) :
  @merge C biproduct_Cocartesian x y z f g
    = bi_copair (biproduct y z) f g :=
  eq_refl.

(* As are the four structural morphisms. / 正如四个结构态射一样。 *)
Example biproduct_exl_is_bi_exl (x y : C) :
  @exl C biproduct_Cartesian x y = bi_exl (biproduct x y) := eq_refl.

Example biproduct_exr_is_bi_exr (x y : C) :
  @exr C biproduct_Cartesian x y = bi_exr (biproduct x y) := eq_refl.

Example biproduct_inl_is_bi_inl (x y : C) :
  @inl C biproduct_Cocartesian x y = bi_inl (biproduct x y) := eq_refl.

Example biproduct_inr_is_bi_inr (x y : C) :
  @inr C biproduct_Cocartesian x y = bi_inr (biproduct x y) := eq_refl.

End BiproductCartesian.

(* * ** The round trip against Structure/Semiadditive.v / * ** 针对 Structure/Semiadditive.v 的往返 *)

(*
 Structure/Semiadditive.v turns a preadditive category with binary
 products into one with biproducts.  Feeding it the products this file
 derives returns the original biproduct object and the original
 projections on the nose; the injections are rebuilt as forks and are
 recovered only up to [≈]. 

 --------
 Structure/Semiadditive.v 将一个具有二元积的预加性范畴转变为具有双积的范畴。将此文件派生的积作为输入，它会返回原始的双积对象和原始的投影；插入被重新构建为叉，并且只能在 [≈] 下恢复。
*)
Section BiproductRoundTrip.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{P : @Preadditive C}.
Context `{B : @HasBiproducts C Z}.

Let Cart : @Cartesian C := biproduct_Cartesian.

Example biproduct_roundtrip_obj (x y : C) :
  biproduct_obj
    (@cartesian_biproduct C Z P Cart x y) = biproduct_obj (biproduct x y) :=
  eq_refl.

Example biproduct_roundtrip_exl (x y : C) :
  bi_exl (@cartesian_biproduct C Z P Cart x y) = bi_exl (biproduct x y) :=
  eq_refl.

Example biproduct_roundtrip_exr (x y : C) :
  bi_exr (@cartesian_biproduct C Z P Cart x y) = bi_exr (biproduct x y) :=
  eq_refl.

(*
 The injections come back only up to [≈]: the reconstruction defines
 them as [id △ 0] and [0 △ id], which are the original injections by the
 four interaction laws and product uniqueness, not by conversion. 

 --------
 注射只回到 [≈]：重构将它们定义为 [id △ 0] 和 [0 △ id]，这是由四个相互作用定律和乘积唯一性得出的原始注射，而不是通过转换得到的。
*)
Lemma biproduct_roundtrip_inl (x y : C) :
  bi_inl (@cartesian_biproduct C Z P Cart x y) ≈ bi_inl (biproduct x y).
Proof.
  exact (bi_pair_unique (biproduct x y) id zero_mor
           (bi_inl (biproduct x y))
           (bi_exl_inl (biproduct x y)) (bi_exr_inl (biproduct x y))).
Qed.

Lemma biproduct_roundtrip_inr (x y : C) :
  bi_inr (@cartesian_biproduct C Z P Cart x y) ≈ bi_inr (biproduct x y).
Proof.
  exact (bi_pair_unique (biproduct x y) zero_mor id
           (bi_inr (biproduct x y))
           (bi_exl_inr (biproduct x y)) (bi_exr_inr (biproduct x y))).
Qed.

End BiproductRoundTrip.
