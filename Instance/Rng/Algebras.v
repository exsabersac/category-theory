(*
 [Coq.QArith.QArith] must be required BEFORE [Category.Lib]: it exports its
 own [equiv], which shadows [Setoid]'s, and the anonymous record
 [{| equiv := _ |}] used below is then rejected with the error
 "equiv: Not a projection".  Instance/FdVect.v records the same
 import-order gotcha. 

 --------
 [Coq.QArith.QArith] 必须在 [Category.Lib] 之前被引入：它导出了自己的 [equiv]，这会覆盖 [Setoid] 的，而下面使用的匿名记录 [{| equiv := _ |}] 会因此被拒绝，并显示错误“equiv: Not a projection”。Instance/FdVect.v 记录了同样的导入顺序问题。
*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Diagonal.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Rng.

Generalizable All Variables.

#[local] Set Transparent Obligations.

(*
   * * Commutative K-algebras as the coslice of commutative rings

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.6
   Exercise 1 (printed p. 47) [maclane:II.6:ex1].  The catalog's
   paraphrase of the exercise — its wording, not the book's — reads:
   "For a commutative ring K, show the comma category (K ↓ CRng) is the
   usual category of all small commutative K-algebras."  The comma
   category in question is §II.6's [maclane:II.6:def3], the category of
   objects S-under b for S the identity functor: objects are the arrows
   f : K ~> A of CRng, arrows ⟨f, A⟩ → ⟨f', A'⟩ are the CRng-arrows
   h : A ~> A' with h ∘ f = f'.
   nLab: https://ncatlab.org/nlab/show/category
   nLab: https://ncatlab.org/nlab/show/under+category
   nLab: https://ncatlab.org/nlab/show/associative+algebra
   Wikipedia: https://en.wikipedia.org/wiki/Associative_algebra

   WHAT IS ALREADY IN TREE.  The exercise's first half — the category
   [CRng] of commutative rings — is Instance/Rng.v's, not this file's:
   [CRng_Sub] (Instance/Rng.v) selects the commutative [RingObject]s
   and retains every [Rng]-morphism between them, [CRng] is
   [Sub Rng CRng_Sub], [CRng_Full] records the fullness, and
   [Int_CRng] is the witness ℤ.  Consequently an object of [CRng]
   is a dependent pair (R; proof that R is commutative) and a morphism of
   [CRng] is a pair (a [RigHom]; a trivially-true membership witness) —
   [Sub]'s shape, Construction/Subcategory.v.  [Coslice]
   (Construction/Slice.v) and its comma reading [Comma_Coslice]
   (Construction/Slice.v) are likewise pre-existing.

   WHAT THIS FILE ADDS.  The category of commutative K-algebras defined
   DIRECTLY — [KAlgObject]/[KAlgHom]/[KAlg] below — and the proof that it
   agrees with the coslice.  The definition is deliberately given in the
   ELEMENTARY spelling: a [KAlgObject K] is a bare [RingObject] together
   with a commutativity proof and a [RigHom] out of K's underlying ring,
   NOT a [CRng] object together with a [CRng] morphism.  The alternative
   spelling would make [KAlgObject K] literally the coslice's object type
   and the comparison a near-identity; the elementary one keeps a real
   (if small) repackaging on both sides — a [Sub] membership witness and
   two dependent pairs have to be assembled and taken apart — which is
   what the exercise is actually asking one to check.  What it costs is
   that the algebra's ring is not, on the nose, an object of [CRng]; what
   it buys is that the comparison functors below have content, and that
   the exact strength of the agreement can be measured rather than
   asserted.

   STRENGTH, MEASURED.  Two statements are delivered, and they are not
   the same statement:

   [KAlg_Coslice_strict_iso]  KAlg K ≅[StrictCat] Coslice CRng K
   [KAlg_Coslice_iso]         KAlg K ≅[Cat]       Coslice CRng K

   In this library [≅[Cat]] is EQUIVALENCE of categories, since [Cat]'s
   hom-setoid is [Functor_Setoid] (Instance/Cat.v), which identifies
   functors up to natural isomorphism.  The stronger [≅[StrictCat]] is
   the on-the-nose isomorphism: [StrictCat]'s hom-setoid is
   [Functor_StrictEq_Setoid] (Theory/Functor.v), which asks for
   F x = G x at Leibniz equality on objects together with the
   transported agreement of the morphism actions.  The strict reading
   DOES close here, so [KAlg_Coslice_iso] is DERIVED from it
   ([strict_equiv_implies_fun_equiv], Instance/StrictCat/ToCat.v) and
   is the weaker of the two; it carries the name the issue pins, which is
   also the form most of the library's consumers take.

   The two directions are not symmetric, and the asymmetry was measured,
   not guessed:

   * [KAlg_Coslice_round_obj] — going KAlg → Coslice → KAlg returns the
   object DEFINITIONALLY: it is proved by [eq_refl], and is stated as
   an [Example] so the claim is machine-checked rather than asserted.
   [KAlgObject] is a [Record] and primitive projections are in force
   (inherited from Lib/Setoid.v and Lib/Datatypes.v; [About kalg_ring]
   reports "is a primitive projection of KAlgObject"), so records have
   definitional eta and reassembling an algebra from its three
   projections is the algebra.

   * [Coslice_KAlg_round_obj] — going Coslice → KAlg → Coslice returns
   the object only up to a [destruct]-provable Leibniz equality.
   [eq_refl] is REJECTED for it; that was measured, by writing the
   statement out with [eq_refl] as its proof term and reading the
   error ("cannot unify ... and x"), not inferred.  The obstruction is
   that a coslice object over [CRng] is built from [sigT] (twice) and
   from the [True] of [CRng_Sub]'s [shom], and none of those has
   definitional eta in Coq — unlike the [Record] above; the proof
   therefore case-splits and only then closes by [reflexivity].  This
   is the usual record-eta culprit, and here it bites on exactly one
   side.

   Both morphism actions ARE definitional: each comparison functor leaves
   the underlying ring homomorphism untouched, so the two hom-level round
   trips ([KAlg_Coslice_round_hom], [Coslice_KAlg_round_hom]) close by
   [reflexivity] — on the [KAlg] side after one [intro], which only
   unfolds the hom-setoid to the pointwise form [Rng] gives it, since
   setoid [reflexivity] unifies the two sides of the RELATION and the
   relation there is still folded.

   THE COMMA READING.  [KAlg_Comma_iso] composes the above with
   [Comma_Coslice] to land at (=(K) ↓ Id), the shape Mac Lane's
   [maclane:II.6:def3] writes; it is at [Cat] strength, since
   [Comma_Coslice] is stated there.

   UNIVERSES, measured on all 35 NAMED constants of this file with
   [About] under [Set Printing Universes] (the file's four [Program
   Definition]s contribute twelve further obligation constants, each
   also measured for assumptions — 47 in all — but they are transparent
   and carry no universe content of their own).  Every one of them is universe
   polymorphic (the flag is inherited from Lib/Setoid.v).  Three things
   are worth naming, and the first two are the DONORS' doing, not this
   file's:

   * [KAlg K : Category@{o h h}] identifies the hom and proof
   universes.  That is [Rng]'s own shape — [Rng@{u u0} :
   Category@{u u0 u0}] (Instance/Rng.v), which comes from
   [RigHom_Setoid : Setoid@{h h}] (Theory/Algebra/Rig.v) — and
   [CRng] carries it through [Sub].  Nothing here narrows it.

   * Six constants print a literal [Set] as a universe instance
   argument: [Q_KAlg], [Int_to_Q_KAlg], [Int_to_Q_triangle],
   [Q_KAlg_in_Coslice], [Z_KAlg], [Z_KAlg_unit_unique].  In each case
   the donor is already pinned: [ZtoQ] is typed
   [hom Int_Ring@{Set Set Set} Q_Ring@{Set Set Set}]
   (Instance/Rng.v), and [rng_from_Z] takes
   [R : RingObject@{Set Set Set}] (Instance/Rng.v).  Three
   further constants ([Q_KAlg_unit_computes],
   [Q_KAlg_unit_not_surjective], [Q_KAlg_is_canonical]) mention
   [Q_KAlg] and inherit the same instance without printing it.  The [KAlg] spine and both isomorphisms carry no [Set]
   instance, and [Int_KAlg] is fully polymorphic.

   * At either isomorphism three of [KAlg]'s four universe parameters
   collapse to one.  That is what stating an [Isomorphism] in ANY
   category of categories costs — both categories must be objects of
   one and the same instance — and it is NOT specific to [Cat]: the
   collapse is already present at [KAlg_Coslice_strict_iso], since
   [StrictCat] has the same [obj := Category].  Taking the strict form
   does not keep the universes apart (audit-corrected).

   These statements are scoped to the constants of this file, each
   measured individually; nothing is claimed about the donors' other
   constants.

   WHERE COMMUTATIVITY ENTERS.  [kalg_comm] is not decoration: it is
   literally [CRng_Sub]'s membership predicate, recorded by
   [kalg_comm_is_CRng_membership], whose proof term is the field itself
   ([:= kalg_comm A], no tactic).  It is what lets the comparison land in
   [Coslice CRng K] rather than [Coslice Rng (`1 K)] — drop it and the
   coslice one gets is the category of (not necessarily commutative)
   rings under K, which is NOT the category of commutative K-algebras.
   K's own commutativity is carried by K : CRng and is never used below;
   the exercise supplies it because without it "K-algebra" in the usual
   sense is not the right notion.

   WHAT THIS DOES NOT SAY, deferred and disclosed.

   * Non-commutative K-algebras are not treated.  The same coslice
   taken in [Rng] would give rings under K, which is a different and
   larger notion than a K-algebra in the non-commutative sense (there
   the structure map is required to land in the CENTRE, a condition
   that is automatic exactly when the target is commutative).  No
   centre-valued variant is built here.

   * The MODULE-THEORETIC definition is not connected up.  The usual
   textbook definition of a K-algebra is a K-module (Instance/Mod.v's
   [RModObject]) carrying a bilinear multiplication, i.e. a ring plus
   a module structure plus a compatibility law.  The coslice
   definition SIDESTEPS that: for a COMMUTATIVE K the structure map
   K ~> A determines the module action by k · a := f(k)·a, and
   conversely, so the two definitions agree — but that agreement is a
   theorem about [RModObject] and is not proved here.  This file
   proves only the comparison the exercise asks for, between the
   direct definition and the coslice.  Nothing below mentions
   [RModObject], and no claim is made that [KAlg] is equivalent to a
   category of modules.

   * "Small" in the exercise's statement is not formalized as a size
   condition; the library's [Theory/Size.v] vocabulary is not
   invoked, and the categories here sit wherever their universe
   parameters put them. 

   --------
   * * 交换 K-代数作为交换环的余切片

   Mac Lane，《为工作数学家而写的范畴论》，第2版，第§II.6节
   练习1（印刷页47）[maclane:II.6:ex1]。该目录对练习的释义——其用词，而非书中的原文——如下：
   “对于一个交换环 K，证明逗号范畴 (K ↓ CRng) 是所有小型交换 K-代数的通常范畴。” 所讨论的逗号范畴是 §II.6 的 [maclane:II.6:def3]，即对象是 S-under b 的范畴，其中 S 是恒等函子：对象是 CRng 的箭头 f : K ~> A，箭头 ⟨f, A⟩ → ⟨f', A'⟩ 是 CRng 的箭头 h : A ~> A'，满足 h ∘ f = f'。
   nLab: https://ncatlab.org/nlab/show/category
   nLab: https://ncatlab.org/nlab/show/under+category
   nLab: https://ncatlab.org/nlab/show/associative+algebra
   维基百科: https://en.wikipedia.org/wiki/Associative_algebra什么已经在树中。练习的前半部分——交换环类别 [CRng]——是 Instance/Rng.v 的，而不是这个文件的：[CRng_Sub]（Instance/Rng.v）选择交换的 [RingObject] 并且保留它们之间的每个 [Rng]-态射，[CRng] 是 [Sub Rng CRng_Sub]，[CRng_Full] 记录了充满性，[Int_CRng] 是证据 ℤ。因此 [CRng] 的一个对象是一个依赖对 (R; R 是交换的证据)，而 [CRng] 的一个态射是一个对 (一个 [RigHom]；一个显然为真的属于证明)——[Sub] 的形状，Construction/Subcategory.v。[Coslice] (Construction/Slice.v) 及其逗号读法 [Comma_Coslice] (Construction/Slice.v) 也是预先存在的。这个文件的新增内容。直接定义的交换 K-代数类别 —— 下面的 [KAlgObject] / [KAlgHom] / [KAlg] —— 以及证明它与余切片一致。定义有意以初等拼写的方式给出：一个 [KAlgObject K] 是一个简单的 [RingObject]，外加一个交换性证明和一个来自 K 的基础环的 [RigHom]，而不是一个 [CRng] 对象加上一个 [CRng] 态射。另一种拼写方式会让 [KAlgObject K] 字面上成为余切片的对象类型，并使比较几乎是恒等的；初等拼写在两边保持了真正的（虽然很小的）重新打包 —— 需要组装和拆解一个 [Sub] 的成员证明和两个依赖对 —— 这正是练习所要求检查的内容。其代价是代数的环并不是严格意义上 [CRng] 的一个对象；它所带来的好处是下面的比较函子具有实际内容，并且协议的精确强度可以被测量，而不是仅仅断言。

   强度，可测量。 两个陈述被提出，而且它们不是相同的陈述：

   [KAlg_Coslice_strict_iso]   KAlg K ≅ [StrictCat]  Coslice CRng K
   [KAlg_Coslice_iso]          KAlg K ≅ [Cat]        Coslice CRng K在这个库中，[≅[Cat]] 是范畴的等价，因为 [Cat] 的同态集是 [Functor_Setoid]（Instance/Cat.v），它将函子直到自然同构视为相同。更强的 [≅[StrictCat]] 是严格同构：[StrictCat] 的同态集是 [Functor_StrictEq_Setoid]（Theory/Functor.v），它要求 F x = G x 在对象上的莱布尼茨等价，并且在态射作用上的一致性也被传递。严格释义在这里确实封闭，所以 [KAlg_Coslice_iso] 是从它衍生的（[strict_equiv_implies_fun_equiv]，Instance/StrictCat/ToCat.v），并且是两者中较弱的；它承载了“issue pins”的名称，这也是库的大多数使用者采用的形式。

   这两个方向不是对称的，这种不对称是被测量的，而非猜测的：*  [KAlg_Coslice_round_obj] — 从 KAlg → Coslice → KAlg 返回对象是定义上的：这是由 [eq_refl] 证明的，并且被表述为 [Example]，因此该声明是机器检查的而不是直接断言的。[KAlgObject] 是一个 [Record]，并且原始投影是有效的（继承自 Lib/Setoid.v 和 Lib/Datatypes.v；[About kalg_ring] 报告“是 KAlgObject 的原始投影”），因此记录具有定义性的 eta，并且从其三个投影重新组装一个代数就是该代数。*  [Coslice_KAlg_round_obj] — 调用 Coslice → KAlg → Coslice 只会返回该对象，最多在 [destruct] 可证明的 Leibniz 等价下。
   [eq_refl] 因此被拒绝；这是通过将语句写出并使用 [eq_refl] 作为其证明项，然后读取错误信息（“无法统一 ... 和 x”）来测量的，而不是推断出来的。障碍在于，[CRng] 上的 coslice 对象是由 [sigT]（两次）以及 [CRng_Sub] 的 [shom] 的 [True] 构建的，而这些在 Coq 中都没有定义性的 eta——与上面的 [Record] 不同；因此证明会进行 case-split，然后才通过 [reflexivity] 关闭。这是常见的记录 eta 导致的问题，而且在这里恰好发生在一边。两种态射作用都是定义性的：每个比较函子都不改变底层的环同态，因此两个同态层的往返（[KAlg_Coslice_round_hom], [Coslice_KAlg_round_hom]）通过[reflexivity] 关闭——在[KAlg] 侧经过一次[intro] 后，只是将同态集重新展开为点态形式 [Rng] 所给出的形式，因为集 [reflexivity] 统一了关系两边，且那里关系仍然是折叠的。

   逗号阅读。[KAlg_Comma_iso] 将上述与 [Comma_Coslice] 复合以到达 (=(K) ↓ Id)，那是 Mac Lane 的 [maclane:II.6:def3] 所写的形状；它处于 [Cat] 强度，因为 [Comma_Coslice] 在那里被陈述。UNIVERSES，根据本文件的所有35个已命名常数进行测量，在[About]下的[Set Printing Universes]（文件中的四个[程序定义]贡献了另外十二个义务常数，每个也都测量了假设——总共47个——但它们是透明的，并且自身不承载宇宙内容）。它们中的每一个都是宇宙多态的（标记是从Lib/Setoid.v继承的）。有三件事值得一提，前两项是DONORS的工作，而非本文件的：

   * [KAlg K : Category@{o h h}] 标识了 hom 和 proof 宇宙。那是[Rng] 本身的形状——[Rng@{u u0} : Category@{u u0 u0}]（Instance/Rng.v），它来自[RigHom_Setoid : Setoid@{h h}]（Theory/Algebra/Rig.v）——并且[CRng] 将其贯穿至[Sub]。这里没有任何限制它。* 六个常量打印一个字面量 [Set] 作为宇宙实例
   参数: [Q_KAlg], [Int_to_Q_KAlg], [Int_to_Q_triangle],
   [Q_KAlg_in_Coslice], [Z_KAlg], [Z_KAlg_unit_unique]。 在每种情况下
   提供者已经被固定: [ZtoQ] 被标注为
   [hom Int_Ring@{Set Set Set} Q_Ring@{Set Set Set}] (Instance/Rng.v)，并且 [rng_from_Z] 接受
   [R : RingObject@{Set Set Set}] (Instance/Rng.v)。 三个
   进一步的常量 ([Q_KAlg_unit_computes], [Q_KAlg_unit_not_surjective], [Q_KAlg_is_canonical]) 提到
   [Q_KAlg] 并继承相同的实例而不打印它。 [KAlg] 脊以及两个同构不携带任何 [Set]
   实例，并且 [Int_KAlg] 是完全多态的。* 在任意同构下，[KAlg] 的四个宇宙参数中的三个会合并为一个。这就是在任何范畴类别中声明一个 [Isomorphism] 所付出的代价——两个范畴必须是同一实例的对象——这并不是 [Cat] 的特性：这种合并在 [KAlg_Coslice_strict_iso] 就已经存在，因为 [StrictCat] 拥有相同的 [obj := Category]。采用严格形式并不能保持宇宙的分离（经审计修正）。

   这些陈述适用于本文件的常量，每个常量单独测量；不对捐赠者的其他常量作任何声明。交换性介入的地方。[kalg_comm] 不是装饰：它实际上是 [CRng_Sub] 的成员谓词，由 [kalg_comm_is_CRng_membership] 记录，其证明项就是字段本身（[:= kalg_comm A]，没有策略）。这就是使比较落在 [Coslice CRng K] 而不是 [Coslice Rng (`1 K)] 上的原因——如果去掉它，得到的余切片就是 K 下的（不一定交换的）环范畴，而这并不是交换 K-代数的范畴。K 自身的交换性由 K : CRng 承载，并在下面从未使用；练习提供它是因为没有它，通常意义上的“K-代数”并不是正确的概念。

   这段话没有说明的内容，已推迟和披露。* 不处理非交换 K-代数。在 [Rng] 中采用相同的余切会得到 K 上的环，这是一个不同且更大的概念，而不是非交换意义下的 K-代数（在那里，结构映射要求落在中心，这个条件在目标是交换时是自动满足的）。这里没有构建以中心为值的变体。* 模块理论的定义没有连接起来。常规教材中K-代数的定义是一个K-模（Instance/Mod.v 的 [RModObject]）带有双线性乘法，即一个环加上一个模结构再加上兼容性法则。余切片（coslice）定义绕过了这一点：对于交换K，结构映射 K ~> A 决定了模作用，通过 k · a := f(k)·a，反之亦然，所以这两种定义是一致的——但是这种一致性是关于 [RModObject] 的定理，这里没有证明。这个文件只证明练习要求的比较，即直接定义和余切片之间的比较。下面没有提到 [RModObject]，也没有声称 [KAlg] 等价于一个模范畴。* 练习题中“Small”并没有被形式化为一个尺寸条件；库中的 [Theory/Size.v] 词汇没有被调用，这里的类别根据它们的宇宙参数放置在任何位置。
*)

(** ** The direct definition / ** 直接定义 *)

(* A commutative K-algebra: a commutative ring together with a homomorphism out of K. The three fields are, in order, the underlying ring, its commutativity, and the structure map. / 交换 K-代数：一个交换环，附带一个从 K 出发的同态。三个字段依次是基础环、其交换性以及结构映射。 *)
Record KAlgObject (K : CRng) := {
  kalg_ring : RingObject;
  kalg_comm : ∀ a b, rig_mul kalg_ring a b ≈ rig_mul kalg_ring b a;
  kalg_unit : `1 K ~{Rng}~> kalg_ring
}.

Arguments kalg_ring {K} _.
Arguments kalg_comm {K} _ _ _.
Arguments kalg_unit {K} _.

(*
 A morphism of K-algebras is a ring homomorphism commuting with the two
 structure maps.  The orientation of the triangle is [Coslice]'s
 (Construction/Slice.v, `2 y ≈ f ∘ `2 x), so that the comparison
 below needs no transposition. 

 --------
 K-代数的态射是与两个结构映射交换的环同态。三角形的方向是 [Coslice] 的（Construction/Slice.v, `2 y ≈ f ∘ ` 2 x），因此下面的比较不需要转置。
*)
Definition KAlgHom {K : CRng} (A B : KAlgObject K) : Type :=
  ∃ f : kalg_ring A ~{Rng}~> kalg_ring B, kalg_unit B ≈ f ∘ kalg_unit A.

(*
 Two K-algebra morphisms are equal when their underlying ring
 homomorphisms are; the triangle proof is irrelevant.  This matches
 [Coslice]'s convention (Construction/Slice.v). 

 --------
 当两个 K-代数同态的基础环同态相等时，它们就相等；三角形证明无关紧要。这与 [Coslice] 的约定（Construction/Slice.v）一致。
*)
Program Definition KAlgHom_Setoid {K : CRng} (A B : KAlgObject K) :
  Setoid (KAlgHom A B) := {|
  equiv := fun f g => `1 f ≈ `1 g
|}.
Next Obligation.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (`1 g a); [ apply Hfg | apply Hgh ].
Defined.

Lemma kalg_id_triangle {K : CRng} (A : KAlgObject K) :
  kalg_unit A ≈ id ∘ kalg_unit A.
Proof. now rewrite id_left. Defined.

Lemma kalg_comp_triangle {K : CRng} {A B C : KAlgObject K}
      (f : KAlgHom B C) (g : KAlgHom A B) :
  kalg_unit C ≈ (`1 f ∘ `1 g) ∘ kalg_unit A.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (`2 g).
  exact (`2 f).
Defined.

Program Definition KAlg (K : CRng) : Category := {|
  obj     := KAlgObject K;
  hom     := @KAlgHom K;
  homset  := @KAlgHom_Setoid K;
  id      := fun A => (id; kalg_id_triangle A);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; kalg_comp_triangle f g)
|}.
Next Obligation.
  intros f1 f2 Hf g1 g2 Hg a.
  transitivity (rig_map (`1 f1) (rig_map (`1 g2) a)).
  - apply (proper_morphism (rig_map (`1 f1))), Hg.
  - apply Hf.
Defined.

(*
 The commutativity field IS [CRng_Sub]'s membership predicate: this term
 typechecks with the field handed over verbatim.  That is what makes the
 comparison below land in a coslice over [CRng]. 

 --------
 交换性字段是 [CRng_Sub] 的成员谓词：该术语与直接传递的字段类型匹配。这就是为什么下面的比较会落在 [CRng] 的余切片上的原因。
*)
Example kalg_comm_is_CRng_membership (K : CRng) (A : KAlgObject K) :
  sobj Rng CRng_Sub (kalg_ring A) := kalg_comm A.

(** ** The comparison / ** 比较 *)

(*
 An algebra becomes an object under K: package the ring with its
 commutativity to get an object of [CRng], and the structure map with
 [CRng_Sub]'s trivial membership witness to get a morphism of [CRng].
 On morphisms, the triangle carries over verbatim — `2 f is handed to
 the coslice unchanged. 

 --------
 一个代数在 K 下成为一个对象：将环和它的交换性打包以得到 [CRng] 的一个对象，并将结构映射与 [CRng_Sub] 的平凡成员证明一起打包以得到 [CRng] 的一个态射。在态射上，三角形完全照搬——`2 f 被原样传递给余切片。
*)
Program Definition KAlg_to_Coslice (K : CRng) : KAlg K ⟶ Coslice CRng K := {|
  fobj := fun A => ((kalg_ring A; kalg_comm A); (kalg_unit A; I));
  fmap := fun A B f => ((`1 f; I); `2 f)
|}.

(* ...and back: forget the packaging. / ...然后回来：忘掉包装。 *)
Program Definition Coslice_to_KAlg (K : CRng) : Coslice CRng K ⟶ KAlg K := {|
  fobj := fun x => {| kalg_ring := `1 (`1 x);
                      kalg_comm := `2 (`1 x);
                      kalg_unit := `1 (`2 x) |};
  fmap := fun x y g => (`1 (`1 g); `2 g)
|}.

(** ** The round trips / ** 往返旅行 *)

(*
 KAlg → Coslice → KAlg is the identity on objects DEFINITIONALLY: the
 round trip rebuilds the record from its three projections, and records
 have eta here. 

 --------
 KAlg → Coslice → KAlg 在对象上在定义上是恒等的：这个往返重建了记录从它的三个投影，并且记录在这里具有 eta。
*)
Example KAlg_Coslice_round_obj (K : CRng) (A : KAlg K) :
  fobj[Coslice_to_KAlg K] (fobj[KAlg_to_Coslice K] A) = A := eq_refl.

(*
 Coslice → KAlg → Coslice is the identity on objects only up to a
 [destruct]-provable equality: [sigT] (twice) and the [True] of
 [CRng_Sub]'s [shom] have no definitional eta, so [eq_refl] does not
 typecheck here and the proof must case-split first. 

 --------
 Coslice → KAlg → Coslice 在对象上仅在 [destruct] 可证明的相等下是恒等的：[sigT]（二次）以及 [True] 的 [CRng_Sub] 的 [shom] 没有定义的 eta，因此 [eq_refl] 在这里无法类型检查，证明必须先进行情况拆分。
*)
Lemma Coslice_KAlg_round_obj (K : CRng) (x : Coslice CRng K) :
  fobj[KAlg_to_Coslice K] (fobj[Coslice_to_KAlg K] x) = x.
Proof.
  destruct x as [[R comm] [u t]]; destruct t; reflexivity.
Defined.

(*
 Both morphism actions leave the underlying ring homomorphism alone, so
 both hom-level round trips are [reflexivity].  On the coslice side the
 two objects are only propositionally equal, so the statement is made at
 the underlying [Rng]-morphism — which is exactly what either category's
 hom-setoid compares. 

 --------
 两种态射作用都保持底层环同态不变，因此两种同态层往返都是 [reflexivity]。在余切面上，这两个对象只是命题上相等，因此该陈述是在底层 [Rng]-态射上作出的 —— 这正是任一范畴的同态集族所比较的对象。
*)
Lemma KAlg_Coslice_round_hom (K : CRng) (A B : KAlg K) (f : A ~> B) :
  fmap[Coslice_to_KAlg K] (fmap[KAlg_to_Coslice K] f) ≈ f.
Proof. intro a; reflexivity. Qed.

Lemma Coslice_KAlg_round_hom (K : CRng) (x y : Coslice CRng K) (g : x ~> y) :
  `1 (`1 (fmap[KAlg_to_Coslice K] (fmap[Coslice_to_KAlg K] g))) ≈ `1 (`1 g).
Proof. reflexivity. Qed.

(** ** The isomorphism / ** 同构 *)

(*
 Mac Lane's exercise at on-the-nose strength: an isomorphism of
 categories, not merely an equivalence.  Its two components say that the
 composites are strictly equal to the identity functors.  On the coslice
 side the object component is [Coslice_KAlg_round_obj], which reduces to
 [eq_refl] once its argument is a literal pair — which is why the
 coherence goal is discharged by case-splitting on the two objects before
 appealing to reflexivity; on the algebra side the object component is
 [eq_refl] outright. 

 --------
 Mac Lane 的练习在恰到好处的强度上：一个范畴的同构，而不仅仅是等价。它的两个组成部分表明复合严格等于恒等函子。在余切片侧，对象部分是 [Coslice_KAlg_round_obj]，当它的参数是一个字面对时，会简化为 [eq_refl]——这就是为什么在引用自反性之前，通过对两个对象进行情况拆分就可以解决相干性目标；在代数侧，对象部分直接是 [eq_refl]。
*)
Definition KAlg_Coslice_strict_iso (K : CRng) :
  KAlg K ≅[StrictCat] Coslice CRng K.
Proof.
  unshelve refine (@Build_Isomorphism StrictCat (KAlg K) (Coslice CRng K)
    (KAlg_to_Coslice K) (Coslice_to_KAlg K) _ _).
  - (* to ∘ from ≈ id, on the coslice / 到 ∘ 从 ≈ 恒等映射，在余切片上 *)
    exists (Coslice_KAlg_round_obj K).
    intros x y f.
    destruct x as [[Rx cx] [ux tx]], y as [[Ry cy] [uy ty]].
    destruct tx, ty.
    simpl.
    reflexivity.
  - (* from ∘ to ≈ id, on the algebras; the object component is [eq_refl] / 从 ∘ 到 ≈ id，在代数上；对象分量是 [eq_refl] *)
    exists (fun _ => eq_refl).
    intros A B f; simpl.
    reflexivity.
Defined.

(*
 The two composites, named: each is strictly equal to an identity
 functor.  These are the round trips at FUNCTOR level, the object- and
 hom-level statements above being their components. 

 --------
 这两个复合体，命名为：每个严格等于一个恒等函子。这些是在函子层次的往返跳转，上述对象层和态射层的声明是它们的组成部分。
*)
Definition KAlg_Coslice_to_from (K : CRng) :
  @equiv _ (@homset StrictCat (Coslice CRng K) (Coslice CRng K))
    (@compose StrictCat _ _ _ (KAlg_to_Coslice K) (Coslice_to_KAlg K))
    (@id StrictCat (Coslice CRng K)) :=
  iso_to_from (KAlg_Coslice_strict_iso K).

Definition KAlg_Coslice_from_to (K : CRng) :
  @equiv _ (@homset StrictCat (KAlg K) (KAlg K))
    (@compose StrictCat _ _ _ (Coslice_to_KAlg K) (KAlg_to_Coslice K))
    (@id StrictCat (KAlg K)) :=
  iso_from_to (KAlg_Coslice_strict_iso K).

(*
 The same statement read in [Cat], where functors are compared up to
 natural isomorphism.  This is the WEAKER reading — [≅[Cat]] in this
 library is equivalence of categories — and is recorded because it is
 the form most consumers take. 

 --------
 在[Cat]中阅读相同的陈述，其中函子是按照自然同构进行比较的。这是较弱的读法——在这个库中[≅[Cat]是范畴的等价——并且记录下来是因为这是大多数使用者采用的形式。
*)
Definition KAlg_Coslice_iso (K : CRng) : KAlg K ≅[Cat] Coslice CRng K :=
  @Build_Isomorphism Cat (KAlg K) (Coslice CRng K)
    (KAlg_to_Coslice K) (Coslice_to_KAlg K)
    (strict_equiv_implies_fun_equiv _ _ (KAlg_Coslice_to_from K))
    (strict_equiv_implies_fun_equiv _ _ (KAlg_Coslice_from_to K)).

(* The comma reading, Mac Lane's own shape (K ↓ CRng): compose with [Comma_Coslice] (Construction/Slice.v). At [Cat] strength, because that is where [Comma_Coslice] is stated. / 逗号读取，Mac Lane 自身的形状 (K ↓ CRng)：与 [Comma_Coslice] （Construction/Slice.v）组合。在 [Cat] 强度下，因为 [Comma_Coslice] 就是在那里被声明的。 *)
Definition KAlg_Comma_iso (K : CRng) : KAlg K ≅[Cat] (=(K) ↓ Id) :=
  iso_compose (Comma_Coslice CRng K) (KAlg_Coslice_iso K).

(** ** Witnesses / ** 证人 *)

(* ℤ is a ℤ-algebra by way of the identity structure map. / ℤ 通过恒等结构映射成为一个 ℤ-代数。 *)
Definition Int_KAlg : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng Int_Ring Int_Ring_commutative (@id Rng Int_Ring).

Example Int_KAlg_unit_computes :
  rig_map (kalg_unit Int_KAlg) 3%Z = 3%Z := eq_refl.

(* ℚ is commutative, hence an object of [CRng]... / ℚ 是可交换的，因此是 [CRng] 的一个对象 ... *)
Lemma Q_Ring_commutative : ∀ a b, rig_mul Q_Ring a b ≈ rig_mul Q_Ring b a.
Proof. intros a b; simpl; apply Qmult_comm. Qed.

Definition Q_CRng : CRng := (Q_Ring; Q_Ring_commutative).

(*
 ...and a ℤ-algebra by the inclusion ℤ → ℚ, a genuinely non-identity
 structure map: Instance/Rng.v's [ZtoQ_not_surjective] shows it misses
 1/2, so this algebra is not its own base ring in disguise. 

 --------
 ...并且通过包含 ℤ → ℚ 变成一个 ℤ-代数，一个真正的非恒等结构映射：Instance/Rng.v 的 [ZtoQ_not_surjective] 显示它缺少 1/2，所以这个代数并不是自己伪装的基环。
*)
Definition Q_KAlg : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng Q_Ring Q_Ring_commutative ZtoQ.

Example Q_KAlg_unit_computes :
  rig_map (kalg_unit Q_KAlg) 3%Z = inject_Z 3 := eq_refl.

Corollary Q_KAlg_unit_not_surjective :
  (∀ q : Q, exists z : Z, rig_map (kalg_unit Q_KAlg) z == q)%Q → False.
Proof. exact ZtoQ_not_surjective. Qed.

(* A non-identity morphism of ℤ-algebras: the inclusion itself. / ℤ-代数的非同一态射：包含本身。 *)
Lemma Int_to_Q_triangle : kalg_unit Q_KAlg ≈ ZtoQ ∘ kalg_unit Int_KAlg.
Proof. now rewrite id_right. Qed.

Definition Int_to_Q_KAlg : Int_KAlg ~{KAlg Int_CRng}~> Q_KAlg :=
  (ZtoQ; Int_to_Q_triangle).

(*
 More generally, EVERY commutative ring is a ℤ-algebra, canonically:
 [Rng_Initial_Z] (Instance/Rng.v) makes ℤ initial in [Rng], so the
 structure map is not a choice.  This is the general reason the coslice
 under ℤ is the whole of [CRng] again — a statement not made here. 

 --------
 更一般地说，每一个交换环都是一个 ℤ-代数，这是自然的：
 [Rng_Initial_Z]（Instance/Rng.v）使得 ℤ 在 [Rng] 中成为初始对象，所以结构映射不是一个选择。这是 ℤ 下的余切范畴再次成为整个 [CRng] 的一般原因——这里没有给出这个陈述。
*)
Definition Z_KAlg (A : CRng) : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng (`1 A) (`2 A) (rng_from_Z (`1 A)).

(* ...and canonically means uniquely: any structure map out of ℤ on any ℤ-algebra agrees with the canonical one, by [rng_from_Z_unique]. / ...并且从本体上唯一意味着：从 ℤ 到任何 ℤ-代数的任何结构映射都与 [rng_from_Z_unique] 所述的范式映射一致。 *)
Lemma Z_KAlg_unit_unique (A : KAlgObject Int_CRng) (z : Z) :
  rig_map (kalg_unit A) z ≈ rig_map (kalg_unit (Z_KAlg (kalg_ring A; kalg_comm A))) z.
Proof. apply rng_from_Z_unique. Qed.

(*
 In particular the ℚ witness's chosen structure map IS the canonical one:
 the two descriptions of ℚ as a ℤ-algebra agree.  This is also where
 [Q_CRng] is exercised — [(kalg_ring Q_KAlg; kalg_comm Q_KAlg)] and
 [Q_CRng] are the same pair, so [Z_KAlg_unit_unique] applies at it
 directly. 

 --------
 特别地，ℚ 见证者选择的结构映射就是典型的那个：作为 ℤ-代数，ℚ 的两种描述是一致的。这也是 [Q_CRng] 被使用的地方——[(kalg_ring Q_KAlg; kalg_comm Q_KAlg)] 和 [Q_CRng] 是同一对，所以 [Z_KAlg_unit_unique] 直接应用于它。
*)
Example Q_KAlg_is_canonical (z : Z) :
  rig_map (kalg_unit Q_KAlg) z ≈ rig_map (kalg_unit (Z_KAlg Q_CRng)) z.
Proof. exact (Z_KAlg_unit_unique Q_KAlg z). Qed.

(* The witnesses transport across the comparison, so the coslice is inhabited too, on the nose. / 证人在比较中被传送，所以余切也被占据，就这样。 *)
Example Q_KAlg_in_Coslice :
  fobj[KAlg_to_Coslice Int_CRng] Q_KAlg = ((Q_Ring; Q_Ring_commutative); (ZtoQ; I))
  := eq_refl.
