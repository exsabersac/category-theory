Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(** * Finite products in the category of internal monoids / * 内部幺半群范畴中的有限积 *)

(*
Mac Lane, Categories for the Working Mathematician, 2nd ed., Section VII.3,
   Exercise 1.

   For a monoidal category (B, ⨂, I) with finite products, the category
   Mon(B) of internal monoids and monoid homomorphisms again has finite
   products, carried by the product of the underlying objects: the forgetful
   functor Mon(B) ⟶ B sends them to B's own products ON THE NOSE.

   The multiplication put on x × y is

     μ := (μ_X ∘ (exl ⨂ exl)) △ (μ_Y ∘ (exr ⨂ exr))
                                    : (x × y) ⨂ (x × y) ~> x × y

   and the unit is η := η_X △ η_Y : I ~> x × y.  Note that TWO different
   binary operations on objects occur here and must not be confused: ⨂ is the
   monoidal tensor, in which the monoid laws are stated, and × is the
   categorical product, which is what is being built.  No compatibility
   between the two is assumed, and none is needed.

   The terminal monoid is the terminal object 1 of B, with μ and η the unique
   maps into it; every morphism into 1 is then automatically a homomorphism,
   by [one_unique].

   HYPOTHESES, MEASURED RATHER THAN GUESSED.  The binary half needs
   [Cartesian C] ALONE — no [Terminal C], and no interaction between × and ⨂.
   This mirrors [Class Cartesian] itself, which “axiomatizes the binary
   product; the nullary product (the terminal object 1) is supplied separately
   by [Terminal]” (Structure/Cartesian.v).  The nullary half needs
   [Terminal C] alone and does not mention [Cartesian] at all.  Both halves
   are stated over an ARBITRARY monoidal structure M on C; the cartesian
   monoidal structure [CC_Monoidal] appears only in the final comparison
   section.

   WHAT IS PROVED HERE, IN ORDER

   (1) [Monoid_Product] — the product monoid, over an arbitrary monoidal base.
   (2) [Terminal_Monoid] — the monoid carried by the terminal object.
   (3) [mon_exl_hom], [mon_exr_hom], [mon_fork_hom], [mon_one_hom] — the
       projections, the pairing and the unique map are monoid homomorphisms.
   (4) [Mon_Cartesian] : @Cartesian (Mon C) and [Mon_Terminal] :
       @Terminal (Mon C) — the deliverables.
   (5) [Monoid_of_MonoidObject] / [MonoidObject_of_Monoid] — the passage
       between the two in-tree monoid-object classes, with both round trips,
       and the negative [AbstractBaseProbe] showing it cannot bridge an
       abstract M to [CC_Monoidal].
   (6) [Product_Monoid_as_Monoid] and the comparison with [Product_Monoid]
       (Structure/Monoid.v) at the cartesian monoidal base, with the
       strict form of the multiplication comparison refuted and pinned.
   (7) [Mon_Sets_Cartesian] and [Mon_Sets_Terminal] — the concrete
       instantiation at [Mon Sets], with two further negatives showing that
       [Product_Monoid] would NOT have reached it.

   THE TWO CLASSES NAMED “Monoid”, AND WHY THE PASSAGE IS NOT THE ROUTE TAKEN

   This tree carries two definitions of an internal monoid:

     Theory/Algebra/Monoid.v   Class Monoid (X : C)
                               fields mu, eta, mu_assoc,
                               mu_unit_left, mu_unit_right
     Structure/Monoid.v        Class MonoidObject (mon : C)
                               fields mempty, mappend, mempty_left,
                               mempty_right, mappend_assoc

   They have the same laws with renamed fields in a different order, and
   Structure/Monoid.v additionally declares
   [Definition Monoid := @MonoidObject C CC_Monoidal] — a THIRD spelling,
   which is [MonoidObject] pinned to the cartesian tensor.  A display hazard
   follows, and it is narrower than an earlier draft of this header claimed:
   TWO of the three print alike, not three.  [Check @Monoid] and
   [Check @MonoidObject] both print [∀ C : Category, Monoidal → obj[C] →
   Type] and are indistinguishable by type display; but the [Monoid] alias
   prints [∀ C : Category, Cartesian → Terminal → obj[C] → Type], which is
   VISIBLY DIFFERENT, and [Check @Product_Monoid] even prints its ARGUMENT
   types qualified.  The claim “type display alone cannot tell the three
   apart” was FALSE and is withdrawn: a single [Check] separates the alias.
   What is true, and is the part that actually bites, is that
   [Product_Monoid] prints its CONCLUSION as [MonoidObject (x × y)] with the
   monoidal instance SUPPRESSED — so the conclusion does not reveal which
   tensor it is at.

   [Mon] (Theory/Algebra/Monoid/Hom.v) is built on the FIRST of these.

   Three routes to this issue's deliverable were available.

     (a) Build the passage [MonoidObject x → Monoid x] and route
         [Product_Monoid] through it.
     (b) Prove the product monoid structure directly on the mu/eta class,
         over an arbitrary monoidal base.
     (c) Re-found [Mon] on [MonoidObject].

   Route (b) is taken.  The reason is not taste: [Product_Monoid] concludes
   [@MonoidObject C CC_Monoidal (x × y)], so its tensor IS the categorical
   product.  Routing through it therefore requires the monoidal structure of
   [Mon] to be [CC_Monoidal], which restricts the theorem from “for every
   monoidal B with finite products” to “for B monoidal via its own products” —
   a restriction relative to both Mac Lane's statement and [Mon]'s own
   signature, which quantifies over an arbitrary [M : @Monoidal C].  The
   passage of route (a) does not repair this: it relates the two classes only
   AT A FIXED monoidal base — it is field renaming and cannot change the
   tensor — and the [Fail Check] in [AbstractBaseProbe] below MEASURES that
   the obvious attempt does not typecheck for a variable M.  Read that as a
   measurement at the current definitions; NO impossibility is proved and none
   is claimed.  The restriction is not hypothetical either, and
   section (7) makes that concrete AT THE TREE'S OWN [Mon Sets]: that category
   is [@Mon Sets Sets_Product_Monoidal] (Instance/Roster.v), whose base is
   [Sets]'s hand-built monoidal structure (Instance/Sets.v) and NOT
   [@CC_Monoidal Sets _ _] — the two are pinned as not the same term — so
   [Product_Monoid] does not typecheck as a monoid structure there, which is
   also pinned.  Route (c) would edit a file this issue has
   no licence to touch and would break every existing consumer of [Mon].

   The passage of route (a) is nevertheless BUILT here — it is what
   “reconcile the two definitions” asks for — and it is then used for what it
   can actually do: exhibit [Product_Monoid] as the [CC_Monoidal] special case
   of [Monoid_Product] (section 6).  That comparison is an [≈], not an
   [eq_refl], and the residue is diagnosed below.

   STRENGTHS, MEASURED STRICT-FIRST

   - Both round trips of the class passage close by [eq_refl] on the WHOLE
     record ([monoid_round], [monoid_object_round]): both classes are
     declared under [Set Primitive Projections] (Lib/Foundation.v), so
     record eta holds and rebuilding the five fields returns the original.
   - The forgetful functor's action on the product object and on the terminal
     object is [eq_refl] ([Mon_Forget_product], [Mon_Forget_terminal]), as are
     the underlying morphisms of the projections, the pairing and the unique
     map ([Mon_Forget_exl], [Mon_Forget_exr], [Mon_Forget_fork],
     [Mon_Forget_one]).  So the forgetful functor's agreement with C's own
     finite products is definitional on DATA — Leibniz equalities, not
     isomorphisms and not [≈].  CREATION in the technical sense of
     Structure/Limit/Creation.v is NOT proved and is not claimed; neither is
     preservation stated at cone level.
   - [Monoid_Product]'s unit agrees with [Product_Monoid]'s at [eq_refl]
     ([Monoid_Product_eta_is_Product_Monoid]); its multiplication agrees only
     at [≈] ([Monoid_Product_mu_is_Product_Monoid]), and the [eq_refl] form is
     REFUTED and pinned ([Fail Example Monoid_Product_mu_not_strict]) against
     [Monoid_Product_mu_is_Product_Monoid] as its control — that [≈] form,
     not the unit Example, is what names [mu] and [mappend].
     DIAGNOSIS: the residue is three
     rewrites, none of which is a proof field or an eta gap — the underlying
     MORPHISMS genuinely differ as terms.  [Product_Monoid] writes the
     multiplication as [split μ_X μ_Y ∘ toggle], a fork composed with a
     morphism, where this file writes the fork of the two composites; one
     [fork_comp] distributes that pairing over [toggle], [fork_inv] reduces to
     the two components, and [exl_fork]/[exr_fork] read the two halves of
     [toggle] back.  All four ARE [Qed] corollaries of
     Structure/Cartesian.v, and the shipped proof also spends [comp_assoc], a
     [Category] law rather than a [Cartesian] corollary — so “three rewrites”
     undercounts, and [fork_inv] is [apply]d rather than rewritten.  An
     earlier draft added “so no unfolding converts one side to the other”;
     that is a NON SEQUITUR and is withdrawn — opacity of the LEMMAS used in
     an [≈] proof says nothing about convertibility of the two MORPHISM
     terms.  The terms are non-convertible because one is a fork of
     composites and the other a composite of a fork, an identity holding by
     the product's universal property rather than by computation; it would
     remain non-convertible were [fork_comp] [Defined].
   - Engineering note, RETRACTED in part.  An earlier draft said the
     comparison proof must unfold [bimap] by name because [simpl] does not
     reduce [bimap exl exl] to [split exl exl].  The NECESSITY claim is
     false: [bimap exl exl ≈ split exl exl] closes by bare [reflexivity],
     and the comparison compiles unchanged with [bimap] removed from its
     [unfold] list.  What [simpl] leaves in the goal DISPLAY is untested and
     nothing is claimed about it.

   NEGATIVES.  Four, of two different KINDS kept lexically apart, each
   stripped and its failure kind read off the message.

   - [AbstractBaseProbe] — TYPING.  Stripping the [Fail] reports that
     [Product_Monoid X Y] has type [@MonoidObject C (@CC_Monoidal C _ _)
     (x × y)] where [@MonoidObject C M (x × y)] is wanted.  Control:
     [Product_Monoid_as_Monoid], the same application at M := [CC_Monoidal].
   - [Monoid_Product_mu_not_strict] — CONVERSION.  “cannot unify” between the
     two multiplications.  Control: [Monoid_Product_mu_is_Product_Monoid],
     the [≈] form, which names every constant occurring in the negative.
   - [Sets_Product_Monoidal_is_CC_Monoidal] — CONVERSION.  “cannot unify
     ”Sets_Product_Monoidal“ and ”CC_Monoidal“”.  Controls:
     [Mon_Sets_Cartesian] and [Mon_Sets_Terminal], which name all four of
     [Sets_Product_Monoidal], [Sets_Cartesian], [Sets_Terminal] and [Sets].
   - The unnamed [Fail Check] in [SetsWitness] — TYPING, the [Sets] instance
     of the first negative.  Same controls.

   PROBE HYGIENE, recorded because the first version of the first negative was
   a FALSE PASS and only strip-and-read caught it.  Written INSIDE
   [Section MonProduct], where C and M are section VARIABLES rather than
   parameters, [@Monoid_of_MonoidObject C M (x × y) X] passes C into the
   [x] slot: the command failed with “The term ”C“ has type ”Category“ while
   it is expected to have type ”obj[C]“” — an arity error at an argument
   elaborated before the nominal subject, which says nothing at all about the
   monoidal instance.  The probe is therefore placed AFTER [End MonProduct],
   with its own [Context], where the constant carries all its parameters.

   Rename-simulated over the thirteen constants the four negatives name:
   eleven ([Product_Monoid], [MonoidObject], [CC_Monoidal], [Monoidal], [mu],
   [mappend], [Sets], [Sets_Product_Monoidal], [Sets_Cartesian],
   [Sets_Terminal], [product_obj]) break at a positive command when renamed.
   The other two
   ([Monoid_Product], [Monoid_of_MonoidObject]) are defined in THIS file, so a
   consistent rename is not the threat model; both are consumed by positive
   commands here ([Mon_Cartesian], [monoid_round],
   [Product_Monoid_as_Monoid], [Monoid_Product_mu_is_Product_Monoid]), so
   removing either breaks the build rather than silencing a negative.

   AXIOMS.  All 40 constants of this file — 31 named plus 9 [Program]
   obligations, the latter invisible to a [.glob] sweep and queried by
   fully-qualified name — report “Closed under the global context”.  The
   [Instance/Sets] witnesses of section (7) are included in that count and
   add nothing.

   UNIVERSES.  Measured in the constraint blocks AND read off the binders,
   which is the whole point here: several constants below have a block
   containing only BOUNDS while their binder already carries an
   IDENTIFICATION.  Reading either alone gets it wrong.

   - THE BINDER.  Every constant in this file THAT BINDS A [C] is over
     [C : Category@{u u0 u0}] — C's hom and proof universes are IDENTIFIED.
     (The qualifier matters: [Mon_Sets_Cartesian] and [Mon_Sets_Terminal]
     bind no [C] at all, being at a fixed base.)
     That is INHERITED, from THREE donors independently, and the attribution
     is probed rather than assumed: in a section declaring [Constraint uh <
     up] over [C : Category@{uo uh up}], each of [@Monoidal C], [@Cartesian C]
     and [@Terminal C] is rejected with “Cannot enforce up = uh”, while
     [x ~> y] and [id[x]] are ACCEPTED at those very levels.  So no one of the
     three is “the” cause, nothing in this file adds to it, and it is not
     claimed unavoidable — all three are declared over an unannotated
     [Context {C : Category}], which is the minimization family this tree
     records elsewhere.
   - THE BLOCKS, part one.  [mon_prod_mu@{u u0}], [mon_prod_eta@{u u0}],
     [mon_prod_assoc_leg@{u u0}], [prod_fork_eta@{u u0}],
     [Terminal_Monoid@{u u0}], [mon_one_hom@{u u0}],
     [Monoid_of_MonoidObject@{u u0}] and [MonoidObject_of_Monoid@{u u0}] carry
     ONLY bounds of C's two levels by the [projections] levels of the setoid
     library.  No further identification, and no [Set] anywhere in the file.
   - THE BLOCKS, part two.  [Monoid_Product@{u u0 u1}], [mon_exl_hom],
     [mon_exr_hom], [mon_fork_hom] and the three comparison constants
     ([Product_Monoid_as_Monoid], [Monoid_Product_eta_is_Product_Monoid],
     [Monoid_Product_mu_is_Product_Monoid]) add [u0 < u1] and three
     [prod_rect] bounds.  TWO SEPARATE CAUSES, and an earlier draft of this
     header attributed both to the first: [fork_inv] (Structure/Cartesian.v)
     concludes a TYPE-valued conjunction which the associativity obligation
     destructs, and THAT accounts for the three [prod_rect] bounds ONLY.  The
     strict [u0 < u1] comes from setoid [rewrite] inside a [Program]
     obligation, isolated by rebuilding this file's own shape twice: a
     [Program Definition] whose obligations are discharged by [apply
     mu_assoc] and siblings elaborates at [@{u u0}], while the identical
     definition with [now rewrite mu_assoc] elaborates at [@{u u0 u1}] with
     [u0 < u1].  Which [Morphisms]/[CMorphisms] constant supplies the level is
     NOT identified here.  Either way it is a strict inequality, not an
     identification.  The six [Mon_Forget_*] Examples are [@{u u0 u1 u2}] with
     [u0 < u2], [u <= u1], [u0 <= u1] and three [prod_rect] bounds, and belong
     to neither list above; [mon_prod_mu_exl]/[_exr],
     [mon_prod_eta_exl]/[_exr], [monoid_round] and [monoid_object_round] are
     [@{u u0}] and belong to part one.
   - THE PACKAGING IS NOT FREE, and an earlier draft of this header wrongly
     said it was.  [Mon_Cartesian@{u u0 u1 u2}] concludes
     [Cartesian@{u2 u0}] and [Mon_Terminal@{u u0 u1 u2}] concludes
     [Terminal@{u2 u0}]: a NEW level [u2] carries the objects of [Mon C],
     bounded below by BOTH of C's levels ([u <= u2] and [u0 <= u2]).  The two
     bounds are MEASURED; the natural attribution — an object of [Mon C] is
     the sigma [{ x : C & Monoid x }], whose second component mentions C's
     homs — is an explanation and is not separately probed.  [u2] is
     identified with NEITHER of C's levels; a bound is not an identification,
     so a consumer loses nothing, but the level is real and is recorded.
   - The comparison section instantiates M := [CC_Monoidal], built from
     [InternalProductFunctor].  Measured, it inherits nothing beyond the
     above: the two comparison constants have the same block shape as
     [Monoid_Product], with no [Set] and no new identification.
   - At [Sets] the new level of the previous bullet costs nothing, and that is
     measured rather than assumed: [Mon_Sets_Cartesian@{u u0}] concludes
     [Cartesian@{u0 u}] — the objects of [Mon Sets] sit at [u0], the SAME
     level as [obj[Sets]], because [Sets@{u u0}]'s own [u < u0] already puts
     its objects above its homs, so the two bounds [u <= u2] and [u0 <= u2]
     are satisfied by [u2 := u0].  Still no [Set] and no identification; the
     extra entries in that block ([Basics.compose], [eq_ind], [ID]) are
     Instance/Sets.v's, not this file's.

   NOT DELIVERED, with reasons.

   - No [Cocartesian (Mon C)].  The coproduct of monoids is NOT carried by the
     coproduct of the underlying objects (it is a free product / tensor
     algebra), so nothing here dualises; Structure/Cocartesian.v's own header
     quotes Mac Lane 1950 on exactly this asymmetry.
   - No exponentials, hence no [Closed (Mon C)]; Structure/Monoid.v's
     [Hom_Monoid] puts a monoid on [y ^ x], which is a different statement and
     is not related here.
   - No infinite or indexed products: this matches [Cartesian], which is
     binary.
   - No monoidal structure on [Mon C], and therefore no claim that [Mon C] is
     cartesian MONOIDAL; that would need [CC_Monoidal] at [Mon C] and is not
     assembled.
   - [Mon_Sets_Cartesian] and [Mon_Sets_Terminal] are plain [Definition]s,
     NOT registered [Instance]s, and no other concrete category is
     instantiated ([CMon], [Grp], [Coq] and the rest are untouched).
     Instance/Roster.v is deliberately not required — its [Mon_Sets] is
     [@Mon Sets Sets_Product_Monoidal] by definition, which is what is written
     out here, and requiring it would pull in that file's closure.
   - The class passage is NOT claimed to be an equivalence of CATEGORIES: no
     category of [MonoidObject]s exists in tree, so there is nothing to
     compare [Mon] with, and only the object-level bijection is proved.
   - Nothing is proved about how [Monoid_Product] interacts with the group
     structure of Structure/Group.v; the group case is owned elsewhere.

--------
Mac Lane，《为工作数学家准备的范畴》，第2版，第VII.3节，练习1。

对于具有有限积的单幺范畴 (B, ⨂, I)，其内部幺半群及幺半群同态组成的范畴 Mon(B) 也有有限积，这些积由底层对象的积承载：忘却函子 Mon(B) ⟶ B 将它们精确地映射到 B 自身的积上。

乘法作用在 x × y 上是

μ := (μ_X ∘ (exl ⨂ exl)) △ (μ_Y ∘ (exr ⨂ exr))
                                    : (x × y) ⨂ (x × y) ~> x × y

并且单位是 η := η_X △ η_Y : I ~> x × y。注意，这里出现了两个不同的对象上的二元运算，不应混淆：⨂ 是单体张量，用于说明幺半群定律，而 × 是范畴积，是正在构建的对象。两者之间不假设任何兼容性，也不需要任何兼容性。

终端幺半群是 B 的终端对象 1，μ 和 η 是指向它的唯一映射；根据 [one_unique]，任意指向 1 的态射自动就是一个同态。

假设，经过测量而非猜测。二元部分只需要 [Cartesian C] —— 不需要 [Terminal C]，也不需要 × 和 ⨂ 之间的交互。这反映了 [Class Cartesian] 本身，它“公理化了二元积；零元积（终对象 1）由 [Terminal] 单独提供”（Structure/Cartesian.v）。零元部分只需要 [Terminal C]，并且完全不提及 [Cartesian]。两部分都是在 C 上任意的单体结构 M 下陈述的；笛卡尔单体结构 [CC_Monoidal] 仅出现在最后的比较部分。

这里按顺序证明的是什么

(1) [Monoid_Product] — 在任意单元基础上的乘积幺半群。 
(2) [Terminal_Monoid] — 由终对象承载的幺半群。 
(3) [mon_exl_hom], [mon_exr_hom], [mon_fork_hom], [mon_one_hom] — 投影、配对和唯一映射都是幺半群同态。 
(4) [Mon_Cartesian] : @Cartesian (Mon C) 和 [Mon_Terminal] : @Terminal (Mon C) — 可交付成果。 
(5) [Monoid_of_MonoidObject] / [MonoidObject_of_Monoid] — 在两种树状幺半群对象类之间的传递，包括双向转换，以及负向 [AbstractBaseProbe] 显示它无法桥接抽象 M 到 [CC_Monoidal]。 
(6) [Product_Monoid_as_Monoid] 以及与 [Product_Monoid] (Structure/Monoid.v) 在笛卡尔单元基础上的比较，其中严格形式的乘法比较被驳回并固定。 
(7) [Mon_Sets_Cartesian] 和 [Mon_Sets_Terminal] — 在 [Mon Sets] 上的具体实例化，以及两个进一步的否定显示 [Product_Monoid] 将无法达成它。

被命名为“Monoid”的两个类，以及为什么这段文字不是所采用的路线

这棵树包含内部幺半群的两个定义：

Theory/Algebra/Monoid.v   类 Monoid (X : C)
                               字段 mu, eta, mu_assoc,
                               mu_unit_left, mu_unit_right
     Structure/Monoid.v        类 MonoidObject (mon : C)
                               字段 mempty, mappend, mempty_left,
                               mempty_right, mappend_assoc

它们有相同的定律，只是字段名被重命名并且顺序不同，而 Structure/Monoid.v 另外声明了 [Definition Monoid := @MonoidObject C CC_Monoidal]——第三种拼写方式，它是固定到笛卡尔张量的 [MonoidObject]。随后出现了显示上的问题，并且比该头文件早期草稿所声称的要窄：三者中有两个打印输出相同，而不是三个。[Check @Monoid] 和 [Check @MonoidObject] 都打印 [∀ C : Category, Monoidal → obj[C] → Type]，并且在类型显示上无法区分；但 [Monoid] 别名打印 [∀ C : Category, Cartesian → Terminal → obj[C] → Type]，这在视觉上明显不同，而 [Check @Product_Monoid] 甚至打印其参数类型时带上限定。先前所说的“仅凭类型显示无法区分三者”是错误的，现已撤回：单个 [Check] 就能将别名区分开来。真实情况，并且是实际影响的部分，是 [Product_Monoid] 打印其结论为 [MonoidObject (x × y)]，同时单元实例被抑制——因此结论并不会显示它是哪个张量。

[Mon]（Theory/Algebra/Monoid/Hom.v）是建立在其中的第一个之上的。

有三条路线可以达到本期成果。

(a) 构建通道 [MonoidObject x → Monoid x] 并通过它路由 [Product_Monoid]。
(b) 直接在 mu/eta 类上证明乘积幺半群结构，在任意幺半群基础上。
(c) 在 [MonoidObject] 上重新建立 [Mon]。

采用路线 (b)。原因不是偏好：[Product_Monoid] 得出 [@MonoidObject C CC_Monoidal (x × y)]，因此其张量是范畴乘积。因此通过它进行路由需要 [Mon] 的单体结构为 [CC_Monoidal]，这将定理从“对每个具有有限积的单体 B”限制为“对通过其自身积的 B 单体”——相对于 Mac Lane 的表述以及 [Mon] 自身的形式，这是一个限制，它对任意 [M : @Monoidal C] 进行量化。路线 (a) 的过程不能解决这个问题：它仅在固定单体基上关联这两个类——它只是字段重命名，不能改变张量——而位于 [AbstractBaseProbe] 中的 [Fail Check] 测量表明，对一个变量 M 的明显尝试无法类型检查。按照当前定义将其理解为测量；没有证明任何不可能性，也没有声称存在不可能性。
这种限制也不是假设性的，且第（7）节在树本身的 [Mon Sets] 上使其具体化：该范畴是 [@Mon Sets Sets_Product_Monoidal]（Instance/Roster.v），其基础是 [Sets] 的手工构建的幺半群结构（Instance/Sets.v），而不是 [@CC_Monoidal Sets _ _] —— 这两者已被固定为不同的项 —— 所以 [Product_Monoid] 在那里无法作为幺半群结构进行类型检查，这一点也已固定。方案（c）将编辑一个该问题无权修改的文件，并会破坏 [Mon] 的所有现有使用者。

路线(a)的通道仍然在这里构建——这正是“调和两个定义”所要求的——然后它被用来做它实际能做到的事情：将[Product_Monoid]展示为[Monoid_Product]（第6节）的[CC_Monoidal]特例。那种比较是一个[≈]，而不是一个[eq_refl]，残余部分将在下文中诊断。

优势，严格优先衡量

- 类的往返传递都在整个记录上通过 [eq_refl] 闭合（[monoid_round], [monoid_object_round]）：两个类都在 [Set Primitive Projections]（Lib/Foundation.v）下声明，因此记录 eta 保持不变，重新构建五个字段会返回原值。 - 忘却函子在积对象和终对象上的作用是 [eq_refl]（[Mon_Forget_product], [Mon_Forget_terminal]），投影、配对以及唯一映射的底层态射也同样如此（[Mon_Forget_exl], [Mon_Forget_exr], [Mon_Forget_fork], [Mon_Forget_one]）。因此，忘却函子与 C 自身有限积的一致性在 DATA 上是定义上的 —— 莱布尼茨等式，而不是同构，也不是 [≈]。在 Structure/Limit/Creation.v 的技术意义上，CREATION 未被证明，也未被声明；在锥层面上也没有说明保持性。
- [Monoid_Product]的单元与[Product_Monoid]在[eq_refl]处一致（[Monoid_Product_eta_is_Product_Monoid]）；其乘法仅在[≈]处一致（[Monoid_Product_mu_is_Product_Monoid]），且[eq_refl]形式被驳斥并固定（[Fail Example Monoid_Product_mu_not_strict]）以[Monoid_Product_mu_is_Product_Monoid]作为其控制——正是[≈]形式，而非单元示例，命名了[mu]和[mappend]。诊断：剩余的是三个重写，其中没有一个是证字段或eta空隙——底层映射在作为项时确实不同。[Product_Monoid]将乘法写为[split μ_X μ_Y ∘ toggle]，这是一个与映射组合的分叉，而该文件将两个复合的分叉写出；一个[fork_comp]将该配对分配到[toggle]上，[fork_inv]简化为两个组件，[exl_fork]/[exr_fork]读回[toggle]的两半。
所有四个都是 Structure/Cartesian.v 的 [Qed] 推论，并且附带的证明也使用了 [comp_assoc]，一个 [Category] 定律而不是 [Cartesian] 推论——所以“三个重写”是低估了，而且 [fork_inv] 是 [apply]d 而不是被重写。早期草稿增加了“因此没有展开能将一边转换为另一边”；那是一个逻辑不顺的陈述，已被撤回——在 [≈] 证明中使用的引理的不透明性并不能说明两个 MORPHISM 项的可转换性。这些项不可转换因为一个是组合的分叉，另一个是分叉的组合，这是由乘积的普遍性而非计算保持的恒等；即便 [fork_comp] [Defined]，也仍然不可转换。——工程注释，部分已撤回。
早期的草稿说比较证明必须按名称展开 [bimap]，因为 [simpl] 不会将 [bimap exl exl] 简化为 [split exl exl]。NECESSITY 主张是错误的：[bimap exl exl ≈ split exl exl] 通过裸 [reflexivity] 关闭，并且在将 [bimap] 从其 [unfold] 列表中移除后，比较仍能不变地编译。[simpl] 在目标 DISPLAY 中留下的内容未经测试，也没有任何关于它的主张。

否定。四个，来自两种不同的类型，在词汇上分开，每个都被剥离，并从消息中读取其失败类型。

- [AbstractBaseProbe] — 类型检查。剥离 [Fail] 报告 [Product_Monoid X Y] 的类型为 [@MonoidObject C (@CC_Monoidal C _ _) (x × y)]，而需要的是 [@MonoidObject C M (x × y)]。控制：[Product_Monoid_as_Monoid]，同样在 M := [CC_Monoidal] 处应用。
- [Monoid_Product_mu_not_strict] — 转换。“无法统一” 两个乘法。控制：[Monoid_Product_mu_is_Product_Monoid]，[≈] 形式，它命名了消极式中出现的每一个常量。
- [Sets_Product_Monoidal_is_CC_Monoidal] — 转换。“无法统一 'Sets_Product_Monoidal' 和 'CC_Monoidal'”。控制：[Mon_Sets_Cartesian] 和 [Mon_Sets_Terminal]，它们命名了 [Sets_Product_Monoidal]、[Sets_Cartesian]、[Sets_Terminal] 和 [Sets] 四个。
- [SetsWitness] 中未命名的 [Fail Check] — 类型检查，第一个消极式的 [Sets] 实例。控制相同。

探针卫生，记录是因为第一个版本的第一个否定是一个假通过，只有剥离读取才捕捉到它。写在 [Section MonProduct] 内，其中 C 和 M 是段变量而不是参数，[@Monoid_of_MonoidObject C M (x × y) X] 将 C 传入 [x] 插槽：命令失败，显示“术语 'C' 类型为 'Category'，而预期类型为 'obj[C]'”——这是在名义主体之前展开的参数的元数错误，这与单模实例完全无关。因此探针被放置在 [End MonProduct] 之后，拥有它自己的 [Context]，其中常量携带所有参数。

在十三个常量中对四个负数名称进行模拟重命名：
   十一个（[Product_Monoid], [MonoidObject], [CC_Monoidal], [Monoidal], [mu],
   [mappend], [Sets], [Sets_Product_Monoidal], [Sets_Cartesian],
   [Sets_Terminal], [product_obj]）在重命名时会在正命令处中断。
   另外两个
   （[Monoid_Product], [Monoid_of_MonoidObject]）定义在此文件中，因此一致的重命名不是威胁模型；这两个常量都被这里的正命令（[Mon_Cartesian], [monoid_round],
   [Product_Monoid_as_Monoid], [Monoid_Product_mu_is_Product_Monoid]）使用，因此移除其中任何一个会破坏构建而不是消除负数。

公理。 本文件的所有40个常量——31个有名称的加上9个[Program]义务，后者对于[.glob]扫描是不可见的，并且可以通过完全限定的名称查询——都报告“在全局上下文下封闭”。第(7)节的[Instance/Sets]见证者包含在该计数中，并且不增加任何内容。

宇宙。 在约束块中测量并从绑定器中读取，这正是重点所在：下面的几个常量有一个块只包含界限，而它们的绑定器已经带有标识。单独读取任一者都会出错。

- 绑定器。这个文件中每个绑定 [C] 的常量都绑定在 [C : Category@{u u0 u0}] 上——C 的同构和证明宇宙都是被识别的。（限定符很重要：[Mon_Sets_Cartesian] 和 [Mon_Sets_Terminal] 完全不绑定任何 [C]，因为它们位于固定基上。）这是从三个捐赠者独立继承的，并且归属是被探查的而不是假设的：在一个声明 [Constraint uh < up] 作用于 [C : Category@{uo uh up}] 的部分中，[@Monoidal C]、[@Cartesian C] 和 [@Terminal C] 都被拒绝，显示“无法强制 up = uh”，而 [x ~> y] 和 [id[x] 在同一级别上被接受。所以三者中没有一个是“原因”，这个文件中没有任何内容增加了它，也不声称它是不可避免的——三者都声明在一个未标注的 [Context {C : Category}] 上，这就是这个树在其他地方记录的最小化族。- 块，第一部分。
[mon_prod_mu@{u u0}]、[mon_prod_eta@{u u0}]、
[mon_prod_assoc_leg@{u u0}]、[prod_fork_eta@{u u0}]、
[Terminal_Monoid@{u u0}]、[mon_one_hom@{u u0}]、
[Monoid_of_MonoidObject@{u u0}] 和 [MonoidObject_of_Monoid@{u u0}] 仅由集合库的 [projections] 水平承载 C 的两个层次的界限。没有进一步的标识，文件中也没有 [Set]。- 块，第二部分。[Monoid_Product@{u u0 u1}]、[mon_exl_hom]、
[mon_exr_hom]、[mon_fork_hom] 以及三个比较常数
（[Product_Monoid_as_Monoid]、[Monoid_Product_eta_is_Product_Monoid]、
[Monoid_Product_mu_is_Product_Monoid]）增加了 [u0 < u1] 和三个
[prod_rect] 界限。两个独立的原因，以及此头文件的早期草稿都将两者归因于第一个：[fork_inv]（Structure/Cartesian.v）
得出一个类型值的合取，结合律义务将其析构，而这仅解释了三个 [prod_rect] 界限。
严格的 [u0 < u1] 来自 [Program] 义务中的集合 [rewrite]，通过重建此文件自身的形状两次被隔离：一个其义务通过 [apply mu_assoc] 解除的 [Program Definition] 及其兄弟在 [@{u u0}] 处展开，而与 [now rewrite mu_assoc] 相同的定义在 [@{u u0 u1}] 处展开并带有 [u0 < u1]。哪个 [Morphisms]/[CMorphisms] 常量提供级别在此未确定。无论哪种方式，它是严格不等式，而不是识别。六个 [Mon_Forget_*] 示例是 [@{u u0 u1 u2}]，带有 [u0 < u2]、[u <= u1]、[u0 <= u1] 和三个 [prod_rect] 边界，并且不属于上述任何列表；[mon_prod_mu_exl]/[_exr]、[mon_prod_eta_exl]/[_exr]、[monoid_round] 和 [monoid_object_round] 是 [@{u u0}]，并属于第一部分。
- 包装不是免费的，之前该标题的草稿错误地写成了免费。[Mon_Cartesian@{u u0 u1 u2}] 得出 [Cartesian@{u2 u0}] 和 [Mon_Terminal@{u u0 u1 u2}] 得出 [Terminal@{u2 u0}]：一个新的层级 [u2] 承载 [Mon C] 的对象，下界由 C 的两个层级（[u <= u2] 和 [u0 <= u2]）确定。这两个界限是可测量的；自然归属——[Mon C] 的一个对象是 sigma [{ x : C & Monoid x }]，其第二部分提到 C 的 homs——是一个解释，并没有单独探查。[u2] 与 C 的任何一个层级都不相同；边界并不等同于标识，因此消费者没有损失，但该层级是存在的，并已记录。 - 比较部分实例化 M := [CC_Monoidal]，由 [InternalProductFunctor] 构建。
经过测量，它只继承上述内容：两个比较常数的块形与 [Monoid_Product] 相同，没有 [Set]，也没有新的标识。— 在 [Sets]，前一条目的新级别不产生任何成本，这是经过测量而非假定的：[Mon_Sets_Cartesian@{u u0}] 得出 [Cartesian@{u0 u}] — [Mon Sets] 的对象位于 [u0]，与 [obj[Sets] 处于相同级别，因为 [Sets@{u u0}] 自身的 [u < u0] 已经将其对象置于其 homs 之上，所以 [u <= u2] 和 [u0 <= u2] 这两个边界由 [u2 := u0] 满足。仍然没有 [Set]，也没有标识；该块中的额外条目（[Basics.compose]、[eq_ind]、[ID]）属于 Instance/Sets.v，而不是本文件。

未送达，附原因。

- 没有 [Cocartesian (Mon C)]。幺半群的余积并不由其底层对象的余积承载（它是自由积/张量代数），所以这里没有可对偶化的东西；Structure/Cocartesian.v 文件的头部引用了 Mac Lane 1950 年关于正是这种不对称性的论述。 - 没有指数运算，因此没有 [Closed (Mon C)]；Structure/Monoid.v 的 [Hom_Monoid] 在 [y ^ x] 上放置了一个幺半群，这是一个不同的陈述，与此处无关。 - 没有无限或索引乘积：这与 [Cartesian] 一致，该结构是二元的。 - [Mon C] 上没有幺半群结构，因此也不声称 [Mon C] 是笛卡尔幺半群；那将需要在 [Mon C] 上有 [CC_Monoidal]，并且还未组装完成。
- [Mon_Sets_Cartesian] 和 [Mon_Sets_Terminal] 是普通的 [Definition]，
  并非已注册的 [Instance]，而且没有其他具体范畴被实例化（[CMon]、[Grp]、[Coq] 等保持不变）。Instance/Roster.v 是故意不被要求的——它的 [Mon_Sets] 根据定义是 [@Mon Sets Sets_Product_Monoidal]，这正是这里写下的内容，且要求它会引入该文件的闭包。 
- 并不声称该类通道是 CATEGORIES 的等价关系：在树中不存在任何 [MonoidObject] 范畴，因此没有什么可以用 [Mon] 进行比较，只证明了对象级的双射关系。 
- 未对 [Monoid_Product] 如何与 Structure/Group.v 的群结构交互进行证明；群情况在其他地方处理。
*)

Section MonProduct.

Context {C : Category}.
Context `{M : @Monoidal C}.

(** ** The product monoid / ** 积幺半群 *)

Section Binary.

Context `{CA : @Cartesian C}.

(*
Two morphisms into a product are recovered from their two components: the
   eta law for the product, in the form used repeatedly below.

--------
两个映射到积上的态射可以从它们的两个分量中恢复：积的 eta 定律，以下将多次使用的形式。
*)
Lemma prod_fork_eta {x y z : C} (f : z ~> x × y) :
  (exl ∘ f) △ (exr ∘ f) ≈ f.
Proof. rewrite fork_comp; now rewrite fork_exl_exr, id_left. Qed.

Section Data.

Context {x y : C} (X : Monoid x) (Y : Monoid y).

(*
The componentwise multiplication on x × y: project both tensor factors to
   x, multiply there, and likewise on the y side.

--------
x × y 上的逐分量乘法：将两个张量分量投影到 x，在那里进行相乘，y 侧也是同样处理。
*)
Definition mon_prod_mu : (x × y) ⨂ (x × y) ~> x × y :=
  (mu[X] ∘ bimap exl exl) △ (mu[Y] ∘ bimap exr exr).

(* The componentwise unit. / 分量单位。 *)
Definition mon_prod_eta : I ~> x × y := eta[X] △ eta[Y].

Lemma mon_prod_mu_exl : exl ∘ mon_prod_mu ≈ mu[X] ∘ bimap exl exl.
Proof. unfold mon_prod_mu; apply exl_fork. Qed.

Lemma mon_prod_mu_exr : exr ∘ mon_prod_mu ≈ mu[Y] ∘ bimap exr exr.
Proof. unfold mon_prod_mu; apply exr_fork. Qed.

Lemma mon_prod_eta_exl : exl ∘ mon_prod_eta ≈ eta[X].
Proof. unfold mon_prod_eta; apply exl_fork. Qed.

Lemma mon_prod_eta_exr : exr ∘ mon_prod_eta ≈ eta[Y].
Proof. unfold mon_prod_eta; apply exr_fork. Qed.

(*
Associativity of [mon_prod_mu], one component at a time.  The hypothesis
   [Hp] says exactly that p commutes with the two multiplications; both
   projections satisfy it, by [mon_prod_mu_exl] and [mon_prod_mu_exr].  The
   two sides are each normalised to a common form ending in
   [(p ⨂ p) ⨂ p]; the associator's naturality is what lets the two
   normalisations meet, and the target monoid's own [mu_assoc] closes it.

--------
[mon_prod_mu] 的结合性，一次处理一个分量。假设 [Hp] 完全说明了 p 与两个乘法交换；通过 [mon_prod_mu_exl] 和 [mon_prod_mu_exr]，两个投影都满足它。双方各自归一化为一个以 [(p ⨂ p) ⨂ p] 结尾的共同形式；结合子的自然性使得这两个归一化能够相遇，而目标幺半群自身的 [mu_assoc] 完成了它。
*)
Lemma mon_prod_assoc_leg {z} (Z : Monoid z) (p : x × y ~> z)
      (Hp : p ∘ mon_prod_mu ≈ mu[Z] ∘ bimap p p) :
  p ∘ (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])
    ≈ p ∘ (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu ∘ to tensor_assoc).
Proof.
  assert (HL : p ∘ (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])
                 ≈ mu[Z] ∘ bimap mu[Z] id ∘ bimap (bimap p p) p).
  { rewrite comp_assoc, Hp.
    rewrite <- comp_assoc, <- bimap_comp, Hp, id_right.
    rewrite <- comp_assoc, <- bimap_comp.
    now rewrite id_left. }
  assert (HR : p ∘ (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu
                      ∘ to tensor_assoc)
                 ≈ mu[Z] ∘ bimap id mu[Z] ∘ to tensor_assoc
                     ∘ bimap (bimap p p) p).
  { rewrite !comp_assoc, Hp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (bimap p p)).
    rewrite <- bimap_comp, Hp, id_right.
    assert (Hb : p ⨂ (mu[Z] ∘ p ⨂ p) ≈ id[z] ⨂ mu[Z] ∘ p ⨂ (p ⨂ p))
      by (rewrite <- bimap_comp; now rewrite id_left).
    rewrite Hb, <- comp_assoc.
    now rewrite to_tensor_assoc_natural. }
  rewrite HL, HR.
  now rewrite mu_assoc.
Qed.

(*
The product of two internal monoids.  Declared a plain [Program
   Definition] rather than an [Instance]: registering it would add a
   resolution rule for [Monoid (_ × _)], and [Mon] itself is indexed by this
   class, so leaving the database untouched is the conservative choice (the
   [Hom_Representable] precedent, Functor/Representable.v).

--------
两个内部幺半群的乘积。声明为普通的 [Program Definition] 而不是 [Instance]：注册它会为 [Monoid (_ × _)] 添加一个解析规则，而 [Mon] 本身是按此类索引的，因此保持数据库不变是保守的选择（[Hom_Representable] 先例，Functor/Representable.v）。
*)
Program Definition Monoid_Product : Monoid (x × y) := {|
  mu  := mon_prod_mu;
  eta := mon_prod_eta
|}.
Next Obligation.
  (* associativity / 结合性 *)
  rewrite <- (prod_fork_eta (mon_prod_mu ∘ bimap mon_prod_mu id[x × y])).
  rewrite <- (prod_fork_eta (mon_prod_mu ∘ bimap id[x × y] mon_prod_mu
                               ∘ to tensor_assoc)).
  apply fork_inv; split.
  - apply (mon_prod_assoc_leg X exl mon_prod_mu_exl).
  - apply (mon_prod_assoc_leg Y exr mon_prod_mu_exr).
Qed.
Next Obligation.
  (* left unit / 左单元 *)
  unfold mon_prod_mu, mon_prod_eta.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite exl_fork, exr_fork, !id_right.
  rewrite <- (bimap_id_right_left eta[X] exl).
  rewrite <- (bimap_id_right_left eta[Y] exr).
  rewrite !comp_assoc.
  rewrite mu_unit_left, mu_unit_left.
  rewrite <- !to_unit_left_natural.
  rewrite fork_comp.
  now rewrite fork_exl_exr, id_left.
Qed.
Next Obligation.
  (* right unit / 右单元 *)
  unfold mon_prod_mu, mon_prod_eta.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !bimap_comp.
  rewrite exl_fork, exr_fork, !id_right.
  rewrite <- (bimap_id_left_right eta[X] exl).
  rewrite <- (bimap_id_left_right eta[Y] exr).
  rewrite !comp_assoc.
  rewrite mu_unit_right, mu_unit_right.
  rewrite <- !to_unit_right_natural.
  rewrite fork_comp.
  now rewrite fork_exl_exr, id_left.
Qed.

(* The two projections are monoid homomorphisms. / 这两个投影是幺半群同态。 *)
Lemma mon_exl_hom : MonoidHom Monoid_Product X exl.
Proof. split; [ apply mon_prod_mu_exl | apply mon_prod_eta_exl ]. Qed.

Lemma mon_exr_hom : MonoidHom Monoid_Product Y exr.
Proof. split; [ apply mon_prod_mu_exr | apply mon_prod_eta_exr ]. Qed.

(* The pairing of two monoid homomorphisms is a monoid homomorphism. / 两个幺半群同态的配对是一个幺半群同态。 *)
Lemma mon_fork_hom {z} {Z : Monoid z} {f : z ~> x} {g : z ~> y} :
  MonoidHom Z X f → MonoidHom Z Y g → MonoidHom Z Monoid_Product (f △ g).
Proof.
  intros F G.
  split; simpl.
  - unfold mon_prod_mu.
    rewrite <- fork_comp.
    rewrite <- fork_comp.
    apply fork_inv; split.
    + rewrite <- comp_assoc, <- bimap_comp.
      rewrite !exl_fork.
      apply (@hom_mu _ _ _ _ _ _ _ F).
    + rewrite <- comp_assoc, <- bimap_comp.
      rewrite !exr_fork.
      apply (@hom_mu _ _ _ _ _ _ _ G).
  - unfold mon_prod_eta.
    rewrite <- fork_comp.
    apply fork_inv; split.
    + apply (@hom_eta _ _ _ _ _ _ _ F).
    + apply (@hom_eta _ _ _ _ _ _ _ G).
Qed.

End Data.

(** ** Mon(C) is cartesian / ** Mon(C) 是笛卡尔的 *)

(*
Binary products in Mon(C) from binary products in C.  No terminal object of
   C is used, and no compatibility between × and ⨂.

--------
从 C 中的二元乘积在 Mon(C) 中的二元乘积。未使用 C 的终对象，并且 × 与 ⨂ 之间没有兼容性。
*)
#[export] Program Instance Mon_Cartesian : @Cartesian (Mon C) := {|
  product_obj := fun X Y => (`1 X × `1 Y; Monoid_Product `2 X `2 Y);
  fork := fun _ _ _ f g =>
            (`1 f △ `1 g; mon_fork_hom _ _ `2 f `2 g);
  exl := fun X Y => (exl; mon_exl_hom `2 X `2 Y);
  exr := fun X Y => (exr; mon_exr_hom `2 X `2 Y)
|}.
Next Obligation. proper; now apply fork_respects. Qed.
Next Obligation. apply ump_products. Qed.

End Binary.

(** ** The terminal monoid / ** 终端幺半群 *)

Section Nullary.

Context `{TE : @Terminal C}.

(*
The terminal object carries a unique monoid structure: both structure maps
   land in 1, so [one_unique] discharges all three laws.  No [Cartesian] is
   used here.

--------
终端对象携带一个唯一的幺半群结构：两个结构映射都落在 1 上，所以 [one_unique] 满足所有三条定律。这里没有使用 [Cartesian]。
*)
Program Definition Terminal_Monoid : Monoid (1 : C) := {|
  mu  := one;
  eta := one
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(*
Every morphism into the terminal object is a monoid homomorphism, both
   preservation conditions being equations between morphisms into 1.

--------
每个指向终对象的态射都是一个幺半群同态，这两个保持条件都是指向 1 的态射之间的方程。
*)
Lemma mon_one_hom {x : C} (X : Monoid x) :
  MonoidHom X Terminal_Monoid one.
Proof. split; apply one_unique. Qed.

#[export] Program Instance Mon_Terminal : @Terminal (Mon C) := {|
  terminal_obj := ((1 : C); Terminal_Monoid);
  one := fun X => (one; mon_one_hom `2 X)
|}.
Next Obligation. apply one_unique. Qed.

End Nullary.

(** ** The forgetful functor agrees with C's finite products, on the nose / ** 这个遗忘函子与 C 的有限积完全一致 *)

Section Forget.

Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

(*
The underlying object of a product monoid IS the product of the underlying
   objects, and likewise for the projections, the pairing and the unique map
   into the terminal monoid: all at Leibniz equality, by [eq_refl].  This is
   preservation on DATA; creation in the sense of Structure/Limit/Creation.v
   is not proved and is not claimed.

--------
一个乘积幺半群的底层对象就是底层对象的乘积，投影、配对以及进入终幺半群的唯一映射也是如此：这一切在赖布尼茨等式下成立，由 [eq_refl] 保证。这是在数据上的保持；在 Structure/Limit/Creation.v 的意义上，创建未被证明，也未被声称。
*)
Example Mon_Forget_product (X Y : Mon C) :
  fobj[Mon_Forget] (X × Y) = fobj[Mon_Forget] X × fobj[Mon_Forget] Y
  := eq_refl.

Example Mon_Forget_terminal :
  fobj[Mon_Forget] (@terminal_obj (Mon C) Mon_Terminal) = (1 : C)
  := eq_refl.

Example Mon_Forget_exl (X Y : Mon C) :
  fmap[Mon_Forget] (@exl (Mon C) Mon_Cartesian X Y) = exl := eq_refl.

Example Mon_Forget_exr (X Y : Mon C) :
  fmap[Mon_Forget] (@exr (Mon C) Mon_Cartesian X Y) = exr := eq_refl.

Example Mon_Forget_fork (X Y Z : Mon C) (f : X ~> Y) (g : X ~> Z) :
  fmap[Mon_Forget] (@fork (Mon C) Mon_Cartesian _ _ _ f g)
    = fmap[Mon_Forget] f △ fmap[Mon_Forget] g := eq_refl.

Example Mon_Forget_one (X : Mon C) :
  fmap[Mon_Forget] (@one (Mon C) Mon_Terminal X) = one := eq_refl.

End Forget.

(** ** Reconciling the two monoid-object classes / ** 调和这两个幺半群对象类 *)

(*
At a FIXED monoidal base the two classes differ only by the names and the
   order of their fields, so the passage is field renaming in both
   directions.  This says nothing about the tensor: it cannot turn an
   abstract M into [CC_Monoidal], which is why it is not the route by which
   [Mon_Cartesian] is obtained.

--------
在一个固定的单体基上，这两个类仅在其字段的名称和顺序上有所不同，因此两者之间的转换都是字段重命名。这并不涉及张量：它不能将抽象的 M 转换为 [CC_Monoidal]，这就是为什么它不是获得 [Mon_Cartesian] 的途径。
*)

Definition Monoid_of_MonoidObject {x : C} (X : @MonoidObject C M x)
  : Monoid x := {|
  mu           := @mappend _ _ _ X;
  eta          := @mempty _ _ _ X;
  mu_assoc     := @mappend_assoc _ _ _ X;
  mu_unit_left := @mempty_left _ _ _ X;
  mu_unit_right := @mempty_right _ _ _ X
|}.

Definition MonoidObject_of_Monoid {x : C} (X : Monoid x)
  : @MonoidObject C M x := {|
  mempty        := @eta _ _ _ X;
  mappend       := @mu _ _ _ X;
  mempty_left   := @mu_unit_left _ _ _ X;
  mempty_right  := @mu_unit_right _ _ _ X;
  mappend_assoc := @mu_assoc _ _ _ X
|}.

(*
Both round trips close on the WHOLE record by [eq_refl]: both classes are
   declared under [Set Primitive Projections] (Lib/Foundation.v), so record
   eta identifies a record with the tuple of its own projections.

--------
由 [eq_refl] 完成的整个记录的两次往返：两个类都在 [Set Primitive Projections]（Lib/Foundation.v）下声明，因此记录 eta 使用其自身投影的元组来标识记录。
*)
Example monoid_round {x : C} (X : Monoid x) :
  Monoid_of_MonoidObject (MonoidObject_of_Monoid X) = X := eq_refl.

Example monoid_object_round {x : C} (X : @MonoidObject C M x) :
  MonoidObject_of_Monoid (Monoid_of_MonoidObject X) = X := eq_refl.

(*
THE DESIGN CLAIM, MACHINE-CHECKED RATHER THAN ARGUED.  The passage above
   cannot carry [Product_Monoid] to an abstract monoidal base: its conclusion
   lives at [CC_Monoidal], and for a variable M there is no conversion between
   the two.  Stripping the [Fail] reports

     The term “Product_Monoid X Y” has type
      “@MonoidObject C (@CC_Monoidal C ?H ?H0) (x × y)”
     while it is expected to have type “@MonoidObject C M (x × y)”

   — a TYPING failure at the monoidal instance itself, not at any argument
   elaborated before it.  The positive control is in the comparison section
   below, where the same application at M := [CC_Monoidal] is accepted.

--------
设计声明，机器检查而非辩论。上述段落无法将 [Product_Monoid] 传递到抽象的单子基础：其结论存在于 [CC_Monoidal]，对于变量 M，两者之间没有转换。剥去 [Fail] 报告

“术语 'Product_Monoid X Y' 的类型为
 '@MonoidObject C (@CC_Monoidal C ?H ?H0) (x × y)'
而预期类型为 '@MonoidObject C M (x × y)'

——这是单子实例本身的类型错误，而不是在它之前展开的任何参数的错误。正向控制见下方比较部分，在那里对 M := [CC_Monoidal] 的相同应用被接受。
*)

End MonProduct.

Section AbstractBaseProbe.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

Fail Check
  (fun (x y : C) (X : @MonoidObject C CC_Monoidal x)
       (Y : @MonoidObject C CC_Monoidal y) =>
     @Monoid_of_MonoidObject C M (x × y) (Product_Monoid X Y)).

End AbstractBaseProbe.

(** ** [Product_Monoid] is the cartesian special case / ** [Product_Monoid] 是笛卡尔特殊情况 *)

(*
Instantiating the monoidal base at [CC_Monoidal] — where the tensor IS the
   categorical product — makes [Monoid_Product] and Structure/Monoid.v's
   [Product_Monoid] two constructions of a monoid on the same object.  They
   agree; the unit on the nose, the multiplication up to [≈].

--------
在 [CC_Monoidal] 上实例化单目基 —— 在这里张量就是范畴积 —— 会使得 [Monoid_Product] 和 Structure/Monoid.v 的 [Product_Monoid] 成为同一对象上的两种幺半群构造。它们是一致的；单位是完全一致的，乘法则同 [≈] 一致。
*)

Section Comparison.

Context {C : Category}.
Context `{CA : @Cartesian C}.
Context `{TE : @Terminal C}.

(*
[Structure.Monoid.Monoid x] is by definition [@MonoidObject C CC_Monoidal
   x]; the passage above turns it into this file's [Monoid] at the same
   base.

--------
[Structure.Monoid.Monoid x] 按定义为 [@MonoidObject C CC_Monoidal x]；上面的段落将其转换为本文件中相同基础的 [Monoid]。
*)

Example Monoid_Product_eta_is_Product_Monoid
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @eta C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                          (Monoid_of_MonoidObject X)
                          (Monoid_of_MonoidObject Y))
    = @mempty C CC_Monoidal _ (Product_Monoid X Y)
  := eq_refl.

(*
[Product_Monoid] read as a [Monoid] in this file's sense.  This is what
   “so that [Product_Monoid] applies” amounts to, and it doubles as the
   positive control for the negative in [AbstractBaseProbe] above: the very
   same application, at M := [CC_Monoidal] instead of a variable M, IS
   accepted.

--------
[Product_Monoid] 在这个文件的意义上读作 [Monoid]。这就是“以便 [Product_Monoid] 生效”的含义，它同时也作为上面 [AbstractBaseProbe] 中负例的正向对照：完全相同的应用，当 M := [CC_Monoidal] 而不是变量 M 时，被接受。
*)
Definition Product_Monoid_as_Monoid {x y : C}
           (X : @MonoidObject C CC_Monoidal x)
           (Y : @MonoidObject C CC_Monoidal y)
  : @Monoid C CC_Monoidal (x × y)
  := @Monoid_of_MonoidObject C CC_Monoidal (x × y) (Product_Monoid X Y).

(*
The multiplications are NOT the same term.  Control:
   [Monoid_Product_mu_is_Product_Monoid], immediately below, which names every
   constant occurring in this command.

--------
这些乘法不是相同的项。控制：
   [Monoid_Product_mu_is_Product_Monoid]，在下面，列出了此命令中出现的每个常量的名称。
*)
Fail Example Monoid_Product_mu_not_strict
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @mu C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                         (Monoid_of_MonoidObject X)
                         (Monoid_of_MonoidObject Y))
    = @mappend C CC_Monoidal _ (Product_Monoid X Y)
  := eq_refl.

Lemma Monoid_Product_mu_is_Product_Monoid
        {x y : C} (X : @MonoidObject C CC_Monoidal x)
        (Y : @MonoidObject C CC_Monoidal y) :
  @mu C CC_Monoidal _ (@Monoid_Product C CC_Monoidal CA x y
                         (Monoid_of_MonoidObject X)
                         (Monoid_of_MonoidObject Y))
    ≈ @mappend C CC_Monoidal _ (Product_Monoid X Y).
Proof.
  simpl.
  unfold mon_prod_mu, bimap, toggle, split; simpl.
  rewrite <- fork_comp.
  apply fork_inv; split; rewrite <- comp_assoc.
  - now rewrite exl_fork.
  - now rewrite exr_fork.
Qed.

End Comparison.

(** ** A concrete instantiation, and the design claim made concrete / ** 一个具体的实例，以及具体化的设计主张 *)

(*
[Sets] with the setoid product is a monoidal category (its own hand-built
   [Sets_Product_Monoidal], Instance/Sets.v — NOT [CC_Monoidal]), and it
   is cartesian.  So [Mon Sets] at that base — which is exactly
   Instance/Roster.v's [Mon_Sets], by definition there; that file is not
   required here — inherits finite products.

   This is also where the design argument of the header stops being a pointer
   and becomes an in-tree fact: [Product_Monoid] concludes at [CC_Monoidal
   Sets], and the two monoidal structures on [Sets] are NOT the same term, so
   route (a) would not have reached the tree's own [Mon Sets].

--------
带有集合积的 [Sets] 是一个幺半范畴（它自己手工构建的 [Sets_Product_Monoidal]，Instance/Sets.v — 不是 [CC_Monoidal]），并且它是笛卡尔的。因此在那个基对象上的 [Mon Sets] — 正好是 Instance/Roster.v 中的 [Mon_Sets]，根据那里的定义；这个文件在这里不是必须的 — 继承有限积。

这也是标题的设计论证从指针变为树内事实的地方：[Product_Monoid] 在 [CC_Monoidal Sets] 处结束，并且 [Sets] 上的两种幺半结构不是相同的项，所以路线 (a) 不会达到树自身的 [Mon Sets]。
*)

Section SetsWitness.

Definition Mon_Sets_Cartesian
  : @Cartesian (@Mon Sets Sets_Product_Monoidal)
  := @Mon_Cartesian Sets Sets_Product_Monoidal Sets_Cartesian.

Definition Mon_Sets_Terminal
  : @Terminal (@Mon Sets Sets_Product_Monoidal)
  := @Mon_Terminal Sets Sets_Product_Monoidal Sets_Terminal.

(*
CONVERSION negative: [Sets]'s own monoidal structure is not the cartesian
   monoidal structure built from its products.  Stripping the [Fail] gives
   “cannot unify ”Sets_Product_Monoidal“ and ”CC_Monoidal“”.  Controls: the
   two definitions immediately above, which name both [Sets_Product_Monoidal]
   and [Sets_Cartesian] / [Sets_Terminal].

--------
转换错误：[Sets] 自身的幺半群结构不是由其积构建的笛卡尔幺半群结构。去掉 [Fail] 会得到“无法统一 'Sets_Product_Monoidal' 和 'CC_Monoidal'”。控制：上面紧邻的两个定义，它们命名了 [Sets_Product_Monoidal] 和 [Sets_Cartesian] / [Sets_Terminal]。
*)
(*
Control for the negative below.  Without it, `@CC_Monoidal` applied to
   explicit arguments occurs ONLY inside that `Fail`, so a signature change
   to `CC_Monoidal` would make the command fail for the wrong reason —
   `Illegal application` rather than `cannot unify` — and the guard would go
   vacuously green.  This is the same false-pass mode the section probe
   above records.

--------
控制下面的负值。没有它，`@CC_Monoidal` 对显式参数的应用仅发生在该 `Fail` 内，因此对 `CC_Monoidal` 的签名更改会导致命令因错误的原因失败——是 `Illegal application` 而不是 `cannot unify`——并且保护将无条件显示为绿色。这与上面的段探针记录的假通过模式相同。
*)
Check (@CC_Monoidal Sets Sets_Cartesian Sets_Terminal).

Fail Example Sets_Product_Monoidal_is_CC_Monoidal :
  Sets_Product_Monoidal = @CC_Monoidal Sets Sets_Cartesian Sets_Terminal
  := eq_refl.

(*
TYPING negative: consequently [Product_Monoid] does not supply a monoid
   for [Mon Sets].  Stripping the [Fail] gives “The term ”Product_Monoid X Y“
   has type ”@MonoidObject Sets (@CC_Monoidal Sets _ _) (x × y)“ while it is
   expected to have type ”@MonoidObject Sets Sets_Product_Monoidal (x × y)“”.
   Control: [Product_Monoid_as_Monoid] above, the same application where the
   two bases DO agree.

--------
打字错误 negative：因此 [Product_Monoid] 不为 [Mon Sets] 提供幺半群。去除 [Fail] 得到“术语 'Product_Monoid X Y' 的类型是 '@MonoidObject Sets (@CC_Monoidal Sets _ _) (x × y)'，而期望的类型是 '@MonoidObject Sets Sets_Product_Monoidal (x × y)'”。控制：[Product_Monoid_as_Monoid] 上述，同样的应用场景中两个基确实一致。
*)
Fail Check
  (fun (x y : Sets)
       (X : @MonoidObject Sets CC_Monoidal x)
       (Y : @MonoidObject Sets CC_Monoidal y) =>
     @Monoid_of_MonoidObject Sets Sets_Product_Monoidal
       (@product_obj Sets Sets_Cartesian x y) (Product_Monoid X Y)).

End SetsWitness.

(**
* The universe boundary, PINNED

    The UNIVERSES section of this header attributes C's hom = proof
    identification to three donors, measured under a section declaring the
    levels strictly apart.  An earlier revision REPORTED that measurement
    without pinning it anywhere, so nothing in the build would have noticed
    an upstream annotation changing it.  These are that measurement, as
    guarded negatives with their controls.

    Section-local [Universes]/[Constraint] do not leak: a downstream file
    importing this one can still declare its own levels strictly apart.

--------
* 宇宙边界，已固定

    本标题的 UNIVERSES 部分将 C 的同构 = 证明识别归因于三位捐赠者，该测量在声明级别严格分开的部分下进行。早期的修订报告了该测量，但没有将其固定在任何地方，所以构建中的任何内容都不会注意到上游注释的更改。这些就是该测量，作为受控的负数保护。

    部分本地的 [Universes]/[Constraint] 不会泄露：导入该文件的下游文件仍可以声明其自己的级别严格分开。
*)

Section UniverseDonors.

Universes uo uh up.
Constraint uh < up.

(*
CONTROLS: a hom and an identity of such a category are formable at
   exactly these levels, so the rejections below are about the donors and
   not about the levels themselves.

--------
控制：这种类型的同源和同一性恰好可以在这些层次上形成，因此下面的拒绝是关于供体的，而不是关于层次本身的。
*)
Check (fun (C : Category@{uo uh up}) (x y : C) => x ~> y).
Check (fun (C : Category@{uo uh up}) (x : C) => id[x]).

(*
Controls that the three donor names resolve at unconstrained levels;
   without these a rename would leave the negatives succeeding on a
   reference-not-found error rather than on the universe boundary.

--------
控制三个捐赠者名称在无限制级别上解析；没有这些，重命名将使负值由于引用未找到错误而成功，而不是由于宇宙边界。
*)
Check @Monoidal.
Check @Cartesian.
Check @Terminal.

(* NEGATIVE 1 (FORMABILITY). / 负面 1（可形成性）。 *)
Fail Check (fun (C : Category@{uo uh up}) => @Monoidal C).

(* NEGATIVE 2 (FORMABILITY). / 负面 2（可形成性）。 *)
Fail Check (fun (C : Category@{uo uh up}) => @Cartesian C).

(* NEGATIVE 3 (FORMABILITY). / 负 3（可成形性）。 *)
Fail Check (fun (C : Category@{uo uh up}) => @Terminal C).

End UniverseDonors.
