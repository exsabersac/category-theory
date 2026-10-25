(*
   * * Ab, the category of abelian groups

   Mac Lane treats [Ab] as the running example of a category that is
   "concrete" in the same way [Set] is but carries strictly more algebraic
   structure (Categories for the Working Mathematician, 2nd ed., §I.7,
   printed pp. 24-25 (PDF pp. 34-35), following issue #256's locations).  It
   is the base of homological algebra.  Be careful about the relationship to
   Structure/Abelian.v, in two steps that are easy to run together.  Hom-sets
   carrying abelian-group structure is [Additive] (Structure/Additive.v,
   "each hom-setoid UPGRADES from a commutative monoid to an abelian group"),
   NOT [Preadditive] -- Structure/Preadditive.v is explicit that
   "additive inverses are deliberately not demanded, so the class is precisely
   enrichment in commutative monoids".  And [Class Abelian]
   (Structure/Abelian.v) is not that either: hom-group structure is
   one of its five fields, reached transitively through [abelian_additive],
   alongside kernels, cokernels and normality of monos and epis.  This file
   instantiates NONE of [Preadditive], [Additive] or [Abelian] (see SCOPE),
   so it claims to witness none of them; the [Preadditive] instance has
   since landed as Structure/AbCategory.v's [Ab_Preadditive], alongside
   the Ab-enrichment witness [Ab_AbEnriched].

   Cited by location only: the printed text was not consulted while writing
   this file.  The locations follow issue jwiegley/category-theory#256.

   WHAT IS BUILT ON.  An abelian group is a commutative monoid with additive
   inverses, so the objects EXTEND Instance/CMon.v's [CMonObject] by a
   negation rather than restating the carrier and the four monoid laws.  The
   coercion [ab_cmon :> CMonObject] makes [carrier], [cmon_zero],
   [cmon_plus], [cmon_prop], associativity, commutativity and the unit laws
   available unchanged.  ([cmon_prop] joined that list in the PR "algebraic
   carriers are sets" (2026-09-17), which gave [CMonObject] the field; an
   earlier revision of this sentence enumerated the other six and stopped.)
   The homomorphisms are literally [CMonHom]s: preservation of
   negation is a THEOREM ([ab_map_neg] below), not a field, which is the
   standard fact that a monoid map between groups is automatically a group
   map.

   WHY NOT [Instance/Comp.v].  That file does have group inverses concretely
   -- [inv], [inv_left]/[inv_right], the variety [Group], a [Bool] witness -- so it is NOT true that additive
   inverses are absent from the concrete layer, and this file does not claim
   that.  What is true, and what matters here, is narrower: [Instance/Comp.v]
   is a LEIBNIZ-EQUALITY development.  Its [AlgHom]'s [op_commute] uses [=]
   , its hom-setoid is [∀ x, f x = g x], and it invokes
   [functional_extensionality] and
   [functional_extensionality_dep].  [Ab] lives in the
   setoid-carrier layer with [≈] throughout and no axioms, so [CMon] is the
   donor and [Comp] cannot be.

   THE PROPOSITION.  Mac Lane's §I.7 proposition is that a homomorphism of
   abelian groups is monic exactly when it is injective and epic exactly when
   it is surjective.  Both halves are proved below, constructively.  An
   earlier revision stopped there; since the PR "algebraic carriers are sets"
   (2026-09-17) the epic half concludes PROPOSITIONAL surjectivity
   ([AbPropSurjective]), the split notion [AbSurjective] surviving as the
   hypothesis the direct constructions supply.  [ab_epic_surjective] records
   why.

   WHAT MAKES THE EPIC HALF GO THROUGH: COMMUTATIVITY, and nothing else.  For
   [ab_coset_eq] to be a CONGRUENCE -- for [B/fA] to be an [AbObject] rather
   than a bare setoid, and so usable as a probe object at all -- one must
   commute [f a] past another element.  That is the [cmon_plus_comm] step in
   [AbQuotient]'s [cmon_plus_respects] obligation below.  Where the image need
   not be normal, the corresponding quotient is not an object of the category
   and this probe is simply unavailable.  No constructivity consideration is
   involved.

   A NOTE ON THE COMPARISON WITH [Sets], and on how it changed.  When this
   file was first written, Instance/Sets.v's [surjectivity_is_epic] did not
   enter the environment: its proof was abandoned, because the argument then
   used needed a truth-value object whose carrier is [Type], which does not
   fit as an [obj[Sets]] at the same universe.  That is no longer so.
   Instance/Sets.v now proves it outright, via a cokernel-pair setoid
   ([CKSetoid], [ck_left], [ck_right], [ck_agree]) -- which is to say, by
   exactly the kind of quotient probe used here.

   So there is NO contrast to draw, and none is claimed: [Sets] and [Ab] both
   have "epi iff surjective", and both get it by probing with a quotient.  The
   interest of the construction below is the one thing stated above -- that
   commutativity is what makes [B/fA] an object of the category at all -- not
   any comparative strength.

   WHERE THE NEGATION IS SPENT, stated precisely.  Among the three EQUIVALENCE
   laws of the coset relation, symmetry is the only one that consumes
   inverses: reflexivity needs just [g 0 = 0] and transitivity just
   [g (a + a')], while symmetry turns [x ≈ y + g a] into [y ≈ x + g (-a)]
   using that [g (-a)] inverts [g a].  Inverses are ALSO spent elsewhere in
   the construction -- [AbQuotient]'s [ab_neg_respects] and [ab_neg_left]
   obligations both need them -- so the claim is about the equivalence laws,
   not about the development as a whole. 

   --------
   * * Ab，阿贝尔群的范畴Mac Lane 将 [Ab] 作为一个范畴的运行示例，这个范畴的“具体性”与 [Set] 相同，但携带严格更多的代数结构（《为工作数学家准备的范畴论》，第2版，第 I.7 节，印刷页 24-25（PDF 页 34-35），遵循问题 #256 的位置）。它是同调代数的基础。注意与 Structure/Abelian.v 的关系，可以分两步理解，但容易混在一起。携带阿贝尔群结构的 Hom-集是 [Additive]（Structure/Additive.v，“每个 Hom-集合从一个交换幺半群升级为一个阿贝尔群”），而不是 [Preadditive] — Structure/Preadditive.v 明确指出“刻意不要求加法逆元，因此该类完全是在交换幺半群中的增广”。而  [Class Abelian] 
   （Structure/Abelian.v）也不是：hom-群结构是它的五个字段之一，通过  [abelian_additive]  传递到达，
   还包括核、余核以及单射和满射的正规性。此文件
   并未实例化  [Preadditive] 、  [Additive]  或  [Abelian]  （参见 SCOPE），
   因此它声称未证明它们中的任何一个；  [Preadditive]  实例
   已作为 Structure/AbCategory.v 的  [Ab_Preadditive]  落地，
   同 Ab-enrichment 证明者  [Ab_AbEnriched] 一起。

   仅按位置引用：在编写此文件时未参考印刷文本。位置遵循问题 jwiegley/category-theory#256。建立的基础是什么。阿贝尔群是一个带有加法逆元素的交换幺半群，所以对象通过取负操作扩展了 Instance/CMon.v 的 [CMonObject]，而不是重新陈述载体和四条幺半群定律。类型强制 [ab_cmon :> CMonObject] 使 [carrier]、[cmon_zero]、[cmon_plus]、[cmon_prop]、结合律、交换律和单位律保持不变。([cmon_prop] 在 PR “代数载体是集合” (2026-09-17) 中加入了那个列表，这给了 [CMonObject] 域；该句的早期版本列举了另外六个并停止。) 同态映射实际上是 [CMonHom]：保留取负是一个定理 ([ab_map_neg])，而不是域，这是一个标准事实：群之间的幺半群映射自动就是群映射。为什么不 [Instance/Comp.v]。该文件确实有具体的群逆元素
   -- [inv], [inv_left] / [inv_right], 变体 [Group], 一个 [Bool] 见证 -- 因此说加法逆元素在具体层中不存在是不正确的，而且该文件也没有这么声称。正确的、在这里很重要的是更狭义的：[Instance/Comp.v] 是一个 LEIBNIZ-等式发展。它的 [AlgHom] 的 [op_commute] 使用 [=]，其同态集合是 [∀ x, f x = g x]，并且它调用了 [functional_extensionality] 和 [functional_extensionality_dep]。[Ab] 存在于集合承载层中，整个过程中都具有 [≈] 且没有公理，因此 [CMon] 是捐赠者，而 [Comp] 不能是。命题。Mac Lane 的 §I.7 命题是：阿贝尔群的同态恰好在单射时是单态，恰好在满射时是满态。下文以构造性的方式证明了这两个部分。之前的一个修订只到此为止；自从 PR“代数载体是集合”（2026-09-17）之后，满态部分得出命题性满射（[AbPropSurjective]），分裂概念 [AbSurjective] 作为假设由直接构造提供。[ab_epic_surjective] 记录了原因。使史诗一半能够进行的唯一因素是：交换律，别无其他。为了让 [ab_coset_eq] 成为一个同余关系——为了让 [B/fA] 成为一个 [AbObject] 而不是一个简单的集合，同样可以作为探针对象使用——必须将 [f a] 与另一个元素交换。这就是 [AbQuotient] 在下面 [cmon_plus_respects] 义务中的 [cmon_plus_comm] 步骤。当像不需要是正规像时，相应的商对象不是该范畴的对象，这个探针就不可用。这里不涉及任何构造性考虑。关于与 [Sets] 的比较以及它是如何变化的说明。当此文件首次编写时，Instance/Sets.v 中的 [surjectivity_is_epic] 并未进入环境：它的证明被放弃，因为当时使用的论证需要一个载体为 [Type] 的真值对象，而这无法作为同一类型的 [obj[Sets] 使用。现在情况已不再如此。Instance/Sets.v 现在直接证明了它，通过一个余核对偶集合（ [CKSetoid]、[ck_left]、[ck_right]、[ck_agree] ）——也就是说，通过与这里完全相同类型的商探测方法。所以没有对比可以进行，也没有人声称有对比：[Sets] 和 [Ab] 都具有“epi 当且仅当满射”，并且它们都是通过商映射来探测得到的。下面的构造的趣味性在于上面提到的一件事——交换性使得 [B/fA] 成为该范畴的一个对象——而不是任何比较上的强度。确切地说明否定在哪里被使用。在陪集关系的三个等价律中，只有对称性会消耗逆元：自反性只需要 [g 0 = 0]，传递性只需要 [g (a + a')]，而对称性则利用 [g (-a)] 反转 [g a] 将 [x ≈ y + g a] 变为 [y ≈ x + g (-a)]。在构造的其他地方也会使用逆元——[AbQuotient] 的 [ab_neg_respects] 和 [ab_neg_left] 义务都需要它们——所以该说法是关于等价律的，而不是关于整体发展。
*)

(*
  SCOPE.  Issue #256 also asks for [Ab] as a [Preadditive] instance and for a
  forgetful [Ab ⟶ Grp] alongside [Ab ⟶ Sets].  NEITHER is delivered here.
  [Structure/Preadditive.v]'s instance has since landed as
  Structure/AbCategory.v's [Ab_Preadditive] (with the Ab-enrichment
  [Ab_AbEnriched]);
  [Ab ⟶ Grp] had no target when this file
  was written; the category of groups has since landed
  (Instance/Grp.v) and the inclusion is
  Instance/Grp/Abelianization.v's [Ab_to_Grp].  Only [Ab_Forget :
  Ab ⟶ Sets] is provided here.  

  --------
  范围。Issue #256 还要求将 [Ab] 作为 [Preadditive] 的实例，并要求一个健忘的 [Ab ⟶ Grp] 以及 [Ab ⟶ Sets]。但这里没有提供任何一个。[Structure/Preadditive.v] 的实例后来出现在 Structure/AbCategory.v 的 [Ab_Preadditive]（带有 Ab-enrichment [Ab_AbEnriched]）；当编写此文件时 [Ab ⟶ Grp] 没有目标；群的范畴随后出现在 (Instance/Grp.v)，其包含关系在 Instance/Grp/Abelianization.v 的 [Ab_to_Grp]。这里只提供 [Ab_Forget : Ab ⟶ Sets]。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** ** Objects *)

(*
   * An abelian group: a commutative monoid with a negation that is a
   left inverse.  The right inverse law follows by commutativity
   ([ab_neg_right] below), so it is not a field. 

   --------
   * 阿贝尔群：一个带有负元的交换幺半群，负元是左逆元。右逆律由交换律推导（如下 [ab_neg_right]），所以它不是一个域。
*)
Record AbObject := {
  ab_cmon :> CMonObject;

  ab_neg : carrier (cmon_setoid ab_cmon) → carrier (cmon_setoid ab_cmon);
  ab_neg_respects : Proper (equiv ==> equiv) ab_neg;

  ab_neg_left : ∀ a, cmon_plus ab_cmon (ab_neg a) a ≈ cmon_zero ab_cmon
}.

#[export] Existing Instance ab_neg_respects.

Corollary ab_neg_right (A : AbObject) (a : carrier (cmon_setoid A)) :
  cmon_plus A a (ab_neg A a) ≈ cmon_zero A.
Proof.
  rewrite cmon_plus_comm.
  apply ab_neg_left.
Qed.

(*
   * Cancellation, used repeatedly below.  This is the one property that
   genuinely separates a group from a monoid. 

   --------
   * 取消，下文中反复使用。这是唯一真正将群与幺半群区分开的性质。
*)
Lemma ab_cancel_l (A : AbObject) (a b c : carrier (cmon_setoid A)) :
  cmon_plus A a b ≈ cmon_plus A a c → b ≈ c.
Proof.
  intro H.
  rewrite <- (cmon_plus_zero_l A b), <- (cmon_plus_zero_l A c).
  rewrite <- (ab_neg_left A a).
  rewrite !cmon_plus_assoc.
  now rewrite H.
Qed.

(*
   * Negation is determined: anything acting as a left inverse IS the
   negation.  Needed to show homomorphisms preserve it. 

   --------
   * 否定是确定的：任何作为左逆元的东西就是否定。需要证明同态保持它。
*)
Lemma ab_neg_unique (A : AbObject) (a b : carrier (cmon_setoid A)) :
  cmon_plus A b a ≈ cmon_zero A → b ≈ ab_neg A a.
Proof.
  intro H.
  apply (ab_cancel_l A a).
  rewrite (cmon_plus_comm A a b), H.
  now symmetry; apply ab_neg_right.
Qed.

Lemma ab_neg_zero (A : AbObject) : ab_neg A (cmon_zero A) ≈ cmon_zero A.
Proof.
  symmetry; apply ab_neg_unique.
  apply cmon_plus_zero_l.
Qed.

(*
   * Negation distributes over addition.  This needs commutativity, so it is an
   abelian-group fact rather than a group fact, and it is what makes the
   quotient below respect negation. 

   --------
   * 取反对加法具有分配性。这需要交换律，因此它是阿贝尔群的性质，而不是一般群的性质，这也是下方的商群能够尊重取反的原因。
*)
Lemma ab_neg_plus (A : AbObject) (a b : carrier (cmon_setoid A)) :
  ab_neg A (cmon_plus A a b)
    ≈ cmon_plus A (ab_neg A a) (ab_neg A b).
Proof.
  symmetry; apply ab_neg_unique.
  rewrite cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A b) a b).
  rewrite (cmon_plus_comm A (ab_neg A b) a).
  rewrite (cmon_plus_assoc A a (ab_neg A b) b).
  rewrite ab_neg_left, cmon_plus_zero_r.
  apply ab_neg_left.
Qed.

(** ** Morphisms / **态射 *)

(*
   * A homomorphism of abelian groups is exactly a homomorphism of the
   underlying commutative monoids.  Preservation of negation is derived, not
   demanded -- the standard fact that a monoid map between groups is a group
   map. 

   --------
   * 阿贝尔群的同态恰好是其底层交换幺半群的同态。对取负的保留是推导出来的，而不是要求的——这是一个标准事实：群之间的幺半群映射就是群映射。
*)
Definition AbHom (A B : AbObject) := CMonHom A B.

Lemma ab_map_neg {A B : AbObject} (f : AbHom A B) (a : carrier (cmon_setoid A)) :
  cmon_map f (ab_neg A a) ≈ ab_neg B (cmon_map f a).
Proof.
  apply ab_neg_unique.
  rewrite <- cmon_map_plus.
  rewrite ab_neg_left.
  apply cmon_map_zero.
Qed.

(** ** The category / ** 类别 *)

(*
   * [Ab] is the full subcategory of [CMon] on the objects carrying a negation:
   same homs, same identities, same composition, same hom-setoid.  Stating it
   this way is what makes [ab_map_neg] a theorem rather than a coherence
   obligation. 

   --------
   * [Ab] 是 [CMon] 在携带否定的对象上的完全子范畴：同样的态射、同样的恒等映射、同样的复合、同样的态射集合。这样表述使得 [ab_map_neg] 成为一个定理，而不是一个相容性义务。
*)
(*
   * The universes are pinned by hand, for the reason recorded at
   Instance/CMon.v's [CMon]: once [cmon_prop] is a field the record's sort
   carries a [Set+1] and the elaborator stops identifying the record's own
   sort variable with the category's object universe, which would give [Ab] a
   third, redundant universe and refuse every `Ab@{u o}` annotation in the
   tree for arity.  Measured after the change,
   [Ab@{u p} : Category@{u p p}] with the single new constraint [Set < u]. 

   --------
   * 宇宙是手动固定的，原因记录在 Instance/CMon.v 的 [CMon] ：一旦 [cmon_prop] 是一个字段，记录的类型就带有一个 [Set+1]，并且展开器会停止将记录自身的类型变量与类别的对象宇宙进行识别，这会给 [Ab] 一个第三个多余的宇宙，并拒绝树中所有的 `Ab@{u o}` 的元数注解。经过更改后的测量，[Ab@{u p} : Category@{u p p}] 具有单个新约束 [Set < u] 。
*)
Program Definition Ab@{u p} : Category@{u p p} := {|
  obj     := AbObject@{p p p};
  hom     := AbHom@{p};
  homset  := fun A B => @CMonHom_Setoid@{p} A B;
  id      := fun A => @cmon_hom_id@{p} A;
  compose := fun A B C f g => @cmon_hom_compose@{u p} A B C f g;

  (*
 [compose_respects] is inherited from [CMon] literally.  The remaining four
 laws are NOT: they are [Program] obligations, discharged afresh by the
 file-global [Obligation Tactic] (Lib/Tactics.v's [cat_simpl]).  What is
 true is that no new mathematical content is needed -- [Ab]'s homs,
 identities and composition ARE [CMon]'s -- not that nothing is reproved. 

 --------
 [compose_respects] 字面上继承自 [CMon]。其余四条规律不是：它们是 [Program] 的义务，由文件全局的 [Obligation Tactic]（Lib/Tactics.v 中的 [cat_simpl]）重新履行。真实情况是，不需要新的数学内容——[Ab] 的同态、恒等式和复合就是 [CMon] 的——并不是说没有重新证明任何内容。
*)
  compose_respects := fun A B C => @cmon_hom_compose_respects@{u p} A B C
|}.

(** The forgetful functor to [Sets], through the underlying setoid. / 通过底层集合类到 [Sets] 的忘记函子。 *)
Program Definition Ab_Forget : Ab ⟶ Sets := {|
  fobj := fun A => cmon_setoid (ab_cmon A);
  fmap := fun _ _ f => cmon_map f
|}.

(* * ** The zero group as a zero object / * ** 零群作为零对象 *)

(*
   * The one-element abelian group.  Its negation is forced: there is only one
   element, so [ab_neg] is the constant map and the inverse law is
   [reflexivity]. 

   --------
   * 一元素阿贝尔群。它的负数是强制确定的：因为只有一个元素，所以 [ab_neg] 是恒等映射，逆元律是 [reflexivity]。
*)
Definition Ab_trivial : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := CMon_trivial;
    ab_neg  := fun _ => ttt
  |}.
  - intros x y Hxy; reflexivity.
  - intros a; reflexivity.
Defined.

(** Everything maps to the point, and only one map does. / 一切都对应于该点，而且只有一张映射是这样的。 *)
Definition Ab_one (A : AbObject) : A ~{Ab}~> Ab_trivial := CMon_one A.

Lemma Ab_one_unique (A : AbObject) (f : A ~{Ab}~> Ab_trivial) :
  f ≈ Ab_one A.
Proof. intro a; destruct (cmon_map f a); reflexivity. Qed.

Program Definition Ab_Terminal : @Terminal Ab := {|
  terminal_obj := Ab_trivial;
  one          := Ab_one
|}.
Next Obligation. now rewrite (Ab_one_unique _ f), (Ab_one_unique _ g). Qed.

(*
   * Dually: the unique map OUT of the point sends the point to zero.  This is
   where the group being trivial does the work -- there is nothing to choose. 

   --------
   * 对偶地：从该点出的唯一映射将该点映射到零。这正是群体平凡起作用的地方——没有什么可选择的。
*)
Definition Ab_zero_hom (A : AbObject) : Ab_trivial ~{Ab}~> A :=
  CMon_zero_hom A.

Lemma Ab_zero_hom_unique (A : AbObject) (f : Ab_trivial ~{Ab}~> A) :
  f ≈ Ab_zero_hom A.
Proof.
  intro a; destruct a; simpl.
  now rewrite (cmon_map_zero f).
Qed.

Program Definition Ab_Initial : @Initial Ab := {|
  terminal_obj := Ab_trivial : obj[Ab^op];
  one          := Ab_zero_hom
|}.
Next Obligation.
  (*
 Routed through transitivity at the hom-setoid level rather than by
 [rewrite]: rewriting puts both sides under [cmon_map], where it leaves
 undetermined evars. 

 --------
 通过同态集合等价类层面的传递性进行路由，而不是通过 [rewrite]：重写将双方置于 [cmon_map] 下，在那里它会留下未确定的 evars。
*)
  etransitivity;
    [ apply Ab_zero_hom_unique | symmetry; apply Ab_zero_hom_unique ].
Qed.

(*
   * The same object is both, so the coincidence iso is the identity -- exactly
   as at Instance/CMon/Biproduct.v. 

   --------
   * 同一个对象同时属于两者，因此同构重合就是恒等映射——正如在 Instance/CMon/Biproduct.v 中一样。
*)
#[export] Instance Ab_Zero : ZeroObject Ab :=
  @Build_ZeroObject Ab Ab_Terminal Ab_Initial iso_id.

(* * ** Mac Lane's §I.7 proposition: monic = injective, epic = surjective / * ** 麦克·莱恩 §I.7 命题：单射 = 一一映射，满射 = 到射 *)

Definition AbInjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ x y : carrier (cmon_setoid A), cmon_map f x ≈ cmon_map f y → x ≈ y.

Definition AbSurjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ b : carrier (cmon_setoid B), { a & cmon_map f a ≈ b }.

(*
   * The PROPOSITIONAL surjectivity of the same map: a preimage exists, but is
   not handed back as data.  [AbSurjective] above is the SPLIT notion, whose
   witness IS a section of [f] up to `≈`; this one is the image-theoretic
   notion of ordinary mathematics.  The split notion implies this one
   ([ab_surjective_prop] below) and the converse needs choice, so the two are
   kept apart on purpose: constructions that build a preimage directly keep
   proving [AbSurjective], while [ab_epic_surjective] -- which reads its
   witness out of a quotient, and so out of a [Prop] -- concludes this one. 

   --------
   * 同一个映射的命题满射性：存在原像，但不会作为数据返回。上面的 [AbSurjective] 是分裂（SPLIT）概念，其见证者是 [f] 到 `≈` 的一个截面；这是普通数学中的像理论概念。分裂概念蕴含这个概念（下面的 [ab_surjective_prop]），反之则需要选择，因此两者故意区分开：直接构造原像的构造会一直证明 [AbSurjective]，而 [ab_epic_surjective]——它从一个商中读取其见证者，因此也从 [Prop] 中读取——得出的是这个概念。
*)
Definition AbPropSurjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ b : carrier (cmon_setoid B),
    (exists a : carrier (cmon_setoid A),
       @pequiv _ _ (cmon_prop B) (cmon_map f a) b)%type.

Lemma ab_surjective_prop {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → AbPropSurjective f.
Proof.
  intros Hs b.
  destruct (Hs b) as [a Ha].
  exists a.
  now apply pequiv_from.
Qed.

(* * *** The kernel, used as the probe object for the monic half / * *** 核，作为单项半的探针对象使用 *)

(*
   * A probe object is genuinely needed: monic does not imply injective in an
   arbitrary category.  The kernel is the cheapest one available here --
   unlike the usual textbook probe it needs neither the free abelian group on
   one generator nor any scalar action, only a sub-setoid. 

   --------
   * 实际上需要一个探针对象：在任意范畴中，幺态并不意味着单射。这里的核是可用的最便宜的——不像通常教材中的探针，它既不需要一个生成元上的自由阿贝尔群，也不需要任何标量作用，只需要一个子集集体。
*)

Section Kernel.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_ker_carrier : Type :=
  { a : carrier (cmon_setoid A) & cmon_map f a ≈ cmon_zero B }.

Program Definition ab_ker_setoid : Setoid ab_ker_carrier := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.

Lemma ab_ker_zero_pf : cmon_map f (cmon_zero A) ≈ cmon_zero B.
Proof. apply cmon_map_zero. Qed.

Lemma ab_ker_plus_pf (p q : ab_ker_carrier) :
  cmon_map f (cmon_plus A (projT1 p) (projT1 q)) ≈ cmon_zero B.
Proof.
  rewrite cmon_map_plus, (projT2 p), (projT2 q).
  apply cmon_plus_zero_l.
Qed.

Lemma ab_ker_neg_pf (p : ab_ker_carrier) :
  cmon_map f (ab_neg A (projT1 p)) ≈ cmon_zero B.
Proof.
  rewrite ab_map_neg, (projT2 p).
  apply ab_neg_zero.
Qed.

Definition AbKernel : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := ab_ker_carrier ; is_setoid := ab_ker_setoid |}
       ; cmon_zero := existT _ (cmon_zero A) ab_ker_zero_pf
       ; cmon_plus := fun p q =>
           existT _ (cmon_plus A (projT1 p) (projT1 q)) (ab_ker_plus_pf p q)
       ; cmon_prop :=
           sigma_first_PropEquiv ab_ker_setoid
             (fun _ _ h => h) (fun _ _ h => h) (cmon_prop A) |};
    ab_neg := fun p => existT _ (ab_neg A (projT1 p)) (ab_ker_neg_pf p)
  |}.
  - (* cmon_plus_respects / cmon_plus_respects *)
    intros p p' Hp q q' Hq; simpl in *.
    now rewrite Hp, Hq.
  - (* cmon_plus_assoc / cmon_plus_assoc *)
    intros a b c; simpl; apply cmon_plus_assoc.
  - (* cmon_plus_comm / cmon_plus_comm *)
    intros a b; simpl; apply cmon_plus_comm.
  - (* cmon_plus_zero_l / cmon_plus_zero_l *)
    intros a; simpl; apply cmon_plus_zero_l.
  - (* ab_neg_respects / AB 阴性尊重 *)
    intros p q Hpq; simpl in *; now rewrite Hpq.
  - (* ab_neg_left / AB阴性左 *)
    intros a; simpl; apply ab_neg_left.
Defined.

(*
   * The inclusion of the kernel, and the zero map alongside it.  [f] equalizes
   them, which is the whole point. 

   --------
   * 包含核以及与之一起的零映射。[f] 使它们相等，这正是重点。
*)
Program Definition ab_kernel_incl : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun p : ab_ker_carrier => projT1 p |} |}.

Program Definition ab_kernel_zero : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun _ : ab_ker_carrier => cmon_zero A |} |}.
Next Obligation. symmetry; apply cmon_plus_zero_l. Qed.

End Kernel.

Arguments AbKernel {A B} f.
Arguments ab_kernel_incl {A B} f.
Arguments ab_kernel_zero {A B} f.

(** *** Monic *)

(*
   * Monic implies injective, by probing with the kernel: [f] equalizes the
   inclusion and the zero map, so monic collapses them, so every kernel
   element is zero -- and then [f x ≈ f y] puts [x - y] in the kernel.

   NOTE what this does and does not show.  [x - y] is where THIS proof spends
   the group structure, but the THEOREM does not need it: monic implies
   injective already in [CMon], probing with the free commutative monoid on
   one generator ([nat]) instead of a kernel.  So the kernel is a convenient
   probe here, not a necessary one, and the monic half is NOT a place where
   [Ab] does something [CMon] cannot. 

   --------
   * 单射通过对核进行探测意味着单态：  [f]  使包含映射和零映射相等，因此单态会使它们相等，所以每个核元素都是零 —— 然后  [f x ≈ f y]  将  [x - y]  置于核中。

   注意这显示了什么以及没有显示什么。  [x - y]  是这个证明使用群结构的地方，但定理本身不需要它：在  [CMon]  中单态已经意味着单射，可以用一个生成元的自由交换幺半群（ [nat] ）来探测，而不是用核。因此，核在这里是一个方便的探针，而不是必要的，并且单态部分不是  [Ab]  做  [CMon]  不能做的地方。
*)
Lemma ab_monic_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f → AbInjective f.
Proof.
  intros Hm x y Hxy.
  (* Step 1: monic collapses the two maps out of the kernel. / 步骤 1：monic 将两个映射从核中折叠出来。 *)
  assert (Hk : ∀ p : carrier (cmon_setoid (AbKernel f)),
                 projT1 p ≈ cmon_zero A).
  { apply (@monic _ _ _ f Hm (AbKernel f)
             (ab_kernel_incl f) (ab_kernel_zero f)).
    intro p; simpl.
    rewrite (projT2 p).
    symmetry; apply cmon_map_zero. }
  (* Step 2: x - y lies in the kernel. / 步骤 2：x - y 位于核中。 *)
  assert (Hd : cmon_map f (cmon_plus A x (ab_neg A y)) ≈ cmon_zero B).
  { rewrite cmon_map_plus, ab_map_neg, Hxy.
    apply ab_neg_right. }
  (* Step 3: so x - y is zero, hence x ≈ y. / 第3步：所以 x - y 为零，因此 x ≈ y。 *)
  pose proof (Hk (existT _ (cmon_plus A x (ab_neg A y)) Hd)) as Hz.
  simpl in Hz.
  apply (ab_cancel_l A (ab_neg A y)).
  rewrite (cmon_plus_comm A (ab_neg A y) x) in *.
  rewrite Hz.
  now rewrite (cmon_plus_comm A (ab_neg A y) y), ab_neg_right.
Qed.

Lemma ab_injective_monic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbInjective f → Monic f.
Proof.
  intros Hi.
  constructor; intros Z g h Hgh z.
  apply Hi.
  exact (Hgh z).
Qed.

Theorem ab_monic_iff_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f ↔ AbInjective f.
Proof.
  split; [ apply ab_monic_injective | apply ab_injective_monic ].
Qed.

(* * *** The quotient B/fA, used as the probe object for the epic half / * *** 商 B/fA，用作史诗半部分的探测对象 *)

(*
   * Mac Lane's construction.  The carrier is [B] itself; only the equality
   coarsens, to "differ by something in the image of [f]".

   THE RELATION IS [Prop]-VALUED.  An earlier revision of this paragraph said
   the opposite -- "Note the relation is TYPE-valued -- [{ a & ... }], not
   [∃] -- which is what lets the witness be read back out at the end without
   any choice principle" -- and that is no longer so.  Since the PR "algebraic
   carriers are sets" (2026-09-17) every [AbObject] carries [cmon_prop], the
   property that its `≈` is logically equivalent to a [Prop]-valued relation,
   and a quotient's equality has to be a [Prop] too or the field could not be
   supplied.  So [ab_coset_eq] is Coq's [ex], spelled [(exists a, …)%type]
   because this library's bare [∃] and [exists] are [sigT]
   (Lib/Foundation.v).  The consequence is stated where it bites:
   [ab_epic_surjective] below concludes PROPOSITIONAL surjectivity, and the
   split form [AbSurjective] is no longer derivable from an epi.  Its body
   compares through [pequiv] rather than `≈` for the same reason -- the body
   of an [ex] must itself be a [Prop]. 

   --------
   * Mac Lane 的构造。承载体是 [B] 本身；只是等式被粗化，变为“相差于 [f] 的像中的某个元素”。该关系是 [Prop] 值的。该段落的早期修订版本说的是相反的——“注意该关系是 TYPE 值的——[{ a & ... }]，而不是 [∃]——这正是使证据能够在最后被重新读取而无需任何选择原理的原因”——现在不再是这样。自从 PR “代数载体是集合” (2026-09-17) 以来，每个 [AbObject] 都携带 [cmon_prop]，它的 `≈` 逻辑上等价于一个 [Prop] 值的关系，并且商的相等性也必须是 [Prop]，否则该字段无法提供。因此 [ab_coset_eq] 是 Coq 的 [ex]，拼写为 [(exists a, …)%type]，因为该库的裸 [∃] 和 [exists] 都是 [sigT]（Lib/Foundation.v）。结果在其影响处被陈述：
   [ab_epic_surjective] 下得出命题满射性，而分裂形式 [AbSurjective] 不再可以从满射导出。其主体通过 [pequiv] 进行比较，而不是 `≈`，原因相同——[ex] 的主体本身必须是 [Prop]。
*)

Section Quotient.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_coset_eq (x y : carrier (cmon_setoid B)) : Prop :=
  (exists a : carrier (cmon_setoid A),
     @pequiv _ _ (cmon_prop B) x (cmon_plus B y (cmon_map f a)))%type.

Lemma ab_coset_refl (x : carrier (cmon_setoid B)) : ab_coset_eq x x.
Proof.
  exists (cmon_zero A).
  apply pequiv_from.
  rewrite cmon_map_zero.
  symmetry; apply cmon_plus_zero_r.
Qed.

(*
   * SYMMETRY IS WHERE THE INVERSES ARE SPENT.  From [x ≈ y + f a] one recovers
   [y ≈ x + f (-a)] only because [f (-a)] inverts [f a].  This single step is
   the formal reason the construction works in [Ab] and has no analogue one
   level down in [CMon]. 

   --------
   * 对称性是逆元发生作用的地方。从 [x ≈ y + f a] 可以恢复 [y ≈ x + f (-a)]，仅仅因为 [f (-a)] 反转了 [f a]。这一步骤是构造在 [Ab] 中起作用的正式原因，而在 [CMon] 的下一层没有类似的对应物。
*)
Lemma ab_coset_sym (x y : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y x.
Proof.
  intros [a Ha].
  apply pequiv_to in Ha.
  exists (ab_neg A a).
  apply pequiv_from.
  rewrite ab_map_neg, Ha.
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  symmetry; apply cmon_plus_zero_r.
Qed.

Lemma ab_coset_trans (x y z : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y z → ab_coset_eq x z.
Proof.
  intros [a Ha] [b Hb].
  apply pequiv_to in Ha.
  apply pequiv_to in Hb.
  exists (cmon_plus A b a).
  apply pequiv_from.
  rewrite cmon_map_plus.
  rewrite Ha, Hb.
  now rewrite cmon_plus_assoc.
Qed.

Program Definition ab_coset_setoid : Setoid (carrier (cmon_setoid B)) := {|
  equiv := ab_coset_eq
|}.
Next Obligation.
  constructor.
  - exact ab_coset_refl.
  - exact ab_coset_sym.
  - exact ab_coset_trans.
Qed.

Definition AbQuotient : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := carrier (cmon_setoid B)
                         ; is_setoid := ab_coset_setoid |}
       ; cmon_zero := cmon_zero B
       ; cmon_plus := cmon_plus B
       ; cmon_prop :=
           @PropEquiv_of_relation _ ab_coset_setoid ab_coset_eq
             (fun _ _ h => h) (fun _ _ h => h) |};
    ab_neg := ab_neg B
  |}.
  - (* cmon_plus_respects. [simpl] first: the goal is an application of the [equiv] projection, whose ASCRIBED sort is [Type] ([equiv] lives in [crelation]), and a [Prop] hypothesis may not be destructed into a [Type] goal. Reducing the projection exposes [ab_coset_eq], which is a [Prop], and the elimination is then allowed. Every obligation below needs the same step. / cmon_plus_respects。[simpl] 首先：目标是 [equiv] 投影的一个应用，其归属类型是 [Type] （[equiv] 位于 [crelation] 中），并且 [Prop] 假设不能被分解为 [Type] 目标。简化投影会暴露 [ab_coset_eq]，它是一个 [Prop]，然后就允许进行消除。下面的每个义务都需要相同的步骤。 *)
    intros x x' Hx y y' Hy; simpl in Hx, Hy |- *.
    destruct Hx as [a Ha], Hy as [b Hb].
    apply pequiv_to in Ha.
    apply pequiv_to in Hb.
    exists (cmon_plus A a b).
    apply pequiv_from.
    rewrite cmon_map_plus, Ha, Hb.
    (* (x' + f a) + (y' + f b) ≈ (x' + y') + (f a + f b) / (x' + f a) + (y' + f b) ≈ (x' + y') + (f a + f b) *)
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [ | reflexivity ].
    apply cmon_plus_comm.
  - (* cmon_plus_assoc / cmon_plus_assoc *)
    intros x y z; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_assoc.
  - (* cmon_plus_comm / cmon_plus_comm *)
    intros x y; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_comm.
  - (* cmon_plus_zero_l / cmon_plus_zero_l *)
    intros x; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_zero_l.
  - (* ab_neg_respects / AB 阴性尊重 *)
    intros x y Hxy; simpl in Hxy |- *.
    destruct Hxy as [a Ha].
    apply pequiv_to in Ha.
    exists (ab_neg A a).
    apply pequiv_from.
    rewrite ab_map_neg.
    change (ab_neg B x ≈ cmon_plus B (ab_neg B y) (ab_neg B (cmon_map f a))).
    rewrite <- ab_neg_plus.
    now rewrite Ha.
  - (* ab_neg_left / AB阴性左 *)
    intros x; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply ab_neg_left.
Defined.

(*
   * The projection (identity on carriers, coarser equality) and the zero map.
   [f] equalizes them -- which is exactly the statement that [f a] is
   congruent to zero modulo the image. 

   --------
   * 投影（在载体上是恒等映射，更粗的相等关系）与零映射。  
   [f] 使它们相等 —— 这正是 [f a] 模像同余于零的陈述。
*)
Program Definition ab_quot_proj : B ~{Ab}~> AbQuotient :=
  {| cmon_map := {| morphism := fun b : carrier (cmon_setoid B) => b |} |}.
Next Obligation. intros x y Hxy; simpl; exists (cmon_zero A); apply pequiv_from;
  rewrite cmon_map_zero, cmon_plus_zero_r; exact Hxy. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.

Program Definition ab_quot_zero : B ~{Ab}~> AbQuotient :=
  {| cmon_map :=
       {| morphism := fun _ : carrier (cmon_setoid B) => cmon_zero B |} |}.
Next Obligation. intros x y Hxy; apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation.
  simpl.
  exists (cmon_zero A).
  apply pequiv_from.
  rewrite cmon_map_zero, cmon_plus_zero_r.
  symmetry; apply cmon_plus_zero_l.
Qed.

End Quotient.

Arguments AbQuotient {A B} f.
Arguments ab_quot_proj {A B} f.
Arguments ab_quot_zero {A B} f.

(** *** Epic *)

(*
   * Epic implies PROPOSITIONAL surjectivity, constructively and with no
   double-negation.

   [f] equalizes the projection and the zero map into [B/fA], so an epi
   collapses them -- and [ab_quot_proj ≈ ab_quot_zero] says precisely that
   every [b] is congruent to zero modulo the image, which is to say that a
   preimage EXISTS.

   AN EARLIER REVISION concluded the split [AbSurjective] and said the witness
   "IS the preimage -- read straight back out, with nothing chosen and nothing
   doubly negated".  Since the PR "algebraic carriers are sets" (2026-09-17)
   the coset relation is a [Prop] (see [ab_coset_eq] above), so the witness may
   not be read back out into a [Type]-valued goal and the conclusion is
   [AbPropSurjective].  Nothing is doubly negated and nothing is chosen -- the
   existential is Coq's [ex], not a double negation -- but the preimage is no
   longer data.  Test/ProbeAbPropSurjective.v pins the refusal, with the
   surviving direction ([ab_surjective_prop]) as its positive control.  The
   old reading was an artefact of proof-relevant quotients: in Set, epi implies
   surjective, while surjective implies SPLIT only by choice. 

   --------
   * 史诗（Epic）意味着命题性的满射性，构造性地且不使用双重否定。

   [f] 将投影映射和映射到 [B/fA] 的零映射等同化，所以一个史诗将它们压缩——而 [ab_quot_proj ≈ ab_quot_zero] 正确地说明每个 [b] 在模像下同余于零，也就是说，存在一个原象。早期的修订得出分裂 [AbSurjective] 的结论，并且指出证据“是原像——直接读出，无选择且无双重否定”。自从 PR“代数承载是集合”（2026-09-17）之后，陪集关系是 [Prop]（参见上文 [ab_coset_eq]），因此证据可能无法读回为 [Type] 值的目标，结论为 [AbPropSurjective]。没有任何双重否定，也没有任何选择——存在量词是 Coq 的 [ex]，而不是双重否定——但原像不再是数据。Test/ProbeAbPropSurjective.v 钉住了拒绝，幸存方向（[ab_surjective_prop]）作为其正向控制。旧的读法是基于证明相关商的产物：在 Set 中，满射（epi）意味着 surjective，而 surjective 则仅通过选择意味着 SPLIT。
*)
Lemma ab_epic_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f → AbPropSurjective f.
Proof.
  intros He b.
  assert (Hpq : ab_quot_proj f ≈ ab_quot_zero f).
  { apply (@epic _ _ _ f He (AbQuotient f)
             (ab_quot_proj f) (ab_quot_zero f)).
    intro a; simpl.
    exists a.
    apply pequiv_from.
    rewrite cmon_plus_zero_l.
    reflexivity. }
  specialize (Hpq b); simpl in Hpq.
  destruct Hpq as [a Ha].
  apply pequiv_to in Ha.
  exists a.
  apply pequiv_from.
  rewrite cmon_plus_zero_l in Ha.
  now symmetry.
Qed.

Lemma ab_surjective_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  destruct (Hs b) as [a Ha].
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(*
   * The same implication from the propositional notion.  The target's equation
   is [Type]-valued, so the [Prop] existential may not be destructed into it
   directly; [pequiv_to] puts a [Prop] goal in front of the elimination and
   converts back afterwards.  This is the pattern every consumer of a
   truncated relation follows. 

   --------
   * 同样的含义来自命题概念。目标的方程是 [Type] 值的，因此 [Prop] 存在量化不能直接将其分解；[pequiv_to] 会在消解前放置一个 [Prop] 目标，然后再转换回来。这是每个截断关系的使用者遵循的模式。
*)
Lemma ab_prop_surjective_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbPropSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  apply (@pequiv_to _ _ (cmon_prop Z)).
  destruct (Hs b) as [a Ha].
  apply pequiv_from.
  apply pequiv_to in Ha.
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(*
   * Mac Lane §I.7's proposition, second half.  An earlier revision stated it
   with [AbSurjective] on the right; see [ab_epic_surjective] for why the
   right-hand side is now the propositional notion.  The split notion still
   implies [Epic] ([ab_surjective_epic] above), so no direction is lost -- only
   the shape of the witness the forward direction produces. 

   --------
   * Mac Lane §I.7 命题，下半部分。之前的一个修订版本在右边使用了 [AbSurjective]；参见 [ab_epic_surjective] 了解为什么现在右边是命题概念。分裂概念仍然意味着 [Epic]（上面的 [ab_surjective_epic]），因此没有方向丢失——只是前向方向产生的见证的形状不同。
*)
Theorem ab_epic_iff_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f ↔ AbPropSurjective f.
Proof.
  split; [ apply ab_epic_surjective | apply ab_prop_surjective_epic ].
Qed.

(* * ** The hom-setoids are propositional / * ** 同态集合是命题性的 *)

(*
   * L8: [Ab]'s hom-setoid IS [CMonHom_Setoid] (see [Ab] above), so
   Instance/CMon.v's [CMonHom_PropEquiv] supplies the whole family at once.
   This is what lets a construction that turns an object of an ambient
   category into an abelian group -- [hom_ab] of Adjunction/Additive.v,
   [ehom_ab] of Construction/Enriched/Ab.v -- be instantiated at [Ab] itself
   without a hand-written hypothesis. 

   --------
   * L8:  [Ab] 的同态集合是 [CMonHom_Setoid]（见上文 [Ab]），所以 Instance/CMon.v 的 [CMonHom_PropEquiv] 一次性提供了整个族。这就是为什么一个将环境范畴的对象变为阿贝尔群的构造——Adjunction/Additive.v 的 [hom_ab]、Construction/Enriched/Ab.v 的 [ehom_ab]——可以直接在 [Ab] 上实例化，而无需手写假设。
*)
#[export] Instance Ab_LocallyPropositional : LocallyPropositional Ab.
Proof.
  constructor.
  intros A B.
  exact (@CMonHom_PropEquiv A B).
Defined.
