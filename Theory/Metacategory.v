From Coq Require Import DecidableTypeEx.
From Coq Require Import FMapFacts.
Require Import Category.Lib.FMapExt.
From Coq Require Import PeanoNat.

(* Override ++> notation with the crelation-based version. / 使用基于 crelation 的版本覆盖 ++> 符号。 *)
#[local] Set Warnings "-notation-overridden".
Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** Arrows-only metacategories / 仅箭头的元范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/metacategory
   nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   The single-sorted ("arrows-only") axiomatization of a category, due to
   Mac Lane (Categories for the Working Mathematician, I.1, "arrows-only"
   description). A category is presented purely by a collection of arrows
   together with a partial composition (a partial magma on arrows); there is
   no separate sort of objects. Objects are recovered as the identity arrows.
   Mac Lane's notion of identity is conditional — [u] is an identity when
   [f ∘ u ≈ f] whenever [f ∘ u] is defined, and [u ∘ g ≈ g] whenever [u ∘ g]
   is defined — but the [identity] field below drops both guards and demands
   the two equations for EVERY arrow (see the note there). Two consequences
   are worth stating plainly. First, over a finite table of composable pairs
   that condition cannot be met at all, since it requires an entry [(f, u)]
   for every [f : nat]: no arrow of [ZeroArrows], [OneArrow], [TwoArrows] or
   [ThreeArrows] is an identity in this sense, so each category [FromArrows]
   builds from them — [Three] included — has no objects. Second, the three
   axioms below are NOT shown here to capture exactly a category: neither
   direction is proved, and the third axiom [identity_law] is moreover vacuous
   as written (again, see its note). What [FromArrows] does establish is the
   one direction, that every metacategory in the present sense yields a
   [Category] whose objects are the identity arrows [∃ i, identity M i].
   Theory/Metacategory/General.v carries the axioms over an arbitrary arrow
   type with neither defect, and proves both passages together with the sense
   in which they are mutually inverse.

   This module shows that an "arrows-only" metacategory is sufficient to
   define a category. The axioms defined by Mac Lane are used, with the
   "defined set of composable pairs" and "composite assignments" both encoded
   using a key-value map provided by FMap, since that provides just the
   structure we need: [M.MapsTo (f, g) h pairs] records that the composable
   pair [(f, g)] has composite [h]. Natural numbers are used to differentiate
   arrows.

   Theory/Metacategory/ArrowsOnly.v is a parallel development of the same idea
   over [arrow := N] with a more direct [find]-based composition; it carries
   the polished form of these definitions.

--------
nLab: https://ncatlab.org/nlab/show/metacategory
   nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   范畴的单排序（「仅箭头」）公理化，归于 Mac Lane（《Categories for the Working
   Mathematician》, I.1，「仅箭头」描述）。范畴纯由箭头汇集连同偏复合（箭头上的偏岩浆）
   呈现；没有单独的对象排序。对象恢复为恒等箭头。Mac Lane 的恒等概念是条件性的——
   当 [f ∘ u] 有定义时 [f ∘ u ≈ f]，当 [u ∘ g] 有定义时 [u ∘ g ≈ g]，则 [u] 是恒等——
   但下文 [identity] 字段去掉两道守卫，要求对*每个*箭头成立两方程（见彼处注记）。
   两个后果宜直说。第一，在有限可复合对表上该条件根本无法满足，因它要求对每个
   [f : nat] 有条目 [(f, u)]：[ZeroArrows]、[OneArrow]、[TwoArrows]、[ThreeArrows]
   的箭头在此意义下都不是恒等，故 [FromArrows] 由它们建成的每个范畴——含 [Three]——
   都没有对象。第二，下文三公理*未*在此证明恰好刻画范畴：两方向皆未证，且第三公理
   [identity_law] 按书写还是空虚的（再见图注）。[FromArrows] 确立的是一方向：本意义下
   每个元范畴都产出对象为恒等箭头 [∃ i, identity M i] 的 [Category]。
   Theory/Metacategory/General.v 在任意箭头类型上携带无上述缺陷的公理，并证明两通路
   及它们在何种意义下互逆。

   本模块表明「仅箭头」元范畴足以定义范畴。使用 Mac Lane 的公理，「可复合对的定义集」
   与「复合赋值」都用 FMap 提供的键值映射编码，因它恰提供所需结构：
   [M.MapsTo (f, g) h pairs] 记录可复合对 [(f, g)] 的复合为 [h]。用自然数区分箭头。

   Theory/Metacategory/ArrowsOnly.v 是同一想法在 [arrow := N] 上的平行开发，复合更直接
   基于 [find]；它携带这些定义的打磨形式。
*)

(*
The first-order theory of categories, and its computable models

   nLab: https://ncatlab.org/nlab/show/metacategory
   SEP:  https://plato.stanford.edu/entries/category-theory/
   Paper: Eilenberg, Mac Lane, "General Theory of Natural
          Equivalences", Trans. AMS 58, 1945

   The word "metacategory" carries the point of the whole construction.
   Mac Lane reserves "category" for a metacategory whose objects and
   arrows form sets, and uses "metacategory" for any model of the
   first-order theory of categories, stated before a set theory is fixed.
   It follows that the (large) category Cat of small categories stands
   apart from the metacategory CAT of all categories: the latter is too
   big to be a category, yet it remains a lawful model of the same axioms
   (nLab, "metacategory"). The existing header states the arrows-only
   data and laws; this block records why an objects-free axiomatization
   was wanted, and what the finite encoding here makes computable.

   The idea is present at the origin. Eilenberg and Mac Lane defined a
   category as an "aggregate Ob" of objects with mappings under axioms C1
   through C5, and remarked at once that the objects play a secondary
   role and could be omitted, since axiom C5 attaches a unique object to
   each identity mapping (SEP, "Category Theory"). The later text makes
   this a graded build-up: a metagraph is objects and arrows with domain
   and codomain; a metacategory adds identity and composition under
   associativity and unit laws; a category is a metacategory whose data
   form sets (CWM, I.1). The arrows-only description then sets the object
   sort aside and keeps only arrows, the composable pairs, and their
   composite — the presentation this file follows. Others took the
   set-theoretic route: Grothendieck (1957) and Freyd (1964) defined
   categories through hom-sets, and the metacategory is the first-order
   ancestor those accounts specialize (SEP).

   Two purposes are served. The first is foundational: stating the axioms
   first-order makes "category" meaningful independently of a chosen set
   theory, so that a category is simply a metacategory interpreted in
   sets. This is the entry to Lawvere's elementary programme, in which the
   category of sets and the category of categories are each axiomatized
   directly (Lawvere, "An Elementary Theory of the Category of Sets",
   PNAS 52, 1964; "The Category of Categories as a Foundation for
   Mathematics", 1966). The second purpose is structural: the object sort
   is inessential, since objects ARE the identity arrows. That reduction
   is not left as a remark — [FromArrows] is its machine-checked witness,
   taking the arrow data and the three axioms to a [Category] whose
   objects are the identities [∃ i, identity M i].

   Setting the objects aside leaves an algebra. Composition is a partial
   binary operation, defined exactly when a codomain meets a domain, so a
   category reads as a partial monoid with many units — a partial
   semigroup carrying source and target — of which a one-object category
   is the ordinary total monoid ("Relational Semigroups and Object-Free
   Categories", arXiv:2001.11895, 2020). The file holds this partiality
   as data: [defined f g] records that the pair [(f, g)] has an entry,
   [composite f g h] names its value, and [pairs] is the whole partial
   operation kept as one finite table.

   Because that operation is a single finite datum, small categories are
   literal data and their laws reduce to computation rather than case
   analysis. The witnesses [ZeroArrows], [OneArrow], [TwoArrows] and
   [ThreeArrows] are written as explicit tables of composable pairs;
   [Three] is [FromArrows ThreeArrows]; [cardinality] counts the identity
   arrows, the entries [(i, i)] mapping to [i], and [ThreeArrows_card_3]
   evaluates it to three. The [structure] and [check_structure] tactics
   discharge the membership obligations for these witnesses.
   Theory/Metacategory/DecideExample.v presses the point further,
   settling the associativity coherences over
   Theory/Metacategory/ArrowsOnly.v through the proof-by-reflection
   decider of Lib/MapDecide.v ([map_decide], [solve_map]), over the
   finite-map extension Lib/FMapExt.v ([simplify_maps], [MapsTo_fun]).

   The module stands apart from the working library: nothing in Instance/,
   Construction/ or Structure/ depends on it. It is a self-contained
   witness that the arrows-only axiomatization suffices to rebuild
   [Category], and a place to hold small categories as computable data.
   The name itself has largely fallen out of general use (nLab,
   "metacategory"); the size distinctions it once marked are, in this
   library, carried instead by universe polymorphism.

--------
范畴的一阶理论及其可计算模型

nLab: https://ncatlab.org/nlab/show/metacategory
   SEP:  https://plato.stanford.edu/entries/category-theory/
   论文: Eilenberg, Mac Lane, 《自然等价的一般理论》，美国数学会汇刊 58, 1945

“元范畴”这个词表达了整个构造的要点。  Mac Lane 将“范畴”保留给那些对象和箭头构成集合的元范畴，并将“元范畴”用于任何范畴的一阶理论模型，该理论在固定集合论之前陈述。因此，小范畴的（大）范畴 Cat 与所有范畴的元范畴 CAT 是分开的：后者对于范畴来说太大了，但它仍然是同一公理的合法模型（nLab，“metacategory”）。现有的标题陈述了仅箭头的数据和定律；这一块记录了为何需要无对象的公理化，以及这里的有限编码能够计算的内容。

这个思想自起源之初便已存在。Eilenberg 和 Mac Lane 将一个范畴定义为具有映射的对象“总集（Ob）”，在公理 C1 到 C5 下，并立即指出对象扮演次要角色，可以省略，因为公理 C5 将每个恒等映射唯一地附加到一个对象上（SEP，“范畴论”）。后来的文本将其描述为分级构建：一个元图是具有域和余域的对象和箭头；一个元范畴在结合律和单位律下增加恒等和复合；一个范畴是其数据形成集合的元范畴（CWM, I.1）。仅箭头的描述则将对象范畴搁置，只保留箭头、可复合对及其复合——本文件遵循这种呈现方法。其他人则采用集合论方式：Grothendieck（1957）和 Freyd（1964）通过 Hom 集定义范畴，而元范畴是这些描述专门化的一阶祖先（SEP）。

有两个目的。第一个是基础性的：先以一阶公理来陈述，使“范畴”在不依赖所选集合论的情况下变得有意义，因此范畴仅仅是解释为集合的元范畴。这是Lawvere初等计划的切入点，其中特别集合范畴和范畴范畴各自被直接公理化（Lawvere，《集合范畴的初等理论》，PNAS 52, 1964；《作为数学基础的范畴范畴》，1966）。第二个目的是结构性的：对象类是非本质的，因为对象就是恒等箭头。这个简化并非仅作为注释——[FromArrows] 是其经机器验证的证据，利用箭头数据和三个公理生成一个 [Category]，其对象即是恒等 [∃ i, identity M i]。

将对象放到一边会留下一个代数。组合是一种部分二元运算，仅在一个余域满足一个域时才定义，因此一个范畴可以视为一个具有多个单位的部分幺半群——一个携带源和目标的部分半群——其中一个单对象范畴就是普通的完全幺半群（“Relational Semigroups and Object-Free Categories”，arXiv:2001.11895，2020）。该文件将这种部分性作为数据保存：[defined f g] 记录了 [(f, g)] 这一对有一个条目，[composite f g h] 给出了其值，而 [pairs] 是整个作为一个有限表格保存的部分运算。

因为该操作是一个单一的有限数据，小范畴是字面数据，它们的律归结为计算而不是情况分析。证人 [ZeroArrows]、[OneArrow]、[TwoArrows] 和 [ThreeArrows] 被写成可组合对的显式表；[Three] 等于 [FromArrows ThreeArrows]；[cardinality] 计算恒等箭头、映射到 [i] 的条目 [(i, i)]，并且 [ThreeArrows_card_3] 将其求值为三。[structure] 和 [check_structure] 策略解除这些证人的成员资格义务。 Theory/Metacategory/DecideExample.v 进一步强调了这一点，通过 Lib/MapDecide.v 的反射证明裁决器 ([map_decide], [solve_map]) 解决了 Theory/Metacategory/ArrowsOnly.v 上的结合性一致性问题，以及在有限映射扩展 Lib/FMapExt.v 上 ([simplify_maps], [MapsTo_fun])。

该模块独立于工作库之外：Instance/、Construction/ 或 Structure/ 中没有任何内容依赖它。它是一个自包含的证明，表明仅使用箭头的公理化就足以重建 [Category]，同时也是存放可计算数据的小范畴的地方。这个名称本身现在已基本不再普遍使用（nLab，"元范畴"）；它曾经标示的大小区分，在该库中则由宇宙多态性来表示。
*)

Module PNN := PairUsualDecidableType Nat_as_DT Nat_as_DT.

Module Metacategory (M : WSfun PNN).

Module Import FMapExt := FMapExt PNN M.
Module P := FMapExt.P.
Module F := P.F.

Definition defined x y := M.In (elt:=nat) (x, y).

(*
Mac Lane: "Since the objects of a metacategory correspond exactly to its
   identity arrows, it is technically possible to dispense altogether with the
   objects and deal only with arrows."

--------
麦克莱恩："由于元范畴的对象与其恒等箭头完全对应，从技术上讲，可以完全省略对象，仅处理箭头。"
*)
Record Metacategory := {
  (* "The data for an arrows-only metacategory C consist of arrows," / 只包含箭头的元范畴 C 的数据包括箭头， *)
  arr := nat;

  (* "certain ordered pairs ⟨g, f⟩, called the composable pairs of arrows," / 某些有序对 ⟨g, f⟩，称为箭头的可组合对， *)
  pairs : M.t arr;

  (*
"and an operation assigning to each composable pair ⟨g, f⟩ an arrow g∙f,
     called their composite. We say 'g∙f is defined' for '⟨g, f⟩ is a
     composable pair'".

--------
以及一个操作，将每个可组合对 ⟨g, f⟩ 分配一个箭头 g∙f，称为它们的复合。我们说“g∙f 已定义”表示“⟨g, f⟩ 是一个可组合对”。
*)
  composite (f g h : arr) := M.MapsTo (f, g) h pairs;

  (*
"With these data one defines an identity of C to be an arrow u such that
     f∙u = f whenever the composite f∙u is defined and u∙g = g whenever u∙g is
     defined."

--------
利用这些数据，可以将 C 的恒等元定义为一个箭头 u，使得每当复合 f∙u 定义时，都有 f∙u = f，并且每当 u∙g 定义时，都有 u∙g = g。
*)
  (*
Note: Mac Lane's definition is conditional ("whenever ... defined"). The
     encoding below drops the definedness guard and instead requires
     [composite f u f] (and [composite u g g]) for *every* arrow, i.e. that
     [f ∙ u] and [u ∙ g] are defined and equal to [f]/[g] for all [f]/[g]. This
     is strictly stronger than Mac Lane's notion and is NOT satisfiable over a
     finite table (see the file header: no enumerated arrow is an identity in
     this sense, so [FromArrows] yields the empty category); the [FromArrows]
     obligations below rely on it all the same. The parallel development in
     Theory/Metacategory/ArrowsOnly.v keeps the guard, [defined f u → ...].

--------
注意：Mac Lane 的定义是有条件的（“每当……定义时”）。下面的编码取消了定义性保护，而是要求每一条箭头都满足 [composite f u f]（和 [composite u g g]），即对于所有的 [f]/[g]，[f ∙ u] 和 [u ∙ g] 都被定义并且等于 [f]/[g]。这严格强于 Mac Lane 的概念，并且在有限表上无法满足（参见文件头：没有列举的箭头在此意义下是恒等箭头，因此 [FromArrows] 会产生空范畴）；下面的 [FromArrows] 义务仍依赖于此。Theory/Metacategory/ArrowsOnly.v 中的并行开发保留了该保护，[defined f u → ...]。
*)
  identity (u : arr) :=
    (∀ (f : arr), composite f u f) ∧ (∀ (g : arr), composite u g g);

  (* "The data are then required to satisfy the following three axioms:" / 然后数据需要满足以下三个公理： *)

  (* First axiom: / 第一公理： *)

  (*
"The composite (k∙g)∙f is defined if and only if the composite k∙(g∙f) is
     defined. When either is defined, they are equal (and this triple
     composite is written as k∙g∙f)."

--------
复合 (k∙g)∙f 当且仅当复合 k∙(g∙f) 定义时才定义。当其中任意一个定义时，它们是相等的（这个三重复合记作 k∙g∙f）。
*)
  composition_law (k g f kg gf : arr) :
    composite k g kg ->
    composite g f gf ->
    ∀ kgf, composite kg f kgf ↔ composite k gf kgf;

  (* Second axiom: / 第二条公理： *)

  (*
"The triple composite k∙g∙f is defined whenever both composites k∙g and
     g∙f are defined."

--------
当且仅当复合 k∙g 和 g∙f 都已定义时，三重复合 k∙g∙f 才被定义。
*)
  triple_composition (k g f kg gf : arr) :
    composite k g kg ->
    composite g f gf → (exists kgf : arr, composite kg f kgf)%type;

  (* Third axiom: / 第三公理： *)

  (*
"For each arrow g of C there exist identity arrows u and u' of C such
     that u'∙g and g∙u are defined."

--------
对于 C 的每个箭头 g，存在 C 的单位箭头 u 和 u'，使得 u'∙g 和 g∙u 是定义的。
*)
  (*
jww (TODO): The use of [->] below should be [/\]. The current form is
     vacuously true (any non-identity [u] makes the implication trivially
     hold), so this axiom imposes no real constraint. Substituting [/\] is not
     by itself a repair, and in THIS file even cutting the arrow type down to
     the table's support would not suffice: the [identity] field above drops
     Mac Lane's definedness guards, and under the unguarded reading no arrow
     of the tables below is an identity even restricted to the support -- so
     the conjunctive axiom would have no witnesses to point at. A faithful
     repair here must both restore the guards on [identity] and bound the
     quantifiers, in that order. The
     mistake does not affect [FromArrows], which builds its category from
     [obj := ∃ i, identity M i], not from [identity_law] — though note that
     with the unguarded [identity] above, that object type is empty for every
     example in this file.

--------
jww（待办）：下面使用的 [->] 应该是 [/\]。目前的形式是徒然成立的（任何非同一的 [u] 都会使该蕴涵显然成立），因此这个公理没有施加真正的约束。仅仅代入 [/\] 本身并不是修复，而且在本文件中，即使将箭头类型缩小到表的支撑也不足够：上面的 [identity] 字段去掉了 Mac Lane 定义的存在性保护，并且在没有保护的解释下，下面表中的任何箭头即使限制在支撑上也不是同一箭头——因此合取公理没有可以指向的证据。这里的忠实修复必须同时恢复 [identity] 上的保护并绑定量词，顺序不能颠倒。这个错误不影响 [FromArrows]，它是从 [obj := ∃ i, identity M i] 构建其范畴，而不是从 [identity_law] 构建——不过注意，上面未受保护的 [identity] 会导致在本文件的每个例子中，该对象类型为空。
*)
  identity_law (g : arr) :
    ∃ u,  identity u  ->
    ∃ u', identity u' ->
      defined g u pairs ∧ defined u' g pairs;
}.

Definition composite_defined (M : Metacategory) (f g h : arr M) :
  composite M f g h → defined f g (pairs M) := fun H =>
  proj2 (@in_mapsto_iff _ _ _) (ex_intro _ h H).

Program Definition defined_composite (M : Metacategory) (f g : arr M) :
  defined f g (pairs M) → ∃ h : arr M, composite M f g h.
Proof.
  intro H.
  unfold defined in H.
  destruct (M.find (f, g) (pairs M)) eqn:Heqe.
  - exists n.
    apply (M.find_2 Heqe).
  - apply F.in_find_iff in H.
    contradiction.
Defined.

Lemma identity_morphism (M : Metacategory) (i : arr M) :
  identity M i → composite M i i i.
Proof. intro H; apply H. Qed.

Lemma identity_composition_between (M : Metacategory) :
  ∀ f g u,
    identity M u ->
    defined f u (pairs M) ->
    defined u g (pairs M) ->
    defined f g (pairs M).
Proof.
  intros.
  destruct H as [c c0].
  pose proof (@triple_composition M f u g f g (c f) (c0 g)) as H3;
  simpl in H3.
  destruct H3.
  apply composite_defined with (h:=x).
  exact H.
Defined.

Lemma identity_composition_left (M : Metacategory) :
  ∀ f g fg u,
    identity M u ->
    composite M f g fg ->
    defined u f (pairs M) ->
    defined u fg (pairs M).
Proof.
  intros.
  destruct H as [_ c0].
  apply composite_defined with (h:=fg); auto;
  try solve [ apply c0 ].
Qed.

Lemma identity_composition_right (M : Metacategory) :
  ∀ f g fg u,
    identity M u ->
    composite M f g fg ->
    defined g u (pairs M) ->
    defined fg u (pairs M).
Proof.
  intros.
  destruct H as [c _].
  apply composite_defined with (h:=fg); auto;
  try solve [ apply c ].
Qed.

#[local] Obligation Tactic := intros.

Program Definition FromArrows (M : Metacategory) : Category := {|
  (*
The objects of the category are given by all the identity arrows of the
     arrows-only metacategory.

--------
这个范畴的对象由只含箭头的上范畴的所有恒等箭头给出。
*)
  obj := ∃ i : arr M, identity M i;

  (*
The morphisms of the category from id[x] to id[y] are given by those
     arrows whose domain composes with id[x], and whose codomain composes with
     id[y].

--------
从 id[x] 到 id[y] 的范畴的态射由那些其定义域可以与 id[x] 复合，并且其余域可以与 id[y] 复合的箭头给出。
*)
  hom := fun x y =>
    ∃ f : arr M, defined f ``x (pairs M) ∧ defined ``y f (pairs M);

  homset := fun _ _ => {| Setoid.equiv := fun f g => `1 f = `1 g |}
|}.
Next Obligation.
  equivalence; simpl in *; subst; reflexivity.
Qed.
Next Obligation.                (* id *)
  destruct x as [i [Hil Hir]].
  exists i.
  split; apply composite_defined with (h:=i); auto;
  try solve [ apply Hil
            | apply Hir ].
Defined.
Next Obligation.                (* compose / 撰写 *)
  destruct x as [x x_id];
  destruct y as [y y_id];
  destruct z as [z z_id];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]]; simpl in *.
  pose proof (identity_composition_between M f g y y_id fl gr).
  destruct (defined_composite _ _ _ H) as [fg Hfg].
  exists fg; split.
  - eapply identity_composition_right; eauto.
  - eapply identity_composition_left; eauto.
Defined.
Next Obligation.
  proper.
  unfold FromArrows_obligation_3; simpl in *; subst.
  destruct (defined_composite _ _ _); reflexivity.
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x, y, f, i as [c c0], i0 as [c1 c2], p; simpl in *; subst.
  destruct (defined_composite _ _ _) as [x2 c3].
  pose proof (c2 x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x, y, f, i as [c c0], i0 as [c1 c2], p; simpl in *; subst.
  destruct (defined_composite _ _ _) as [x2 c3].
  pose proof (c x1).
  unfold composite in c3, H.
  apply (FMapExt.F.MapsTo_fun c3 H).
Qed.
Next Obligation.
  unfold FromArrows_obligation_3; simpl.
  destruct x as [x [xl_id xr_id]];
  destruct y as [y [yl_id yr_id]];
  destruct z as [z [zl_id zr_id]];
  destruct w as [w [wl_id wr_id]];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]];
  destruct h as [h [hl hr]];
  simpl in *.
  repeat destruct (defined_composite _ _ _).
  unfold composite in *.
  pose proof (fst (composition_law M f g h x2 x0 c1 c x3) c2).
  simpl in H.
  apply (FMapExt.F.MapsTo_fun c0 H).
Qed.
Next Obligation.
  symmetry.
  unfold FromArrows_obligation_3; simpl.
  destruct x as [x [xl_id xr_id]];
  destruct y as [y [yl_id yr_id]];
  destruct z as [z [zl_id zr_id]];
  destruct w as [w [wl_id wr_id]];
  destruct f as [f [fl fr]];
  destruct g as [g [gl gr]];
  destruct h as [h [hl hr]];
  simpl in *.
  repeat destruct (defined_composite _ _ _).
  unfold composite in *.
  pose proof (fst (composition_law M f g h x2 x0 c1 c x3) c2).
  simpl in H.
  apply (FMapExt.F.MapsTo_fun c0 H).
Qed.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac structure :=
  simpl in *;
  repeat (
    match goal with
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H; subst
    | [ |- ?X = ?Y → False ] =>
      let H := fresh "H" in
      intro H; inversion H; tauto
    | [ H : M.MapsTo _ _ _ |- _ ] => simplify_maps
    | [ |- M.MapsTo _ _ _ ] => simplify_maps
    | [ |- _ ↔ _ ] => split; intros
    | [ |- _ /\ _ ] => split
    | [ |- _ \/ _ ] => solve [ left; structure | right; structure ]
    end; intuition idtac; try congruence).

Ltac check_structure :=
  first [ unfold defined;
          repeat (unshelve eexists; try assumption; intros []);
          split; apply in_mapsto_iff;
          eexists; intuition
        | unshelve (structure; eexists; structure); exact 0%nat
        | structure ].

#[local] Obligation Tactic := program_simpl; check_structure.

Program Definition ZeroArrows : Metacategory := {|
  pairs := [map]
|}.

Program Definition OneArrow : Metacategory := {|
  pairs := [map (0, 0) +=> 0 ]%nat
|}.

Program Definition TwoArrows : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1

           ;    (0, 2) +=> 2
           ;    (2, 1) +=> 2 ]%nat
|}.

Program Definition ThreeArrows : Metacategory := {|
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (2, 2) +=> 2

           ;    (0, 3) +=> 3
           ;    (3, 1) +=> 3

           ;    (1, 4) +=> 4
           ;    (4, 2) +=> 4

           ;    (3, 4) +=> 5

           ;    (0, 5) +=> 5
           ;    (5, 2) +=> 5 ]%nat
|}.

Definition Three : Category := FromArrows ThreeArrows.

Definition cardinality (M : Metacategory) : nat :=
  M.cardinal (P.filter (fun '(dom, cod) v =>
                          ((dom =? v)%nat && (cod =? v)%nat)%bool)
                       (pairs M)).

Lemma elements_filter {elt} (m : M.t elt) (P : M.key → elt → bool) :
  M.elements (P.filter P m)
    = filter (fun p => P (fst p) (snd p)) (M.elements m).
Proof.
  unfold P.filter.
  apply P.fold_rec; intros.
  - rewrite (proj1 (P.elements_Empty m0) H); simpl.
    apply P.elements_empty.
  - destruct (P k e) eqn:Heqe.
    + apply add_equal_iff in H1.
Abort.

Lemma length_elements_filter {elt} (m : M.t elt) k v (P : M.key * elt → bool) :
  length (filter P (M.elements (M.add k v m)))
    = length (filter P ((k, v) :: M.elements m)).
Proof.
Abort.

Theorem elements_rect {elt} (P : list (M.key * elt) → Type) :
  (∀ m1 m2, M.Equal m1 m2 → P (M.elements m1) → P (M.elements m2))
  → ∀ m k v, P ((k, v) :: M.elements m) → P (M.elements (M.add k v m)).
Proof.
Abort.

(*
jww (2017-06-10): This needs automation. A computational tactic that
   reflects on map structures would be valuable here, since we are computing
   on known results.

--------
jww (2017-06-10)：这需要自动化。一种能够反映映射结构的计算策略在这里会很有价值，因为我们正在对已知结果进行计算。
*)
Lemma ThreeArrows_card_3 : cardinality ThreeArrows = 3%nat.
Proof.
  (* unfold cardinality; simpl. / 展开基数；简化 *)
  (* rewrite M.cardinal_1. / 重写 M.cardinal_1。 *)
  (* rewrite elements_filter. / 重写 elements_filter。 *)
  (* apply elements_rect; simpl; intros. / 应用 elements_rect；简化；引入。 *)
  assert (P.transpose_neqkey
            M.Equal
            (λ (k : M.key) (e : nat) (m : M.t nat),
             if (let '(dom, cod) := k in
                 λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
             then k +=> e m
             else m)). {
    intros ??????.
    destruct k, k'.
    assert (n ≠ n1 \/ n0 ≠ n2). {
      destruct (Nat.eq_dec n n1); subst.
      - right; congruence.
      - left; assumption.
    }
    destruct ((n =? e)%nat && (n0 =? e)%nat) eqn:Heqe.
    - apply andb_true_iff in Heqe.
      destruct Heqe.
      apply Nat.eqb_eq in H1.
      apply Nat.eqb_eq in H2.
      subst.
      destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
      * apply andb_true_iff in Heqe2.
        destruct Heqe2.
        apply Nat.eqb_eq in H1.
        apply Nat.eqb_eq in H2.
        subst.
        apply add_associative.
        intros; congruence.
      * reflexivity.
    - destruct ((n1 =? e')%nat && (n2 =? e')%nat) eqn:Heqe2.
      * apply andb_true_iff in Heqe2.
        destruct Heqe2.
        apply Nat.eqb_eq in H1.
        apply Nat.eqb_eq in H2.
        subst.
        reflexivity.
      * reflexivity.
  }

  assert (Proper (eq ==> eq ==> M.Equal ==> M.Equal)
                 (λ (k : M.key) (e : nat) (m : M.t nat),
                  if (let '(dom, cod) := k in
                      λ v : nat, (dom =? v)%nat && (cod =? v)%nat) e
                  then k +=> e m
                  else m)). {
    intros ?????????.
    destruct x, y; subst.
    inversion H0; clear H0; subst.
    destruct ((n1 =? y0)%nat && (n2 =? y0)%nat) eqn:Heqe.
    - apply andb_true_iff in Heqe.
      destruct Heqe.
      apply Nat.eqb_eq in H0.
      apply Nat.eqb_eq in H1.
      subst.
      rewrite H2; reflexivity.
    - assumption.
  }

  unfold cardinality; simpl.
  unfold P.filter; simpl.
  repeat (rewrite P.fold_add; eauto; relational; simpl);
  try (apply not_in_mapsto_iff; intros;
       repeat (unfold not; intros; simplify_maps; try congruence)).
  rewrite P.fold_Empty; auto; [| apply M.empty_1 ].

  assert (P.transpose_neqkey eq (λ (_ : M.key) (_ : nat), S)) by proper.

  rewrite P.cardinal_fold.
  repeat (rewrite P.fold_add; eauto; relational; simpl);
  try (apply not_in_mapsto_iff; intros;
       repeat (unfold not; intros; simplify_maps; try congruence)).
  rewrite P.fold_Empty; auto; apply M.empty_1.
Qed.

(* Definition objects_of (M : Metacategory) : / 定义 objects_of (M : 元范畴) : *)
(*   ∀ P : nat → Type, P 0%nat → (∀ n : nat, P n → P (S n)) → ∀ n : nat, P n / ∀ P : nat → 类型, P 0%nat → (∀ n : nat, P n → P (S n)) → ∀ n : nat, P n *)

#[local] Obligation Tactic := program_simpl.

(*
Program Definition FromThree {C : Category} (c : C) : Three ⟶ C := {|
  fobj := fun x =>
   match x with
   | existT _ 0%nat _ => c
   | existT _ 1%nat _ => c
   | existT _ 2%nat _ => c
   | _ => False_rect _ _
   end
|}.
Next Obligation.
  destruct x. specialize (H1 X); contradiction.
  destruct x. specialize (H X); contradiction.
  destruct x. specialize (H0 X); contradiction.
  destruct X.
  pose proof (c0 0%nat).
  unfold composite in H2; simpl in H2.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. discriminate.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. structure.
  simplify_maps. discriminate.
  simplify_maps. structure.
Qed.

--------
程序定义 FromThree {C : 范畴} (c : C) : 三 ⟶ C := {|
  fobj := fun x =>
   match x with
   | existT _ 0%nat _ => c
   | existT _ 1%nat _ => c
   | existT _ 2%nat _ => c
   | _ => False_rect _ _
   end
|}。
下一义务。
  拆解 x。特别化 (H1 X)；矛盾。
  拆解 x。特别化 (H X)；矛盾。
  拆解 x。特别化 (H0 X)；矛盾。
  拆解 X。
  引入定理 (c0 0%nat)。
  展开 composite 在 H2 中；在 H2 中化简。
  简化映射。结构。
  简化映射。结构。
  简化映射。结构。
  简化映射。矛盾。
  简化映射。结构。
  简化映射。结构。
  简化映射。结构。
  简化映射。结构。
  简化映射。矛盾。
  简化映射。结构。
证毕。
*)

End Metacategory.
