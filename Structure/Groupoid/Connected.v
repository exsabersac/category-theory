Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(*
   * * Connected categories, and the structure of a connected groupoid 

   --------
   * * 连接的范畴，以及连接群的结构
*)

(*
 nLab:      https://ncatlab.org/nlab/show/connected+category
 nLab:      https://ncatlab.org/nlab/show/groupoid
 Wikipedia: https://en.wikipedia.org/wiki/Groupoid
 Book:      Riehl, "Category Theory in Context", §1.5, printed p. 35 (the
 running definition of a connected category) and Proposition
 1.5.13, printed pp. 35-36
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §I.5, printed p. 20 (the remark following Definition 9)

 A category is CONNECTED when any two objects are joined by a finite
 zig-zag of morphisms: a chain

 x --> a_1 <-- a_2 --> ... <-- y

 in which each step points either forwards or backwards.  [ZigZag] below is
 that chain as an inductive type and [Connected C] is the statement that one
 exists between every pair of objects.

 COLLAPSE TO THE ONE-ARROW FORM.  In a groupoid the zig-zag form and the
 much simpler "there is an arrow x ~> y" agree, because a backward step can
 be inverted and the chain composed: [zigzag_hom] does exactly that, and
 [hom_zigzag] is the trivial converse.  Outside groupoids the two forms come
 apart, and the difference is not a technicality — [Roof] (the walking span
 RNeg <-- RZero --> RPos) is connected in the zig-zag sense while carrying
 no arrow whatever between RNeg and RPos.  That is proved below
 ([Roof_Connected], [Roof_no_arrow_neg_pos], [Roof_not_groupoid]), so the
 zig-zag form is not merely the more general definition on paper; it is
 strictly more general in this library, and it is the form that will be
 reusable for connected limits.

 ALTERNATION.  Riehl's chain alternates direction.  Requiring strict
 alternation costs nothing: [Fence] below is the strictly alternating form
 (each step a span x --> m <-- y), and [fence_zigzag]/[zigzag_fence] convert
 between the two in both directions — the interesting direction pads a lone
 step with an identity arrow.  So [Connected] is stated with the free chain
 without loss.

 Contents:

 ZigZag x y             a finite chain of arrows in either direction
 Connected C            a zig-zag between every pair of objects
 Fence x y              the strictly alternating (span-chain) form
 fence_zigzag, zigzag_fence   the two forms are interderivable
 zigzag_hom G           collapse of a zig-zag in a groupoid
 connected_arrow        Connected + IsGroupoid gives an arrow x ~> y
 arrow_connected        and conversely
 vertex_incl G x        B (hom(x,x)) ⟶ C, fully faithful
 connected_deloop_equiv Riehl Proposition 1.5.13
 deloop_equiv_connected its converse: the hypothesis is necessary
 connected_iff_deloop_equiv       the two directions together
 WideDeloop M A         a concrete connected groupoid with |A| objects
 Bool_Wide_structure    the structure theorem at a two-object groupoid
 Roof_Connected         a connected category that is NOT a groupoid
 Two_Discrete_no_deloop_equivalence  a groupoid where the conclusion
 is false, connectedness having
 been dropped 

 --------
 nLab:       https://ncatlab.org/nlab/show/connected+category 
 nLab:       https://ncatlab.org/nlab/show/groupoid 
 维基百科:  https://en.wikipedia.org/wiki/Groupoid 
 书籍:      Riehl, 《Category Theory in Context》，§1.5，第35页印刷版（连通范畴的运行定义）和命题1.5.13，第35-36页印刷版
 书籍:      Mac Lane, 《Categories for the Working Mathematician》，第2版，GTM 5，§I.5，第20页印刷版（定义9之后的备注）

 当任意两个对象通过有限的形如之链的态射连接时，范畴是连通的：一条链

 x --> a_1 <-- a_2 --> ... <-- y

 每一步都指向向前或向后。下面的 [ZigZag] 是将该链作为归纳类型，[Connected C] 是每对对象之间存在该链的陈述。折叠为单箭头形式。在群族中，之字形（zig-zag）形式与更简单的“存在一条箭头 x ~> y”的形式是一致的，因为后退步骤可以取反并将链条组合起来：[zigzag_hom] 就是这样做的，而 [hom_zigzag] 则是平凡的逆形式。在群族之外，这两种形式会分开，并且这种差异并非技术细节——[Roof]（行走的跨度 RNeg <-- RZero --> RPos）在之字形意义上是连通的，但在 RNeg 与 RPos 之间实际上没有任何箭头。这在下面得到了证明（[Roof_Connected], [Roof_no_arrow_neg_pos], [Roof_not_groupoid]），因此之字形形式不仅仅是在纸面上更一般的定义；在本库中，它严格来说更一般，它也是可用于连通极限的可重复形式。交替。Riehl 的链条方向交替。要求严格交替不花费任何代价：下面的 [Fence] 是严格交替的形式（每步都是跨度 x --> m <-- y），而 [fence_zigzag] / [zigzag_fence] 可以在两个方向之间转换——有趣的方向用恒等箭头填充单独的一步。因此 [Connected] 在没有损失的情况下陈述了自由链条。

 内容：ZigZag x y             在任意方向上的有限箭链
 Connected C            每对对象之间的之字形链
 Fence x y              严格交替的（跨链）形式
 fence_zigzag, zigzag_fence   两种形式是可互导的
 zigzag_hom G           群类中之字形链的折叠
 connected_arrow        Connected + IsGroupoid 给出箭 x ~> y
 arrow_connected        反之亦然
 vertex_incl G x        B (hom(x,x)) ⟶ C，完全忠实
 connected_deloop_equiv Riehl 命题 1.5.13
 deloop_equiv_connected 其逆命题：假设是必要的
 connected_iff_deloop_equiv       两个方向一起
 WideDeloop M A         一个具体的、具有 |A| 个对象的连通群类
 Bool_Wide_structure    结构e 定理在一个二元对象群体上的应用
 Roof_Connected         一个连通的类别，但不是群体
 Two_Discrete_no_deloop_equivalence  一个群体，其中结论为假，连通性已被排除
*)

(*
 What the structure theorem says, and what it does not

 nLab:  https://ncatlab.org/nlab/show/fundamental+groupoid
 Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of the
 London Mathematical Society 19, 1987

 Mac Lane's remark after §I.5 Definition 9, and Riehl's Proposition 1.5.13,
 say the same thing: a connected groupoid is determined, up to equivalence,
 by a single vertex group.  The proof is one line once the pieces are in
 place — the inclusion of the vertex group is fully faithful BY DEFINITION
 of hom(x, x), and essentially surjective BY connectedness, so the
 full-and-faithful-and-essentially-surjective criterion applies.  In this
 library that criterion is Theory/Equivalence/FullFaithful.v's
 [FF_ESO_Equivalence], and the whole of [connected_deloop_equiv] is the
 assembly of three small records.

 The content is in what "up to equivalence" does and does not mean.  The
 delooping has ONE object; a connected groupoid may have a proper class of
 them, all isomorphic.  So the theorem cannot be an isomorphism of
 categories, and the statement is not that a connected groupoid IS a group,
 but that no categorical property distinguishes it from one.  The witness
 below makes the gap concrete: [WideDeloop Bool_Xor_Grp bool] has two
 objects and eight arrows, [Deloop Bool_Xor_Grp] has one object and two
 arrows, and [connected_deloop_equiv] relates them.

 This is also the precise sense in which the fundamental groupoid of a
 path-connected space carries no more information than its fundamental
 group, while for a space with several path components — where the
 groupoid is not connected — it carries strictly more, which is Brown's
 argument for the groupoid-valued van Kampen theorem (Brown 1987).

 Connectedness is not merely a sufficient hypothesis.  It is equivalent to
 the conclusion ([connected_iff_deloop_equiv]), and the groupoid with two
 objects and only their identity arrows refutes the conclusion outright
 ([Two_Discrete_no_deloop_equivalence]) while satisfying every other
 hypothesis — it is a groupoid, and Structure/Groupoid.v's
 [conjugation_iso] applies to it just the same. 

 --------
 结构定理的内容，以及它不包括的内容

 nLab:   https://ncatlab.org/nlab/show/fundamental+groupoid 
 论文: Brown, "From groups to groupoids: a brief survey", Bulletin of the
 London Mathematical Society 19, 1987

 Mac Lane 在 §I.5 定义 9 之后的评论，以及 Riehl 的命题 1.5.13，
 说的是同一件事：连通的群族在等价意义下由单个顶点群决定。一旦各部分到位，证明就是一句话——顶点群的包含是完全忠实的（根据 hom(x, x) 的定义），由于连通性，它在本质上是满射的，因此可以应用完全忠实且本质满射的标准。在这个库里，该标准是 Theory/Equivalence/FullFaithful.v 的
 [FF_ESO_Equivalence]，并且整个 [connected_deloop_equiv] 是三个小记录的组合。内容在于“至等价”意味着和不意味着什么。去环化有一个对象；一个连通群类可能有一个真正类别的对象，它们都是同构的。因此，该定理不能是范畴的同构，陈述的内容也不是说一个连通群类就是一个群，而是没有范畴性质能将它与群区分开来。下面的实例使这一差距具体化：[WideDeloop Bool_Xor_Grp bool] 有两个对象和八条箭头，[Deloop Bool_Xor_Grp] 有一个对象和两条箭头，而 [connected_deloop_equiv] 将它们联系起来。这也是一种精确的意义，即一个路径连通空间的基本群范畴所携带的信息不比其基本群更多，而对于具有多个路径分支的空间——此时群范畴不是连通的——它携带的信息严格更多，这就是布朗提出的群范畴值的范肯彭定理的论证（Brown 1987）。

 连通性不仅仅是一个充分条件，它等价于结论（[connected_iff_deloop_equiv]），而具有两个对象且只有它们自身同一箭头的群范畴直接否定了该结论（[Two_Discrete_no_deloop_equivalence]），同时满足其他所有假设——它是一个群范畴，并且 Structure/Groupoid.v 中的 [conjugation_iso] 对其同样适用。
*)

(** ** Zig-zags *)

(*
 A finite chain of arrows between x and y, each step pointing either
 forwards ([zz_fwd]) or backwards ([zz_bwd]).  This is Riehl's §1.5
 definition made into data: an inhabitant is an actual chain, not the mere
 assertion that one exists, which is what lets [zigzag_hom] compute the
 composite arrow in a groupoid.  It therefore lands in [Type] rather than
 [Prop], in the same split, choice-carrying style as
 [EssentiallySurjective] (Theory/Equivalence.v: "there exists a preimage"
 becomes "here is one"). 

 --------
 在 x 和 y 之间的有限箭头链，每一步要么指向前方（[zz_fwd]），要么指向后方（[zz_bwd]）。这是 Riehl §1.5 的定义变成数据：一个元素是一个实际的链，而不仅仅是存在的断言，这使得 [zigzag_hom] 可以计算群组中的复合箭头。因此它落在 [Type] 中而不是 [Prop] 中，以与 [EssentiallySurjective] 相同的分裂、携带选择的方式（Theory/Equivalence.v：“存在一个前像”变为“这里有一个”）。
*)
Inductive ZigZag {C : Category} : C → C → Type :=
  | zz_nil (x : C) : ZigZag x x
  | zz_fwd (x y z : C) (f : x ~> y) (s : ZigZag y z) : ZigZag x z
  | zz_bwd (x y z : C) (f : y ~> x) (s : ZigZag y z) : ZigZag x z.

Arguments zz_nil {C} x.
Arguments zz_fwd {C x y z} f s.
Arguments zz_bwd {C x y z} f s.

(*
 Riehl §1.5: C is connected when every pair of objects is joined by a
 zig-zag. 

 --------
 Riehl §1.5：当每一对对象都通过曲折路径连接时，C 是连通的。
*)
Definition Connected (C : Category) : Type := ∀ x y : C, ZigZag x y.

(*
 A single arrow is a one-step zig-zag, so the one-arrow form implies the
 zig-zag form in ANY category. 

 --------
 一支箭是一种一步之内的之字形，所以一箭形式意味着任何类别中的之字形形式。
*)
Definition hom_zigzag {C : Category} {x y : C} (f : x ~> y) : ZigZag x y :=
  zz_fwd f (zz_nil y).

Definition arrow_connected {C : Category} (H : ∀ x y : C, x ~> y) :
  Connected C := fun x y => hom_zigzag (H x y).

(*
 Zig-zags compose end to end, which is what makes "joined by a zig-zag" a
 transitive relation (with [zz_nil] for reflexivity).  It is not symmetric
 by this operation alone; symmetry needs the chain reversed, which is
 [zigzag_sym] below. 

 --------
 之字形端对端地组合，这就是“通过之字形连接”是一种传递关系的原因（用 [zz_nil] 表示自反性）。仅凭这种操作，它不是对称的；对称性需要将链反转，如下所示为 [zigzag_sym]。
*)
Fixpoint zigzag_trans {C : Category} {x y z : C}
  (s : ZigZag x y) : ZigZag y z → ZigZag x z :=
  match s in ZigZag a b return ZigZag b z → ZigZag a z with
  | zz_nil _     => fun t => t
  | zz_fwd f s'  => fun t => zz_fwd f (zigzag_trans s' t)
  | zz_bwd f s'  => fun t => zz_bwd f (zigzag_trans s' t)
  end.

(*
 Reversal, by turning every forward step into a backward one and vice
 versa.  Stated through [zigzag_trans] because a reversed chain is built
 from the tail outwards. 

 --------
 逆转，通过将每一个前进的步骤变成后退，反之亦然。通过 [zigzag_trans] 表述，因为逆向链条是从尾部向外构建的。
*)
Fixpoint zigzag_sym {C : Category} {x y : C} (s : ZigZag x y) : ZigZag y x :=
  match s in ZigZag a b return ZigZag b a with
  | zz_nil w    => zz_nil w
  | zz_fwd f s' => zigzag_trans (zigzag_sym s') (zz_bwd f (zz_nil _))
  | zz_bwd f s' => zigzag_trans (zigzag_sym s') (zz_fwd f (zz_nil _))
  end.

(** ** The strictly alternating form / ** 严格交替形式 *)

(*
 A fence: a chain of spans x --> m <-- y, each step alternating forwards
 then backwards by construction.  This is Riehl's "alternating directions"
 read literally. 

 --------
 栅栏：一系列跨度 x --> m <-- y，每一步按构造交替向前然后向后。这就是 Riehl 的“交替方向”，按字面理解。
*)
Inductive Fence {C : Category} : C → C → Type :=
  | fence_nil (x : C) : Fence x x
  | fence_cons (x m y z : C) (f : x ~> m) (g : y ~> m) (t : Fence y z) :
      Fence x z.

Arguments fence_nil {C} x.
Arguments fence_cons {C x} m {y z} f g t.

(*
 A fence is a zig-zag: expand each span into a forward step followed by a
 backward one. 

 --------
 栅栏是之字形的：将每一段扩展为向前一步然后向后一步。
*)
Fixpoint fence_zigzag {C : Category} {x y : C} (t : Fence x y) : ZigZag x y :=
  match t with
  | fence_nil w             => zz_nil w
  | fence_cons _ f g t'     => zz_fwd f (zz_bwd g (fence_zigzag t'))
  end.

(*
 And conversely — the direction that shows strict alternation is no
 restriction.  A lone forward step x ~> y is padded to the span
 x --> y <-- y with an identity, and a lone backward step to x --> x <-- y;
 so every chain becomes alternating at the cost of identity arrows only. 

 --------
 反之——显示严格交替的方向并不构成限制。一个单独的向前步骤 x ~> y 会通过一个恒等箭头扩展为跨度 x --> y <-- y，而一个单独的向后步骤则扩展为 x --> x <-- y；因此，每个链条都可以以仅增加恒等箭头的代价变为交替的。
*)
Fixpoint zigzag_fence {C : Category} {x y : C} (s : ZigZag x y) : Fence x y :=
  match s with
  | zz_nil w      => fence_nil w
  | zz_fwd f s'   => fence_cons _ f id (zigzag_fence s')
  | zz_bwd f s'   => fence_cons _ id f (zigzag_fence s')
  end.

(* * ** Collapse to the one-arrow form in a groupoid / * ** 折叠为群的单箭头形式 *)

(*
 In a groupoid a zig-zag composes to a single arrow: forward steps compose
 as they stand and backward steps are inverted first.  Together with
 [hom_zigzag] this is the promised collapse — for a groupoid, "joined by a
 zig-zag" and "joined by an arrow" are inhabited together. 

 --------
 在一个群oid中，之字形路径可以组合成一条箭头：前进的步骤按原样组合，后退的步骤先取逆。 与 [hom_zigzag] 一起，这就是承诺的塌缩——对于一个群oid，“通过之字形路径连接”和“通过箭头连接”是可以共存的。
*)
Fixpoint zigzag_hom {C : Category} (G : IsGroupoid C) {x y : C}
  (s : ZigZag x y) : x ~> y :=
  match s in ZigZag a b return a ~> b with
  | zz_nil w    => id[w]
  | zz_fwd f s' => zigzag_hom G s' ∘ f
  | zz_bwd f s' => zigzag_hom G s' ∘ ginv G f
  end.

Definition connected_arrow {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x y : C) : x ~> y := zigzag_hom G (K x y).

(*
 And therefore any two objects of a connected groupoid are isomorphic —
 the form the structure theorem consumes. 

 --------
 因此，一个连通群范畴中的任何两个对象都是同构的——这是结构定理所采用的形式。
*)
Definition connected_iso {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x y : C) : x ≅ y := giso G (connected_arrow G K x y).

(** ** The structure theorem / ** 结构定理 *)

(*
 The inclusion of the vertex group at x: the delooping of hom(x, x) sent to
 the single object x, an arrow of the delooping being an endomorphism of x
 already.  The morphism action is the identity function, so respectfulness
 is immediate; and composition in [Deloop (vertex_group G x)] IS
 composition in C, and its identity IS id[x], so both functor laws are
 reflexivity of `≈`.  No obligation survives the ambient Program tactic,
 which is why no proof script follows.

 This is a fully faithful functor, not a subcategory: nothing here claims
 that its object map is a monomorphism onto a class of objects of C, only
 that the hom-map is bijective.  (Its object map is in fact injective, the
 source having a single object, but the useful statement is the one about
 homs.) 

 --------
 在 x 处包含顶点组：hom(x, x) 的解环映射到单个对象 x，解环的箭头本身就是 x 的一个自同态。态射作用是恒等函数，因此守恒性是显而易见的；而在 [Deloop (vertex_group G x)] 中的复合正是 C 中的复合，其恒等式是 id [x]，因此两个函子律都是 `≈` 的自反性。在外部 Program 策略下没有义务残留，这就是为什么没有后续证明脚本的原因。

 这是一个完全忠实的函子，而不是子范畴：这里没有任何内容声称它的对象映射是指向 C 的某个对象类的单射，只是说 hom 映射是双射。（其实它的对象映射确实是单射，源只包含一个对象，但有用的陈述是关于 hom 的那个。）
*)
Program Definition vertex_incl {C : Category} (G : IsGroupoid C) (x : C) :
  Deloop (vertex_group G x) ⟶ C := {|
  fobj := fun _ => x;
  fmap := fun _ _ f => f
|}.

(*
 Fullness and faithfulness hold with NO hypothesis on C beyond the groupoid
 structure used to form the vertex group: the hom-map is the identity
 function on hom(x, x).  This is Riehl's "fully faithful by definition of
 the vertex group", and both records are correspondingly NEAR-TRIVIAL —
 the chosen preimage is the arrow itself and injectivity is the identity
 implication.  The mathematical work of the structure theorem is entirely
 in [vertex_incl_ESO] below; these two are recorded because
 [FF_ESO_Equivalence] consumes them, not because they are difficult.

 As with [conjugation] in Structure/Groupoid.v, each record below is built
 by applying its constructor to an explicit functor argument: the field
 types mention [fobj[?F]], which the identity hom-map does not determine by
 unification. 

 --------
 在不对 C 假设任何超出用于形成顶点群的群道结构的情况下，充满性和忠实性依然成立：hom 映射在 hom(x, x) 上是恒等函数。这就是 Riehl 所说的“由顶点群的定义自动完全忠实”，两个记录也是相应的几乎平凡——选择的原像就是箭头本身，而单射性就是恒等的蕴含。结构定理的数学工作完全在下文的 [vertex_incl_ESO] 中；记录这两条是因为 [FF_ESO_Equivalence] 使用它们，而不是因为它们难以理解。

 与 Structure/Groupoid.v 中的 [conjugation] 类似，下述每个记录都是通过将其构造函数应用于显式函子参数而构建的：字段类型提到 [fobj[?F]，而恒等 hom 映射并不能通过统一来决定它们。
*)
Definition vertex_incl_Full {C : Category} (G : IsGroupoid C) (x : C) :
  Full (vertex_incl G x) :=
  @Build_Full _ _ (vertex_incl G x)
    (fun _ _ g => g) (fun _ _ g => reflexivity g).

Definition vertex_incl_Faithful {C : Category} (G : IsGroupoid C) (x : C) :
  Faithful (vertex_incl G x) :=
  @Build_Faithful _ _ (vertex_incl G x) (fun _ _ _ _ H => H).

(*
 Essential surjectivity is where connectedness enters, and it is the ONLY
 place it enters: every object of C is isomorphic to x because a zig-zag
 from x to it collapses to an arrow, which the groupoid structure inverts. 

 --------
 本质上满射性是连通性介入的地方，而且它是唯一的介入点：C 的每一个对象都同构于 x，因为从 x 到它的之字形路径会收缩为一条箭头，而群类结构将其取逆。
*)
Definition vertex_incl_ESO {C : Category} (G : IsGroupoid C) (K : Connected C)
  (x : C) : EssentiallySurjective (vertex_incl G x) :=
  @Build_EssentiallySurjective _ _ (vertex_incl G x)
    (fun _ => ttt) (fun d => connected_iso G K x d).

(*
 Riehl, Proposition 1.5.13; Mac Lane §I.5, the remark after Definition 9.
 A connected groupoid is equivalent to the delooping of the vertex group at
 ANY of its objects — x is universally quantified, and no property of it is
 used. 

 --------
 Riehl，第 1.5.13 命题；Mac Lane §I.5，定义 9 之后的备注。
 一个连通的群族等价于其任意对象顶点群的去环化 —— x 是全称量化的，并且没有使用它的任何性质。
*)
Theorem connected_deloop_equiv {C : Category} (G : IsGroupoid C)
  (K : Connected C) (x : C) : EquivalenceOfCategories (vertex_incl G x).
Proof.
  exact (@FF_ESO_Equivalence _ _ (vertex_incl G x)
           (vertex_incl_Full G x) (vertex_incl_Faithful G x)
           (vertex_incl_ESO G K x)).
Defined.

(*
 The quasi-inverse, extracted: it sends every object of C to the single
 object of the delooping, and an arrow to its conjugate into hom(x, x). 

 --------
 提取的拟逆：它将 C 的每个对象映射到去环化的单个对象，并将每条箭头映射到其在 hom(x, x) 中的共轭。
*)
Definition connected_deloop_inverse {C : Category} (G : IsGroupoid C)
  (K : Connected C) (x : C) : C ⟶ Deloop (vertex_group G x) :=
  @quasi_inverse _ _ _ (connected_deloop_equiv G K x).

(* * ** Connectedness is necessary, not merely sufficient / * ** 连通性是必要的，而不仅仅是充分的 *)

(*
 [vertex_incl G x] sends EVERY object to x, so an essential-surjectivity
 witness for it is exactly a family of isomorphisms x ≅ d — the chosen
 preimage object carries no information, there being only one to choose. 

 --------
 [vertex_incl G x] 将每个对象发送到 x，因此它的一个本质满射的证明正好是一族同构 x ≅ d — 所选择的原像对象不携带任何信息，因为只有一个可以选择。
*)
Definition vertex_incl_ESO_iso {C : Category} (G : IsGroupoid C) (x : C)
  (E : EssentiallySurjective (vertex_incl G x)) (d : C) : x ≅ d :=
  @eso_iso _ _ (vertex_incl G x) E d.

(*
 Hence the converse of the structure theorem.  If the inclusion of the
 vertex group at some object is an equivalence, C is connected: every
 object is isomorphic to x, so any two are joined through x by a
 one-step chain.  Connectedness is therefore not a convenient hypothesis
 that happens to make the proof go through — it is equivalent to the
 conclusion. 

 --------
 因此是结构定理的逆命题。如果某个对象的顶点群的包含是一个等价，那么 C 是连通的：每个对象都与 x 同构，因此任意两个对象都通过一个一步链通过 x 相连。因此，连通性并不是一个恰好使证明成立的便利假设——它与结论是等价的。
*)
Theorem deloop_equiv_connected {C : Category} (G : IsGroupoid C) (x : C)
  (E : EquivalenceOfCategories (vertex_incl G x)) : Connected C.
Proof.
  pose proof (Equivalence_EssSurj E) as Eso.
  intros y z.
  apply hom_zigzag.
  exact (to (vertex_incl_ESO_iso G x Eso z)
           ∘ from (vertex_incl_ESO_iso G x Eso y)).
Defined.

(*
 The two directions together.  For a groupoid with a chosen object, being
 connected and being equivalent to the delooping of the vertex group at
 that object are interderivable. 

 --------
 两个方向一起。对于一个选定了对象的群类，连通性与它等价于该对象的顶点群的去环化是可以互相推导的。
*)
Theorem connected_iff_deloop_equiv {C : Category} (G : IsGroupoid C) (x : C) :
  Connected C ↔ EquivalenceOfCategories (vertex_incl G x).
Proof.
  split.
  - intro K.
    exact (connected_deloop_equiv G K x).
  - intro E.
    exact (deloop_equiv_connected G x E).
Defined.

(** ** A concrete connected groupoid / ** 一个具体的连通范畴 *)

(*
 The delooping of M spread over a whole type of objects: same object set A,
 the elements of M as the arrows between EVERY pair, composition and
 identity as in [Deloop].  Every category law is again a monoid law by
 projection, exactly as in Construction/Deloop.v — the single object of
 [Deloop] plays no role in any of them, which is why widening it changes
 nothing.

 For A = [poly_unit] this is [Deloop] on the nose ([WideDeloop_Deloop]
 below).  For A with more than one element it is a genuinely larger
 category with the same vertex group at every object, and it is the witness
 that exercises the structure theorem beyond the trivial case. 

 --------
 M 的解环延伸覆盖了一整类对象：相同的对象集合 A，M 的元素作为每一对对象之间的箭头，组合和单位如 [Deloop] 所示。每一个范畴律通过投影再次成为一个幺半群律，正如 Construction/Deloop.v 中所示——[Deloop] 的单一对象在其中没有任何作用，这就是为什么扩展它不会改变任何东西。

 对于 A = [poly_unit]，这正是 [Deloop]（如下 [WideDeloop_Deloop]）。对于元素多于一个的 A，它是一个真正更大的范畴，每个对象都有相同的顶点群，并且它是那个在平凡情况下之外演示结构定理的见证。
*)
Definition WideDeloop (M : MonObject) (A : Type) : Category := {|
  obj     := A;
  hom     := fun _ _ => carrier M;
  homset  := fun _ _ => is_setoid M;
  id      := fun _ => mon_unit;
  compose := fun _ _ _ f g => mon_op f g;

  compose_respects := fun _ _ _ => mon_op_respects M;

  id_left  := fun _ _ => mon_op_unit_l;
  id_right := fun _ _ => mon_op_unit_r;

  comp_assoc     := fun _ _ _ _ => mon_op_assoc;
  comp_assoc_sym := fun _ _ _ _ => mon_op_assoc_sym M
|}.

(*
 The delooping is the one-object case, on the nose.  (An equality of
 CATEGORIES, which is far stronger than anything stated with `≈`; it holds
 by [eq_refl] because every field of [Deloop] is repeated verbatim above
 with [poly_unit] in place of A.) 

 --------
 去环化是单对象的情况，完全准确。（一个范畴的相等，比用 `≈` 陈述的任何内容都要强；它通过 [eq_refl] 成立，因为 [Deloop] 的每个域在上面都被逐字重复，ZWW2WZZ 代替了 A。）
*)
Example WideDeloop_Deloop (M : MonObject) : WideDeloop M poly_unit = Deloop M
  := eq_refl.

(*
 Its endomorphism monoid at every object is M itself, on the nose — the
 [hom_monoid_Deloop] round trip of Construction/Deloop.v, widened. 

 --------
 它在每个对象上的自同态幺半群本身就是 M，完全一样——Construction/Deloop.v 的 [hom_monoid_Deloop] 往返过程的扩展版本。
*)
Example WideDeloop_hom_monoid (M : MonObject) (A : Type) (a : A) :
  hom_monoid (WideDeloop M A) a = M := eq_refl.

(*
 If M is a group then [WideDeloop M A] is a groupoid: the inverse of an
 arrow is the inverse of the element, at any pair of objects. 

 --------
 如果 M 是一个群，那么 [WideDeloop M A] 是一个群族：箭头的逆元是该元素的逆元，适用于任意一对对象。
*)
Definition WideDeloop_IsGroupoid (G : GrpObject) (A : Type) :
  IsGroupoid (WideDeloop G A).
Proof.
  intros x y f.
  refine (@Build_IsIsomorphism (WideDeloop G A) x y f (grp_inv f) _ _).
  - apply grp_inv_r.
  - apply grp_inv_l.
Defined.

(*
 And it is connected, by the one-step zig-zag carrying the unit of M —
 every hom-set is inhabited, whatever A is. 

 --------
 它通过携带 M 单位的一步之字形连接——无论 A 是什么，每个同态集合都是可达的。
*)
Definition WideDeloop_Connected (M : MonObject) (A : Type) :
  Connected (WideDeloop M A) :=
  @arrow_connected (WideDeloop M A) (fun _ _ => mon_unit).

(* * ** The structure theorem, exercised / * ** 结构定理，已练习 *)

(*
 Two objects, eight arrows, vertex group Z/2 at each of them. 

 --------
 两个对象，八个箭头，每个对象上的顶点群为 Z/2。
*)
Definition Bool_Wide : Category := WideDeloop Bool_Xor_Grp bool.

Definition Bool_Wide_IsGroupoid : IsGroupoid Bool_Wide :=
  WideDeloop_IsGroupoid Bool_Xor_Grp bool.

Definition Bool_Wide_Connected : Connected Bool_Wide :=
  WideDeloop_Connected Bool_Xor_Grp bool.

(*
 Its vertex group at [true] really is Z/2: both data fields agree with
 [Bool_Xor_Grp] on the nose. 

 --------
 它在 [true] 的顶点群确实是 Z/2：两个数据字段与 [Bool_Xor_Grp] 完全一致。
*)
Example Bool_Wide_vertex_monoid :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid true) = grp_monoid Bool_Xor_Grp
  := eq_refl.

Example Bool_Wide_vertex_inv :
  @grp_inv (vertex_group Bool_Wide_IsGroupoid true) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(*
 The structure theorem at this groupoid: the two-object [Bool_Wide] is
 equivalent to the one-object delooping of its vertex group at [true].  The
 objects [true] and [false] are distinct, so the equivalence genuinely
 contracts the object set rather than being an identity in disguise. 

 --------
 这个群群体的结构定理：两个对象 [Bool_Wide] 等价于其顶点群在 [true] 的单对象解环。对象 [true] 和 [false] 是不同的，因此该等价关系实际上是收缩对象集，而不是伪装的恒同映射。
*)
Definition Bool_Wide_structure :
  EquivalenceOfCategories (vertex_incl Bool_Wide_IsGroupoid true) :=
  connected_deloop_equiv Bool_Wide_IsGroupoid Bool_Wide_Connected true.

(*
 The same statement at the other object, to exhibit the "any one vertex
 group" clause with a second choice actually made. 

 --------
 在另一个对象上的相同声明，用第二个实际作出的选择来展示“任意一个顶点组”条款。
*)
Definition Bool_Wide_structure_false :
  EquivalenceOfCategories (vertex_incl Bool_Wide_IsGroupoid false) :=
  connected_deloop_equiv Bool_Wide_IsGroupoid Bool_Wide_Connected false.

(*
 And the conjugation isomorphism between the two vertex groups, which is
 what makes the two statements above compatible. 

 --------
 以及两个顶点群之间的共轭同构，这就是使上述两个陈述兼容的原因。
*)
Definition Bool_Wide_conjugation :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  conjugation_iso Bool_Wide_IsGroupoid
    (connected_arrow Bool_Wide_IsGroupoid Bool_Wide_Connected true false).

(* * ** Connected does not mean "joined by an arrow" / * ** 连接并不意味着“被箭头连接” *)

(*
 [Roof] (Instance/Roof.v) is the walking span RNeg <-- RZero --> RPos.  It
 is connected: every pair of objects is joined by a zig-zag through RZero. 

 --------
 [Roof]（Instance/Roof.v）是步行跨距 RNeg <-- RZero --> RPos。它是连接的：每对对象都通过 RZero 的之字形连接起来。
*)
Definition Roof_Connected : Connected Roof.
Proof.
  intros x y.
  (*
 [destruct] replaces the objects by bare [RoofObj] constructors, which no
 longer carry the category in their type, so each chain names [Roof]
 explicitly. 

 --------
 [destruct] 用裸 [RoofObj] 构造函数替换对象，这些构造函数的类型中不再包含类别，因此每个链都显式命名 [Roof]。
*)
  destruct x, y.
  - exact (@zz_nil Roof RNeg).
  - exact (@zz_bwd Roof RNeg RZero RZero ZeroNeg (@zz_nil Roof RZero)).
  - exact (@zz_bwd Roof RNeg RZero RPos ZeroNeg
             (@zz_fwd Roof RZero RPos RPos ZeroPos (@zz_nil Roof RPos))).
  - exact (@zz_fwd Roof RZero RNeg RNeg ZeroNeg (@zz_nil Roof RNeg)).
  - exact (@zz_nil Roof RZero).
  - exact (@zz_fwd Roof RZero RPos RPos ZeroPos (@zz_nil Roof RPos)).
  - exact (@zz_bwd Roof RPos RZero RNeg ZeroPos
             (@zz_fwd Roof RZero RNeg RNeg ZeroNeg (@zz_nil Roof RNeg))).
  - exact (@zz_bwd Roof RPos RZero RZero ZeroPos (@zz_nil Roof RZero)).
  - exact (@zz_nil Roof RPos).
Defined.

(*
 Yet there is no arrow at all from RNeg to RPos, so the one-arrow form of
 connectedness does NOT hold of [Roof].  This is what makes the zig-zag
 definition strictly more general, rather than merely more verbose.
 (Instance/Roof.v proves the emptiness of that hom-set as
 [RNeg_RPos_absurd]; it is restated here at the categorical hom so the
 claim is about [Roof] as a category.) 

 --------
 然而，从 RNeg 到 RPos 完全没有箭头，因此单箭头形式的连通性不适用于 [Roof]。这正是使之之字形定义严格更一般，而不仅仅是更冗长的原因。(Instance/Roof.v 证明了该同态集的空性为 [RNeg_RPos_absurd]；这里在范畴同态处重新陈述，所以该断言是关于 [Roof] 作为一个范畴的。)
*)
Theorem Roof_no_arrow_neg_pos : (RNeg ~{Roof}~> RPos) → False.
Proof. exact RNeg_RPos_absurd. Qed.

Corollary Roof_not_arrow_connected : (∀ x y : Roof, x ~> y) → False.
Proof. intro H. exact (Roof_no_arrow_neg_pos (H RNeg RPos)). Qed.

(*
 The two forms can come apart only outside groupoids, since [zigzag_hom]
 collapses them inside one.  [Roof] is indeed not a groupoid: the arrow
 ZeroNeg has no inverse, there being no arrow RNeg ~> RZero. 

 --------
 这两种形式只有在群类之外才能分开，因为 [zigzag_hom] 会在一个群类内将它们合并。[Roof] 确实不是一个群类：箭头 ZeroNeg 没有逆，因为不存在箭头 RNeg ~> RZero。
*)
Theorem Roof_not_groupoid : IsGroupoid Roof → False.
Proof.
  intro G.
  exact (RNeg_RZero_absurd (ginv G ZeroNeg)).
Qed.

(*
 And the link is not merely suggestive: the same conclusion follows from
 the two facts just proved, with no further inspection of [Roof].  Were
 [Roof] a groupoid, [zigzag_hom] would collapse the chain
 RNeg <-- RZero --> RPos into the arrow RNeg ~> RPos that
 [Roof_no_arrow_neg_pos] rules out.  So the collapse really is what the
 groupoid hypothesis buys, and its absence really is what separates the
 two forms here. 

 --------
 而这种联系不仅仅是暗示性的：相同的结论可以从刚刚证明的两个事实得出，而无需进一步检查 [Roof]。如果 [Roof] 是一个群类，[zigzag_hom] 将会把链 RNeg <-- RZero --> RPos 崩塌为箭头 RNeg ~> RPos，而 [Roof_no_arrow_neg_pos] 排除了这种情况。所以这种崩塌确实是群类假设带来的结果，而它的缺失确实是这里两种形式之间的区别。
*)
Corollary Roof_not_groupoid_via_collapse : IsGroupoid Roof → False.
Proof.
  intro G.
  exact (Roof_no_arrow_neg_pos (zigzag_hom G (Roof_Connected RNeg RPos))).
Qed.

(*
   * ** A groupoid that is not connected, and for which the theorem's
   conclusion is false 

   --------
   * ** 一个不连通的群格，并且该定理的结论为假
*)

(*
 [Two_Discrete] (Instance/Two/Discrete.v) has two objects and only their
 identity arrows.  It is a groupoid — an identity is its own inverse — so
 it satisfies every hypothesis of the structure theorem except
 connectedness, and it shows that hypothesis cannot be dropped. 

 --------
 [Two_Discrete]（Instance/Two/Discrete.v）有两个对象，并且只有它们的同一箭头。它是一个群族——一个同一箭头是其自身的逆——所以它满足结构定理的每一个假设，除了连通性，而且它表明该假设不能被省略。
*)
Definition Two_Discrete_IsGroupoid : IsGroupoid Two_Discrete.
Proof.
  intros x y f.
  destruct f.
  - refine (@Build_IsIsomorphism Two_Discrete TwoDX TwoDX TwoDIdX TwoDIdX _ _);
      reflexivity.
  - refine (@Build_IsIsomorphism Two_Discrete TwoDY TwoDY TwoDIdY TwoDIdY _ _);
      reflexivity.
Defined.

(*
 Every arrow of a discrete category has equal endpoints, so every zig-zag
 does too — a chain cannot leave the object it starts at. 

 --------
 离散范畴的每一箭头都有相等的端点，因此每一个之字形路径也一样——链条不能离开它开始的对象。
*)
Lemma TwoDHom_endpoints {x y : TwoDObj} (f : TwoDHom x y) : x = y.
Proof. now destruct f. Qed.

Lemma Two_Discrete_zigzag_endpoints {x y : Two_Discrete} (s : ZigZag x y) :
  x = y.
Proof.
  induction s as [ w | a b c f s' IH | a b c f s' IH ].
  - reflexivity.
  - transitivity b; [ exact (TwoDHom_endpoints f) | exact IH ].
  - transitivity b; [ symmetry; exact (TwoDHom_endpoints f) | exact IH ].
Qed.

Theorem Two_Discrete_not_connected : Connected Two_Discrete → False.
Proof.
  intro K.
  pose proof (Two_Discrete_zigzag_endpoints (K TwoDX TwoDY)) as H.
  discriminate H.
Qed.

(*
 So the conclusion of the structure theorem is genuinely false here: the
 delooping of the vertex group at TwoDX is NOT equivalent to
 [Two_Discrete].  This is [deloop_equiv_connected] used in earnest — the
 necessity direction turns a missing hypothesis into a refutation. 

 --------
 因此，结构定理的结论在这里确实是错误的：TwoDX 处顶点群的去环化并不等价于 [Two_Discrete]。这实际上使用的是 [deloop_equiv_connected]——必要性方向将一个缺失的假设变成了反驳。
*)
Theorem Two_Discrete_no_deloop_equivalence :
  EquivalenceOfCategories (vertex_incl Two_Discrete_IsGroupoid TwoDX) → False.
Proof.
  intro E.
  exact (Two_Discrete_not_connected
           (deloop_equiv_connected Two_Discrete_IsGroupoid TwoDX E)).
Qed.
