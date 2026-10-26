Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.

Generalizable All Variables.

(* * * Base points: the vertex groups of a connected groupoid / * * 基点：一个连通群族的顶点群 *)

(*
 nLab:      https://ncatlab.org/nlab/show/groupoid
 nLab:      https://ncatlab.org/nlab/show/vertex+group
 nLab:      https://ncatlab.org/nlab/show/delooping
 nLab:      https://ncatlab.org/nlab/show/fully+faithful+functor
 nLab:      https://ncatlab.org/nlab/show/equivalence+of+categories
 Book:      Riehl, “Category Theory in Context”, Corollary 1.5.14, printed
 p. 36 (PDF p. 56), the corollary drawn there from Proposition
 1.5.13 (printed pp. 35-36)
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 GTM 5, §I.5, printed p. 20 (the remark following Definition 9)

 In a connected groupoid the vertex groups at any two objects are isomorphic
 as GROUPS.  Riehl records this at the location above as a corollary of the
 structure theorem for connected groupoids — her Proposition 1.5.13, which is
 Structure/Groupoid/Connected.v's [connected_deloop_equiv].  That
 sentence, and everything else this file says about what a printed source
 states, is a paraphrase of the statement at the cited location and not a
 quotation; the proof below is this library's own.

 Contents:

 Full_Compose             fullness is closed under functor composition
 Faithful_Compose         and so is faithfulness
 deloop_ff_moniso         a fully faithful functor between one-object
 categories is a monoid isomorphism
 deloop_equiv_moniso      the same for an equivalence, via Full+Faithful
 connected_vertex_moniso  the headline: vertex groups at any two objects
 of a connected groupoid are isomorphic
 Bool_Wide_vertex_moniso  the headline instantiated at a groupoid with
 two distinct objects, both of whose vertex
 groups are Z/2
 Bool_Wide_vertex_groups_agree,
 Bool_Wide_vertex_moniso_trivial
 and the measurement of exactly how much that
 instantiation demonstrates: not much

 EXPORTED, WITH NO CURRENT CONSUMER.  Counted from the `.glob` reference
 records rather than by reading, seven of the 27 constants below are
 referenced by nothing in the tree, this file included.  Six of them are
 terminal by design — [Bool_Wide_objects_distinct],
 [Bool_Wide_vertex_monoid_false], [Bool_Wide_vertex_inv_false],
 [Bool_Wide_vertex_groups_agree], [Bool_Wide_vertex_moniso_trivial] and
 [Bool_Wide_vertex_moniso] exist precisely to be the end of a chain.  The
 seventh, [deloop_equiv_moniso], is a genuine orphan: it is the
 equivalence-level form of [deloop_ff_moniso], and the headline does not go
 through it because [connected_vertex_moniso] has [Full] and [Faithful] of a
 COMPOSITE in hand rather than an [EquivalenceOfCategories] of it, so it
 calls [deloop_ff_moniso] directly.  It completes the pair and is kept;
 nothing here is removed on this file's own judgement, and the decision to
 keep or drop is the maintainer's.  (The headline [connected_vertex_moniso]
 itself is not in that list: Instance/Top/FundamentalGroupoid.v uses it.) 

 --------
 nLab：       https://ncatlab.org/nlab/show/groupoid
 nLab：       https://ncatlab.org/nlab/show/vertex+group
 nLab：       https://ncatlab.org/nlab/show/delooping
 nLab：       https://ncatlab.org/nlab/show/fully+faithful+functor
 nLab：       https://ncatlab.org/nlab/show/equivalence+of+categories
 书籍：      Riehl，《上下文中的范畴论》，推论 1.5.14，印刷页 36（PDF 页 56），该推论由命题 1.5.13（印刷页 35-36）得出
 书籍：      Mac Lane，《为工作中的数学家准备的范畴》，第二版，GTM 5，第 I.5 节，印刷页 20（定义 9 之后的备注）在一个连通的群族中，任意两个对象的顶点群作为群是同构的。Riehl 在上文位置将此作为连通群族结构定理的一个推论——她的命题 1.5.13，即 Structure/Groupoid/Connected.v 的 [connected_deloop_equiv]。该句子，以及该文件中关于印刷来源所述内容的其他所有描述，都是对所引用位置陈述的意译，而非引用；下面的证明是该库的原创。

 目录：Full_Compose             完全性在函子组合下是封闭的
 Faithful_Compose         保真性也是如此
 deloop_ff_moniso         单对象范畴之间的全保真函子是一个幺半群同构
 deloop_equiv_moniso      等价情况下也是如此，通过完全+保真
 connected_vertex_moniso  概要：连通群组oid中任意两个对象的顶点群是同构的
 Bool_Wide_vertex_moniso  在具有两个不同对象的群组oid中实例化的概要，这两个对象的顶点群都是Z/2
 Bool_Wide_vertex_groups_agree,
 Bool_Wide_vertex_moniso_trivial
 以及精确测量多少哦，那实例化显示：没什么特别的

 已导出，目前没有消费者。根据 `.glob` 参考记录进行计数，而不是通过读取，下列 27 个常量中有 7 个在树中没有任何引用，包括此文件。它们中的 6 个是按设计为终端的——[Bool_Wide_objects_distinct]、[Bool_Wide_vertex_monoid_false]、[Bool_Wide_vertex_inv_false]、[Bool_Wide_vertex_groups_agree]、[Bool_Wide_vertex_moniso_trivial] 和 [Bool_Wide_vertex_moniso] 的存在正是为了作为链的末端。第七个，[deloop_equiv_moniso]，是一个真正的孤立值：它是 [deloop_ff_moniso] 的等价级形式，而标题没有通过它，因为 [connected_vertex_moniso] 手中有 COMPOSITE 的 [Full] 和 [Faithful]，而不是它的 [EquivalenceOfCategories]，所以它直接调用 [deloop_ff_moniso]。它完成了这一对并被保留；此文件自身不会删除任何内容，是否保留或删除由维护者决定。（标题 [connected_vertex_moniso] 本身不在该列表中：Instance/Top/FundamentalGroupoid.v 使用了它。）
*)

(*
 Two routes to the same type, and why this file takes the longer one

 The type [MonIso (vertex_group G x) (vertex_group G y)] is ALREADY
 inhabited in this tree.  Structure/Groupoid.v's [conjugation_iso] takes
 an arrow f : x ~> y and produces a [MonIso] between those very two vertex
 groups by conjugation, a ↦ f ∘ a ∘ f⁻¹, checking the two round trips by a
 direct cancellation; and Structure/Groupoid/Connected.v's
 [Bool_Wide_conjugation] is that route taken at a concrete connected
 groupoid, with the arrow supplied by Connected.v's [connected_arrow].
 That is the short route, and it is not the one taken here.

 This file derives the isomorphism from the STRUCTURE THEOREM instead.  The
 chain is:

 - [vertex_incl G x] (Connected.v) includes the delooping of the
 vertex group at x into C, fully faithfully (Connected.v);

 - [connected_deloop_equiv G K y] (Connected.v) says the corresponding
 inclusion at y is an EQUIVALENCE OF CATEGORIES — not an isomorphism of
 categories, and the difference is real: the delooping has exactly one
 object (Structure/Groupoid.v's [Deloop_one_object]) while the
 [Bool_Wide] witness at the end of this file has two.  Its quasi-inverse
 Q : C ⟶ B(hom(y,y)) is again full and faithful, by
 Theory/Equivalence/FullFaithful.v's [Equivalence_Full] applied to
 the symmetric equivalence (Theory/Equivalence.v's
 [EquivalenceOfCategories_sym]) and by that file's
 [Equivalence_Inverse_Faithful];

 - so the composite Q ◯ [vertex_incl G x] is a full and faithful functor
 between two DELOOPINGS, and [deloop_ff_moniso] below turns any such
 functor into a [MonIso] — a pair of monoid homomorphisms that are
 mutually inverse up to `≈`, hence an isomorphism of the underlying
 setoids, rather than only an equivalence of one-object categories.

 Two honest caveats.  First, nothing here claims the isomorphism produced
 below agrees with the conjugation isomorphism; both are constructed from
 choices (a zig-zag, a quasi-inverse), and no comparison between them is
 proved.  Second, “isomorphic as groups” is justified because
 Structure/Groupoid.v's [MonHom_grp_inv] shows a monoid homomorphism
 between groups automatically preserves inverses — the reason that file
 defines no separate class of group homomorphisms, as its own note at lines
 401-407 records.  So [MonIso] between the underlying monoids of two vertex
 groups IS a group isomorphism, and its fields do assert an element-level
 correspondence: [moniso_to_from] and [moniso_from_to]
 (Structure/Groupoid.v) say the two maps are mutually inverse up
 to `≈`.

 What the longer route buys is that the group-level statement is exhibited
 as a CONSEQUENCE of the category-level one rather than as a parallel fact
 proved twice.  The intermediate step, [deloop_ff_moniso], is the missing
 half of the group/one-object-groupoid dictionary that Construction/Deloop.v
 deliberately left out: its header defers “the functor-level
 half of the dictionary — that functors between deloopings are exactly
 monoid homomorphisms” to later work.  This is the isomorphism-level part of
 that half. 

 --------
 两条通向同一类型的路径，以及为什么此文件采取了较长的路径

 类型 [MonIso (vertex_group G x) (vertex_group G y)] 已经
 存在于这棵树中。Structure/Groupoid.v 的 [conjugation_iso] 接受一个箭头 f : x ~> y 并通过共轭 a ↦ f ∘ a ∘ f⁻¹ 在这两个顶点群之间产生一个 [MonIso]，通过直接消去检查两个往返路径；而 Structure/Groupoid/Connected.v 的 [Bool_Wide_conjugation] 是在具体连通群范畴中采取那条路径，箭头由 Connected.v 的 [connected_arrow] 提供。这是短路径，但这里没有采取它。

 此文件改为从结构定理推导同构。链条是：

 - [vertex_incl G x]（Connected.v）将顶点群在 x 的去环化完整忠实地包含到 C（Connected.v）中；-  [connected_deloop_equiv G K y]（Connected.v）说，对于 y 的相应包含是范畴的等价——而不是范畴的同构，这两者之间是有区别的：去环化恰好有一个对象（Structure/Groupoid.v 的 [Deloop_one_object]），而本文件末尾的 [Bool_Wide] 证明有两个。它的拟逆 Q : C ⟶ B(hom(y,y)) 同样是充满且忠实的，这是通过 Theory/Equivalence/FullFaithful.v 中的 [Equivalence_Full] 应用于对称等价（Theory/Equivalence.v 的 [EquivalenceOfCategories_sym]）以及该文件的 [Equivalence_Inverse_Faithful] 得到的；- 因此复合函子 Q ◯ [vertex_incl G x] 是两个 DELOOPINGS 之间的满且忠实函子，而下方的 [deloop_ff_moniso] 将任何这样的函子转换为 [MonIso] —— 一个单体同态对，其互为 `≈` 意义下的逆，因此它是基础集合论的同构，而不仅仅是单对象范畴的等价。有两个坦率的警告。首先，这里没有声称下面产生的同构与共轭同构相一致；两者都是从选择（之字形、拟逆）构造的，并且没有证明它们之间的比较。其次，“作为群同构”是有理由的，因为 Structure/Groupoid.v 中的 [MonHom_grp_inv] 显示群之间的幺半群同态自动保持逆元——这也是该文件在第 401-407 行的注释中指出没有定义单独的群同态类的原因。所以两个顶点群的基础幺半群之间的 [MonIso] 确实是群同构，并且其字段确实断言了元素级对应：ZWZ17WZZ 和 [moniso_from_to]（Structure/Groupoid.v）表明这两个映射是互为逆映射，直到 `≈`。较长路线的好处在于，群体层面的陈述被展示为类别层面陈述的结果，而不是作为一个被证明了两次的平行事实。中间步骤，[deloop_ff_moniso]，是 Construction/Deloop.v 故意省略的群体/单对象群体字典的缺失一半：它的标题将“字典的函子层面的一半——即去环绕之间的函子恰好是幺半群同态”推迟到后续的工作中。这是那一半的同构层面部分。
*)

(* * ** Fullness and faithfulness are closed under composition / * ** 完备性和忠实性在复合下是封闭的 *)

(*
 Neither lemma is in the tree: no in-tree statement concludes [Full] or
 [Faithful] of a composite.  Both are immediate.

 In each proof the two [Full] (resp. [Faithful]) hypotheses are ordinary
 explicit arguments, and every projection below names its record in full —
 [@prefmap C D G FG x y ...] rather than a bare [prefmap].  No instance
 search takes part in either proof, so nothing turns on which of the two
 hypotheses resolution would otherwise have picked. 

 --------
 两个引理都不在树中：树中没有任何陈述能得出复合体的 [Full] 或 [Faithful]。它们都是立即成立的。

 在每个证明中，这两个 [Full]（分别为 [Faithful]）假设都是普通的显式参数，并且下面的每个投影都完整地命名其记录——使用 [@prefmap C D G FG x y ...] 而不是单纯的 [prefmap]。在任何一个证明中都没有实例搜索参与，因此无论解析本来会选择哪一个假设，都不会影响结果。
*)

(*
 The composite of two full functors is full: take the preimage under F
 first, then the preimage of THAT under G.  [fmap[F ◯ G]] is
 [fmap[F] ∘ fmap[G]] by definition of Theory/Functor.v's [Compose], so
 the two sections cancel in turn — the inner one underneath [fmap[F]], where
 [fmap_respects] carries it, and the outer one outright. 

 --------
 两个满函子（full functors）的复合是满的：首先取 F 下的原像，然后取那个原像在 G 下的原像。[fmap[F ◯ G] ] 根据 Theory/Functor.v 的定义 [Compose] ，是 [fmap[F] ∘ fmap [G] ]，所以两个部分依次抵消——内部部分在 [fmap[F] ] 之下，由 [fmap_respects]  承载，而外部部分直接抵消。
*)
Definition Full_Compose {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  (FF : Full F) (FG : Full G) : Full (F ◯ G).
Proof.
  refine (@Build_Full C E (F ◯ G)
            (fun x y h => @prefmap C D G FG x y
                            (@prefmap D E F FF (G x) (G y) h)) _).
  intros x y h.
  transitivity (@fmap D E F (G x) (G y) (@prefmap D E F FF (G x) (G y) h)).
  - apply (@fmap_respects D E F (G x) (G y)).
    exact (@fmap_sur C D G FG x y (@prefmap D E F FF (G x) (G y) h)).
  - exact (@fmap_sur D E F FF (G x) (G y) h).
Defined.

(*
 The composite of two faithful functors is faithful: reduce the goal by G's
 injectivity, then by F's, which lands exactly on the hypothesis. 

 --------
 两个忠实函子的复合是忠实的：首先通过 G 的单射性来简化目标，然后通过 F 的单射性，这正好对应假设。
*)
Definition Faithful_Compose {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  (FF : Faithful F) (FG : Faithful G) : Faithful (F ◯ G).
Proof.
  refine (@Build_Faithful C E (F ◯ G) _).
  intros x y f g H.
  apply (@fmap_inj C D G FG x y).
  apply (@fmap_inj D E F FF (G x) (G y)).
  exact H.
Defined.

(* * ** A fully faithful functor between deloopings is a monoid isomorphism / * ** 在去圈化之间的完全忠实函子是一个单子同构 *)

(*
 Construction/Deloop.v makes [Deloop M] a category with the single
 object [ttt] (its object type is [poly_unit], as
 Structure/Groupoid.v's [Deloop_one_object] records by [eq_refl]), whose
 hom-setoid at that object IS the carrier setoid of M, whose identity IS the
 unit and whose composition IS the operation.  Each of those is a
 definitional equality, not a coincidence to be transported; they are among
 the agreements that let Construction/Deloop.v's [hom_monoid_Deloop]
 close by [eq_refl] (the note there adds the law fields and record eta).

 Consequently a functor F : B M ⟶ B N carries, at the unique object, a map
 [carrier M → carrier N] which is a monoid homomorphism for free — the two
 functor laws ARE the two homomorphism laws, and [fmap_respects] IS the
 [Proper] field.  That direction is [deloop_fwd] below and costs nothing.

 The content is the other direction.  [Full] (Theory/Functor.v) supplies
 only a SECTION [prefmap] of the hom-map, with no functoriality demanded of
 it — that file's header says so in terms, recording that a
 previous definition's [prefmap_respects], [prefmap_id] and [prefmap_comp]
 fields were extraneous.  So that [prefmap] is a monoid homomorphism has to
 be PROVED, and faithfulness is what proves it: each law is checked after
 applying the injective [fmap[F]], where the section law [fmap_sur] collapses
 everything.  [deloop_bwd_respects], [deloop_bwd_unit] and [deloop_bwd_op]
 below are those three arguments written out.

 The [Proof using F FF Ffaith] annotation appears on FOUR lemmas below, not
 three: those three, and [deloop_bwd_fwd], which settles the other round
 trip by the same appeal to faithfulness.  The annotation is forced by the
 [Default Proof Using “Type”] setting of Lib.v: [Ffaith] is used in each
 of those four proofs but does not occur in any of their statements, so it
 would otherwise not be retained when the section closes.  The section's
 other four lemmas — [deloop_fwd_bwd], [deloop_fwd_respects],
 [deloop_fwd_unit] and [deloop_fwd_op] — do not need it: the last three are
 functor laws read off through the delooping dictionary and the first is
 [Full]'s section law verbatim, so none of them mentions [Ffaith] at all.
 This is the same per-lemma idiom as Adjunction/Continuity.v rather than
 Construction/Localization/Universal.v's file-wide
 [Set Default Proof Using “All”]. 

 --------
 Construction/Deloop.v 将 [Deloop M] 构造成一个只有单个对象 [ttt] 的范畴（其对象类型是 [poly_unit]，正如 Structure/Groupoid.v 的 [Deloop_one_object] 通过 [eq_refl] 记录的那样），该对象处的同态集合是 M 的承载集合，其恒等元是单位元，组合是运算。每一个都是定义上的等式，而非需要传递的巧合；它们属于让 Construction/Deloop.v 的 [hom_monoid_Deloop] 通过 [eq_refl] 闭合的协议（那里注释里增加了律字段和记录 η）。

 因此，一个函子 F : B M ⟶ B N 在唯一对象上携带一个映射 [carrier M → carrier N]，它自然就是一个幺半群同态——两个函子律就是两个同态律，[fmap_respects] 就是 [Proper] 字段。这个方向就是下面的 [deloop_fwd]，且不需要额外代价。内容是相反方向的。[Full]（Theory/Functor.v）仅提供了同态映射的一个 SECTION [prefmap]，并没有要求它具有函子性——那个文件的头部以术语的形式说明了这一点，记录了先前定义的 [prefmap_respects]、[prefmap_id] 和 [prefmap_comp] 字段是多余的。因此 [prefmap] 是一个幺半群同态必须被证明，而忠实性就是证明它的方法：在应用单射 [fmap[F] 后检查每条定律，其中段法则 [fmap_sur] 将一切折叠。下面的 [deloop_bwd_respects]、[deloop_bwd_unit] 和 [deloop_bwd_op] 是这三个参数的完整写法。[Proof using F FF Ffaith] 注释出现在下面的四个引理中，而不是三个：那三个，以及 [deloop_bwd_fwd]，它通过同样依赖忠实性的方式解决了另一次往返。这个注释是由 Lib.v 的 [Default Proof Using “Type”] 设置强制的：[Ffaith] 在这四个证明中每一个都被使用，但在它们的陈述中并未出现，因此在章节关闭时否则不会被保留。该章节的其他四个引理——[deloop_fwd_bwd]、[deloop_fwd_respects]、[deloop_fwd_unit] 和 [deloop_fwd_op]——不需要它：后三个是通过 delooping 字典读取的函子律，第一个是 [Full] 的章节律逐字引用，因此它们都没有提到 [Ffaith]。这与 Adjunction/Continuity.v 的每个引理习惯相同，而不是 Construction/Localization/Universal.v 的整个文件范围的 [Set Default Proof Using “All”]。
*)

Section DeloopFullyFaithful.

Context {M N : MonObject}.
Context (F : Deloop M ⟶ Deloop N).
Context (FF : Full F).
Context (Ffaith : Faithful F).

(*
 The forward map: the hom-map of F at the unique object.  Its type is
 [carrier M → carrier N] on the nose, the hom-setoids of the two deloopings
 being the two carrier setoids. 

 --------
 前向映射：F 在唯一对象处的同态映射。它的类型正是 [carrier M → carrier N]，两个去环化的同态集构成两个载体同态集。
*)
Definition deloop_fwd (a : carrier M) : carrier N := @fmap _ _ F ttt ttt a.

(* The backward map: the chosen section of that hom-map. / 反向映射：该同态映射的选定部分。 *)
Definition deloop_bwd (b : carrier N) : carrier M :=
  @prefmap _ _ F FF ttt ttt b.

(* One round trip is the section law verbatim. / 一次往返是该条文逐字的部分。 *)
Lemma deloop_fwd_bwd (b : carrier N) : deloop_fwd (deloop_bwd b) ≈ b.
Proof. exact (@fmap_sur _ _ F FF ttt ttt b). Qed.

(* The other follows from it by faithfulness: the two elements have the same image under the injective hom-map. / 另一个由忠诚性从中得出：这两个元素在单射同态映射下具有相同的像。 *)
Lemma deloop_bwd_fwd (a : carrier M) : deloop_bwd (deloop_fwd a) ≈ a.
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  exact (@fmap_sur _ _ F FF ttt ttt (deloop_fwd a)).
Qed.

(*
 The forward map is a monoid homomorphism, by the three functor laws read
 through the delooping dictionary: [fmap_respects] is respectfulness,
 [fmap_id] is preservation of the unit (the identity arrow IS the unit), and
 [fmap_comp] is preservation of the operation (composition IS the
 operation). 

 --------
 通过绕回字典阅读三个函子定律，前向映射是一个幺半群同态：[fmap_respects] 表示尊重性，[fmap_id] 表示单位的保持（恒等箭头就是单位），而 [fmap_comp] 表示运算的保持（组合就是运算）。
*)
Lemma deloop_fwd_respects : Proper (equiv ==> equiv) deloop_fwd.
Proof. exact (@fmap_respects _ _ F ttt ttt). Qed.

Lemma deloop_fwd_unit : deloop_fwd mon_unit ≈ mon_unit.
Proof. exact (@fmap_id _ _ F ttt). Qed.

Lemma deloop_fwd_op (a b : carrier M) :
  deloop_fwd (mon_op a b) ≈ mon_op (deloop_fwd a) (deloop_fwd b).
Proof. exact (@fmap_comp _ _ F ttt ttt ttt a b). Qed.

(*
 The backward map is a monoid homomorphism too, but nothing in [Full]
 asserts it: each of the three laws is established by applying the injective
 forward map and then cancelling with [deloop_fwd_bwd]. 

 --------
 逆映射也是一个幺半群同态，但在 [Full] 中没有任何内容断言它：这三个定律中的每一个都是通过应用单射的正向映射然后与 [deloop_fwd_bwd] 抵消来建立的。
*)

Lemma deloop_bwd_respects : Proper (equiv ==> equiv) deloop_bwd.
Proof using F FF Ffaith.
  intros b b' Hb.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity b; [ exact (deloop_fwd_bwd b) | ].
  transitivity b'; [ exact Hb | ].
  symmetry.
  exact (deloop_fwd_bwd b').
Qed.

Lemma deloop_bwd_unit : deloop_bwd mon_unit ≈ mon_unit.
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity (@mon_unit N); [ exact (deloop_fwd_bwd mon_unit) | ].
  symmetry.
  exact deloop_fwd_unit.
Qed.

Lemma deloop_bwd_op (a b : carrier N) :
  deloop_bwd (mon_op a b) ≈ mon_op (deloop_bwd a) (deloop_bwd b).
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity (mon_op a b); [ exact (deloop_fwd_bwd (mon_op a b)) | ].
  transitivity (mon_op (deloop_fwd (deloop_bwd a)) (deloop_fwd (deloop_bwd b))).
  - apply (mon_op_respects N); symmetry; apply deloop_fwd_bwd.
  - symmetry.
    exact (deloop_fwd_op (deloop_bwd a) (deloop_bwd b)).
Qed.

(*
 The two records are built the way [conjugation] is at
 Structure/Groupoid.v — constructor applied to explicit monoid arguments
 rather than record syntax.  The note there gives the
 reason: the field type [carrier (mon_setoid ?M)] does not determine ?M by
 unification alone. 

 --------
 这两个记录的构建方式是 [conjugation] 在 Structure/Groupoid.v 中——构造函数应用于显式的幺半群参数，而不是使用记录语法。那里的注释给出了原因：字段类型 [carrier (mon_setoid ?M)] 本身无法仅通过统一确定 ?M。
*)
Definition deloop_MonHom_fwd : MonHom M N :=
  @Build_MonHom M N deloop_fwd deloop_fwd_respects deloop_fwd_unit
    deloop_fwd_op.

Definition deloop_MonHom_bwd : MonHom N M :=
  @Build_MonHom N M deloop_bwd deloop_bwd_respects deloop_bwd_unit
    deloop_bwd_op.

Definition deloop_ff_moniso : MonIso M N :=
  @Build_MonIso M N deloop_MonHom_fwd deloop_MonHom_bwd
    deloop_fwd_bwd deloop_bwd_fwd.

End DeloopFullyFaithful.

(*
 The equivalence-level form, by the two halves of the full-and-faithful
 characterization in Theory/Equivalence/FullFaithful.v ([Equivalence_Full]
 and [Equivalence_Faithful]). 

 --------
 等价水平形式，由 Theory/Equivalence/FullFaithful.v（[Equivalence_Full] 和 [Equivalence_Faithful]）中完整且忠实刻画的两个部分组成。
*)
Definition deloop_equiv_moniso {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (E : EquivalenceOfCategories F) : MonIso M N :=
  deloop_ff_moniso F (Equivalence_Full E) (Equivalence_Faithful E).

(* * ** The headline: base-point independence of the vertex group / * **标题：顶点群的基点独立性 *)

(*
 Riehl's Corollary 1.5.14, in the form paraphrased at the head of this file.
 The comparison functor is assembled from the structure theorem at the
 TARGET base point y: quasi-invert the inclusion of hom(y, y), then precede
 it by the inclusion of hom(x, x).  What comes out is a functor between two
 one-object categories, and [deloop_ff_moniso] converts it. 

 --------
 Riehl 的推论 1.5.14，以本文件开头的释义形式。比较函子是从目标基点 y 的结构定理组装而成：将 hom(y, y) 的包含准逆，然后在它之前加上 hom(x, x) 的包含。结果是两个单对象类别之间的函子，而 [deloop_ff_moniso] 进行转换。
*)

Section ConnectedVertex.

Context {C : Category}.
Context (G : IsGroupoid C).
Context (K : Connected C).
Context (x y : C).

(* The structure theorem at y. / 在 y 处的结构定理。 *)
Definition basepoint_equiv : EquivalenceOfCategories (vertex_incl G y) :=
  connected_deloop_equiv G K y.

(*
 The comparison functor B(hom(x, x)) ⟶ B(hom(y, y)).  It factors through C,
 which is the whole point: the two vertex groups are compared THROUGH the
 groupoid, not by a formula written down in advance. 

 --------
 比较函子 B(hom(x, x)) ⟶ B(hom(y, y))。它通过 C 进行分解，这正是关键点：两个顶点群是通过群对象来比较的，而不是事先写下的公式。
*)
Definition basepoint_compare :
  Deloop (vertex_group G x) ⟶ Deloop (vertex_group G y) :=
  @quasi_inverse _ _ _ basepoint_equiv ◯ vertex_incl G x.

(*
 Its fullness: the right factor by [vertex_incl_Full], the left by
 [Equivalence_Full] at the symmetric equivalence — the quasi-inverse of an
 equivalence is an equivalence, hence full. 

 --------
 它的充足性：在对称等价下，由 [vertex_incl_Full] 作用于右边，由 [Equivalence_Full] 作用于左边 — 等价的拟逆是等价，因此是充足的。
*)
Definition basepoint_compare_Full : Full basepoint_compare :=
  Full_Compose (@quasi_inverse _ _ _ basepoint_equiv) (vertex_incl G x)
    (@Equivalence_Full _ _ _
       (@EquivalenceOfCategories_sym _ _ _ basepoint_equiv))
    (vertex_incl_Full G x).

(*
 Its faithfulness, the same way; the left factor is
 [Equivalence_Inverse_Faithful], which is that same symmetric-equivalence
 argument already packaged in Theory/Equivalence/FullFaithful.v. 

 --------
 它的忠实度，以同样的方式；左因子是 [Equivalence_Inverse_Faithful]，这就是已经在 Theory/Equivalence/FullFaithful.v 中打包好的相同对称等价论证。
*)
Definition basepoint_compare_Faithful : Faithful basepoint_compare :=
  Faithful_Compose (@quasi_inverse _ _ _ basepoint_equiv) (vertex_incl G x)
    (Equivalence_Inverse_Faithful basepoint_equiv)
    (vertex_incl_Faithful G x).

(*
 The vertex groups at any two objects of a connected groupoid are isomorphic
 as groups.  Both objects are universally quantified and no property of
 either is used, so the vertex groups at ALL objects of a connected groupoid
 are isomorphic to one another.

 Not proved, and not claimed: that this family of isomorphisms is coherent —
 that the one from x to z agrees with the composite of those from x to y and
 from y to z.  Each is built from a choice (the zig-zag inside K, the
 quasi-inverse inside [basepoint_equiv]), and no comparison between choices
 is made anywhere below. 

 --------
 连通群体的任意两个对象的顶点群作为群是同构的。两个对象都是全称量化的，并且没有使用它们的任何性质，因此连通群体中所有对象的顶点群彼此同构。

 未证明且未声明：这族同构是相干的——即从 x 到 z 的同构与从 x 到 y 再到 z 的复合同构一致。每个同构都是由一个选择构建的（K 内的之字形，[basepoint_equiv] 内的准逆），并且在下面的任何地方都没有对这些选择进行比较。
*)
Definition connected_vertex_moniso :
  MonIso (vertex_group G x) (vertex_group G y) :=
  deloop_ff_moniso basepoint_compare
    basepoint_compare_Full basepoint_compare_Faithful.

End ConnectedVertex.

(* * ** The hypotheses are satisfiable, and the derivation runs / * ** 假设是可满足的，并且推导可以运行 *)

(*
 [Bool_Wide] (Structure/Groupoid/Connected.v) is
 [WideDeloop Bool_Xor_Grp bool]: its objects are the booleans, and its
 hom-setoid at every pair is the carrier setoid of Z/2.  It is a groupoid
 (Connected.v) and connected (Connected.v), which are exactly the two
 hypotheses of the headline, so [connected_vertex_moniso] applies to it, and
 [Bool_Wide_vertex_moniso] below is that application.

 WHAT THIS WITNESS DOES NOT SHOW, AND WHY.  It does not show that the
 conclusion is ever informative, and the reason is structural rather than
 incidental.  [WideDeloop] fixes the hom TYPE uniformly — Connected.v
 reads [hom := fun _ _ => carrier M] — so the vertex group at [true] and the
 vertex group at [false] are not merely isomorphic groups but the SAME
 monoid.  [Bool_Wide_vertex_groups_agree] below records that by [eq_refl] at
 the monoid data field, which is exactly the field a [MonIso] is a statement
 about; and [Bool_Wide_vertex_moniso_trivial] then inhabits the very type of
 [Bool_Wide_vertex_moniso] with the identity maps and [reflexivity] alone —
 no [Connected], no [deloop_ff_moniso], no structure theorem, nothing from
 this file.  So what [Bool_Wide_vertex_moniso] exercises is that the two
 HYPOTHESES are satisfiable together and that the derivation type-checks;
 the type it lands in was already inhabited without any of it.  Choosing a
 different group would not help: [WideDeloop S3_Grp bool] has the same
 defect, at every [M] and every [A].

 The objects [true] and [false] are indeed distinct
 ([Bool_Wide_objects_distinct] below), so the instance does compare vertex
 groups at two different OBJECTS rather than at one object with itself.
 That is a statement about the objects and NOT about the groups: here
 distinct objects do not give distinct vertex groups, and an earlier
 revision of this note put the two side by side in a way that implied they
 did.

 NO IN-TREE OBJECT DOES BETTER TODAY.  The only connected groupoids the
 library builds are the [WideDeloop] family, which has the defect just
 described, and [FundamentalGroupoid X] for a path-connected X, whose sole
 witness is [TwoPoint_Indiscrete] (Instance/Top/FundamentalGroupoid.v —
 a forward reference; that file depends on this one and not the other way
 round).  There the two vertex groups are at least different monoids, on
 different carriers, so the identity does not inhabit the type; but both are
 TRIVIAL ([TwoPoint_Indiscrete_loops_trivial] there), so an isomorphism is
 again available without the theorem.  ([Roof] is connected but is not a
 groupoid, so it does not enter.)  Making the conclusion informative would
 need a connected groupoid whose vertex group depends on the object and is
 nonabelian; Structure/Groupoid.v's [S3_Grp] supplies such a group, but
 nothing in the tree spreads it over objects non-uniformly.

 Both vertex groups really are Z/2, in both data fields and on the nose.
 Connected.v records the underlying monoid and the inversion
 operation at [true]; two of the [Example]s below record the same at
 [false].  (Each [=] is an equality of a data field, which is strictly
 stronger than any statement made with `≈`, and each holds by [eq_refl].)

 Nothing is asserted about the underlying map of [Bool_Wide_vertex_moniso]:
 it is built from the quasi-inverse chosen by [FF_ESO_Equivalence], this
 file computes nothing about it, and in particular it is NOT proved to be
 the identity isomorphism exhibited below. 

 --------
 [Bool_Wide]（Structure/Groupoid/Connected.v）是
 [WideDeloop Bool_Xor_Grp bool]：它的对象是布尔值，并且每对对象的同态集是 Z/2 的承载集合。它是一个群族（Connected.v）并且是连通的（Connected.v），这正好是标题中的两个假设，因此 [connected_vertex_moniso] 可应用于它，而下面的 [Bool_Wide_vertex_moniso] 是该应用。这个证据没有展示的内容，以及原因。它没有表明结论是有信息量的，并且原因是结构性的而非偶然的。[WideDeloop] 统一地固定了同态类型 — Connected.v 读取 [hom := fun _ _ => carrier M] — 因此在 [true] 的顶点群和在 [false] 的顶点群不仅仅是同构群，而是相同的幺半群。下面的 [Bool_Wide_vertex_groups_agree] 记录了在幺半群数据字段 [eq_refl] 的情况，这正是 [MonIso] 所陈述的字段；然后 [Bool_Wide_vertex_moniso_trivial] 占据了 [Bool_Wide_vertex_moniso] 的类型，仅使用恒等映射和 [reflexivity] — 没有 [Connected]，没有 [deloop_ff_moniso]，没有结构定理，也没有该文件中的其他内容。所以 [Bool_Wide_vertex_moniso] 的练习是两个假设可以同时满足，并且推导类型检查有效；它最终得到的类型在没有任何这些的情况下已经是有定义的。选择不同的群组也无济于事：[WideDeloop S3_Grp bool] 在每一个 [M] 和每一个 [A] 上都有同样的缺陷。

 对象 [true] 和 [false] 确实是不同的（如下 [Bool_Wide_objects_distinct]），因此实例确实是在两个不同的对象上比较顶点群组，而不是在同一个对象上自比较。这是关于对象的陈述，而不是关于群组的：这里不同的对象并不产生不同的顶点群组，并且此笔记的早期修订版将它们并排放置，给人一种它们是不同的印象。今天没有任何树内对象表现更好。该库构建的唯一连通群oid是 [WideDeloop] 系列，它有前面描述的缺陷，以及对于路径连通的 X 的 [FundamentalGroupoid X]，其唯一的例子是 [TwoPoint_Indiscrete]（Instance/Top/FundamentalGroupoid.v — 前向引用；该文件依赖于此文件，而不是反过来）。在那里，两个顶点群至少是不同的幺半群，在不同的载体上，因此恒等式不属于该类型；但两者都是平凡的（那里是 [TwoPoint_Indiscrete_loops_trivial]），所以无需定理仍然可以得到同构。([Roof] 是连通的，但不是群类，所以它不进入。) 使结论具有信息性需要一个连通的群类，其顶点群依赖于对象且是非阿贝尔的；Structure/Groupoid.v 的 [S3_Grp] 提供了这样的群，但树中的任何东西都没有在对象上以非均匀方式传播它。

 两个顶点群实际上都是 Z/2，无论是在数据字段中还是准确无误地。Connected.v 在 [true] 记录了底层的幺半群和逆运算；下面的两个 [Example] 在 [false] 记录了相同的内容。（每个 [=] 是数据字段的相等性，这严格强于用 `≈` 所做的任何陈述，并且每个都由 [eq_refl] 成立。）关于 [Bool_Wide_vertex_moniso] 的基础映射没有任何断言：它是由 [FF_ESO_Equivalence] 选择的拟逆构建的，该文件不计算任何关于它的内容，特别是它并没有被证明是下面展示的恒等同构。
*)

Example Bool_Wide_objects_distinct : (true : Bool_Wide) = false → False.
Proof. discriminate. Qed.

Example Bool_Wide_vertex_monoid_false :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid false) = grp_monoid Bool_Xor_Grp
  := eq_refl.

Example Bool_Wide_vertex_inv_false :
  @grp_inv (vertex_group Bool_Wide_IsGroupoid false) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(*
 The two vertex groups are the same monoid, not two isomorphic ones.  The
 whole [GrpObject]s are NOT equal — their law fields are distinct opaque
 proof terms, the point Structure/Groupoid.v makes for
 [vertex_group_Deloop_monoid] — but [MonIso] reads only the monoid, which is
 the field compared here. 

 --------
 这两个顶点群是相同的幺半群，而不是两个同构的幺半群。整个 [GrpObject] 并不相等——它们的律域是不同的不透明证明项，Structure/Groupoid.v 针对 [vertex_group_Deloop_monoid] 所建立的——但是 [MonIso] 只读取幺半群，这就是这里比较的域。
*)
Example Bool_Wide_vertex_groups_agree :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid true)
    = grp_monoid (vertex_group Bool_Wide_IsGroupoid false) := eq_refl.

(*
 Hence the type of [Bool_Wide_vertex_moniso] is inhabited by the identity,
 with no appeal to connectedness or to the structure theorem.  Every field is
 [fun a => a] or [reflexivity], and each typechecks only because of the
 agreement recorded just above. 

 --------
 因此，[Bool_Wide_vertex_moniso] 的类型是由恒等元构成的，不需要诉诸连通性或结构定理。每个域都是 [fun a => a] 或 [reflexivity]，并且每种类型仅仅因为上面记录的那个一致性而能够类型检查。
*)
Example Bool_Wide_vertex_moniso_trivial :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  @Build_MonIso _ _
    (@Build_MonHom (vertex_group Bool_Wide_IsGroupoid true)
                   (vertex_group Bool_Wide_IsGroupoid false)
       (fun a => a) (fun _ _ H => H) (reflexivity _) (fun a b => reflexivity _))
    (@Build_MonHom (vertex_group Bool_Wide_IsGroupoid false)
                   (vertex_group Bool_Wide_IsGroupoid true)
       (fun a => a) (fun _ _ H => H) (reflexivity _) (fun a b => reflexivity _))
    (fun b => reflexivity b) (fun a => reflexivity a).

Definition Bool_Wide_vertex_moniso :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  connected_vertex_moniso Bool_Wide_IsGroupoid Bool_Wide_Connected true false.
