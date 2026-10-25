Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Normal subgroups, the quotient group, and its universal property

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.1
   (printed pp. 57-59) [maclane:III.1:construction5, maclane:III.1:ex4];
   Awodey, "Category Theory", 2nd ed., §4.2 (printed pp. 83-85)
   [awodey:4.2:construction-factor-group, awodey:4.2:thm4].
   nLab: https://ncatlab.org/nlab/show/quotient+group
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_group

   For N normal in G, the projection p : G -> G/N is a UNIVERSAL ELEMENT
   of the functor of homomorphisms killing N.  Mac Lane's point in §III.1
   is that every further property of quotient groups follows from that
   universality alone, with no second look at cosets; this file proves the
   universality, and Instance/Grp/Quotient/Isomorphism.v draws the named
   consequences from it.

   ERRATUM, recorded here rather than only in a commit message.  Issue
   #313's "Current state in the library" section says the area is
   "Absent", that a search for quotient/normal/coset vocabulary "returns
   zero formal hits", and that "no category Grp exists".  All three were
   stale when this file was written: #255 landed Instance/Grp.v with
   [GrpObject], [GrpHom], [Grp], [Grp_Forget], [Grp_Zero],
   [Grp_Cartesian] and [Grp_injectivity_is_monic], and the tree also
   carries Instance/Grp/Abelianization.v, Instance/Grp/Epi.v,
   Instance/Grp/Center.v, Instance/Grp/Free.v and Instance/Ab.v, several
   of which quotient by something.  What IS absent, and was measured
   against the parent commit rather than taken on the issue's word, is a
   [NormalSubgroup] interface: AT THE PARENT COMMIT the token occurred in
   the tree exactly once, at Instance/Grp/Abelianization.v, and there
   it occurred inside a prose disclosure that no such class existed.
   (That paragraph is rewritten by this same change, so the line number
   is a statement about the parent commit and not about the tree as it
   now stands.)  The only [Subgroup] record in the tree is
   Instance/Ab/Character/Finite.v, which is over [AbObject] and
   carries a DECIDABILITY field [sg_dec]; it is therefore not a donor
   here, since nothing below decides membership.

   THE FIVE FACTS.  Instance/Grp/Abelianization.v's "SCOPE OF THE
   QUOTIENT" paragraph (at the parent commit) disclosed that its
   quotient by the commutator subgroup consumes only five properties of
   that subgroup -- "≈-saturation, unit, closure under product and
   inverse, normality" -- and that a generic quotient "is extractable by
   abstraction over exactly those five facts", left as future work.  That
   is what [Subgroup] and [NormalSubgroup] below are: four laws and one
   more, no membership decision, no smallness, no choice.  The extraction
   is carried out rather than merely announced -- Abelianization.v is
   refactored in the same change to obtain its five congruence lemmas
   from the generic ones, with its statements byte-identical (the
   Theory/EckmannHilton.v precedent), and its [CommutatorNS] supplies the
   five fields with the five facts it had already proved.

   WHAT THE UNIFICATION DOES AND DOES NOT COVER, measured.  The same
   disclosure counts "three unshared quotient constructions
   (Instance/Ab.v's [ab_coset_eq], Instance/Grp/Epi.v's [Grp_Coset], and
   this one)".  Reading the two other constructions' actual record types
   corrects the count:

   - Instance/Grp/Epi.v's [Grp_Coset] is a [SetoidObject], NOT a
   [GrpObject], and it is the coset space of the image of an
   ARBITRARY homomorphism.  Epi.v's whole argument turns on that
   image being possibly NON-normal (its own header, two later
   passages, and the witness [grp_two_sym3] are explicit that the
   non-normal case is the one the file exists for).  So it is not a
   quotient GROUP, is not an instance of anything below, and could
   not be: a normal-subgroup quotient is exactly what it declines to
   assume.  It is left untouched.

   - Instance/Ab.v's [ab_coset_eq] IS a quotient group, of an
   abelian group by the image of a homomorphism.  (An earlier revision
   of this sentence cited where that definition stood
   before the PR "algebraic carriers are sets" (2026-09-17); the same
   PR also turned the relation into a [Prop] -- it is now Coq's [ex],
   spelled [(exists a, …)%type] -- so it is no longer a [Type]-valued
   sigma either.)  It is not routed
   through this file either, and the reason is a dependency
   direction rather than a mathematical obstruction: [AbObject]
   extends [CMonObject], Instance/Ab.v requires neither
   Instance/Grp.v nor anything below it, and the only bridge in tree,
   [Ab_to_GrpOb], lives DOWNSTREAM in Abelianization.v.  Routing
   Ab.v's quotient through a [GrpObject]-level construction would
   move that bridge upstream and give Ab.v a dependency on Grp.
   That is a defensible change and it is deliberately not made here.

   So of the three, one is unified, one is shown not to be an instance of
   the notion at all, and one is declined with its reason stated.  No
   fourth quotient construction is introduced: everything below, and
   everything in the two sibling files, quotients by [quot_rel].

   THE SETOID QUOTIENT.  As in Abelianization.v, G/N needs no new
   carrier: it is G's carrier under the coarser relation
   [quot_rel N a b := N (a * b⁻¹)] -- or rather, since the PR "algebraic
   carriers are sets" (2026-09-17), under its PROPOSITIONAL TRUNCATION
   [inhabited (quot_rel N a b)], the relation itself staying [Type]-valued
   because [sub_mem] does.  The equivalence laws are the group
   laws; multiplication and inversion respect the relation by NORMALITY,
   which is where [ns_conj] earns its keep.  Elements of G/N are
   therefore elements of G, and no coset object is ever formed -- which
   is convenient, but is NOT what makes the derivations below universal:
   the arguments in the sibling files run through [quot_universal_element] and
   the mediator's uniqueness, not through element representatives, and
   where an element-level step does occur it is called out.

   WHAT IS DELIVERED HERE.  [Subgroup] and [NormalSubgroup]; the subgroup
   as an object of [Grp] with its inclusion; [QuotientGrp] with the
   projection [quot_proj]; the functor [KillsFunctor N : Grp ⟶ Sets] of
   homomorphisms killing N, and [quot_universal_element], the statement
   that ⟨G/N, p⟩ is a universal element of it, over #303's
   [AUniversalElement] -- the CLASS is used directly, and none of
   Theory/Universal/Element.v's Yoneda packaging
   ([universal_element_yoneda], [universal_element_representation]) is
   touched, so the universe restriction that packaging carries (object,
   hom and proof universes identified) is not inherited; the sibling
   files likewise reach [universal_element_iso], which lives in that
   file's Yoneda-free section;
   Awodey's Theorem 4.4 as the biconditional [hom_theorem]; the kernel of
   a homomorphism as a normal subgroup ([KernelNS], the transplant from
   #301); and the degenerate cases named and separated by proof
   ([TrivialNS], [TotalNS], and the S3 witnesses).

   WHAT IS NOT DELIVERED HERE.  No lattice of subgroups, no index, no
   Lagrange, no correspondence theorem, no solvability; no [HasCokernels]
   instance for [Grp] (the cokernel of a SINGLE map is built in the
   Colimit sibling, but no choice of cokernel for every map is packaged);
   no [Subgroup]-of-[Subgroup] calculus beyond what the second
   isomorphism theorem consumes; and no comparison with
   Instance/Ab/Character/Finite.v's decidable [Subgroup].

   NO UNIVERSAL-ARROW PACKAGING, and the reason is structural rather than
   a shortage of effort.  Theory/Universal/Element.v's
   [universal_element_arrow_subsumption] relates universal elements of a
   functor H to universal arrows exactly when H has the shape
   d ↦ Hom(c, S d) for a functor S.  [KillsFunctor N] does not: it is the
   SUBfunctor of Hom(G, −) cut out by the killing condition, and that
   condition mentions N, which is data attached to G rather than
   something a functor out of [Grp] supplies.  So the universal-ELEMENT
   reading is the one Mac Lane's §III.1 states and the only one taken
   here; no [AUniversalArrow] is claimed. 

   --------
   * * 正规子群、商群及其泛性质

   Mac Lane，《为工作数学家准备的范畴论》，第2版，第III.1节
   （印刷页 57-59） [maclane:III.1:construction5, maclane:III.1:ex4]；
   Awodey，《范畴论》，第2版，第4.2节（印刷页 83-85）
   [awodey:4.2:construction-factor-group, awodey:4.2:thm4]。
   nLab：https://ncatlab.org/nlab/show/quotient+group
   维基百科：https://en.wikipedia.org/wiki/Quotient_group

   对于 G 中的正规子群 N，投射 p : G -> G/N 是
   将 N 映为零的同态函子中的一个泛元素。Mac Lane 在第III.1节的观点
   是，每个商群的进一步性质都仅仅由这种泛性得到，而无需再次考察陪集；
   本文件证明了这种泛性，而 Instance/Grp/Quotient/Isomorphism.v 则从中
   推导出了已命名的结果。勘误，记录在这里，而不仅仅是在提交信息中。Issue #313 的“库中的当前状态”部分说该区域是“缺失的”，搜索 quotient/normal/coset 词汇“没有返回正式匹配”，并且“没有 Grp 类别存在”。当此文件编写时，这三点信息都是过时的：#255 已经引入了 Instance/Grp.v，其中包含 [GrpObject]、[GrpHom]、[Grp]、[Grp_Forget]、[Grp_Zero]、[Grp_Cartesian] 和 [Grp_injectivity_is_monic]，并且代码树还包含 Instance/Grp/Abelianization.v、Instance/Grp/Epi.v、Instance/Grp/Center.v、Instance/Grp/Free.v 和 Instance/Ab.v，其中几个进行了某些对象的商操作。缺失的部分，并且是以父提交为衡量标准，而不是根据问题本身的说法，是一个 [NormalSubgroup] 接口：在父提交时，该标记在树中恰好出现过一次，位于 Instance/Grp/Abelianization.v 中，并且它出现在一个说明该类不存在的文字说明中。（该段落被同一次更改重写，因此行号是关于父提交的说明，而不是关于当前树的状态。）树中唯一的 [Subgroup] 记录是 Instance/Ab/Character/Finite.v，它位于 [AbObject] 之上，并携带一个 DECIDABILITY 字段 [sg_dec]；因此，它在此处不是捐赠者，因为下面没有任何东西决定成员资格。五个事实。Instance/Grp/Abelianization.v 中“商的范围”（SCOPE OF THE QUOTIENT）段落（在父提交处）披露，其通过交换子子群的商仅消耗了该子群的五个属性——“≈-饱和性、单位元、在乘积和逆元下的封闭性、正规性”——并且一个一般性商“可以通过对正好这五个事实的抽象来提取”，留作未来工作。这正是下面的 [Subgroup] 和 [NormalSubgroup]：四条定律和另外一条，没有成员决定、没有小性、没有选择。提取是被执行的，而不仅仅是宣布——Abelianization.v 在同一次更改中被重构，以从泛型引理中获得其五个同余引理，其陈述完全相同（Theory/EckmannHilton.v 的先例），其 [CommutatorNS] 为这五个字段提供了它已经证明的五个事实。

   统一所覆盖和不覆盖的内容，经测量。同样的披露计算 "三个未共享的商构造（Instance/Ab.v 的 [ab_coset_eq]、Instance/Grp/Epi.v 的 [Grp_Coset]，以及这个构造）"。阅读另外两个构造的实际记录类型修正了计数：- Instance/Grp/Epi.v 的 [Grp_Coset] 是一个 [SetoidObject]，不是 [GrpObject]，并且它是任意同态映射的像的陪集空间。Epi.v 的整个论证都基于该像可能是非正规子群（它自己的标题、之后的两段以及见证 [grp_two_sym3] 都明确说明了非正规情况是该文件存在的原因）。因此它不是一个商群，也不是下面任何东西的实例，并且也不可能是：一个正规子群的商群正是它拒绝假定的内容。它保持不变。- 实例/Ab.v 的 [ab_coset_eq] 是一个商群，由一个阿贝尔群通过同态的像得到的。（这句话的早期修订版引用了该定义在 PR “代数承载是集合” 之前的位置（2026-09-17）；相同的 PR 也将该关系变为 [Prop] —— 它现在是 Coq 的 [ex]，拼写为 [(exists a, …)%type] —— 所以它也不再是 [Type] 值的西格玛。）它也没有通过这个文件路由，其原因是依赖方向而非数学障碍：[AbObject] 扩展 [CMonObject]，实例/Ab.v 既不需要实例/Grp.v，也不需要它下面的任何东西，而树中的唯一桥梁 [Ab_to_GrpOb] 位于 Abelianization.v 的下游。路由
   将 Ab.v 的商通过 [GrpObject] 级别的构造，会将该桥移动到上游，并使 Ab.v 对 Grp 产生依赖。这是一个可辩护的更改，但在此处故意没有执行。

   因此，在三者中，一个是统一的，一个被证明根本不是该概念的实例，另一个已被拒绝并说明了原因。没有引入第四个商构造：下方的所有内容，以及两个兄弟文件中的所有内容，都是通过 [quot_rel] 来进行商运算的。集合商。与 Abelianization.v 中一样，G/N 不需要新的载体：它是在较粗关系 [quot_rel N a b := N (a * b⁻¹)] 下的 G 的载体——或者更确切地说，由于公理“代数载体是集合”（2026-09-17），是在其命题截断 [inhabited (quot_rel N a b)] 下，关系本身保持 [Type] 值，因为 [sub_mem] 也是如此。等价律就是群律；乘法和取逆通过正规性遵守该关系，这就是 [ns_conj] 的作用所在。因此，G/N 的元素是 G 的元素，并且从不形成陪集对象 —— 这很方便，但这并不是使下面推导普遍化的原因：同级文件中的论证是通过 [quot_universal_element] 和调解者的唯一性进行的，而不是通过元素代表，并且当确实发生元素级步骤时，会被明确指出。这里交付的是什么。[Subgroup] 和 [NormalSubgroup]；子群作为 [Grp] 的一个对象及其包含；ZW43WZZ 与投影 [quot_proj]；同态函子 [KillsFunctor N : Grp ⟶ Sets] 用于消去 N，以及 [quot_universal_element]，声明 ⟨G/N, p⟩ 是它的一个普遍元素，基于 #303 的 [AUniversalElement] —— CLASS 被直接使用，并且 Theory/Universal/Element.v 的 Yoneda 封装（[universal_element_yoneda]、[universal_element_representation]）未被触碰，因此该封装携带的宇宙限制（对象、同态及证明宇宙认同）未被继承；同级文件同样到达 [universal_element_iso]，它位于该文件的 Yoneda-free 部分；Awodey 的定理 4.4 作双条件 [hom_theorem]；同态的核作为正规子群（[KernelNS]，从 #301 移植）；以及被命名和分割的退化情况由证据证明（[TrivialNS]、[TotalNS] 以及 S3 证人）。这里没有提供的内容。没有子群格，没有指标，没有拉格朗日定理，没有对应定理，没有可解性；没有 [HasCokernels] 对 [Grp] 的实例（单个映射的余核在 Colimit 的对应部分中已经构建，但并没有为每个映射提供余核的选择）；没有超出第二同构定理所涵盖的 [Subgroup] 对 [Subgroup] 的演算；也没有与 Instance/Ab/Character/Finite.v 中可判定的 [Subgroup] 的比较。没有通用箭头打包，原因是结构性的，而不是努力不足。Theory/Universal/Element.v 的 [universal_element_arrow_subsumption] 将函子 H 的通用元素与通用箭头联系起来，只有当 H 的形状为 d ↦ Hom(c, S d) 且 S 是一个函子时才成立。[KillsFunctor N] 不符合：它是 Hom(G, −) 的子函子，被杀死条件限定，而该条件提到了 N，这是附加到 G 的数据，而不是 [Grp] 提供的函子输出的数据。因此，通用元素的解读是 Mac Lane §III.1 所陈述的，也是此处采用的唯一解读；没有声称存在 [AUniversalArrow]。
*)

(* * ** Subgroups and normal subgroups / * ** 子群与正规子群 *)

(*
 A subgroup is a `≈`-saturated predicate containing the unit and closed
 under product and inverse.  Membership is [Type]-valued, following
 Instance/Grp/Epi.v's [GrpImage] and Instance/Ab/Character/Finite.v's
 [sg_mem].

 CORRECTION.  An earlier revision gave the REASON as "the library's `≈` is
 itself [Type]-valued, so a [Prop]-valued membership could not be
 eliminated into a hom-setoid equation".  That reason is gone: since the PR
 "algebraic carriers are sets" (2026-09-17) a [GrpObject] carries
 [grp_prop], and a [Prop] hypothesis reaches an `≈` goal through
 [pequiv_to] (Lib/Setoid/Propositional.v).  The CONCLUSION stands, for a
 different reason: consumers READ THE WITNESS.  Instance/Grp/Quotient/
 Isomorphism.v's [image_med] projects a preimage out of a membership proof
 into a [Type] goal, and the first isomorphism theorem rests on it.  What
 the PR did move is the QUOTIENT's own equality, which is now the
 propositional truncation [inhabited (quot_rel N a b)]; see [quot_equiv]
 below.

 There is deliberately NO decidability field, unlike
 Instance/Ab/Character/Finite.v, and nothing below decides
 membership. 

 --------
 子群是一个 `≈`-饱和的谓词，包含单位元，并在乘积和逆元下封闭。成员资格是 [Type] 值的，遵循 Instance/Grp/Epi.v 的 [GrpImage] 和 Instance/Ab/Character/Finite.v 的 [sg_mem]。更正。之前的修订将原因列为“图书馆的 `≈` 本身是 [Type] 值的，因此 [Prop] 值的成员无法被消去为齐次集等式”。该原因已不再存在：自从 PR“代数载体是集合”（2026-09-17）之后，一个 [GrpObject] 承载 [grp_prop]，并且一个 [Prop] 假设通过 [pequiv_to] 达到 `≈` 目标（Lib/Setoid/Propositional.v）。结论依然成立，但理由不同：消费者读取见证。Instance/Grp/Quotient/Isomorphism.v 的 [image_med] 将成员证明的原像投影到 [Type] 目标，并且第一同构定理基于此。PR 改动的是商本身的等式，现在它是命题截断 [inhabited (quot_rel N a b)]；见下面的 [quot_equiv]。与 Instance/Ab/Character/Finite.v 不同，这里故意没有可判定性字段，而且下面没有任何东西决定成员身份。
*)
Record Subgroup (G : GrpObject) := {
  sub_mem : carrier G → Type;

  (* (1) ≈-saturation / (1) ≈-饱和 *)
  sub_resp : ∀ a b : carrier G, a ≈ b → sub_mem a → sub_mem b;
  (* (2) the unit *)
  sub_unit : sub_mem (grp_unit G);
  (* (3) closure under product / (3) 在乘积下的封闭性 *)
  sub_mul : ∀ a b : carrier G,
    sub_mem a → sub_mem b → sub_mem (grp_mul G a b);
  (* (4) closure under inverse / (4) 在逆运算下的封闭性 *)
  sub_inv : ∀ a : carrier G, sub_mem a → sub_mem (grp_inv G a)
}.

Arguments sub_mem {G} _ _.
Arguments sub_resp {G} _ _ _ _ _.
Arguments sub_unit {G} _.
Arguments sub_mul {G} _ _ _ _ _.
Arguments sub_inv {G} _ _ _.

(* A normal subgroup adds the fifth fact: closure under conjugation. The five laws are exactly the five that Abelianization.v names. / 正规子群增加了第五条规律：关于共轭的封闭性。这五条规律正是 Abelianization.v 所命名的五条规律。 *)
Record NormalSubgroup (G : GrpObject) := {
  ns_sub :> Subgroup G;

  (* (5) normality / （5）正常性 *)
  ns_conj : ∀ t a : carrier G, sub_mem ns_sub a →
    sub_mem ns_sub (grp_mul G (grp_mul G t a) (grp_inv G t))
}.

Arguments ns_sub {G} _.
Arguments ns_conj {G} _ _ _ _.

(*
 Saturation in the argument-implicit shape the proofs below want, so
 that they read like Abelianization.v's [inc_resp] applications. 

 --------
 论证中隐含的饱和度塑造了下面希望的证明，使它们读起来像 Abelianization.v 的 [inc_resp] 应用。
*)
Definition sub_at {G : GrpObject} (S : Subgroup G) {a b : carrier G}
  (Hab : a ≈ b) (Ha : sub_mem S a) : sub_mem S b := sub_resp S a b Hab Ha.

(* * ** The subgroup as an object of Grp / * ** 作为Grp对象的子群 *)

(* The sigma carrier over membership, compared on elements -- the shape Instance/Grp.v's [Grp_kernel] and Instance/Grp/Center.v use, so the membership witness carries no equational weight. / 关于元素的 σ 搬运量在隶属关系上的比较——形状 Instance/Grp.v 的 [Grp_kernel] 和 Instance/Grp/Center.v 使用，因此隶属证据没有等式权重。 *)
Definition sub_carrier {G : GrpObject} (S : Subgroup G) : Type :=
  { a : carrier G & sub_mem S a }.

(*
 The carrier setoid is written INLINE, as it was before the PR "algebraic
 carriers are sets" (2026-09-17), and [grp_prop] is supplied as a trailing
 obligation instead of as a field.  An intermediate revision named the setoid
 -- a [Program] record literal cannot carry a [PropEquiv] FIELD naming a
 setoid written inline in the same literal -- but naming it puts one more
 unfolding step between the expected type of each [existT] below and the
 sigma it builds, and Coq 8.19/8.20 then infer a CONSTANT predicate and
 refuse the term ("has type ∃ _ : …, … while it is expected to have type
 carrier …"; Instance/Rng/Zp.v's header records the trap, and
 Instance/Grp/Center.v records the same one for [mk_central]).  Rocq 9.1
 accepts either.  The obligation route keeps every term below exactly as the
 released toolchains already compiled it, which is why it is taken here and
 at [Grp_kernel] (Instance/Grp.v). 

 --------
 承载集合子（carrier setoid）写作 INLINE，就像在 PR “代数承载是集合”（2026-09-17）之前一样，而 [grp_prop] 被作为后续义务提供，而不是作为字段。一个中间版本为集合子命名 —— [Program] 记录字面值不能携带一个 [PropEquiv] 字段来命名在同一个字面值中以内联方式写的集合子 —— 但是命名它会在下面每个 [existT] 的期望类型与它构建的 sigma 之间增加一步展开，而且 Coq 8.19/8.20 然后会推断一个 CONSTANT 谓词并拒绝该项（“类型为 ∃ _ : …, …，而期望类型为 carrier …”；Instance/Rng/Zp.v 的头部记录了这个陷阱，而 Instance/Grp/Center.v 对 [mk_central] 也记录了同样的情况）。Rocq 9.1 接受任意一种。义务路径保持每个术语与已发布工具链编译的完全相同，这就是为什么在此处以及在 [Grp_kernel]（Instance/Grp.v）中采用它的原因。
*)
Program Definition SubgroupGrp {G : GrpObject} (S : Subgroup G) : GrpObject := {|
  grp_setoid := {| carrier := sub_carrier S
                 ; is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |} |};
  grp_unit := existT _ (grp_unit G) (sub_unit S);
  grp_mul := fun p q =>
    existT _ (grp_mul G (`1 p) (`1 q)) (sub_mul S _ _ (`2 p) (`2 q));
  grp_inv := fun p => existT _ (grp_inv G (`1 p)) (sub_inv S _ (`2 p))
|}.
Next Obligation. intros G S; equivalence; now transitivity (`1 y). Qed.
Next Obligation.
  intros G S a a' Ha b b' Hb; simpl in *; now rewrite Ha, Hb.
Qed.
Next Obligation. intros G S a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G S a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G S a; simpl; apply grp_mul_inv_l. Qed.
Next Obligation.
  (*
 The subgroup's `≈` compares first projections in [G], so it is
 propositional exactly when [G]'s own `≈` is.  [sigma_first_PropEquiv] is
 applied in the TACTIC form, the one the term form is refused in. 

 --------
 该子群的 `≈` 比较 [G] 中的第一个投影，因此当 [G] 自身的 `≈` 为命题时，它也是命题。[sigma_first_PropEquiv] 以 TACTIC 形式应用，这是在项形式被拒绝时使用的形式。
*)
  intros G S.
  unshelve refine (sigma_first_PropEquiv _ _ _ (grp_prop G)).
  - intros p q Hpq; exact Hpq.
  - intros p q Hpq; exact Hpq.
Defined.

(* The inclusion of a subgroup: the first projection. / 子群的包含：第一次投影。 *)
Program Definition sub_incl {G : GrpObject} (S : Subgroup G) :
  SubgroupGrp S ~{Grp}~> G := {|
  grp_map := {| morphism := fun p : sub_carrier S => `1 p |}
|}.
Next Obligation. intros G S a b Hab; exact Hab. Qed.
Next Obligation. intros G S; simpl; reflexivity. Qed.
Next Obligation. intros G S a b; simpl; reflexivity. Qed.

(*
 The inclusion is injective, hence monic in [Grp] by
 Instance/Grp.v's biconditional. 

 --------
 该包含是单射，因此根据 Instance/Grp.v 的双条件在 [Grp] 中是单态的。
*)
Lemma sub_incl_injective {G : GrpObject} (S : Subgroup G)
  (a b : carrier (SubgroupGrp S)) :
  grp_map (sub_incl S) a ≈ grp_map (sub_incl S) b → a ≈ b.
Proof. intro Hab; exact Hab. Qed.

Lemma sub_incl_monic {G : GrpObject} (S : Subgroup G) : Monic (sub_incl S).
Proof.
  apply (fst (Grp_injectivity_is_monic (sub_incl S))).
  apply sub_incl_injective.
Qed.

(** ** The quotient relation / ** 商关系 *)

(* a ~ b when a * b⁻¹ lies in N. The orientation matches Instance/Grp/Abelianization.v's [abel_eq], which this generalizes. / 当 a * b⁻¹ 位于 N 中时，a ~ b。方向匹配 Instance/Grp/Abelianization.v 中的 [abel_eq]，这一内容对此进行了推广。 *)
Definition quot_rel {G : GrpObject} (N : Subgroup G) (a b : carrier G) : Type :=
  sub_mem N (grp_mul G a (grp_inv G b)).

Section QuotientRelation.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

(* The finer relation implies the coarser one. / 更精细的关系暗示着更粗糙的关系。 *)
Lemma quot_rel_of_equiv (a b : carrier G) : a ≈ b → quot_rel N a b.
Proof.
  intro Hab; unfold quot_rel.
  apply (sub_at N (a := grp_unit G)); [| exact (sub_unit N) ].
  rewrite Hab.
  symmetry; apply (grp_mul_inv_r G).
Qed.

Lemma quot_rel_refl (a : carrier G) : quot_rel N a a.
Proof. apply quot_rel_of_equiv; reflexivity. Qed.

Lemma quot_rel_sym (a b : carrier G) : quot_rel N a b → quot_rel N b a.
Proof.
  unfold quot_rel; intro K.
  apply (sub_at N (a := grp_inv G (grp_mul G a (grp_inv G b)))).
  - rewrite (grp_inv_mul G a (grp_inv G b)).
    rewrite (grp_inv_inv G b).
    reflexivity.
  - exact (sub_inv N _ K).
Qed.

Lemma quot_rel_trans (a b c : carrier G) :
  quot_rel N a b → quot_rel N b c → quot_rel N a c.
Proof.
  unfold quot_rel; intros K1 K2.
  apply (sub_at N
           (a := grp_mul G (grp_mul G a (grp_inv G b))
                   (grp_mul G b (grp_inv G c)))).
  - rewrite (grp_mul_assoc G a (grp_inv G b)
               (grp_mul G b (grp_inv G c))).
    rewrite <- (grp_mul_assoc G (grp_inv G b) b (grp_inv G c)).
    rewrite (grp_mul_inv_l G b).
    rewrite (grp_mul_unit_l G (grp_inv G c)).
    reflexivity.
  - exact (sub_mul N _ _ K1 K2).
Qed.

(*
 Multiplication respects the relation.  This is the first of the two
 places where NORMALITY is spent: the correction term a * (b * b'⁻¹) * a⁻¹
 is a conjugate of a member. 

 --------
 乘法遵循该关系。这是两个花费正常性的地方中的第一个：校正项 a * (b * b'⁻¹) * a⁻¹ 是一个成员的共轭。
*)
Lemma quot_rel_mul (a a' b b' : carrier G) :
  quot_rel N a a' → quot_rel N b b' →
  quot_rel N (grp_mul G a b) (grp_mul G a' b').
Proof.
  unfold quot_rel; intros K1 K2.
  apply (sub_at N
           (a := grp_mul G
                   (grp_mul G (grp_mul G a (grp_mul G b (grp_inv G b')))
                      (grp_inv G a))
                   (grp_mul G a (grp_inv G a')))).
  - rewrite (grp_inv_mul G a' b').
    rewrite (grp_mul_assoc G
               (grp_mul G a (grp_mul G b (grp_inv G b')))
               (grp_inv G a) (grp_mul G a (grp_inv G a'))).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a (grp_inv G a')).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_l G (grp_inv G a')).
    rewrite (grp_mul_assoc G a (grp_mul G b (grp_inv G b'))
               (grp_inv G a')).
    rewrite (grp_mul_assoc G b (grp_inv G b') (grp_inv G a')).
    rewrite (grp_mul_assoc G a b
               (grp_mul G (grp_inv G b') (grp_inv G a'))).
    reflexivity.
  - exact (sub_mul N _ _ (ns_conj N a _ K2) K1).
Qed.

(* Inversion respects the relation; normality again. / 倒置尊重这种关系；再次正常。 *)
Lemma quot_rel_inv (a a' : carrier G) :
  quot_rel N a a' → quot_rel N (grp_inv G a) (grp_inv G a').
Proof.
  unfold quot_rel; intros K.
  apply (sub_at N
           (a := grp_mul G
                   (grp_mul G (grp_inv G a)
                      (grp_inv G (grp_mul G a (grp_inv G a'))))
                   (grp_inv G (grp_inv G a)))).
  - rewrite (grp_inv_mul G a (grp_inv G a')).
    rewrite (grp_inv_inv G a').
    rewrite (grp_inv_inv G a).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a' (grp_inv G a)).
    rewrite (grp_mul_assoc G (grp_mul G (grp_inv G a) a')
               (grp_inv G a) a).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_r G (grp_mul G (grp_inv G a) a')).
    reflexivity.
  - exact (ns_conj N (grp_inv G a) _ (sub_inv N _ K)).
Qed.

(*
 Membership IS congruence to the unit: the quotient relation at the unit
 is membership on the nose.  Both directions, and the forward one by
 [reflexivity] under the relation's own unfolding. 

 --------
 成员资格就是与单位的一致性：单位上的商关系就是成员资格。两个方向，前向的通过 [reflexivity] 在关系自身展开下。
*)
Lemma quot_rel_unit_iff (a : carrier G) :
  quot_rel N a (grp_unit G) ↔ sub_mem N a.
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at N (a := grp_mul G a (grp_inv G (grp_unit G)))); [| exact K ].
    rewrite (grp_inv_unit G).
    apply (grp_mul_unit_r G).
  - apply (sub_at N (a := a)); [| exact K ].
    rewrite (grp_inv_unit G).
    symmetry; apply (grp_mul_unit_r G).
Qed.

End QuotientRelation.

(* * ** The quotient group and its projection / * ** 商群及其投射 *)

(*
 The quotient's `≈` is the PROPOSITIONAL TRUNCATION of [quot_rel].

 An earlier revision wrote [equiv := quot_rel N] directly.  Since the PR
 "algebraic carriers are sets" (2026-09-17) a [GrpObject] carries
 [grp_prop], and [quot_rel N a b] is [sub_mem N (a * b⁻¹)], a [Type]: the
 membership witness stays [Type]-valued (its consumers read it -- see the
 correction at the [Subgroup] record above), so the quotient's own equality
 is its truncation, exactly as Instance/Mod/Quotient.v's [mquot_rel] and
 Instance/Rng/Quotient.v's [rquot_rel] are truncated.  Nothing about
 [quot_rel] itself moves: all eleven [quot_rel_*] lemmas keep their
 statements verbatim, and every place PROVING a quotient equation gains one
 [constructor] while every place CONSUMING one gains a [destruct], legal
 because the goal there is a [Prop] or is reached through [pequiv_to]. 

 --------
 商 `≈` 是 [quot_rel] 的命题截断。早期的修订直接写了 [equiv := quot_rel N]。自从 PR“代数承载体是集合”（2026-09-17）之后，一个 [GrpObject] 承载 [grp_prop]，并且 [quot_rel N a b] 是 [sub_mem N (a * b⁻¹)]，一个 [Type]：成员资格证明保持 [Type] 值（它的使用者会读取它——参见上面 [Subgroup] 记录中的更正），所以商的自身相等性就是它的截断，正如 Instance/Mod/Quotient.v 中的 [mquot_rel] 和 Instance/Rng/Quotient.v 中的 [rquot_rel] 被截断一样。[quot_rel] 本身没有任何变化：所有十一条 [quot_rel_*] 引理都保持原样陈述，每个证明商等式的地方增加一个 [constructor]，而每个使用等式的地方增加一个 [destruct]，这是合法的，因为那里的目标是一个 [Prop] 或通过 [pequiv_to] 达到。
*)
Definition quot_equiv {G : GrpObject} (N : NormalSubgroup G)
  (a b : carrier G) : Prop := inhabited (quot_rel N a b).

(* The setoid is named rather than written inline in the record below: a [Program] record literal cannot carry a [PropEquiv] field naming a setoid written inline in the same literal. / 在下面的记录中，集合类型是被命名的，而不是内联书写的： record 字面量无法携带一个字段，为同一个字面量中内联书写的集合类型命名。 *)
Program Definition quot_setoid {G : GrpObject} (N : NormalSubgroup G) :
  SetoidObject := {|
  carrier := carrier G;
  is_setoid := {| equiv := quot_equiv N |}
|}.
Next Obligation.
  intros G N.
  constructor.
  - intro a; constructor; apply quot_rel_refl.
  - intros a b [Hab]; constructor; now apply quot_rel_sym.
  - intros a b c [Hab] [Hbc]; constructor; now apply (quot_rel_trans N a b).
Qed.

Program Definition QuotientGrp {G : GrpObject} (N : NormalSubgroup G) :
  GrpObject := {|
  grp_setoid := quot_setoid N;
  grp_unit := grp_unit G;
  grp_mul := grp_mul G;
  grp_inv := grp_inv G;
  (* The relation IS a [Prop], so the two implications are the identity. / 该关系是一个 [Prop]，所以这两个蕴涵都是恒等式。 *)
  grp_prop :=
    @PropEquiv_of_relation _ (is_setoid (quot_setoid N)) (@quot_equiv G N)
      (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation.
  (*
 [@equiv _ S x y] is ascribed sort [Type] even when the underlying
 relation is a [Prop], so the hypotheses and the goal are converted to
 the [inhabited] form before the elimination. 

 --------
 [@equiv _ S x y] 被归属为类型[Type]，即使底层
 关系是一个[Prop]，因此假设和目标都转换为
 [inhabited]在淘汰前形成。
*)
  intros G N a a' Ha b b' Hb.
  change (inhabited (quot_rel N a a')) in Ha.
  change (inhabited (quot_rel N b b')) in Hb.
  change (inhabited (quot_rel N (grp_mul G a b) (grp_mul G a' b'))).
  destruct Ha as [Ha], Hb as [Hb]; constructor; now apply quot_rel_mul.
Qed.
Next Obligation.
  intros G N a b c; constructor; apply quot_rel_of_equiv, grp_mul_assoc.
Qed.
Next Obligation.
  intros G N a; constructor; apply quot_rel_of_equiv, grp_mul_unit_l.
Qed.
Next Obligation.
  intros G N a; constructor; apply quot_rel_of_equiv, grp_mul_inv_l.
Qed.

(*
 NO NOTATION for the quotient.  An unscoped infix [/] at level 40 would
 sit in the core scope and compete with the stdlib's scope-bound
 division notations in every file that imports this one; the tree's only
 other [/] notation, Instance/Field/Frac.v, is [Local] and prefix
 for exactly that kind of reason.  [QuotientGrp N] is written out. 

 --------
 商没有记号。一个未限定的中缀 [/] 在第 40 级会位于核心作用域，并且在每个导入该文件的文件中与标准库的作用域绑定除法记号竞争；树中唯一的另一个 [/] 记号，Instance/Field/Frac.v，是 [Local] 并且是前缀的，正是出于这种原因。[QuotientGrp N] 是写出来的。
*)

(*
 The projection: the identity function, read from the fine setoid into
 the coarse one. 

 --------
 投影：同一函数，从细集合读取到粗集合。
*)
Program Definition quot_proj {G : GrpObject} (N : NormalSubgroup G) :
  G ~{Grp}~> QuotientGrp N := {|
  grp_map := {| morphism := fun a : carrier G => a |}
|}.
Next Obligation.
  intros G N a b Hab; constructor; apply quot_rel_of_equiv, Hab.
Qed.
Next Obligation. intros G N; simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation. intros G N a b; simpl; constructor; apply quot_rel_refl. Qed.

(* The projection kills N, which is the statement that gives the universal element below its element. / 投影消去 N，即给出其元素下的通用元素的语句。 *)
Lemma quot_proj_kills {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  sub_mem N a → grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N).
Proof.
  intro Ha; simpl.
  constructor.
  exact (snd (quot_rel_unit_iff N a) Ha).
Qed.

(*
 Conversely, anything the projection kills lies in N: the projection's
 kernel is exactly N, as a biconditional rather than an inclusion. 

 --------
 相反，投影所消去的任何东西都位于 N 中：投影的核恰好是 N，这是一个双条件，而不是包含关系。
*)
(*
 An earlier revision read
 [grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N) ↔ sub_mem N a].
 Since the quotient's `≈` is now the truncation of [quot_rel], the
 biconditional is up to [inhabited]; the untruncated direction is kept whole
 as [quot_proj_kills] above, which is what every consumer in tree uses. 

 --------
 早期的修订版本是
 [grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N) ↔ sub_mem N a] 。
 由于商 `≈` 现在是 [quot_rel] 的截断，
 双向条件为 [inhabited]；未截断的方向保持完整
 如上文所示的 [quot_proj_kills] ，这是树中每个消费者使用的。
*)
Lemma quot_proj_kernel {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N) ↔ inhabited (sub_mem N a).
Proof.
  split; intro K.
  - change (inhabited (quot_rel N a (grp_unit G))) in K.
    destruct K as [K]; constructor; exact (fst (quot_rel_unit_iff N a) K).
  - change (inhabited (quot_rel N a (grp_unit G))).
    destruct K as [K]; constructor; exact (snd (quot_rel_unit_iff N a) K).
Qed.

(*
 The projection is surjective on elements -- indeed the identity -- and
 hence epic.  Recorded because the isomorphism-theorem chases in the
 sibling file cancel it on the right. 

 --------
 该投影在元素上是满射的——确切地说，是单位元——因此是史诗性的。记录下来是因为同构定理在兄弟文件中在右侧消掉它。
*)
Lemma quot_proj_epic {G : GrpObject} (N : NormalSubgroup G) :
  Epic (quot_proj N).
Proof.
  constructor; intros K g h Hgh a.
  exact (Hgh a).
Qed.

(* * ** The functor of homomorphisms killing N / * ** 杀死 N 的同态函子 *)

(*
 Kills N K is the set of homomorphisms G -> K that send every member of
 N to the unit.  It is covariant in K by postcomposition, which is what
 makes ⟨G/N, p⟩ a universal element in Mac Lane's covariant sense rather
 than a representing object of a presheaf. 

 --------
 Kills N K 是从 G 到 K 的同态集合，它将 N 的每个成员映射到单位元。它在 K 中是协变的，通过后组合，这是使 ⟨G/N, p⟩ 在 Mac Lane 的协变意义下成为一个普遍元素，而不是预层的表示对象的原因。
*)
Definition Kills {G : GrpObject} (N : NormalSubgroup G) (K : GrpObject) : Type :=
  { h : G ~{Grp}~> K & ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K }.

(* Two members are compared by their underlying homomorphisms; the killing witness carries no equational weight, exactly as the membership witness does not in [sub_carrier]. / 两个成员通过它们的基础同态进行比较；消去证据没有方程权重，就像在 [sub_carrier] 中成员证据没有方程权重一样。 *)
Program Definition Kills_Setoid {G : GrpObject} (N : NormalSubgroup G)
  (K : GrpObject) : Setoid (Kills N K) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros G N K.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q r Hpq Hqr; now transitivity (`1 q).
Qed.

Lemma Kills_post {G : GrpObject} (N : NormalSubgroup G) {K K' : GrpObject}
  (k : K ~{Grp}~> K') (p : Kills N K) (a : carrier G) :
  sub_mem N a → grp_map (k ∘ `1 p) a ≈ grp_unit K'.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  rewrite (`2 p a Ha).
  apply (grp_map_unit k).
Qed.

Program Definition KillsFunctor {G : GrpObject} (N : NormalSubgroup G) :
  Grp ⟶ Sets := {|
  fobj := fun K => {| carrier := Kills N K ; is_setoid := Kills_Setoid N K |};
  fmap := fun K K' k =>
    {| morphism := fun p : Kills N K =>
         existT _ (k ∘ `1 p) (Kills_post N k p) |}
|}.
Next Obligation.
  intros G N K K' k p q Hpq a; simpl in *.
  unfold Basics.compose.
  now rewrite (Hpq a).
Qed.
Next Obligation.
  intros G N K K' k k' Hk p a; simpl.
  unfold Basics.compose.
  exact (Hk _).
Qed.
Next Obligation. intros G N K p a; simpl; reflexivity. Qed.
Next Obligation. intros G N K K' K'' k k' p a; simpl; reflexivity. Qed.

(** ** The mediating homomorphism / ** 中介同态 *)

Section Mediator.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).
Context {K : GrpObject}.
Context (p : Kills N K).

(*
 Descent: a homomorphism killing N cannot tell N-congruent elements
 apart.  From N (a * b⁻¹) one gets h a * (h b)⁻¹ ≈ e, and cancelling
 (h b)⁻¹ on the right gives h a ≈ h b.  This is the ONE computation the
 quotient's universal property costs. 

 --------
 下降：一个将 N 映成零的同态无法区分 N 同余的元素。从 N (a * b⁻¹) 可以得到 h a * (h b)⁻¹ ≈ e，并且在右边抵消 (h b)⁻¹ 得到 h a ≈ h b。这就是商的泛性质所需要的唯一计算。
*)
Lemma kills_descends (a b : carrier G) :
  quot_rel N a b → grp_map (`1 p) a ≈ grp_map (`1 p) b.
Proof.
  intro Hab.
  apply (grp_cancel_r K (grp_inv K (grp_map (`1 p) b))).
  rewrite (grp_mul_inv_r K (grp_map (`1 p) b)).
  rewrite <- (grp_map_inv (`1 p) b).
  rewrite <- (grp_map_mul (`1 p)).
  exact (`2 p _ Hab).
Qed.

Program Definition quot_med : QuotientGrp N ~{Grp}~> K := {|
  grp_map := {| morphism := fun a : carrier (QuotientGrp N) =>
                              grp_map (`1 p) a |}
|}.
(*
 THE one repair the truncation costs.  [Hab] is now the [inhabited] form
 and the goal is a [Type], so the elimination is put behind [pequiv]: move
 the goal into [K]'s own [Prop] equality, destruct there, and come back. 

 --------
 修复截断的成本。[Hab] 现在是 [inhabited] 形式，目标是 [Type]，所以消除放在 [pequiv] 之后：将目标移动到 [K] 自身的 [Prop] 等式中，在那里拆解，然后返回。
*)
Next Obligation.
  intros a b Hab.
  apply (@pequiv_to _ _ (grp_prop K)).
  change (inhabited (quot_rel N a b)) in Hab.
  destruct Hab as [Hab].
  apply (@pequiv_from _ _ (grp_prop K)).
  exact (kills_descends a b Hab).
Qed.
Next Obligation. simpl; apply (grp_map_unit (`1 p)). Qed.
Next Obligation. intros a b; simpl; apply (grp_map_mul (`1 p)). Qed.

(*
 The mediator's defining triangle, at the level of the underlying
 homomorphisms: it holds by reflexivity, since the projection is the
 identity function. 

 --------
 调解者的定义三角形，在底层同态的层面上：它由于自反性而成立，因为投影是恒等函数。
*)
Lemma quot_med_commutes : quot_med ∘ quot_proj N ≈ `1 p.
Proof. intro a; simpl; reflexivity. Qed.

Lemma quot_med_unique (v : QuotientGrp N ~{Grp}~> K)
  (Hv : v ∘ quot_proj N ≈ `1 p) : quot_med ≈ v.
Proof. intro a; simpl; symmetry; exact (Hv a). Qed.

End Mediator.

Arguments quot_med {G} N {K} p.

(* * ** Mac Lane's construction 5: ⟨G/N, p⟩ is a universal element / * ** 麦克莱恩的构造 5：⟨G/N, p⟩ 是一个泛元素 *)

(* The projection, packaged as an element of (Kills N)(G/N). / 该投影被打包为 (Kills N)(G/N) 的一个元素。 *)
Definition quot_elem {G : GrpObject} (N : NormalSubgroup G) :
  Kills N (QuotientGrp N) :=
  existT _ (quot_proj N) (quot_proj_kills N).

(*
 Mac Lane, §III.1 construction 5.  Every homomorphism out of G that
 kills N is (Kills N u) applied to the projection, for a UNIQUE
 u : G/N -> K.  The class is #303's [AUniversalElement], used DIRECTLY:
 the class sits upstream of both of Theory/Universal/Element.v's routes
 to [Representable], so neither the Yoneda packaging nor the hand-built
 alternative to it is touched here.  Nothing below mentions
 [Yoneda_Lemma], [ue_yoneda_obj] or [universal_element_representation],
 so the universe restriction those carry (object, hom and proof
 universes identified) is not inherited. 

 --------
 Mac Lane，第§III.1节 构造5。每一个从G出发且消灭N的同态都是（消灭N u）应用于投射，对于唯一的u : G/N -> K。该类是#303的[AUniversalElement]，直接使用：该类位于Theory/Universal/Element.v中通向[Representable]的两条路径的上游，因此此处不涉及Yoneda封装或其手工构建的替代方案。下面没有提及[Yoneda_Lemma]、[ue_yoneda_obj]或[universal_element_representation]，因此它们所携带的宇宙限制（对象、同态和证明宇宙相同）不会被继承。
*)
Program Definition quot_universal_element {G : GrpObject}
  (N : NormalSubgroup G) : AUniversalElement (KillsFunctor N) (QuotientGrp N) := {|
  aue_elem := quot_elem N
|}.
Next Obligation.
  intros G N K x.
  unshelve refine {| unique_obj := quot_med N x |}.
  - exact (quot_med_commutes N x).
  - intros v Hv; simpl in *.
    exact (quot_med_unique N x v Hv).
Defined.

(*
 The universal element's underlying homomorphism IS the projection, by
 convertibility -- the [eq_refl] exception to the `≈` discipline, and
 the check that the packaging did not silently rebuild it. 

 --------
 通用元素的基础同态是投影，通过可转换性 —— [eq_refl] 对 `≈` 规范的例外，以及检查包装是否没有悄悄重建它。
*)
Example quot_universal_elem_is_proj {G : GrpObject} (N : NormalSubgroup G) :
  `1 (@aue_elem _ (KillsFunctor N) (QuotientGrp N) (quot_universal_element N))
    = quot_proj N.
Proof. reflexivity. Qed.

(* And the mediator extracted from the class is the fixpoint-free direct one, again by convertibility. / 从类中提取的中介者是无不动点的直接中介者，同样通过可转换性得到。 *)
Example quot_universal_med_is_quot_med {G : GrpObject} (N : NormalSubgroup G)
  {K : GrpObject} (x : Kills N K) :
  unique_obj (@aue_universal _ (KillsFunctor N) (QuotientGrp N)
                (quot_universal_element N) K x)
    = quot_med N x.
Proof. reflexivity. Qed.

(* * ** Awodey Theorem 4.4: the homomorphism theorem, as a biconditional / * ** Awodey 定理 4.4：同态定理，作为双条件 *)

(*
 N ⊆ ker h if and only if h factors uniquely through the projection.
 The forward direction is the universal property; the backward one is
 the observation that every member of N is projected to the unit, so a
 factorization forces h to kill N. 

 --------
 当且仅当 h 可以唯一地通过投影因式分解时，才有 N ⊆ ker h。正向方向是泛性质；反向方向是观察到 N 的每个元素都被投影到单位元，因此因式分解迫使 h 将 N 映为零。
*)
Theorem hom_theorem {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K) :
  (∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K)
    ↔ (∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h).
Proof.
  split.
  - intro Hkill.
    pose (x := existT (fun h : G ~{Grp}~> K =>
                         ∀ a : carrier G, sub_mem N a →
                           grp_map h a ≈ grp_unit K) h Hkill).
    unshelve refine {| unique_obj := quot_med N x |}.
    + exact (quot_med_commutes N x).
    + intros v Hv.
      exact (quot_med_unique N x v Hv).
  - intros [u Hu _] a Ha.
    transitivity (grp_map u (grp_map (quot_proj N) a)).
    + symmetry; exact (Hu a).
    + transitivity (grp_map u (grp_unit (QuotientGrp N))).
      * apply proper_morphism.
        exact (quot_proj_kills N a Ha).
      * exact (grp_map_unit u).
Qed.

(* The two halves separately, in the shape a consumer applies. / 两个部分分开，以消费者使用的形状。 *)
Definition hom_theorem_factor {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hkill : ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) :
  ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h :=
  fst (hom_theorem N h) Hkill.

Definition hom_theorem_kills {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hfac : ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h) :
  ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K :=
  snd (hom_theorem N h) Hfac.

(*
   * ** The kernel of a homomorphism is a normal subgroup

   The transplant from #301.  Awodey's Theorem 4.4 opens with this
   clause, and it is what makes the isomorphism theorems in the sibling
   file able to quotient by a kernel at all. 

   --------
   * ** 同态的核是正规子群

   来自#301的移植。阿沃迪定理4.4开头是这样
   这正是使同构定理在兄弟姐妹中形成的原因
   文件能够被内核商化。
*)

Program Definition KernelNS {G K : GrpObject} (h : G ~{Grp}~> K) :
  NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun a : carrier G => grp_map h a ≈ grp_unit K |}
|}.
Next Obligation.
  intros G K h a b Hab Ha; simpl in *.
  now rewrite <- Hab.
Qed.
Next Obligation. intros G K h; simpl; apply (grp_map_unit h). Qed.
Next Obligation.
  intros G K h a b Ha Hb; simpl in *.
  rewrite (grp_map_mul h), Ha, Hb.
  apply (grp_mul_unit_l K).
Qed.
Next Obligation.
  intros G K h a Ha; simpl in *.
  rewrite (grp_map_inv h), Ha.
  apply (grp_inv_unit K).
Qed.
Next Obligation.
  intros G K h t a Ha; simpl in *.
  rewrite !(grp_map_mul h), (grp_map_inv h), Ha.
  rewrite (grp_mul_unit_r K).
  apply (grp_mul_inv_r K).
Qed.

(* Membership in the kernel subgroup IS the defining equation, by convertibility. / 通过可转换性，属于核子群就是定义方程。 *)
Example KernelNS_mem {G K : GrpObject} (h : G ~{Grp}~> K) (a : carrier G) :
  sub_mem (KernelNS h) a = (grp_map h a ≈ grp_unit K).
Proof. reflexivity. Qed.

(*
 The subgroup object of the kernel normal subgroup has the same carrier
 as Instance/Grp.v's [Grp_kernel], by convertibility. 

 --------
 核正规子群的子群对象与 Instance/Grp.v 中的 [Grp_kernel] 拥有相同的载体，因为它们是可转换的。
*)
Example KernelNS_carrier_is_Grp_kernel {G K : GrpObject} (h : G ~{Grp}~> K) :
  carrier (SubgroupGrp (KernelNS h)) = carrier (Grp_kernel h).
Proof. reflexivity. Qed.

(* * ** The degenerate normal subgroups, named and separated / * ** 退化的正规子群，命名并区分 *)

(* The trivial normal subgroup {e}. / 平凡正规子群 {e}。 *)
Program Definition TrivialNS (G : GrpObject) : NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun a : carrier G => a ≈ grp_unit G |}
|}.
Next Obligation. intros G a b Hab Ha; simpl in *; now rewrite <- Hab. Qed.
Next Obligation. intros G; simpl; reflexivity. Qed.
Next Obligation.
  intros G a b Ha Hb; simpl in *.
  rewrite Ha, Hb; apply (grp_mul_unit_l G).
Qed.
Next Obligation.
  intros G a Ha; simpl in *.
  rewrite Ha; apply (grp_inv_unit G).
Qed.
Next Obligation.
  intros G t a Ha; simpl in *.
  rewrite Ha, (grp_mul_unit_r G).
  apply (grp_mul_inv_r G).
Qed.

(* The whole group, as a normal subgroup of itself. / 整个群自身作为它自己的正规子群。 *)
Program Definition TotalNS (G : GrpObject) : NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun _ : carrier G => poly_unit |}
|}.
Next Obligation. intros G a b Hab Ha; exact ttt. Qed.
Next Obligation. intros G; exact ttt. Qed.
Next Obligation. intros G a b Ha Hb; exact ttt. Qed.
Next Obligation. intros G a Ha; exact ttt. Qed.
Next Obligation. intros G t a Ha; exact ttt. Qed.

(*
 Quotienting by the trivial subgroup changes nothing: the coarse
 relation coincides with `≈`, in both directions. 

 --------
 对平凡子群取商不会改变任何东西：粗糙关系在两个方向上都与 `≈` 一致。
*)
Lemma quot_trivial_iff (G : GrpObject) (a b : carrier G) :
  quot_rel (TrivialNS G) a b ↔ a ≈ b.
Proof.
  split.
  - intro K; simpl in K.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite K.
    symmetry; apply (grp_mul_inv_r G).
  - intro Hab; simpl.
    rewrite Hab; apply (grp_mul_inv_r G).
Qed.

(* Quotienting by the whole group collapses everything. / 对整个群取商会把一切都压缩掉。 *)
Lemma quot_total_collapses (G : GrpObject) (a b : carrier G) :
  quot_rel (TotalNS G) a b.
Proof. exact ttt. Qed.

(* * ** Quotients by coextensive normal subgroups agree / * ** 由共延拓正规子群得到的商群一致 *)

(*
 Two normal subgroups with the same members give isomorphic quotients,
 the comparison being the identity function in both directions.  This is
 what lets a quotient by a kernel be renamed as a quotient by the
 subgroup that kernel computes to, without a transport. 

 --------
 具有相同成员的两个正规子群给出同构的商群，比较是在两个方向上的恒等函数。这就是为什么可以将一个核的商群重新命名为该核计算出的子群的商群，而无需传递。
*)
Program Definition quot_congr {G : GrpObject} (N N' : NormalSubgroup G)
  (H1 : ∀ a : carrier G, sub_mem N a → sub_mem N' a)
  (H2 : ∀ a : carrier G, sub_mem N' a → sub_mem N a) :
  QuotientGrp N ≅[Grp] QuotientGrp N' := {|
  to := {| grp_map := {| morphism := fun a : carrier (QuotientGrp N) => a |} |};
  from := {| grp_map := {| morphism := fun a : carrier (QuotientGrp N') => a |} |}
|}.
(*
 The two respectfulness obligations are the only places the truncation is
 visible: unwrap the hypothesis, apply the inclusion, wrap again. 

 --------
 这两种尊重义务是截断唯一可见的地方：展开假设，应用包含，再重新包装。
*)
Next Obligation.
  intros G N N' H1 H2 a b Hab.
  change (inhabited (quot_rel N a b)) in Hab.
  change (inhabited (quot_rel N' a b)).
  destruct Hab as [Hab]; constructor; exact (H1 _ Hab).
Qed.
Next Obligation. intros G N N' H1 H2; simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation.
  intros G N N' H1 H2 a b; simpl; constructor; apply quot_rel_refl.
Qed.
Next Obligation.
  intros G N N' H1 H2 a b Hab.
  change (inhabited (quot_rel N' a b)) in Hab.
  change (inhabited (quot_rel N a b)).
  destruct Hab as [Hab]; constructor; exact (H2 _ Hab).
Qed.
Next Obligation. intros G N N' H1 H2; simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation.
  intros G N N' H1 H2 a b; simpl; constructor; apply quot_rel_refl.
Qed.
Next Obligation.
  intros G N N' H1 H2 a; simpl; constructor; apply quot_rel_refl.
Qed.
Next Obligation.
  intros G N N' H1 H2 a; simpl; constructor; apply quot_rel_refl.
Qed.

(*
   * ** Non-degeneracy over a nonabelian witness

   Everything above holds for all groups, so nothing yet shows the
   quotient does not collapse.  S3 (Instance/Grp/TwoFunctors.v, the
   semidirect presentation over the decidable carrier rot * bool) with
   its rotation subgroup A3 is the smallest witness with a PROPER
   nontrivial normal subgroup, and it is nonabelian, so the degeneracies
   that make conjugation inert (Instance/Grp/TwoFunctors.v's
   [Grp_conj_abelian]) are excluded by proof rather than by assumption. 

   --------
   * ** 非退化性关于非阿贝尔见证  

   上述内容对所有群都成立，因此目前还没有显示商群不会崩塌。S3（Instance/Grp/TwoFunctors.v，关于可判定载体 rot * bool 的半直和表示）及其旋转子群 A3 是最小的具有适当非平凡正规子群的见证，并且它是非阿贝尔的，因此使共轭操作失效的退化情况（Instance/Grp/TwoFunctors.v 中的 [Grp_conj_abelian]）是通过证明排除了，而不是通过假设排除的。
*)

(*
 A3, the rotations: the elements whose reflection component is false.
 S3's setoid IS propositional equality
 (Instance/Grp/TwoFunctors.v's [S3_equiv_is_eq]), so saturation is
 substitution and every closure law is a finite check. 

 --------
 A3，旋转：其反射分量为假的元素。
 S3 的集合等价类是命题等式
 （Instance/Grp/TwoFunctors.v 的 [S3_equiv_is_eq]），因此饱和是替换，每个闭包律都是有限检查。
*)
Program Definition A3 : NormalSubgroup S3 := {|
  ns_sub := {| sub_mem := fun a : carrier S3 => snd a = false |}
|}.
Next Obligation. intros a b Hab Ha; simpl in *; now subst. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hb Hc; simpl in *; subst; reflexivity.
Qed.
Next Obligation. intros [i b] Hb; simpl in *; subst; reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hc; simpl in *; subst.
  destruct i, j, b; reflexivity.
Qed.

(* A3 is PROPER: the reflection is not a rotation. / A3 是正确的：反射不是旋转。 *)
Lemma A3_proper : sub_mem A3 S3_s → False.
Proof. simpl; discriminate. Qed.

(* A3 is NONTRIVIAL: it contains a non-unit element. / A3 是非平凡的：它包含一个非单位元。 *)
Lemma A3_nontrivial : sub_mem A3 S3_r * (S3_r ≈ s3_unit → False).
Proof. split; [ reflexivity | discriminate ]. Qed.

(*
 Normality of A3 is not vacuous: conjugation in S3 genuinely moves
 elements ([S3_conj_s_nontrivial]), so [ns_conj] is doing work here
 rather than holding because conjugation is the identity. 

 --------
 A3 的正规性并非空洞：在 S3 中的共轭确实会移动元素（[S3_conj_s_nontrivial]），所以 [ns_conj] 在这里起作用，而不是因为共轭是恒等而保持不变。
*)
Lemma A3_conjugation_nontrivial : Grp_conj S3 S3_s ≈ @id Grp S3 → False.
Proof. exact S3_conj_s_nontrivial. Qed.

(* THE QUOTIENT DOES NOT COLLAPSE: the reflection stays apart from the unit in S3/A3. / 商不坍缩：反射保持与 S3/A3 中的单位分离。 *)
Theorem S3_mod_A3_not_collapsed : quot_rel A3 S3_s s3_unit → False.
Proof. simpl; discriminate. Qed.

(* Nor does the quotient projection identify the two generators, so S3/A3 has at least two elements. / 商投影也不将这两个生成元识别为相同，因此 S3/A3 至少有两个元素。 *)
(*
 The quotient's `≈` is the truncation of [quot_rel] since the PR
 "algebraic carriers are sets" (2026-09-17), so the hypothesis is unwrapped
 before the computation; the goal [False] is a [Prop], which is what makes
 the elimination legal. 

 --------
 商  `≈`  是  [quot_rel]  的截断，因为 PR "代数承载是集合"（2026-09-17），所以假设在计算之前被展开；目标  [False]  是一个  [Prop] ，这使得消去合法。
*)
Theorem S3_mod_A3_two_elements :
  grp_map (quot_proj A3) S3_s ≈ grp_map (quot_proj A3) s3_unit → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(* But it does collapse the rotations, so the projection is not injective -- the quotient is a genuine quotient and not a relabelling of S3. / 但它确实会折叠旋转，所以投影不是单射的——商是一个真正的商，而不是 S3 的重新标记。 *)
Theorem S3_mod_A3_collapses_rotations :
  grp_map (quot_proj A3) S3_r ≈ grp_map (quot_proj A3) s3_unit.
Proof. constructor; reflexivity. Qed.

Theorem quot_proj_A3_not_injective :
  (∀ a b : carrier S3,
     grp_map (quot_proj A3) a ≈ grp_map (quot_proj A3) b → a ≈ b) → False.
Proof.
  intro Hinj.
  pose proof (Hinj S3_r s3_unit S3_mod_A3_collapses_rotations) as E.
  discriminate E.
Qed.

(*
 The two-element subgroup generated by the reflection: the elements with
 trivial rotation part.  It is a SUBGROUP but NOT a normal one, and both
 halves are proved -- so the sibling files have a witness at which the
 plain-[Subgroup] hypothesis of the second isomorphism theorem is not
 secretly a normal one, and at which the normal closure of a subgroup is
 strictly larger than the subgroup. 

 --------
 由反射生成的二元子群：具有平凡旋转部分的元素。它是一个子群，但不是正规子群，并且两个部分都已被证明——因此兄弟文件中有一个证据，表明第二同构定理的平凡 [Subgroup] 假设并不是隐藏的正规子群，并且一个子群的正规闭包严格大于该子群。
*)
Program Definition S3_refl_sub : Subgroup S3 := {|
  sub_mem := fun a : carrier S3 => fst a = rot0
|}.
Next Obligation. intros a b Hab Ha; simpl in *; now subst. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hb Hc; simpl in *; subst; now destruct b.
Qed.
Next Obligation. intros [i b] Hb; simpl in *; subst; now destruct b. Qed.

Theorem S3_refl_sub_not_normal :
  (∀ t a : carrier S3, sub_mem S3_refl_sub a →
     sub_mem S3_refl_sub (grp_mul S3 (grp_mul S3 t a) (grp_inv S3 t)))
  → False.
Proof.
  intro Hn.
  pose proof (Hn S3_r S3_s (eq_refl : fst S3_s = rot0)) as E.
  simpl in E.
  discriminate E.
Qed.
