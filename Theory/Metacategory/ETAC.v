(** * ETAC: the elementary language of an abstract category, and duality / * ETAC：抽象范畴的初等语言，以及对偶性 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(*
Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
              §II.1 “Duality” and §II.2 “Contravariance and Opposites”,
              printed pp. 31–33 (PDF pp. 41–43) — maclane:II.1:def1 (the
              elementary language), maclane:II.1:def2 (the dual of a
              statement), maclane:II.1:thm1 (the duality principle),
              maclane:II.1:remark2 (extension to functors),
              maclane:II.2:lem1 (duality is realized by the opposite)
   Book:      Awodey, “Category Theory” (1st ed., 2005 pre-print), §3.1,
              Propositions 3.1 and 3.2, printed pp. 58–59 (PDF pp. 67–68)
              — awodey:3.1:prop1 (formal duality), awodey:3.1:prop2
              (conceptual duality): the same two theorems
   nLab:      https://ncatlab.org/nlab/show/duality
   Wikipedia: https://en.wikipedia.org/wiki/Dual_(category_theory)

   Mac Lane's §II.1 introduces ETAC, the elementary (first-order) theory
   of an abstract category: a two-sorted language with equality whose
   atomic statements say “a is the domain of f”, “a is the codomain of
   f”, “u is the identity arrow of a”, “h is the composite of g and f”,
   “f and g are equal arrows”, and “a and b are equal objects” — the two
   equality atoms being what let monos and epis be expressed at all —
   closed under the propositional connectives and quantifiers over both
   sorts.
   The DUAL of a statement interchanges domain with codomain and reverses
   every composite; the duality principle says a statement provable from
   the category axioms has a provable dual.  §II.2's lemma grounds the
   principle semantically: a statement holds of arrows in C exactly when
   its dual holds in C^op.  Awodey's §3.1 states the same pair as formal
   and conceptual duality.

   This file DEEP-EMBEDS the language and proves all of it semantically:

     - [atom]/[formula]: the two-sorted syntax, de Bruijn over object
       and arrow variables ([FAllOb]/[FExOb] bind the object sort,
       [FAllArr]/[FExArr] the arrow sort)
     - [holds]: Type-valued satisfaction over a [Category] and a pair
       of environments, arrow equality rendered as the hom-setoid [≈];
       [closed_below]/[sentence] with [holds_sentence_env_irrel] — a
       closed formula's satisfaction is environment-independent
     - [dual]/[dual_invol]: the syntactic dual, an involution
     - [holds_dual]: Mac Lane's §II.2 lemma — C satisfies the dual of
       Σ exactly when C^op satisfies Σ under the transported
       environment
     - [duality_principle]: if a formula holds in every category under
       every assignment, so does its dual
     - [functor_statement_duality]: the one-functor case of
       maclane:II.1:remark2, recorded over [F^op] (design note 4)

   Design:

   1. ARROWS ARE BUNDLED WITH THEIR ENDPOINTS.  The language's arrow
      variables range over [Arr C := { p : obj × obj & fst p ~> snd p }]
      — an arrow together with its endpoints, the semantic counterpart
      of ETAC's untyped arrow sort (in the first-order language nothing
      forces an arrow variable to have particular endpoints).  Domain
      and codomain atoms compare endpoints by Leibniz equality of
      OBJECTS — the reading Mac Lane's object sort carries, and the
      only relation the language's object atoms mention; the hom-setoid
      [≈] enters exactly where the book's language has arrow equations:
      identity, composite, and arrow-equality atoms.  Those three atoms
      carry their endpoint equalities as sigma-packaged DATA and
      transport along them with [acast], the endpoint-cast this file
      defines (the [mcast]/[dsq_coerce] idiom of Theory/Multicategory.v
      and Theory/DoubleCategory.v, specialized to plain homs).

   2. SATISFACTION IS TYPE-VALUED.  [∃] is [sigT], [∨] is [sum], and
      the arrow equations are [≈], so [holds] lands in [Type]; the
      duality lemma is accordingly a Type-valued [iffT].  No
      decidability, no choice, no axiom: every principal artifact
      below is closed under the global context.

   3. THE DUALITY LEMMA IS TRANSPORT-FREE.  [op_arr] swaps an arrow
      bundle's endpoints — the SAME underlying arrow, since
      [hom (C^op) y x] is definitionally [hom C x y] — and [holds_dual]
      relates satisfaction in C to satisfaction in C^op through it.
      The bookkeeping happens in the six [sat_*_op]/[sat_*_unop]
      transports, whose proofs move to literal-pair bundles along the
      propositional eta [arr_eta] and then destruct every endpoint
      equality down to [eq_refl] — no cast lemma is consumed.  (The
      [acast_op]/[acast_split]/[acast_comm]/[acast_middle] kit below
      the cast's definition is exported as reusable cast algebra; no
      proof in this file needs it.)  Because the lemma quantifies over
      the C-side environment and transports it forward, the duality
      PRINCIPLE needs no double-op unwinding: instantiating the
      hypothesis at C^op already yields the dual at C.

   4. THE FUNCTOR EXTENSION IS SCOPED (maclane:II.1:remark2).  Mac
      Lane remarks that the language extends to several categories
      connected by functors.  This file records the one-functor case
      as theorems about [F^op] — the object and arrow actions of
      [F^op] ARE those of [F], so any functor-statement dualizes by
      the same environment transport — and defers the two-sorted
      functor LANGUAGE (atoms “T c = b”, “T f = h”) to future work:
      embedding it costs a second indexed syntax with nothing new in
      the induction, and §IV.3's exercise rows it would serve are
      already in force in-tree (Functor/Opposite.v's
      [Opposite_Functor] with involution,
      Natural/Transformation/Opposite.v's [Opposite_Transform],
      Adjunction/Opposite.v's [Opposite_Adjunction] with the
      transposes swapped, and its transformation sibling).  The two
      rows §IV.3 adds beyond those — fullness and faithfulness across
      op for an ARBITRARY functor — land in Functor/Opposite.v in this
      same change ([Full_op]/[Faithful_op] and converses), and the
      inverse-pair rows land in Theory/Morphisms/Duality.v
      ([op_Retraction_of_Section] and its three siblings, next to the
      Monic/Epic quartet).  The one-functor recording below,
      [arr_fmap_op], is a bundle-level commutation — the honest
      content of the remark at this scoping is the disclosure plus
      the definitional agreement of [F^op]'s actions with [F]'s.

   5. VALIDITY IS NOT ISOMORPHISM-INVARIANT.  Because the object atoms
      compare by Leibniz equality — the only relation this library's
      [Category] carries on objects — [valid] is a statement about
      strict structure: a sentence's truth in C can turn on object
      identity, and nothing here transports [valid] along equivalences
      of categories.  That is the honest reading of a first-order
      language with object equality over these models.

--------
书籍：      Mac Lane，《为在职数学家准备的范畴论》，第2版，
              §II.1 “对偶” 和 §II.2 “逆变与对偶对象”，
              印刷页 31–33（PDF 页 41–43）—— maclane:II.1:def1（基础语言），maclane:II.1:def2（命题的对偶），maclane:II.1:thm1（对偶原理），
              maclane:II.1:remark2（推广到函子），
              maclane:II.2:lem1（对偶通过对偶对象实现）
书籍：      Awodey，《范畴论》（第1版，2005 预印本），§3.1，
              命题 3.1 和 3.2，印刷页 58–59（PDF 页 67–68）—— awodey:3.1:prop1（形式对偶），awodey:3.1:prop2（概念对偶）：同样的两个定理
nLab：      https://ncatlab.org/nlab/show/duality
维基百科：  https://en.wikipedia.org/wiki/Dual_(category_theory)

麦克·莱恩（Mac Lane）§II.1 引入了 ETAC，即抽象范畴的初等（一阶）理论：一种带有等号的双类型语言，其原子命题为“a 是 f 的定义域”、“a 是 f 的值域”、“u 是 a 的恒等箭头”、“h 是 g 与 f 的复合”、“f 与 g 是相等的箭头”以及“a 与 b 是相等的对象”——这两个等号原子正是允许表达单射和满射的内容——并且在命题联结词和对两种类型的量词下封闭。命题的对偶（DUAL）是将定义域与值域互换并反转每个复合；对偶原则指出，从范畴公理可证明的命题，其对偶也可被证明。§II.2 的引理在语义上为该原则提供了基础：命题在 C 中对箭头成立，当且仅当其对偶在 C^op 中成立。Awodey §3.1 将同一对关系表述为形式对偶和概念对偶。

此文件深入嵌入语言，并在语义上证明了所有内容：

- [atom]/[formula]：两种排序的语法，de Bruijn 表示对象和箭头变量（[FAllOb]/[FExOb] 绑定对象排序，[FAllArr]/[FExArr] 绑定箭头排序）
- [holds]：对 [Category] 及一对环境的类型值满足性，箭头等价表示为同构集 [≈]；[closed_below]/[sentence] 与 [holds_sentence_env_irrel] —— 封闭公式的满足性与环境无关
- [dual]/[dual_invol]：语法对偶，递归映射
- [holds_dual]：Mac Lane §II.2 引理 —— 当 C 在传递的环境下满足 Σ 的对偶时，C^op 刚好满足 Σ
- [duality_principle]：如果一个公式在每个范畴下每个赋值中成立，其对偶也成立
- [functor_statement_duality]：Mac Lane:II.1:remark2 中的单函子情况，在 [F^op] 上记录（设计说明 4）

设计：

1. 箭头与它们的端点捆绑在一起。该语言的箭头变量范围包括 [Arr C := { p : obj × obj & fst p ~> snd p }] —— 一个包含其端点的箭头，是 ETAC 无类型箭头类型的语义对应（在一阶语言中，没有任何东西强制箭头变量必须有特定的端点）。定义域和余域原子通过 OBJECTS 的 Leibniz 等式比较端点——这是 Mac Lane 的对象类型所承载的含义，也是该语言的对象原子唯一提到的关系；同质集合 [≈] 恰好用于书中语言有箭头方程的地方：恒等、复合和箭头相等原子。这三个原子携带其端点相等性，作为 sigma 打包的 DATA，并通过 [acast]（本文件定义的端点转换）沿着它们传输（Theory/Multicategory.v 和 Theory/DoubleCategory.v 中的 [mcast]/[dsq_coerce] 习惯用法，专用于普通同态）。

2. 满意度是类型值。[∃] 是 [sigT]，[∨] 是 [sum]，并且箭头方程是 [≈]，因此 [holds] 落在 [Type] 中；相应地，对偶引理是一个类型值的 [iffT]。没有可判定性，没有选择，没有公理：下面的每个主要工件在全局上下文下都是封闭的。

3. 对偶引理是无需传输的。[op_arr] 交换箭头束的端点——同样的基础箭头，因为 [hom (C^op) y x] 定义上就是 [hom C x y]——而 [holds_dual] 通过它将 C 中的满足性与 C^op 中的满足性联系起来。簿记发生在六个 [sat_*_op]/[sat_*_unop] 传输中，其证明沿命题 eta [arr_eta] 移动到字面对束，然后将每个端点的等式分解到 [eq_refl]——没有使用任何转换引理。（在转换的定义下方的 [acast_op]/[acast_split]/[acast_comm]/[acast_middle] 套件被导出为可重用的转换代数；本文件中没有任何证明需要它。）因为引理对 C 端环境进行量化并向前传输它，对偶原理不需要双重 op 展开：在 C^op 上实例化假设已经得到 C 上的对偶。

4. 函子扩展是有范围的（Mac Lane: II.1: remark2）。Mac Lane 指出，这种语言可以扩展到由函子连接的多个范畴。此文件记录了单函子情况作为关于 [F^op] 的定理——[F^op] 的对象和箭头作用与 [F] 相同，因此任何函子陈述都可以通过相同的环境传输进行对偶化——并将两排序函子语言（atoms “T c = b”, “T f = h”）延迟到未来工作中：嵌入它需要第二个索引语法，而在归纳中没有新增内容，并且 §IV.3 的练习行它将服务的内容已经在树中生效（Functor/Opposite.v 中带有反演的 [Opposite_Functor]，Natural/Transformation/Opposite.v 的 [Opposite_Transform]，Adjunction/Opposite.v 中转置交换的 [Opposite_Adjunction] 以及它的变换兄弟部分）。
两行 §IV.3 在此之外添加的 —— 对一个任意函子而言的充满性和忠实性 —— 在相同更改中的 Functor/Opposite.v 中落地（[Full_op]/[Faithful_op] 及其对偶），而逆对行落地在 Theory/Morphisms/Duality.v 中（[op_Retraction_of_Section] 及其三个兄弟，紧挨着 Monic/Epic 四重奏）。下面的一函子记录，[arr_fmap_op]，是一个束级别的换位 —— 此作用域中的注释的真实内容是揭示以及 [F^op] 的操作与 [F] 的定义一致性。

5. 有效性不是同构不变的。因为对象原子通过莱布尼茨等式进行比较——这是该库在对象上唯一携带的关系——[valid] 是关于严格结构的陈述：句子在 C 中的真值可能取决于对象恒等，而这里没有任何东西可以沿着范畴等价传递 [valid]。这就是在这些模型上具有对象等式的一阶语言的诚实解读。
*)

(** ** Arrow bundles and endpoint casts / ** 箭矢包和端点投射 *)

(*
An arrow together with its endpoints: the semantic domain of the
   language's arrow variables.

--------
一支箭及其端点：语言箭头变量的语义域。
*)
Definition Arr (C : Category) : Type :=
  { p : obj[C] * obj[C] & fst p ~> snd p }.

Definition arr_dom {C : Category} (f : Arr C) : obj[C] := fst (projT1 f).
Definition arr_cod {C : Category} (f : Arr C) : obj[C] := snd (projT1 f).
Definition arr_map {C : Category} (f : Arr C) : arr_dom f ~> arr_cod f :=
  projT2 f.

(* Endpoint cast: transport a hom along equalities of its endpoints. / 端点转换：沿其端点的等式运输同态。 *)
Definition acast {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : x ~> y) : x' ~> y' :=
  eq_rect x (fun w => w ~> y') (eq_rect y (fun z => x ~> z) f y' ey) x' ex.

Lemma acast_refl {C : Category} {x y : obj[C]} (f : x ~> y) :
  acast eq_refl eq_refl f = f.
Proof. reflexivity. Qed.

(*
Casting in the opposite category is casting with the endpoint
   equalities exchanged (design note 3).

--------
在相反范畴中的投射是端点等式交换后的投射（设计说明3）。
*)
Lemma acast_op {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : y ~> x) :
  @acast (C^op) x y x' y' ex ey f = @acast C y x y' x' ey ex f.
Proof.
  destruct ex, ey; reflexivity.
Qed.

(*
Cast algebra, each law by destructing its equalities: a two-sided
   cast splits into its sides, independent side-casts commute, and a
   codomain cast crosses a composition as a domain cast.  Exported as
   reusable algebra for downstream consumers of [acast]; the proofs in
   THIS file reach literal-pair bundles instead (via [arr_eta]) and
   never consume it — disclosed in design note 3.

--------
构造代数，通过破坏其等式来构造每条规律：双边构造拆分为各自的边，独立的边构造可交换，余域构造在组合中像定义域构造一样穿越。作为可重用的代数导出，供 [acast] 的下游使用；本文件中的证明最终得到的是字面对捆（通过 [arr_eta]）而从不使用它——在设计说明 3 中已披露。
*)
Lemma acast_split {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : x ~> y) :
  acast ex ey f = acast eq_refl ey (acast ex eq_refl f).
Proof. destruct ex, ey; reflexivity. Qed.

Lemma acast_comm {C : Category} {x y x' y' : obj[C]}
  (ex : x = x') (ey : y = y') (f : x ~> y) :
  acast ex eq_refl (acast eq_refl ey f)
    = acast eq_refl ey (acast ex eq_refl f).
Proof. destruct ex, ey; reflexivity. Qed.

Lemma acast_middle {C : Category} {x y y' z : obj[C]}
  (e : y = y') (f : y' ~> z) (g : x ~> y) :
  f ∘ acast eq_refl e g ≈ acast (eq_sym e) eq_refl f ∘ g.
Proof. destruct e; simpl; reflexivity. Qed.

(*
The endpoint swap: an arrow of C, read as an arrow of C^op.  The
   underlying arrow is untouched.

--------
端点交换：一个 C 的箭头，被读作 C^op 的箭头。底层箭头保持不变。
*)
Definition op_arr {C : Category} (f : Arr C) : Arr (C^op) :=
  ((arr_cod f, arr_dom f); arr_map f).

Definition unop_arr {C : Category} (f : Arr (C^op)) : Arr C :=
  ((arr_cod f, arr_dom f); arr_map f).

Lemma op_unop_arr {C : Category} (f : Arr (C^op)) :
  op_arr (unop_arr f) = f.
Proof.
  destruct f as [[x y] f]; reflexivity.
Qed.

(*
The three arrow-equation satisfactions, standalone: stated over
   generic bundles so their op-transport lemmas can destruct everything
   in sight (the endpoint pairs first, then the equalities), which the
   in-place forms cannot — abstracting an endpoint of an environment
   value crosses the other components.

--------
三个箭头方程的满足情况，独立存在：在通用捆绑上说明，因此它们的运算传输引理可以分解所有可见内容（首先是端点对，然后是等式），而就地形式则无法做到——抽象环境值的一个端点会影响其他组件。
*)

Definition sat_id {C : Category} (a : obj[C]) (f : Arr C) : Type :=
  { ed : arr_dom f = a
  & { ec : arr_cod f = a
    & acast ed ec (arr_map f) ≈ id[a] } }.

Definition sat_comp {C : Category} (h g f : Arr C) : Type :=
  { e1 : arr_dom f = arr_dom h
  & { e2 : arr_cod f = arr_dom g
    & { e3 : arr_cod g = arr_cod h
      & acast eq_refl e3 (arr_map g) ∘ acast e1 e2 (arr_map f)
          ≈ arr_map h } } }.

Definition sat_eqarr {C : Category} (f g : Arr C) : Type :=
  { ed : arr_dom f = arr_dom g
  & { ec : arr_cod f = arr_cod g
    & acast ed ec (arr_map f) ≈ arr_map g } }.

(*
Bundles are propositionally their own eta-expansions; rewriting along
   this puts any environment value into literal-pair form, where the
   generic lemmas below apply and every destruct is between plain
   variables.

--------
捆绑在命题上是它们自身的 eta 展开；按照这个进行重写会将任何环境值转换为字面对形式，在这种形式下下面的通用引理适用，并且每个解构都发生在普通变量之间。
*)
Lemma arr_eta {C : Category} (s : Arr C) :
  s = ((arr_dom s, arr_cod s); arr_map s).
Proof.
  destruct s as [[x y] m]; reflexivity.
Qed.

Lemma sat_id_op_gen {C : Category} (a x y : obj[C]) (m : x ~> y) :
  sat_id a (((x, y); m) : Arr C) →
  @sat_id (C^op) a (op_arr (((x, y); m) : Arr C)).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  destruct ed.
  revert m H; destruct ec; intros m H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_id_unop_gen {C : Category} (a x y : obj[C]) (m : x ~> y) :
  @sat_id (C^op) a (op_arr (((x, y); m) : Arr C)) →
  sat_id a (((x, y); m) : Arr C).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  destruct ed.
  revert m H; destruct ec; intros m H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_comp_op_gen {C : Category}
  (xh yh xg yg xf yf : obj[C])
  (mh : xh ~> yh) (mg : xg ~> yg) (mf : xf ~> yf) :
  sat_comp (((xh, yh); mh) : Arr C) ((xf, yf); mf) ((xg, yg); mg) →
  @sat_comp (C^op)
    (op_arr (((xh, yh); mh) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C))
    (op_arr (((xf, yf); mf) : Arr C)).
Proof.
  intros [e1 [e2 [e3 H]]]; cbn in e1, e2, e3.
  revert mh mg mf H; destruct e1, e2, e3; intros mh mg mf H.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_comp_unop_gen {C : Category}
  (xh yh xg yg xf yf : obj[C])
  (mh : xh ~> yh) (mg : xg ~> yg) (mf : xf ~> yf) :
  @sat_comp (C^op)
    (op_arr (((xh, yh); mh) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C))
    (op_arr (((xf, yf); mf) : Arr C)) →
  sat_comp (((xh, yh); mh) : Arr C) ((xf, yf); mf) ((xg, yg); mg).
Proof.
  intros [e1 [e2 [e3 H]]]; cbn in e1, e2, e3.
  revert mh mg mf H; destruct e1, e2, e3; intros mh mg mf H.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_eqarr_op_gen {C : Category}
  (xf yf xg yg : obj[C]) (mf : xf ~> yf) (mg : xg ~> yg) :
  sat_eqarr (((xf, yf); mf) : Arr C) ((xg, yg); mg) →
  @sat_eqarr (C^op)
    (op_arr (((xf, yf); mf) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C)).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  revert mf mg H; destruct ed, ec; intros mf mg H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_eqarr_unop_gen {C : Category}
  (xf yf xg yg : obj[C]) (mf : xf ~> yf) (mg : xg ~> yg) :
  @sat_eqarr (C^op)
    (op_arr (((xf, yf); mf) : Arr C))
    (op_arr (((xg, yg); mg) : Arr C)) →
  sat_eqarr (((xf, yf); mf) : Arr C) ((xg, yg); mg).
Proof.
  intros [ed [ec H]]; cbn in ed, ec.
  revert mf mg H; destruct ed, ec; intros mf mg H.
  exists eq_refl, eq_refl; simpl.
  exact H.
Qed.

Lemma sat_id_op {C : Category} (a : obj[C]) (f : Arr C) :
  sat_id a f → @sat_id (C^op) a (op_arr f).
Proof.
  rewrite (arr_eta f); apply sat_id_op_gen.
Qed.

Lemma sat_id_unop {C : Category} (a : obj[C]) (f : Arr C) :
  @sat_id (C^op) a (op_arr f) → sat_id a f.
Proof.
  rewrite (arr_eta f); apply sat_id_unop_gen.
Qed.

Lemma sat_comp_op {C : Category} (h g f : Arr C) :
  sat_comp h f g → @sat_comp (C^op) (op_arr h) (op_arr g) (op_arr f).
Proof.
  rewrite (arr_eta h), (arr_eta g), (arr_eta f); apply sat_comp_op_gen.
Qed.

Lemma sat_comp_unop {C : Category} (h g f : Arr C) :
  @sat_comp (C^op) (op_arr h) (op_arr g) (op_arr f) → sat_comp h f g.
Proof.
  rewrite (arr_eta h), (arr_eta g), (arr_eta f); apply sat_comp_unop_gen.
Qed.

Lemma sat_eqarr_op {C : Category} (f g : Arr C) :
  sat_eqarr f g → @sat_eqarr (C^op) (op_arr f) (op_arr g).
Proof.
  rewrite (arr_eta f), (arr_eta g); apply sat_eqarr_op_gen.
Qed.

Lemma sat_eqarr_unop {C : Category} (f g : Arr C) :
  @sat_eqarr (C^op) (op_arr f) (op_arr g) → sat_eqarr f g.
Proof.
  rewrite (arr_eta f), (arr_eta g); apply sat_eqarr_unop_gen.
Qed.

(** ** Syntax / ** 语法 *)

(* Atoms, over de Bruijn indices into the two sorts. / 原子，通过 de Bruijn 指数映射到这两种类型。 *)
Inductive atom : Type :=
  | ADom (f a : nat)          (* object a is the domain of arrow f / 对象 a 是箭头 f 的定义域 *)
  | ACod (f a : nat)          (* object a is the codomain of arrow f / 对象 a 是箭头 f 的陪域 *)
  | AId (a f : nat)           (* arrow f is the identity arrow of a / 箭头 f 是 a 的恒等箭头 *)
  | AComp (h g f : nat)       (* h is the composite g ∘ f / h 是复合函数 g ∘ f *)
  | AEqArr (f g : nat)        (* arrows f and g are equal / 箭头 f 和 g 相等 *)
  | AEqOb (a b : nat).        (* objects a and b are equal / 对象 a 和 b 相等 *)

Inductive formula : Type :=
  | FAtom (t : atom)
  | FTop
  | FBot
  | FAnd (p q : formula)
  | FOr (p q : formula)
  | FImpl (p q : formula)
  | FNot (p : formula)
  | FAllOb (p : formula)      (* binds object variable 0 / 绑定对象变量 0 *)
  | FExOb (p : formula)
  | FAllArr (p : formula)     (* binds arrow variable 0 / 绑定箭头变量 0 *)
  | FExArr (p : formula).

(** ** Satisfaction / ** 满足 *)

Section Satisfaction.

Context {C : Category}.

Definition ocons (x : obj[C]) (ρ : nat → obj[C]) : nat → obj[C] :=
  fun n => match n with O => x | S k => ρ k end.

Definition acons (s : Arr C) (σ : nat → Arr C) : nat → Arr C :=
  fun n => match n with O => s | S k => σ k end.

(*
Satisfaction of an atom.  Object comparisons are Leibniz; the three
   arrow equations are ≈ under endpoint casts carried as data (design
   note 1).

--------
原子的满足。对象比较是莱布尼茨；三个箭头方程在端点转换作为数据携带时是≈（设计说明1）。
*)
Definition holds_atom (ρ : nat → obj[C]) (σ : nat → Arr C)
  (t : atom) : Type :=
  match t with
  | ADom f a => arr_dom (σ f) = ρ a
  | ACod f a => arr_cod (σ f) = ρ a
  | AId a f => sat_id (ρ a) (σ f)
  | AComp h g f => sat_comp (σ h) (σ g) (σ f)
  | AEqArr f g => sat_eqarr (σ f) (σ g)
  | AEqOb a b => ρ a = ρ b
  end.

Fixpoint holds (ρ : nat → obj[C]) (σ : nat → Arr C)
  (p : formula) : Type :=
  match p with
  | FAtom t => holds_atom ρ σ t
  | FTop => poly_unit
  | FBot => False
  | FAnd p q => holds ρ σ p * holds ρ σ q
  | FOr p q => holds ρ σ p + holds ρ σ q
  | FImpl p q => holds ρ σ p → holds ρ σ q
  | FNot p => holds ρ σ p → False
  | FAllOb p => ∀ x : obj[C], holds (ocons x ρ) σ p
  | FExOb p => { x : obj[C] & holds (ocons x ρ) σ p }
  | FAllArr p => ∀ s : Arr C, holds ρ (acons s σ) p
  | FExArr p => { s : Arr C & holds ρ (acons s σ) p }
  end.

End Satisfaction.

(* Satisfaction depends on environments only pointwise. / 满意度仅在各点取决于环境。 *)
Lemma holds_env_ext {C : Category} (p : formula) :
  ∀ (ρ ρ' : nat → obj[C]) (σ σ' : nat → Arr C),
  (∀ n, ρ n = ρ' n) → (∀ n, σ n = σ' n) →
  holds ρ σ p → holds ρ' σ' p.
Proof.
  induction p; simpl; intros ρ ρ' σ σ' Hρ Hσ H.
  - destruct t; simpl in *;
    repeat rewrite <- (Hσ _); repeat rewrite <- (Hρ _); exact H.
  - exact H.
  - exact H.
  - exact (IHp1 _ _ _ _ Hρ Hσ (fst H), IHp2 _ _ _ _ Hρ Hσ (snd H)).
  - destruct H as [H|H].
    + left; exact (IHp1 _ _ _ _ Hρ Hσ H).
    + right; exact (IHp2 _ _ _ _ Hρ Hσ H).
  - intro Hq.
    refine (IHp2 _ _ _ _ Hρ Hσ (H _)).
    refine (IHp1 _ _ _ _ (fun n => eq_sym (Hρ n))
              (fun n => eq_sym (Hσ n)) Hq).
  - intro Hq.
    refine (H (IHp _ _ _ _ (fun n => eq_sym (Hρ n))
                 (fun n => eq_sym (Hσ n)) Hq)).
  - intro x.
    refine (IHp _ _ _ _ _ Hσ (H x)).
    intros [|n]; simpl; [ reflexivity | exact (Hρ n) ].
  - destruct H as [x H]; exists x.
    refine (IHp _ _ _ _ _ Hσ H).
    intros [|n]; simpl; [ reflexivity | exact (Hρ n) ].
  - intro s.
    refine (IHp _ _ _ _ Hρ _ (H s)).
    intros [|n]; simpl; [ reflexivity | exact (Hσ n) ].
  - destruct H as [s H]; exists s.
    refine (IHp _ _ _ _ Hρ _ H).
    intros [|n]; simpl; [ reflexivity | exact (Hσ n) ].
Qed.

(** ** Sentences: closed formulas / ** 句子：封闭公式 *)

(*
Well-scopedness below a pair of de Bruijn bounds, and sentences as
   the formulas closed below (0, 0) — Mac Lane's “statements”.  A
   sentence's satisfaction does not depend on the environment at all.

--------
在一对 de Bruijn 界限之下的良定义性，以及句子作为在 (0, 0) 之下封闭的公式——麦克莱恩的“陈述”。句子的满足性完全不依赖于环境。
*)
Definition atom_below (ko ka : nat) (t : atom) : Prop :=
  match t with
  | ADom f a => (f < ka)%nat /\ (a < ko)%nat
  | ACod f a => (f < ka)%nat /\ (a < ko)%nat
  | AId a f => (a < ko)%nat /\ (f < ka)%nat
  | AComp h g f => (h < ka)%nat /\ (g < ka)%nat /\ (f < ka)%nat
  | AEqArr f g => (f < ka)%nat /\ (g < ka)%nat
  | AEqOb a b => (a < ko)%nat /\ (b < ko)%nat
  end.

Fixpoint closed_below (ko ka : nat) (p : formula) : Prop :=
  match p with
  | FAtom t => atom_below ko ka t
  | FTop => True
  | FBot => True
  | FAnd p q => closed_below ko ka p /\ closed_below ko ka q
  | FOr p q => closed_below ko ka p /\ closed_below ko ka q
  | FImpl p q => closed_below ko ka p /\ closed_below ko ka q
  | FNot p => closed_below ko ka p
  | FAllOb p => closed_below (S ko) ka p
  | FExOb p => closed_below (S ko) ka p
  | FAllArr p => closed_below ko (S ka) p
  | FExArr p => closed_below ko (S ka) p
  end.

Definition sentence (p : formula) : Prop := closed_below 0 0 p.

(*
Satisfaction of a formula closed below the bounds depends only on the
   environments below them.

--------
在界限以下闭合的公式的满足性仅依赖于它们以下的环境。
*)
Lemma holds_agree {C : Category} (p : formula) :
  ∀ (ko ka : nat) (ρ ρ' : nat → obj[C]) (σ σ' : nat → Arr C),
  closed_below ko ka p →
  (∀ n, (n < ko)%nat → ρ n = ρ' n) →
  (∀ n, (n < ka)%nat → σ n = σ' n) →
  holds ρ σ p → holds ρ' σ' p.
Proof.
  induction p; simpl; intros ko ka ρ ρ' σ σ' Hc Hρ Hσ H.
  - destruct t; cbn in Hc; simpl in *.
    + destruct Hc as [Hf Ha].
      rewrite <- (Hσ f Hf), <- (Hρ a Ha); exact H.
    + destruct Hc as [Hf Ha].
      rewrite <- (Hσ f Hf), <- (Hρ a Ha); exact H.
    + destruct Hc as [Ha Hf].
      rewrite <- (Hρ a Ha), <- (Hσ f Hf); exact H.
    + destruct Hc as [Hh [Hg Hf]].
      rewrite <- (Hσ h Hh), <- (Hσ g Hg), <- (Hσ f Hf); exact H.
    + destruct Hc as [Hf Hg].
      rewrite <- (Hσ f Hf), <- (Hσ g Hg); exact H.
    + destruct Hc as [Ha Hb].
      rewrite <- (Hρ a Ha), <- (Hρ b Hb); exact H.
  - exact H.
  - exact H.
  - destruct Hc as [Hc1 Hc2].
    exact (IHp1 _ _ _ _ _ _ Hc1 Hρ Hσ (fst H),
           IHp2 _ _ _ _ _ _ Hc2 Hρ Hσ (snd H)).
  - destruct Hc as [Hc1 Hc2].
    destruct H as [H|H].
    + left; exact (IHp1 _ _ _ _ _ _ Hc1 Hρ Hσ H).
    + right; exact (IHp2 _ _ _ _ _ _ Hc2 Hρ Hσ H).
  - destruct Hc as [Hc1 Hc2].
    intro Hq.
    refine (IHp2 _ _ _ _ _ _ Hc2 Hρ Hσ (H _)).
    refine (IHp1 _ _ _ _ _ _ Hc1
              (fun n Hn => eq_sym (Hρ n Hn))
              (fun n Hn => eq_sym (Hσ n Hn)) Hq).
  - intro Hq.
    refine (H (IHp _ _ _ _ _ _ Hc
                 (fun n Hn => eq_sym (Hρ n Hn))
                 (fun n Hn => eq_sym (Hσ n Hn)) Hq)).
  - intro x.
    refine (IHp _ _ _ _ _ _ Hc _ Hσ (H x)).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hρ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ko) Hn).
  - destruct H as [x H]; exists x.
    refine (IHp _ _ _ _ _ _ Hc _ Hσ H).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hρ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ko) Hn).
  - intro sarr.
    refine (IHp _ _ _ _ _ _ Hc Hρ _ (H sarr)).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hσ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ka) Hn).
  - destruct H as [sarr H]; exists sarr.
    refine (IHp _ _ _ _ _ _ Hc Hρ _ H).
    intros [|n] Hn; simpl; [ reflexivity | ].
    apply Hσ; exact (proj2 (PeanoNat.Nat.succ_lt_mono n ka) Hn).
Qed.

(* A sentence's satisfaction is environment-independent. / 一个句子的满足性与环境无关。 *)
Corollary holds_sentence_env_irrel {C : Category} (p : formula) :
  sentence p →
  ∀ (ρ ρ' : nat → obj[C]) (σ σ' : nat → Arr C),
  holds ρ σ p → holds ρ' σ' p.
Proof.
  intros Hs ρ ρ' σ σ' H.
  refine (holds_agree p 0 0 ρ ρ' σ σ' Hs _ _ H);
  intros n Hn; exfalso; exact (PeanoNat.Nat.nlt_0_r n Hn).
Qed.

(** ** The syntactic dual / ** 句法双重性 *)

(*
Interchange domain with codomain, reverse composites (Mac Lane
   §II.1's table); identity, equality, and the propositional structure
   are self-dual.

--------
将域与陪域互换，反转复合（Mac Lane §II.1 的表格）；恒等、等式和命题结构是自对偶的。
*)
Definition dual_atom (t : atom) : atom :=
  match t with
  | ADom f a => ACod f a
  | ACod f a => ADom f a
  | AId a f => AId a f
  | AComp h g f => AComp h f g
  | AEqArr f g => AEqArr f g
  | AEqOb a b => AEqOb a b
  end.

Fixpoint dual (p : formula) : formula :=
  match p with
  | FAtom t => FAtom (dual_atom t)
  | FTop => FTop
  | FBot => FBot
  | FAnd p q => FAnd (dual p) (dual q)
  | FOr p q => FOr (dual p) (dual q)
  | FImpl p q => FImpl (dual p) (dual q)
  | FNot p => FNot (dual p)
  | FAllOb p => FAllOb (dual p)
  | FExOb p => FExOb (dual p)
  | FAllArr p => FAllArr (dual p)
  | FExArr p => FExArr (dual p)
  end.

(* Dualizing twice is the identity, on the nose. / 双重对偶就是恒等操作，确切无误。 *)
Lemma dual_atom_invol (t : atom) : dual_atom (dual_atom t) = t.
Proof. destruct t; reflexivity. Qed.

Lemma dual_invol (p : formula) : dual (dual p) = p.
Proof.
  induction p; simpl;
  try rewrite IHp; try rewrite IHp1; try rewrite IHp2;
  try rewrite dual_atom_invol; reflexivity.
Qed.

(** ** The semantic duality lemma (Mac Lane §II.2) / ** 语义对偶引理（Mac Lane §II.2） *)

(* Transport an arrow environment to the opposite category. / 将箭头范畴传输到对偶范畴。 *)
Definition op_env {C : Category} (σ : nat → Arr C) : nat → Arr (C^op) :=
  fun n => op_arr (σ n).

Lemma holds_dual_to {C : Category} (p : formula) :
  ∀ (ρ : nat → obj[C]) (σ : nat → Arr C),
  holds ρ σ (dual p) → @holds (C^op) ρ (op_env σ) p
with holds_dual_from {C : Category} (p : formula) :
  ∀ (ρ : nat → obj[C]) (σ : nat → Arr C),
  @holds (C^op) ρ (op_env σ) p → holds ρ σ (dual p).
Proof.
  - induction p; simpl; intros ρ σ H.
    + destruct t; simpl in *; unfold op_env, op_arr; simpl.
      * exact H.
      * exact H.
      * exact (sat_id_op _ _ H).
      * exact (sat_comp_op _ _ _ H).
      * exact (sat_eqarr_op _ _ H).
      * exact H.
    + exact H.
    + exact H.
    + exact (IHp1 _ _ (fst H), IHp2 _ _ (snd H)).
    + destruct H as [H|H]; [ left; exact (IHp1 _ _ H)
                           | right; exact (IHp2 _ _ H) ].
    + intro Hq; exact (IHp2 _ _ (H (holds_dual_from C p1 _ _ Hq))).
    + intro Hq; exact (H (holds_dual_from C p _ _ Hq)).
    + intro x; exact (IHp _ _ (H x)).
    + destruct H as [x H]; exists x; exact (IHp _ _ H).
    + intro s.
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _
                (IHp _ (acons (unop_arr s) σ) (H (unop_arr s)))).
      intros [|n]; simpl.
      * exact (op_unop_arr s).
      * reflexivity.
    + destruct H as [s H].
      exists (op_arr s).
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _
                (IHp _ (acons s σ) H)).
      intros [|n]; simpl; reflexivity.
  - induction p; simpl; intros ρ σ H.
    + destruct t; simpl in *; unfold op_env, op_arr in H; simpl in H.
      * exact H.
      * exact H.
      * exact (sat_id_unop _ _ H).
      * exact (sat_comp_unop _ _ _ H).
      * exact (sat_eqarr_unop _ _ H).
      * exact H.
    + exact H.
    + exact H.
    + exact (IHp1 _ _ (fst H), IHp2 _ _ (snd H)).
    + destruct H as [H|H]; [ left; exact (IHp1 _ _ H)
                           | right; exact (IHp2 _ _ H) ].
    + intro Hq; exact (IHp2 _ _ (H (holds_dual_to C p1 _ _ Hq))).
    + intro Hq; exact (H (holds_dual_to C p _ _ Hq)).
    + intro x; exact (IHp _ _ (H x)).
    + destruct H as [x H]; exists x; exact (IHp _ _ H).
    + intro s.
      refine (IHp _ (acons s σ) _).
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _
                (H (op_arr s))).
      intros [|n]; simpl; reflexivity.
    + destruct H as [s H].
      exists (unop_arr s).
      refine (IHp _ (acons (unop_arr s) σ) _).
      refine (holds_env_ext p _ _ _ _ (fun n => eq_refl) _ H).
      intros [|n]; simpl.
      * exact (eq_sym (op_unop_arr s)).
      * reflexivity.
Qed.

(*
The lemma in its stated form: C satisfies the dual of Σ under an
   assignment iff C^op satisfies Σ under the transported assignment.

--------
命题引理的表述形式：在某个赋值下，C 满足 Σ 的对偶当且仅当 C^op 在传递的赋值下满足 Σ。
*)
Definition holds_dual {C : Category} (p : formula)
  (ρ : nat → obj[C]) (σ : nat → Arr C) :
  holds ρ σ (dual p) ↔ @holds (C^op) ρ (op_env σ) p :=
  (holds_dual_to p ρ σ, holds_dual_from p ρ σ).

(** ** The duality principle (Mac Lane §II.1, Awodey §3.1) / ** 对偶性原理（Mac Lane §II.1, Awodey §3.1） *)

(* A formula valid in every category under every assignment. / 在每个范畴下，在每个赋值下都成立的公式。 *)
Definition valid (p : formula) : Type :=
  ∀ (C : Category) (ρ : nat → obj[C]) (σ : nat → Arr C), holds ρ σ p.

(*
If Σ holds in every category, so does its dual: instantiate the
   hypothesis at C^op and transport back — no double-op unwinding
   needed (design note 3).

--------
如果 Σ 在每个范畴中都成立，那么它的对偶也成立：在 C^op 上实例化假设，然后再传回——无需双重取对偶展开（设计注 3）。
*)
Theorem duality_principle (p : formula) : valid p → valid (dual p).
Proof.
  intros V C ρ σ.
  exact (holds_dual_from p ρ σ (V (Opposite C) ρ (op_env σ))).
Qed.

(*
The principle self-composes: applying it twice returns to the
   original statement, by the syntactic involution.

--------
原则上自我组成：通过语法上的内反作用，应用两次会返回到原始陈述。
*)
Corollary duality_principle_invol (p : formula) :
  valid p → valid (dual (dual p)).
Proof.
  intro V; rewrite dual_invol; exact V.
Qed.

(** ** The one-functor case (maclane:II.1:remark2, scoped) / ** 单函子情况（Mac Lane: II.1: 注意2，作用域限定） *)

(*
The one-functor recording (design note 4): the object and arrow
   actions of F^op are literally those of F, stated at BUNDLE level —
   this is a definitional commutation, not a statement-level theorem;
   the statement-level functor language is the deferred half of the
   remark, and the disclosure in the header is its honest delivery.

--------
单函子记录（设计注4）：F^op 的对象和箭头作用严格上与 F 相同，在 BUNDLE 级别上说明——这是一个定义上的交换，而不是陈述级别的定理；陈述级别的函子语言是该备注的延迟部分，标题中的披露是其如实呈现。
*)
(* The arrow action of a functor, on bundles. / 函子在丛上的箭头作用。 *)
Definition arr_fmap {C D : Category} (F : C ⟶ D) (s : Arr C) : Arr D :=
  ((F (arr_dom s), F (arr_cod s)); fmap[F] (arr_map s)).

Lemma arr_fmap_op {C D : Category} (F : C ⟶ D)
  (s : Arr C) :
  arr_fmap F s = unop_arr (arr_fmap (F^op) (op_arr s)).
Proof.
  destruct s as [[x y] f]; reflexivity.
Qed.
