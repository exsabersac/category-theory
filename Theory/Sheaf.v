Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(** * Presheaves, sites (coverages), and sheaves / * 预层、站点（覆盖）、层 *)

(*
nLab: https://ncatlab.org/nlab/show/presheaf
   Wikipedia: https://en.wikipedia.org/wiki/Presheaf_(category_theory)

   A C-valued presheaf on a category U is a functor U^op ⟶ C; the classical
   case takes C := Sets. Its action fmap[X] f on a morphism f : a ~> b of U is
   the restriction map X(b) → X(a). Presheaves on U form the functor category
   [U^op, C], and a copresheaf is the covariant variant U ⟶ C (a presheaf on
   U^op).

--------
nLab: https://ncatlab.org/nlab/show/presheaf
   Wikipedia: https://en.wikipedia.org/wiki/Presheaf_(category_theory)

   范畴 U 上取值于 C 的预层 (presheaf) 是函子 U^op ⟶ C；经典情形取 C := Sets。
   其对 U 的态射 f : a ~> b 的作用 fmap[X] f 是限制映射 X(b) → X(a)。U 上的预层
   构成函子范畴 [U^op, C]；余预层 (copresheaf) 是共变变体 U ⟶ C（即 U^op 上的预层）。
*)

(*
nLab: https://ncatlab.org/nlab/show/site
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_topology

   A site is a category C equipped with a coverage J, which assigns to each
   object u a collection of covering families { fᵢ : uᵢ ~> u } subject to the
   pullback-stability axiom: for any covering family of u and any g : v ~> u
   there is a covering family { hⱼ : vⱼ ~> v } of v such that every composite
   g ∘ hⱼ factors through some fᵢ (i.e. fᵢ ∘ k ≈ g ∘ hⱼ for some k).

--------
nLab: https://ncatlab.org/nlab/show/site
   Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_topology

   位 (site) 是配备 Grothendieck 拓扑的范畴：对每个对象指定覆盖筛，服从稳定性与局部性公理。
*)

(*
nLab: https://ncatlab.org/nlab/show/sheaf
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   A presheaf X : C^op ⟶ Sets is a sheaf for a covering family
   { fᵢ : uᵢ ~> u } when every matching (compatible) family of local sections
   xᵢ ∈ X(uᵢ) — sections agreeing on overlaps, X(g)(xᵢ) ≈ X(h)(xⱼ) whenever
   fᵢ ∘ g ≈ fⱼ ∘ h — glues to a unique global section x ∈ X(u) with
   X(fᵢ)(x) ≈ xᵢ for all i (existence is the gluing axiom, uniqueness is the
   separated/locality axiom). A separated presheaf asks only for uniqueness.

--------
nLab: https://ncatlab.org/nlab/show/sheaf
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   层 (sheaf) 是满足下降条件的预层：对拓扑中的每个覆盖，截面由兼容的局部截面唯一胶合。
*)

(*
Where sheaves come from, and what they are for

   nLab:      https://ncatlab.org/nlab/show/sheaf
   nLab:      https://ncatlab.org/nlab/show/Grothendieck+topology
   Wikipedia: https://en.wikipedia.org/wiki/Sheaf_(mathematics)

   A sheaf is the systematic bookkeeping of the passage from local data
   to global data.  A presheaf already assigns data to each object and,
   through the restriction maps that are the contravariant action of a
   [Presheaf], cuts that data down along morphisms; the sheaf condition
   adds the discipline that makes the data behave like genuine sections
   on a space.  Two clauses carry it.  Gluing, the existence clause, asks
   that local sections on a cover which agree on their overlaps determine
   an actual global section; locality, or separatedness, the uniqueness
   clause, asks that a section be fixed by its restrictions to a cover,
   so that two sections agreeing locally everywhere coincide (Wikipedia,
   "Sheaf (mathematics)").  Equivalently, the value over a covered object
   is the limit — an equalizer — of the values on the cover, so the sheaf
   condition IS a descent condition (nLab, "sheaf").  This is the content
   a mere presheaf may lack, and [restriction] is what the in-tree
   [Sheaf] class records over the single [coverage] family that a [Site]
   supplies; the header above and Theory/Sheaf/Category.v disclose that
   this per-object, per-leg encoding is a deliberately scoped
   approximation of the classical predicate.

   The subject has a dated origin.  Jean Leray, held as a prisoner of war
   in Oflag XVII-A from 1940 to 1945, there developed sheaves, sheaf
   cohomology, and spectral sequences, coining "faisceau" in his 1946
   Comptes Rendus notes (Haynes Miller, "Leray in Oflag XVIIA: The
   origins of sheaf theory, sheaf cohomology, and spectral sequences").
   Henri Cartan's seminar then reworked the notion through étalé spaces,
   Serre carried it into algebraic geometry as coherent sheaves (Serre,
   "Faisceaux Algébriques Cohérents", Annals of Mathematics 1955), and
   Godement fixed the standard formalism (Godement, "Topologie
   algébrique et théorie des faisceaux", 1958).  To do cohomology on
   schemes, where the Zariski topology is too coarse, and to attack the
   Weil conjectures, Grothendieck replaced open covers by covering
   families in an abstract category — a Grothendieck topology, hence a
   site — first as a pretopology in Artin's 1962 Harvard notes and then
   through sieves in SGA 4 (nLab, "Grothendieck topology"); sieves
   themselves are Theory/Sieve.v.

   The utility runs well past geometry.  For a site the sheaves form a
   Grothendieck topos: a reflective, left-exact localization of a
   presheaf topos, carrying a subobject classifier and an internal
   higher-order intuitionistic logic whose truth values form a Heyting
   algebra rather than two points (Mac Lane, Moerdijk, "Sheaves in
   Geometry and Logic: A First Introduction to Topos Theory", Springer
   1992).  The subobject classifier of the presheaf category is now
   proved in tree: Instance/Fun/Classifier.v's [Fun_Classifier]
   classifies subobjects in [[C^op, Sets]] over the sieve presheaf of
   Theory/Sieve.v, conditionally on #402's [Untruncate].  Nothing below
   consumes it — this file's [Class Site] is untouched — and the sheaf
   topos, the localization and the Heyting structure remain narrative
   prose.  Such a topos is read as the sheaf theory of a generalized
   space, and for a subcanonical topology the Yoneda map composed with
   sheafification embeds that space fully faithfully into its own sheaves
   (nLab, "Grothendieck topology").  Fong and Spivak model a behavior
   type as a sheaf on a space of time, where a truth value is the open
   set of times on which a property holds and safety becomes a statement
   of temporal logic (Fong, Spivak, "Seven Sketches in Compositionality",
   Cambridge UP 2019, Ch. 7).  Abramsky and Brandenburger recast quantum
   non-locality and contextuality as the obstruction to a global section
   of a sheaf of local empirical models, grading the Bell, Hardy, and GHZ
   arguments in a hierarchy (Abramsky, Brandenburger, "The
   Sheaf-Theoretic Structure of Non-Locality and Contextuality", New
   Journal of Physics 2011).

   The split carries a type-theoretic reading.  A presheaf is a family of
   local states indexed by objects, its restriction a contravariant
   reindexing; the sheaf condition is then a descent obligation, taking a
   cover-indexed tuple of locally consistent pieces to a unique whole —
   the agree-on-overlaps merge discipline of distributed data.  The
   in-tree [Site] and [Sheaf] classes make that obligation a proof
   obligation whose covering and matching data carry computational
   witnesses, which is why the file states them over the Type-valued
   [ForallT] and [ExistsT] rather than the Prop-valued vector predicates.
   The other half of the story is sheafification: every presheaf reflects
   into a sheaf, the inclusion into presheaves having a left-exact left
   adjoint (Wikipedia, "Sheaf (mathematics)"; nLab, "sheaf").  That
   reflection is the piece deferred here (ledger 1), though
   Theory/Sheaf/Category.v already builds Sheaves C as the full
   subcategory of presheaves cut out by [Sheaf].  Presheaf categories
   themselves recur across the library: the free cocompletion and target
   of the Yoneda embedding (Instance/Fun.v, Functor/Hom/Yoneda.v), the
   subobject presheaf feeding the classifier (Theory/Subobject/Functor.v),
   and the elementary topos development (Structure/Topos.v).

--------
滑轮从何而来，有何用途

nLab：https://ncatlab.org/nlab/show/sheaf
 nLab：https://ncatlab.org/nlab/show/Grothendieck+topology
 维基百科：https://en.wikipedia.org/wiki/Sheaf_(mathematics)

捆是对本地数据中的段落进行系统的簿记
 到全球数据。 预束已经将数据分配给每个对象，并且，
 通过限制图，这是a的逆变作用
 [Presheaf]，沿着态射削减数据； 轴状况
 添加了使数据表现得像真实部分的规则
 在一个空间上。 有两个子句承载它。 粘合，存在子句，询问
 封面上就其重叠达成一致的局部部分确定
 实际的全局部分； 局部性或分离性、唯一性
 条款，要求通过其对封面的限制来固定一个部分，
 以便两个部分在各处都一致（维基百科，
 “捆（数学）”）。
等效地，覆盖对象的值
 是封面上的值的限制（均衡器），因此束
 条件是下降条件（nLab，“束”）。 这是内容
 仅仅一个 presheaf 可能会缺少，而 [restriction] 就是树内的
 [Sheaf] 类记录超过 [coverage] 系列，[Site]
 用品； 上面的标题和 Theory/Sheaf/Category.v 披露了这一点
 这个每个对象、每个腿的编码是有意限定范围的
 经典谓词的近似。

该主题有一个有日期的起源。 让·勒雷 (Jean Leray)，作为战俘被关押
 在 Oflag XVII-A 从 1940 年到 1945 年，开发了滑轮、滑轮
 上同调和谱序列，在 1946 年创造了“faisceau”
 Comptes Rendus 笔记（Haynes Miller，“Oflag XVIIA 中的 Leray：The
 层理论、层上同调和谱序列的起源”）。
 亨利·嘉当的研讨会随后通过 étalé 空间重新设计了这个概念，
 塞尔将其作为相干滑轮带入代数几何（Serre，
 “Faisceaux Algébriques Cohérents”，数学年鉴 1955），以及
 Godement 确定了标准形式主义（Godement，“拓扑学
 algébrique et théorie des faisceaux”，1958）。 做上同调
 方案，其中 Zariski 拓扑过于粗糙，并攻击
 韦尔猜想，格洛腾迪克用覆盖代替了开放覆盖
 抽象范畴中的族——格洛腾迪克拓扑，因此
 站点——首先作为 Artin 1962 年哈佛笔记中的预拓扑，然后
 通过 SGA 4 中的筛子（nLab，“Grothendieck 拓扑”）； 筛子
 它们本身就是 Theory/Sieve.v。

该实用程序远远超出了几何学。 对于某个地点，滑轮形成一个
 格罗滕迪克拓扑：反思性的左精确定位
 presheaf topos，携带子对象分类器和内部
 高阶直觉逻辑，其真值形成 Heyting
 代数而不是两点（Mac Lane，Moerdijk，“Sheaves in
 几何与逻辑：拓扑理论初介”，施普林格
 1992）。 presheaf 范畴的子对象分类器现在是
 在树中证明：Instance/Fun/Classifier.v 的 [Fun_Classifier]
 在 [[C^op, Sets]] 的筛预轴上对子对象进行分类
 Theory/Sieve.v，有条件地基于 #402 的 [Untruncate]。 下面什么都没有
 消耗它 — 该文件的 [Class Site] 未受影响 — 并且捆
 拓扑、本地化和 Heyting 结构仍然是叙述性的
 散文。
这样的拓扑被解读为广义的层理论
 空间，对于亚规范拓扑，米田映射由
 束化将该空间完全忠实地嵌入到其自己的滑轮中
 （nLab，“格洛腾迪克拓扑”）。 Fong 和 Spivak 模拟行为
 类型为时间空间上的一捆，其中真值是开
 财产持有和安全成为声明的一组时间
 时间逻辑（Fong，Spivak，“组合性的七个草图”，
 剑桥 UP 2019，第 1 章 7). 阿布拉姆斯基和勃兰登堡重塑量子
 非局部性和上下文性作为全局部分的障碍
 一堆局部经验模型，对 Bell、Hardy 和 GHZ 进行分级
 层次结构中的争论（阿布拉姆斯基、勃兰登堡、“
 非局域性和语境性的层理论结构”，新
 物理学杂志 2011）。

这种分裂带有类型理论的解读。 预轴是一个家庭
 由对象索引的局部状态，其限制是逆变的
 重新索引； 然后，层条件是下降义务，采取
 将局部一致的片段覆盖索引元组到一个独特的整体 -
 分布式数据的一致重叠合并规则。 的
 树内 [Site] 和 [Sheaf] 类使该义务成为证明
 覆盖和匹配数据带有计算能力的义务
 见证人，这就是文件在类型值上声明它们的原因
 [ForallT] 和 [ExistsT] 而不是 Prop 值向量谓词。 故事的另一半是束化：每个预束都反映出
 进入滑轮，包含在具有左精确左的预滑轮中
 伴随（维基百科，“Sheaf（数学）”；nLab，“sheaf”）。
那
 不过，反射是此处推迟的部分（分类帐 1）
 Theory/Sheaf/Category.v 已经将 Sheaves C 构建为完整的
 由 [Sheaf] 切割的预滑轮子范畴。 预捆扎范畴
 它们本身在库中重复出现：免费的共同完成和目标
 米田嵌入（Instance/Fun.v、Functor/Hom/Yoneda.v）的
 子对象 presheaf 为分类器提供数据 (Theory/Subobject/Functor.v)，
 以及基本的拓扑开发（Structure/Topos.v）。
*)

(*
A C-valued presheaf on some category U.
  C is often taken to be Sets.

  The universe annotation keeps the two categories' levels independent:
  left to inference, minimization had identified U's hom and proof levels
  with C's — one shared level across both Category instances — which for
  a Sets target pins the elements of its objects to the site's homs,
  shutting out exactly the typical case of a sections presheaf: a small
  site with values one level up (Instance/Top/Presheaf.v's
  [ContinuousPresheaf], whose sections are hom-setoids of [Top]).  Every
  instantiation at shared levels is still available.  [Presheaves] below
  and the copresheaf pair remain inference-minimized; the consumer file
  discloses the consequence.

--------
U 范畴上的一个 C 值预层。C 通常取为集合（Sets）。

宇宙注解保持两个范畴的层级独立：
左侧由推断处理，最小化已经将 U 的同态（hom）和证明（proof）层级
与 C 的层级对齐——在两个范畴实例中共享一个层级——对于 Sets 目标对象来说，这会将其对象的元素固定到站点（site）的同态上，
恰好排除了典型的切片预层（sections presheaf）情况：一个小站点，其值提升到一个层级之上（Instance/Top/Presheaf.v 中的 [ContinuousPresheaf]，其切片是 [Top] 的同态集）。
在共享层级上的每个实例仍然可用。下面的 [Presheaves] 和余预层对（copresheaf pair）仍保持最小化推断；
消费者文件（consumer file）揭示了其结果。
*)
Definition Presheaf@{u1 u2 u3 u4 u5 u6 +}
  (U : Category@{u1 u2 u3}) (C : Category@{u4 u5 u6}) := U^op ⟶ C.

(* The category of C-valued presheaves on a category U. / 在一个范畴 U 上的 C 值预上函子范畴。 *)
Definition Presheaves {U C : Category} := [U^op, C].

(* A C-valued copresheaf on U: a covariant functor, i.e. a presheaf on U^op. / 在 U 上的值为 C 的共预层：一个协变函子，即 U^op 上的预层。 *)
Definition Copresheaf (U C : Category) := U ⟶ C.

(* The category of C-valued copresheaves on a category U. / 在范畴 U 上的 C 值共预函子范畴。 *)
Definition Copresheaves {U C : Category} := [U, C].

(* Custom data type to express Forall propositions on vectors over Type. / 用于在类型上的向量上表达全称命题的自定义数据类型。 *)
Inductive ForallT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ForallT_nil : ForallT (nil A)
  | ForallT_cons (n : nat) (x : A) (v : t A n) :
    P x → ForallT v → ForallT (cons A x n v).

(* Likewise the Type-valued analogue of Vector.Exists, carrying witness data. / 同样是 Vector.Exists 的类型值类比，携带见证数据。 *)
Inductive ExistsT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ExistsT_cons_hd (m : nat) (x : A) (v : t A m) :
    P x → ExistsT (cons A x m v)
  | ExistsT_cons_tl (m : nat) (x : A) (v : t A m) :
    ExistsT v → ExistsT (cons A x m v).

(*
A coverage on a category C consists of a function assigning to each object
   U ∈ C a collection of families of morphisms { fᵢ : Uᵢ → U } (i∈I), called
   covering families, such that

   if { fᵢ : Uᵢ → U } (i∈I) is a covering family
   and g : V → U is a morphism,
   then there exists a covering family { hⱼ : Vⱼ → V }
   such that each composite g ∘ hⱼ factors through some fᵢ.

--------
在一个范畴 C 上的一个覆盖由一个函数组成，该函数将每个对象 U ∈ C 分配给一族态射族 { fᵢ : Uᵢ → U } (i∈I)，称为覆盖族，使得

如果 { fᵢ : Uᵢ → U } (i∈I) 是一个覆盖族，并且 g : V → U 是一个态射，那么存在一个覆盖族 { hⱼ : Vⱼ → V }，使得每个复合 g ∘ hⱼ 可以通过某个 fᵢ 因式分解。
*)

Class Site (C : Category) := {
  (*
A covering family of u is a finite (vector-indexed) list of morphisms
     uᵢ ~> u into u; sigT packages the length together with the vector.

--------
u 的覆盖族是一个有限的（向量索引的）从 uᵢ 到 u 的态射列表；sigT 将长度与向量一起打包。
*)
  covering_family (u : C) := sigT (Vector.t (∃ uᵢ, uᵢ ~> u));

  (*
This encoding picks a single covering family per object rather than the
     usual collection of covering families; it suffices to state the sheaf
     condition below, but is less general than a full coverage.

--------
这种编码为每个对象选择一个单一的覆盖族，而不是通常的覆盖族集合；下面陈述的层条件已经足够，但它不如完整覆盖一般。
*)
  coverage (u : C) : covering_family u;

  (* The coverage axiom (pullback stability), per the site reference above. / 覆盖公理（拉回稳定性），如上网站参考所示。 *)
  coverage_condition
    (u  : C) (fs : covering_family u)
    (v  : C) (g  : v ~> u) :
    ∃ hs : covering_family v,
      ForallT (A := ∃ vⱼ, vⱼ ~> v) (λ '(vⱼ; hⱼ),
          ExistsT (A := ∃ uᵢ, uᵢ ~> u) (λ '(uᵢ; fᵢ),
              ∃ k : vⱼ ~> uᵢ, fᵢ ∘ k ≈ g ∘ hⱼ)
            (`2 fs))
        (`2 hs)
}.

(*
If { fᵢ : Uᵢ → U } (i∈I) is a family of morphisms with codomain U,
   a presheaf X : Cᵒᵖ → Set is called a sheaf for this family if:

   for any collection of elements xᵢ ∈ X(Uᵢ)
   such that,
     whenever g : V → Uᵢ and h : V → Uⱼ
     are such that fᵢ ∘ g = fⱼ ∘ h,
     we have X(g)(xᵢ) = X(h)(xⱼ),
   then there exists a unique x ∈ X(U)
   such that X(fᵢ)(x) = xᵢ for all i .

--------
如果 { fᵢ : Uᵢ → U } (i∈I) 是一个以 U 为陪域的态射族，
一个预层 X : Cᵒᵖ → Set 被称为该族的层，如果：

对于任何元素集合 xᵢ ∈ X(Uᵢ)，
若满足以下条件：
  每当 g : V → Uᵢ 和 h : V → Uⱼ 
  并且 fᵢ ∘ g = fⱼ ∘ h 时，
  我们有 X(g)(xᵢ) = X(h)(xⱼ)，
那么存在唯一的 x ∈ X(U)，
使得对于所有 i，X(fᵢ)(x) = xᵢ。
*)

Class Sheaf `{@Site C} (X : Presheaf C Sets) := {
  restriction :
    ∀ u : C,
      let '(i; f) := coverage u in
      ForallT
        (A := ∃ uᵢ, uᵢ ~> u)
        (λ '(uᵢ; fᵢ),
            ∀ xᵢ : X uᵢ,
              (∀ (v : C) (g : v ~> uᵢ),
                  ForallT
                    (A := ∃ uⱼ, uⱼ ~> u)
                    (λ '(uⱼ; fⱼ),
                      ∀ h : v ~> uⱼ,
                        fᵢ ∘ g ≈ fⱼ ∘ h →
                        ∀ xⱼ : X uⱼ,
                          fmap[X] g xᵢ ≈ fmap[X] h xⱼ)
                    f) →
              ∃! x : X u, fmap[X] fᵢ x ≈ xᵢ)
        f
}.
