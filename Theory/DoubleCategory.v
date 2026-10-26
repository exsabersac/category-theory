Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * Pseudo double categories / * 伪双范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/double+category
   Wikipedia: https://en.wikipedia.org/wiki/Double_category

   A (pseudo) double category has a collection of objects, two kinds of
   morphism between them — STRICT vertical 1-cells (organised as an ordinary
   [Category], [dcat]) and WEAK horizontal 1-cells ([dhor]) — and, for every
   arrangement

        a --h--> b
        |        |
        u        v          (h : dhor a b top, k : dhor c d bottom,
        v        v           u : a ~> c left, v : b ~> d right)
        c --k--> d

   a setoid [dsq h u v k] of squares filling it. Vertical composition of
   squares ([dsq_vcomp]) and the vertical identity square ([dsq_vid]) are
   STRICT and satisfy the ordinary category laws; horizontal composition of
   1-cells ([dhcomp]) is only WEAKLY associative and unital, the coherence
   isomorphisms being invertible GLOBULAR squares (squares whose two vertical
   edges are identities). This is exactly the amount of weakening that lets
   the same class host both the double category of commuting squares of a
   category (Construction/Sq.v — where [dsq h u v k := k ∘ u ≈ v ∘ h] is a
   mere proposition, its setoid trivial, every law automatic) and the double
   category of cospans (Construction/Cospan/Double.v — where squares are
   apex-maps and horizontal composition is a chosen pushout, so [dsq] is
   genuinely proof-relevant and the coherence squares carry real content).

   The horizontal 1-cells live in a plain [Type], but a square's boundary
   mentions the vertical morphisms [u], [v], which are only ever compared up
   to [≈]. So the square family must cohere across [≈] on its boundary. That
   coherence is [dsq_coerce]: along proofs [eu : u ≈ u'], [ev : v ≈ v'] a map
   [dsq h u v k → dsq h u' v' k], proof-irrelevant ([dsq_coerce_id]) and
   functorial ([dsq_coerce_trans]). This is precisely the Phase 10 displayed
   [dtransport] pattern (Theory/Displayed.v) re-applied to the vertical
   boundary of a square: the strict vertical laws are then stated THROUGH
   [dsq_coerce], which absorbs boundary reassociations such as [u' ∘ id]
   versus [u], and the weak coherence laws are stated between globular squares
   after normalising their [id ∘ id] vertical boundaries back to [id].

   Design note (kept minimal so both models supply every field): [dsq] is NOT
   assumed proof-irrelevant beyond what [dsq_setoid] provides, so the cospan
   model — whose squares are not propositions — is admissible; and every
   coherence field is dischargeable in the commuting-squares model, where the
   square setoid identifies all inhabitants. The invertible globular squares
   ([dassoc], [dunit_left], [dunit_right]) are packaged as a forward square, a
   backward square, and the two round-trip identities (a sigma-of-squares),
   which the commuting-squares model produces from associativity/unit laws of
   the base and the cospan model produces from the pushout universal property;
   named accessors ([dassoc_to], [dassoc_from], ...) are provided below.

   SCOPE. This class is the coherence-only fragment of the literature's
   pseudo double category (Grandis–Paré), matching the work order's skeleton.
   Three standard components are deliberately not required as fields:
   (a) horizontal identity squares on general VERTICAL morphisms
       (1_u : dsq (dhid a) u u (dhid c)) together with their functoriality —
       the representability formulation of the vertical zigzag in
       Theory/DoubleCategory/Companion.v exists precisely because of this;
   (b) the unit half of interchange,
       dsq_hcomp (dsq_vid h) (dsq_vid h') ≈ dsq_vid (dhcomp h' h);
   (c) naturality in squares of [dassoc]/[dunit_left]/[dunit_right]
       (contrast the hassoc_natural/hunit_*_natural fields of
       Theory/Bicategory.v).
   Both in-tree instances (Construction/Sq.v, Construction/Cospan/Double.v)
   satisfy all three, so a later phase may add them as fields without
   breaking either model.

   Orientation note: [dassoc] runs right-bracketed to left-bracketed
   (h·(g·f) ⇒ (h·g)·f), the OPPOSITE of tensor_assoc (Structure/Monoidal.v)
   and hassoc (Theory/Bicategory.v); the triangle and pentagon below are the
   standard laws rearranged for that orientation. A future horizontal-
   bicategory bridge must swap to/from accordingly.

--------
nLab: https://ncatlab.org/nlab/show/double+category
   Wikipedia: https://en.wikipedia.org/wiki/Double_category

   双重范畴 (double category) 有对象、水平 1-胞、垂直 1-胞，以及填入方块的 2-胞
   （四方格），水平与垂直方向各有范畴结构，且两方向的复合经交换律 (interchange)
   相容。本库的伪双重范畴变体允许水平复合仅在连贯同构下结合/有单位（类比双范畴），
   垂直方向通常更严格。companions 与 conjoints 是连接两方向的特殊方块，支撑 mates
   对应。本文件给出核心类与边界连贯；历史与用途见下一块注释（后续波次可续译）。
*)

(*
Where double categories come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/double+category
   nLab:  https://ncatlab.org/nlab/show/proarrow+equipment
   Paper: Ehresmann, “Catégories doubles et catégories structurées”,
          C. R. Acad. Sci. Paris 256 (1963), 1198-1201
   Paper: Grandis, Paré, “Limits in double categories”, Cahiers de
          Topologie et Géométrie Différentielle Catégoriques 40 (1999)
   Paper: Shulman, “Framed bicategories and monoidal fibrations”, Theory
          and Applications of Categories 20 (2008), no. 18

   A double category is the two-dimensional structure that keeps two
   different kinds of 1-cell at once. Shulman states the split: in some
   bicategories the 1-cells are morphisms BETWEEN the objects, such as
   functors between categories, while in others they are objects OVER the
   objects, such as bimodules, spans, distributors, or parametrized spectra
   (Shulman, “Framed bicategories and monoidal fibrations”, TAC 20 (2008)).
   A bicategory retains only one kind; a double category retains both — the
   strict “tight” maps as the vertical [Category] [dcat], the weak “loose”
   bridges as the horizontal 1-cells [dhor], the two glued by squares
   [dsq].

   The two directions are asymmetric by design. Composing functions is
   strictly associative, whereas composing bimodules by tensor over a ring,
   spans by pullback, or profunctors by a coend is associative only up to
   coherent isomorphism, since each composite is fixed by a universal
   construction. The structure housing both is therefore the PSEUDO double
   category — strict one way, weak the other — the shape of the class
   above: an ordinary [dcat] for the vertical maps against a weakly
   coherent [dhcomp] whose [dassoc], [dunit_left], and [dunit_right] are
   invertible globular squares.

   Charles Ehresmann introduced double categories in 1963, alongside the
   companion memoir “Catégories structurées” (Ann. Sci. École Norm. Sup. 80
   (1963), 349-426) on internal categories: a double category is precisely
   a category internal to Cat, the category of small categories. Marco
   Grandis and Robert Paré founded the modern theory of the pseudo (weak)
   case, from “Limits in double categories” (Cahiers 40 (1999)) on through
   adjoints and Kan extensions; nLab reports their strictification theorem,
   that every pseudo double category is equivalent to a strict one. The
   SCOPE note of the header names this Grandis–Paré lineage.

   Taming coherence is the recurring motivation. Assembling the plain
   bicategory of bimodules or spans forces one to corral the associativity
   and unit coherence of the tensor or pullback, and base change is
   functorial only up to isomorphism, so the bookkeeping multiplies.
   Shulman keeps the strict maps as a separate tight direction and treats
   base change nonalgebraically, through categorical fibrations, so a
   universal property discharges the coherence in place of hand-tracking. A
   double category in which every vertical arrow carries a companion and a
   conjoint is a framed bicategory (Shulman 2008), the recasting of Wood's
   proarrow equipments (“Abstract pro arrows I”, Cahiers 23 (1982));
   Theory/DoubleCategory/Companion.v realizes that machinery here through
   the records [Companion] and [Conjoint].

   The utility spreads across fields. The motivating example is Prof —
   small categories, functors vertical, profunctors horizontal, natural
   transformations as squares — beside bimodules, spans, and distributors
   (nLab; Shulman 2008). Formal category theory takes equipments as the
   correct home for weighted limits, pointwise Kan extensions, and fully
   faithful maps, notions a bare 2-category does not capture correctly, and
   Grandis–Paré develop limits, adjoints, and Kan extensions natively at
   the double-category level. In applied category theory, open systems
   assemble into symmetric monoidal double categories via structured
   cospans (Baez, Courser, “Structured cospans”, TAC 35 (2020)); the
   in-tree cospans double category is [Cospan_Double] of
   Construction/Cospan/Double.v.

   The computational reading is of two kinds. The commuting-squares model
   renders diagram chasing itself as a structure: in the double category
   [Sq] of Construction/Sq.v a square [dsq] h u v k is the proposition
   k ∘ u ≈ v ∘ h, so [Sq] is the ambient home of every naturality or
   commuting diagram and the [dinterchange] law is the pasting discipline
   that makes grid-shaped diagrams composable. The applied reading is
   dataflow and wiring: a structured cospan is an open system, horizontal
   composition plugs outputs into inputs by pushout, and the symmetric
   monoidal structure is parallel composition. Companions and conjoints
   give the two canonical ways to turn a tight map into a loose bridge — in
   [Sq] every morphism is its own companion ([Sq_companion]) while
   conjoints exist exactly for the isomorphisms ([Sq_conjoint_iso]).

--------
双范畴的来源及其用途

nLab: https://ncatlab.org/nlab/show/double+category
nLab: https://ncatlab.org/nlab/show/proarrow+equipment
论文：Ehresmann，“双范畴与结构范畴”，
      C. R. Acad. Sci. Paris 256 (1963), 1198-1201
论文：Grandis, Paré，“双范畴中的极限”，
      Cahiers de Topologie et Géométrie Différentielle Catégoriques 40 (1999)
论文：Shulman，“带框的双范畴与幺半纤维”，Theory and Applications of Categories 20 (2008), No. 18

双范畴是一种二维结构，可以同时保留两种不同类型的1-胞。Shulman指出了这种区分：在某些双范畴中，1-胞是对象之间的态射，例如范畴之间的函子，而在其他的双范畴中，它们是对象之上的对象，例如双模、跨度、分配器或参数化谱 (Shulman, “Framed bicategories and monoidal fibrations”, TAC 20 (2008))。一个双范畴只保留一种类型；而双范畴则保留两者——严格的“紧”映射作为垂直 [Category] [dcat]，弱的“松”桥梁作为水平1-胞 [dhor]，这两者通过方格 [dsq] 连接起来。

这两个方向在设计上是不对称的。函数的组合是严格结合的，而通过环上的张量组合双模、通过拉回组合跨度，或通过共端组合拟函子，只有在相干同构意义下才是结合的，因为每个组合都是由一个普适构造所固定的。因此，容纳两者的结构是PSEUDO双范畴——一方面严格，另一方面弱——上面类的形状：对于垂直映射是普通[dcat]，对于弱相干的[dhcomp]，其[dassoc]、[dunit_left]和[dunit_right]是可逆的球面方格。

查尔斯·埃雷斯曼（Charles Ehresmann）在1963年引入了双范畴，同时发表了关于内部范畴的伴随论文《结构化范畴》（Catégories structurées，Ann. Sci. École Norm. Sup. 80 (1963), 349-426）：双范畴恰恰是Cat（小范畴的范畴）中的内部范畴。Marco Grandis和Robert Paré从《双范畴中的极限》（Limits in double categories，Cahiers 40 (1999)）起，奠定了现代伪（弱）情形的理论，一直延伸到伴随和Kan扩张；nLab报告了他们的严格化定理，即每一个伪双范畴都等价于一个严格的双范畴。标题的SCOPE说明中提到了这一Grandis–Paré的传承。

驯服相干性是反复出现的动机。组装双模或跨度的普通双范畴迫使人们控制张量或抽回的结合性和单位相干性，而基变换仅在同构意义下是函子性的，因此账目处理倍增。Shulman 将严格映射保持为一个单独的紧方向，并通过范畴纤维非代数地处理基变换，因此一个泛性质代替手动追踪释放相干性。一个每条垂直箭头都携带伴随对象和共伴随对象的双范畴是一个框架双范畴（Shulman 2008），是 Wood 的前箭装备（“Abstract pro arrows I”, Cahiers 23 (1982)）的重述；Theory/DoubleCategory/Companion.v 在此通过记录 [Companion] 和 [Conjoint] 实现该机制。

该实用性遍及各个领域。一个典型示例是 Prof — 小范畴，函子为纵向，协函子为横向，自然变换为方块 — 除了双模、跨距和分配器（nLab；Shulman 2008）。形式范畴理论将装备视为加权极限、逐点 Kan 扩展以及全忠实映射的正确归宿，这些概念是单纯的 2 范畴无法正确捕捉的，而 Grandis–Paré 在双范畴层面上本地发展了极限、伴随以及 Kan 扩展。在应用范畴理论中，开放系统通过结构余跨拼装成对称单体双范畴（Baez, Courser, “Structured cospans”, TAC 35 (2020)）；树内余跨双范畴是 Construction/Cospan/Double.v 的 [Cospan_Double]。

计算性解读有两种。交换方格模型将图表追踪本身呈现为一种结构：在 Construction/Sq.v 的双范畴 [Sq] 中，一个方格 [dsq] h u v k 对应命题 k ∘ u ≈ v ∘ h，因此 [Sq] 是每一个自然性或交换图的环境所在，[dinterchange] 法则是使网格形图可组合的粘接规则。应用性解读是数据流和连线：一个结构化余笞是一个开放系统，水平组合通过推出将输出插入输入，对称单体结构是并行组合。伴随和共伴随提供了将紧映射变成松桥的两种规范方式——在 [Sq] 中每个态射都是它自己的伴随 ([Sq_companion])，而共伴随恰好存在于同构上 ([Sq_conjoint_iso])。
*)

Class DoubleCategory : Type := {
  (* Objects together with their STRICT vertical morphisms. / 对象以及它们严格的垂直态射。 *)
  dcat : Category;

  (* Horizontal 1-cells. / 水平 1 单元格。 *)
  dhor : dcat → dcat → Type;

  (*
A square with horizontal top [h], bottom [k], left vertical [u], and
     right vertical [v].

--------
一个正方形，顶部水平 [h]，底部 [k]，左侧垂直 [u]，右侧垂直 [v]。
*)
  dsq {a b c d : dcat} :
    dhor a b → (a ~{dcat}~> c) → (b ~{dcat}~> d) → dhor c d → Type;

  dsq_setoid {a b c d} {h u v k} : Setoid (@dsq a b c d h u v k);

  (*
Boundary coherence: recast a square along [≈]-equal vertical edges.
     (Sq: the square is a proposition, so this is the identity map;
      Cospan: the apex map is unchanged, only its recorded boundary is.)

--------
( - 奕 -适合于 -就此 -日在 提倡 - 所有成员国 -   这只是曝 - 的例子   我保证  一般 未婚  - 有望 的 - 佑  - 与 天呐真高兴 - 的 已经有了  和工作人员便于 ...   - 的 -  即使  -  知道了 -  与   这次 的可以作为 - 
(潇洒:方块是命题还参加了 以下是身份图 快走
科 咱们的顶部图或其记录: 顶部跨国界图没有并作为肇事遵照. )ất.
*)
  dsq_coerce {a b c d} {h} {u u' : a ~{dcat}~> c} {v v' : b ~{dcat}~> d} {k}
    (eu : u ≈ u') (ev : v ≈ v') : dsq h u v k → dsq h u' v' k;

  dsq_coerce_respects {a b c d} {h} {u u' : a ~{dcat}~> c}
    {v v' : b ~{dcat}~> d} {k} (eu : u ≈ u') (ev : v ≈ v') :
    Proper (equiv ==> equiv) (@dsq_coerce a b c d h u u' v v' k eu ev);

  (*
Proof-irrelevance of the boundary: coercing along a loop is the identity
     (Phase 10 [dtransport_id] style, stated with [≈] on squares).

--------
边界的证明无关性：沿循环强制作用是恒等映射（Phase 10 [dtransport_id] 风格，用 [≈] 在方形上陈述）。
*)
  dsq_coerce_id {a b c d} {h} {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k}
    (eu : u ≈ u) (ev : v ≈ v) (s : dsq h u v k) :
    dsq_coerce eu ev s ≈ s;

  (* Coercions compose. / 强制可以组合。 *)
  dsq_coerce_trans {a b c d} {h}
    {u u' u'' : a ~{dcat}~> c} {v v' v'' : b ~{dcat}~> d} {k}
    (eu : u ≈ u') (eu' : u' ≈ u'') (ev : v ≈ v') (ev' : v' ≈ v'')
    (s : dsq h u v k) :
    dsq_coerce eu' ev' (dsq_coerce eu ev s)
      ≈ dsq_coerce (Equivalence_Transitive _ _ _ eu eu')
                   (Equivalence_Transitive _ _ _ ev ev') s;

  (* Vertical identity square on a horizontal 1-cell. / 水平1-胞上的垂直同一方块。 *)
  dsq_vid {a b} (h : dhor a b) : dsq h id id h;

  (* Vertical pasting of squares. / 方形的垂直粘贴。 *)
  dsq_vcomp {a0 b0 a1 b1 a2 b2}
    {h : dhor a0 b0} {u : a0 ~{dcat}~> a1} {v : b0 ~{dcat}~> b1}
    {k : dhor a1 b1} {u' : a1 ~{dcat}~> a2} {v' : b1 ~{dcat}~> b2}
    {l : dhor a2 b2} :
    dsq h u v k → dsq k u' v' l → dsq h (u' ∘ u) (v' ∘ v) l;

  dsq_vcomp_respects {a0 b0 a1 b1 a2 b2}
    {h u v k u' v' l} :
    Proper (equiv ==> equiv ==> equiv)
      (@dsq_vcomp a0 b0 a1 b1 a2 b2 h u v k u' v' l);

  (* STRICT vertical unit laws, through [dsq_coerce] to absorb [id ∘ u] / u. / 严格的垂直单元法律，通过 [dsq_coerce] 吸收 [id ∘ u] / u。 *)
  dsq_vid_left {a b c d} {h : dhor a b}
    {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k} (s : dsq h u v k) :
    dsq_coerce (id_left u) (id_left v) (dsq_vcomp s (dsq_vid k)) ≈ s;

  dsq_vid_right {a b c d} {h : dhor a b}
    {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k} (s : dsq h u v k) :
    dsq_coerce (id_right u) (id_right v) (dsq_vcomp (dsq_vid h) s) ≈ s;

  (* STRICT vertical associativity, through [dsq_coerce]. / 通过 [dsq_coerce] 的严格垂直结合性。 *)
  dsq_vassoc {a0 b0 a1 b1 a2 b2 a3 b3}
    {h : dhor a0 b0} {u : a0 ~{dcat}~> a1} {v : b0 ~{dcat}~> b1}
    {k : dhor a1 b1} {u' : a1 ~{dcat}~> a2} {v' : b1 ~{dcat}~> b2}
    {l : dhor a2 b2} {u'' : a2 ~{dcat}~> a3} {v'' : b2 ~{dcat}~> b3}
    {m : dhor a3 b3}
    (s : dsq h u v k) (t : dsq k u' v' l) (r : dsq l u'' v'' m) :
    dsq_coerce (comp_assoc u'' u' u) (comp_assoc v'' v' v)
      (dsq_vcomp (dsq_vcomp s t) r)
      ≈ dsq_vcomp s (dsq_vcomp t r);

  (* Horizontal identity 1-cell. / 水平恒等 1-胞 *)
  dhid (a : dcat) : dhor a a;

  (* Horizontal composition of 1-cells (outer then inner, like [∘]). / 1-胞的水平组合（先外后内，就像 [∘]）。 *)
  dhcomp {a b c : dcat} : dhor b c → dhor a b → dhor a c;

  (* Horizontal pasting of squares (sharing the middle vertical edge). / 水平粘贴方块（共享中间的垂直边）。 *)
  dsq_hcomp {a b c a' b' c'}
    {h : dhor a b} {h' : dhor b c}
    {u : a ~{dcat}~> a'} {v : b ~{dcat}~> b'} {w : c ~{dcat}~> c'}
    {k : dhor a' b'} {k' : dhor b' c'} :
    dsq h u v k → dsq h' v w k' → dsq (dhcomp h' h) u w (dhcomp k' k);

  dsq_hcomp_respects {a b c a' b' c'} {h h' u v w k k'} :
    Proper (equiv ==> equiv ==> equiv)
      (@dsq_hcomp a b c a' b' c' h h' u v w k k');

  (*
Interchange: pasting a 2x2 grid vertically-then-horizontally agrees with
     horizontally-then-vertically. The two composites carry the SAME boundary
     ([dhcomp h2 h1] on top, [w1 ∘ u1] / [w3 ∘ u3] on the sides, [dhcomp k2 k1]
     below), so no [dsq_coerce] is required.

--------
交换：将一个 2x2 网格先垂直再水平粘贴，与先水平再垂直粘贴是一致的。这两个组合具有相同的边界（顶部为 [dhcomp h2 h1]，侧边为 [w1 ∘ u1] / [w3 ∘ u3]，底部为 [dhcomp k2 k1]），因此不需要 [dsq_coerce]。
*)
  dinterchange {a b c a' b' c' a'' b'' c''}
    {h1 : dhor a b} {h2 : dhor b c}
    {u1 : a ~{dcat}~> a'} {u2 : b ~{dcat}~> b'} {u3 : c ~{dcat}~> c'}
    {j1 : dhor a' b'} {j2 : dhor b' c'}
    {w1 : a' ~{dcat}~> a''} {w2 : b' ~{dcat}~> b''} {w3 : c' ~{dcat}~> c''}
    {k1 : dhor a'' b''} {k2 : dhor b'' c''}
    (s11 : dsq h1 u1 u2 j1) (s12 : dsq h2 u2 u3 j2)
    (s21 : dsq j1 w1 w2 k1) (s22 : dsq j2 w2 w3 k2) :
    dsq_vcomp (dsq_hcomp s11 s12) (dsq_hcomp s21 s22)
      ≈ dsq_hcomp (dsq_vcomp s11 s21) (dsq_vcomp s12 s22);

  (*
Weak associator: an invertible globular square between the two
     bracketings of a horizontal composite (forward square, backward square,
     two round-trip identities normalised through [dsq_coerce]).

--------
弱结合子：在水平复合的两种括号方式之间的可逆球状方块（前向方块，后向方块，通过 [dsq_coerce] 归一化的两个往返恒等式）。
*)
  dassoc {a b c d} (f : dhor a b) (g : dhor b c) (h : dhor c d) :
    { fwd : dsq (dhcomp h (dhcomp g f)) id id (dhcomp (dhcomp h g) f) &
    { bwd : dsq (dhcomp (dhcomp h g) f) id id (dhcomp h (dhcomp g f)) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp h (dhcomp g f)))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid (dhcomp (dhcomp h g) f)) } };

  (* Weak left unitor: [dhid b · h ≅ h] as an invertible globular square. / 弱左单位元：[dhid b · h ≅ h] 作为可逆的球形方形。 *)
  dunit_left {a b} (h : dhor a b) :
    { fwd : dsq (dhcomp (dhid b) h) id id h &
    { bwd : dsq h id id (dhcomp (dhid b) h) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp (dhid b) h))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid h) } };

  (* Weak right unitor: [h · dhid a ≅ h] as an invertible globular square. / 弱右单位元：[h · dhid a ≅ h] 作为可逆的球形方块。 *)
  dunit_right {a b} (h : dhor a b) :
    { fwd : dsq (dhcomp h (dhid a)) id id h &
    { bwd : dsq h id id (dhcomp h (dhid a)) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp h (dhid a)))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid h) } };

  (*
Triangle coherence (square level): whiskering the left unitor equals the
     associator followed by whiskering the right unitor.

--------
三角一致性（平方级别）：对左单位元进行鞭转等于先进行结合子再对右单位元进行鞭转。
*)
  dcoherence_triangle {a b c} (f : dhor a b) (k : dhor b c) :
    dsq_coerce (id_left id) (id_left id)
      (dsq_vcomp (projT1 (dassoc f (dhid b) k))
                 (dsq_hcomp (dsq_vid f) (projT1 (dunit_right k))))
      ≈ dsq_hcomp (projT1 (dunit_left f)) (dsq_vid k);

  (*
Pentagon coherence (square level): the two globular paths from
     [k · (h · (g · f))] to [((k · h) · g) · f] agree, their [id]-boundaries
     normalised through [dsq_coerce].

--------
五边形相干性（平方级）：从 [k · (h · (g · f))] 到 [((k · h) · g) · f] 的两个球状路径一致，它们通过 [dsq_coerce] 标准化的 [id] 边界。
*)
  dcoherence_pentagon {a b c d e}
    (f : dhor a b) (g : dhor b c) (h : dhor c d) (k : dhor d e) :
    dsq_coerce (id_left (id ∘ id)) (id_left (id ∘ id))
      (dsq_vcomp (dsq_vcomp
          (dsq_hcomp (projT1 (dassoc f g h)) (dsq_vid k))
          (projT1 (dassoc f (dhcomp h g) k)))
        (dsq_hcomp (dsq_vid f) (projT1 (dassoc g h k))))
      ≈ dsq_vcomp (projT1 (dassoc (dhcomp g f) h k))
                  (projT1 (dassoc f g (dhcomp k h)))
}.

#[export] Existing Instance dsq_setoid.
#[export] Existing Instance dsq_coerce_respects.
#[export] Existing Instance dsq_vcomp_respects.
#[export] Existing Instance dsq_hcomp_respects.

(** ** Named accessors for the invertible globular squares. / ** 可逆球形方格的命名访问器。 *)

Definition dassoc_to `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d)
  : dsq (dhcomp h (dhcomp g f)) id id (dhcomp (dhcomp h g) f)
  := projT1 (dassoc f g h).

Definition dassoc_from `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d)
  : dsq (dhcomp (dhcomp h g) f) id id (dhcomp h (dhcomp g f))
  := projT1 (projT2 (dassoc f g h)).

Definition dunit_left_to `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq (dhcomp (dhid b) h) id id h
  := projT1 (dunit_left h).

Definition dunit_left_from `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq h id id (dhcomp (dhid b) h)
  := projT1 (projT2 (dunit_left h)).

Definition dunit_right_to `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq (dhcomp h (dhid a)) id id h
  := projT1 (dunit_right h).

Definition dunit_right_from `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq h id id (dhcomp h (dhid a))
  := projT1 (projT2 (dunit_right h)).

(*
The round-trip identities, named after [iso_to_from]/[iso_from_to] of
   Theory/Isomorphism.v: [X_to_from] cancels at the codomain of [X_to] and
   [X_from_to] at its domain (vertical pasting [dsq_vcomp s t] is the
   composite “t after s”).

--------
往返恒等式，以 Theory/Isomorphism.v 中的 [iso_to_from]/[iso_from_to] 命名：[X_to_from] 在 [X_to] 的陪域取消，而 [X_from_to] 在其定义域取消（垂直粘贴 [dsq_vcomp s t] 是合成“t 在 s 之后”）。
*)

Definition dassoc_from_to `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dassoc_to f g h) (dassoc_from f g h))
    ≈ dsq_vid (dhcomp h (dhcomp g f))
  := fst (projT2 (projT2 (dassoc f g h))).

Definition dassoc_to_from `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dassoc_from f g h) (dassoc_to f g h))
    ≈ dsq_vid (dhcomp (dhcomp h g) f)
  := snd (projT2 (projT2 (dassoc f g h))).

Definition dunit_left_from_to `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_left_to h) (dunit_left_from h))
    ≈ dsq_vid (dhcomp (dhid b) h)
  := fst (projT2 (projT2 (dunit_left h))).

Definition dunit_left_to_from `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_left_from h) (dunit_left_to h))
    ≈ dsq_vid h
  := snd (projT2 (projT2 (dunit_left h))).

Definition dunit_right_from_to `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_right_to h) (dunit_right_from h))
    ≈ dsq_vid (dhcomp h (dhid a))
  := fst (projT2 (projT2 (dunit_right h))).

Definition dunit_right_to_from `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_right_from h) (dunit_right_to h))
    ≈ dsq_vid h
  := snd (projT2 (projT2 (dunit_right h))).

(**
** The derived coercion lemma pack

    Mirrors the [dtransport] pack of Theory/Displayed.v: consumers of the
    class spend their time reorienting and cancelling boundary coercions,
    and each step is one of the lemmas below.

--------
** 派生强制引理包

    反映了 Theory/Displayed.v 中的 [dtransport] 包：该类的使用者花时间重定向和取消边界强制，每一步都是下面引理之一。
*)

Section DoubleCategoryLemmas.

Context {D : DoubleCategory}.

(* Coercing there and back again cancels (left orientation). / 强制来回取消（左向）。 *)
Lemma dsq_coerce_symm_l {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (s : dsq h u v k) :
  dsq_coerce (symmetry eu) (symmetry ev) (dsq_coerce eu ev s) ≈ s.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(* Coercing back and there again cancels (right orientation). / 反复强制取消（正确方向）。 *)
Lemma dsq_coerce_symm_r {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (t : dsq h u' v' k) :
  dsq_coerce eu ev (dsq_coerce (symmetry eu) (symmetry ev) t) ≈ t.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(*
Reorienting a coercion equation: a coercion may be moved to the other
   side of [≈] by inverting the proofs it rides on.

--------
重新定位强制方程：通过反转其依托的证明，强制可以被移到 [≈] 的另一侧。
*)
Lemma dsq_coerce_flip {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (s : dsq h u v k) (t : dsq h u' v' k) :
  dsq_coerce eu ev s ≈ t ↔ s ≈ dsq_coerce (symmetry eu) (symmetry ev) t.
Proof.
  split; intros H.
  - rewrite <- H.
    symmetry; apply dsq_coerce_symm_l.
  - rewrite H.
    apply dsq_coerce_symm_r.
Qed.

(*
Coercion does not depend on the proofs coerced along: the groupoid laws
   [dsq_coerce_id]/[dsq_coerce_trans] force any two parallel proof pairs to
   coerce identically.

--------
强制并不依赖于被强制的证明：群范畴定律 [dsq_coerce_id]/[dsq_coerce_trans] 强制任何两个平行的证明对以相同方式强制。
*)
Lemma dsq_coerce_proof_irrel {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu eu' : u ≈ u') (ev ev' : v ≈ v') (s : dsq h u v k) :
  dsq_coerce eu ev s ≈ dsq_coerce eu' ev' s.
Proof.
  apply (snd (dsq_coerce_flip eu ev s (dsq_coerce eu' ev' s))).
  symmetry; rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(*
[dsq_coerce_trans] with the composite proofs replaced by any proofs of
   the endpoints' relations.

--------
[dsq_coerce_trans]，复合证明被替换为任何端点关系的证明。
*)
Lemma dsq_coerce_trans_any {a b c d : dcat} {h : dhor a b}
  {u u' u'' : a ~> c} {v v' v'' : b ~> d} {k : dhor c d}
  (eu1 : u ≈ u') (eu2 : u' ≈ u'') (eu3 : u ≈ u'')
  (ev1 : v ≈ v') (ev2 : v' ≈ v'') (ev3 : v ≈ v'')
  (s : dsq h u v k) :
  dsq_coerce eu2 ev2 (dsq_coerce eu1 ev1 s) ≈ dsq_coerce eu3 ev3 s.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_proof_irrel.
Qed.

(*
The strict vertical laws along any proofs of the base laws: exactly the
   shape of the unit/associativity obligations of categories built from
   squares.

--------
沿着任何基础定律的证明的严格垂直定律：恰好是由方形构建的范畴的单位/结合性义务的形状。
*)
Lemma dsq_vid_left_any {a b c d : dcat} {h : dhor a b}
  {u : a ~> c} {v : b ~> d} {k : dhor c d}
  (eu : id ∘ u ≈ u) (ev : id ∘ v ≈ v) (s : dsq h u v k) :
  dsq_coerce eu ev (dsq_vcomp s (dsq_vid k)) ≈ s.
Proof.
  transitivity
    (dsq_coerce (id_left u) (id_left v) (dsq_vcomp s (dsq_vid k))).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vid_left.
Qed.

Lemma dsq_vid_right_any {a b c d : dcat} {h : dhor a b}
  {u : a ~> c} {v : b ~> d} {k : dhor c d}
  (eu : u ∘ id ≈ u) (ev : v ∘ id ≈ v) (s : dsq h u v k) :
  dsq_coerce eu ev (dsq_vcomp (dsq_vid h) s) ≈ s.
Proof.
  transitivity
    (dsq_coerce (id_right u) (id_right v) (dsq_vcomp (dsq_vid h) s)).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vid_right.
Qed.

Lemma dsq_vassoc_any {a0 b0 a1 b1 a2 b2 a3 b3 : dcat}
  {h : dhor a0 b0} {u : a0 ~> a1} {v : b0 ~> b1}
  {k : dhor a1 b1} {u' : a1 ~> a2} {v' : b1 ~> b2}
  {l : dhor a2 b2} {u'' : a2 ~> a3} {v'' : b2 ~> b3}
  {m : dhor a3 b3}
  (eu : u'' ∘ (u' ∘ u) ≈ (u'' ∘ u') ∘ u)
  (ev : v'' ∘ (v' ∘ v) ≈ (v'' ∘ v') ∘ v)
  (s : dsq h u v k) (t : dsq k u' v' l) (r : dsq l u'' v'' m) :
  dsq_coerce eu ev (dsq_vcomp (dsq_vcomp s t) r)
    ≈ dsq_vcomp s (dsq_vcomp t r).
Proof.
  transitivity
    (dsq_coerce (comp_assoc u'' u' u) (comp_assoc v'' v' v)
                (dsq_vcomp (dsq_vcomp s t) r)).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vassoc.
Qed.

End DoubleCategoryLemmas.
