Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Instance.Top.FundamentalGroupoid.
Require Import Category.Instance.Top.Presheaf.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.

Generalizable All Variables.

(*
 Lib.v sets [Default Proof Using “Type”], which keeps only the Section
 variables occurring in a lemma's STATEMENT.  Several proofs below consume
 Section hypotheses that their statements do not mention -- the
 multiplication's continuity certificate above all -- and the narrower
 setting would discard them.  This is the same declaration
 Instance/Top/Interval.v, Instance/Top/FundamentalGroupoid.v and
 Instance/Top/Homotopy.v make, for the same reason. 

 --------
 Lib.v 设置了 [Default Proof Using “Type”]，它只保留引理陈述中出现的 Section 变量。下文的几个证明会使用它们陈述中未提到的 Section 假设——尤其是上面的乘法连续性证明——而较狭窄的设置会舍弃它们。这与 Instance/Top/Interval.v、Instance/Top/FundamentalGroupoid.v 和 Instance/Top/Homotopy.v 所做的声明是相同的，原因相同。
*)
Set Default Proof Using "All".

(* * * Loops in a topological group, and the abelian fundamental group / * * 拓扑群中的环路，以及阿贝尔基本群 *)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §II.5 Exercises 4 and 6 (printed p. 45)
 Paper:     Eckmann, Hilton, “Group-like structures in general categories
 I. Multiplications and comultiplications”, Mathematische
 Annalen 145, 1962
 Paper:     Eckmann, Hilton, “Structure maps in group theory”, Fundamenta
 Mathematicae 50, 1961 (Theorem 1.12)
 nLab:      https://ncatlab.org/nlab/show/topological+group
 nLab:      https://ncatlab.org/nlab/show/loop+space
 nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
 Wikipedia: https://en.wikipedia.org/wiki/Topological_group

 Mac Lane's Exercise 4 asks for the interchange law between the two
 operations that loops at the unit of a topological group carry, and
 Exercise 6 asks for the consequence: the fundamental group of a
 topological group is abelian.  Both are proved here, over the two donor
 developments the tree already has -- Instance/Top/FundamentalGroupoid.v
 for paths, homotopy rel endpoints and π(X), and Theory/EckmannHilton.v
 for the abstract argument.

 The two operations.  A loop at the unit e is a path α : [0,1] → G with
 α(0) = α(1) = e.  Two such loops can be composed in two unrelated ways:

 - CONCATENATION, [path_concat] -- run α on the first half of the
 interval and β on the second.  This is the operation of the
 fundamental groupoid (Instance/Top/FundamentalGroupoid.v), and
 its unit up to homotopy is the constant loop.

 - POINTWISE MULTIPLICATION, [loop_mult] below -- multiply the two
 values in the group at each instant, (α · β)(t) = α(t) · β(t).  This
 operation exists only because the ambient space is a group (or, as
 below, only an H-space); it has the constant loop at the unit as a
 STRICT unit, no homotopy needed.

 Exercise 4 is that they INTERCHANGE:

 (α ∗ β) · (γ ∗ δ)  ≈  (α · γ) ∗ (β · δ),

 and the proof is a computation, not a homotopy: at a parameter t ≤ 1/2
 both sides evaluate to α(2t) · γ(2t), and at t ≥ 1/2 both evaluate to
 β(2t−1) · δ(2t−1), because the pointwise product commutes with the split
 at 1/2 that concatenation performs.  The two maps are therefore EQUAL AT
 EVERY POINT, and [pointwise_homotopic]
 (Instance/Top/FundamentalGroupoid.v) upgrades that to a homotopy rel
 endpoints with no surgery of squares anywhere.  This is [loop_interchange]
 below.

 Exercise 6 is then Eckmann and Hilton's: two unital operations that
 interchange coincide, and the one operation that remains is commutative
 and associative.  Theory/EckmannHilton.v proves that over a bare setoid;
 this file instantiates it at the hom-setoid of loops, whose `≈` IS
 homotopy rel endpoints ([Path_Setoid]).  The conclusion transported back
 to π₁ is [pi1_topgroup_abelian].

 THE ORIENTATION, worked out and pinned.  Theory/EckmannHilton.v takes its
 interchange law in the shape

 f (g a b) (g c d)  ≈  g (f a c) (f b d),

 so f is applied LAST on the left and FIRST on the right.  Matching
 against the displayed law above forces

 f := pointwise multiplication      g := concatenation.

 The swapped assignment is NOT false -- the interchange law is self-dual
 under swapping f and g together with a transposition of its middle two
 arguments, so the swapped law is [loop_interchange] with b and c
 exchanged, and instantiating the abstract theorem the other way round
 would deliver the same conclusions with the f- and g-sides exchanged.
 The matching above is forced only in the weak sense that it reads
 Exercise 4's displayed law variable-for-variable; under it the theorem's
 f-side conclusions ([eh_comm], [eh_assoc]) are about POINTWISE
 MULTIPLICATION, and the statement a reader wants about π₁ -- which is a
 group under CONCATENATION -- comes out as the g-side corollary
 [eh_g_comm].  Both are recorded below ([loop_mult_comm] and
 [loop_concat_comm]).

 WHAT THE HYPOTHESES ACTUALLY ARE, and why the record is not [TopGroup].
 Reading the argument off, the multiplication is used exactly three times:
 it must respect `≈`, it must be jointly continuous (so that the pointwise
 product of two paths is again a path, and the pointwise product of two
 homotopies again a homotopy), and it must have a STRICT two-sided unit at
 the base point (so that the pointwise product of two loops at e is again
 a loop at e, and so that the constant loop is a strict unit for it).
 Neither associativity nor inverses are used anywhere.  The record below,
 [HTopMonoid], carries exactly those three requirements and nothing else;
 it is the classical sharpening of the exercise -- the fundamental group
 of an H-SPACE with a strict unit is abelian -- and it is what
 [pi1_topgroup_abelian] is stated over.  [TopGroup] then extends it with
 an inverse, its two laws and its continuity, so that Mac Lane's named
 object exists in the tree; [pi1_TopGroup_abelian] is his literal
 statement and is one line.  DISCLOSURE: nothing on the path to the
 theorem consumes the inverse, either of its laws, or its continuity.
 [tg_inv_cont] has exactly one consumer, [tg_inv_nbhd], which restates it
 and is itself consumed by nothing; [tg_inv_left] and [tg_inv_right] have
 no consumer at all.  They are carried because the exercise names a group,
 not because the theorem needs one.

 A COMPANION NON-CLAIM, since the two operations are visibly different
 constructions (one splits the interval at 1/2, the other does not):
 [loop_mult_concat_agree] says they agree UP TO HOMOTOPY, which is
 Eckmann and Hilton's [eh_ops] and is a conclusion, not an assumption.  It
 does not say the two maps are pointwise equal, and no witness here
 separates them pointwise -- separating them would be a statement about
 chosen representatives rather than about π₁, which is why none is built.

 WHY THE CONTINUITY OF THE MULTIPLICATION IS A CERTIFICATE.  Instance/Top.v
 builds no products, so there is no space G × G whose opens could be
 quantified over and no arrow G × G ⟶ G to be called continuous.  Joint
 continuity is therefore carried in the two-open form directly -- for every
 open V containing m(x, y), opens U ∋ x and W ∋ y with m(U × W) ⊆ V --
 which is the same accommodation Instance/Top/Homotopy.v makes for the
 cylinder (its [htpy_cont] field states the rectangle condition
 pointwise for exactly this reason).  The inverse is not affected: with
 one variable the ordinary preimage form is available, and [tg_inv_cont]
 below is the unfolded form of [Continuous G G] for the inversion map
 (the constant itself expects a bundled [SetoidMorphism], which [tg_inv]
 deliberately is not).  [tg_inv_nbhd] restates it in the pointwise form
 for symmetry with the multiplication.

 WHAT IS DEFERRED, disclosed.  (1) No space in this tree has a nontrivial
 fundamental group -- Instance/Top/FundamentalGroupoid.v says so in its own
 header, and both of its witnesses have trivial vertex groups at every base
 point -- so the witness below, the additive reals, exercises the
 HYPOTHESES and the derivation, not the strength of the conclusion.  π₁(ℝ)
 is trivial, hence abelian for a reason that has nothing to do with this
 theorem.  The circle, whose π₁ is ℤ and whose case would be the honest
 test, needs covering-space theory.  (2) [open_of_nbhds] below is a fact
 about every topological space and belongs in Instance/Top.v; it is proved
 here rather than upstream to keep this file's change surface to one new
 file, and it is an upstreaming candidate.  (3) The loop space Ω(G, e) is
 not built as a SPACE (that needs the compact-open topology, hence
 function spaces, which Instance/Top.v does not have); what is built is
 the two operations on its points, which is all the exercises ask for. 

 --------
 书籍：      Mac Lane, 《Categories for the Working Mathematician》，第2版，§II.5 练习题4和6（第45页印刷）
 论文：      Eckmann, Hilton, 《一般范畴中的类群结构 I. 乘法和余乘法》，数学年刊 145, 1962
 论文：      Eckmann, Hilton, 《群论中的结构映射》，基础数学 50, 1961（定理1.12）
 nLab：       https://ncatlab.org/nlab/show/topological+group
 nLab：       https://ncatlab.org/nlab/show/loop+space
 nLab：       https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
 维基百科：  https://en.wikipedia.org/wiki/Topological_groupMac Lane的练习4要求给出拓扑群单位元的环上的两个运算之间的交换律，练习6要求说明其结果：拓扑群的基本群是阿贝尔群。这里都进行了证明，基于该树已经具有的两个基础发展——用于路径、端点固定的同伦及π(X)的 Instance/Top/FundamentalGroupoid.v，以及用于抽象论证的 Theory/EckmannHilton.v。

 这两个运算。单位元e处的一个环是路径 α : [0,1] → G 且 α(0) = α(1) = e。这样的两个环可以通过两种无关的方式组合：- 连接，[path_concat] —— 在区间的前半部分运行 α，在后半部分运行 β。这是基本群oid 的操作（Instance/Top/FundamentalGroupoid.v），其到同伦的单位是常数环路。

 - 点乘，[loop_mult] —— 在每个时刻在群中将两个值相乘，(α · β)(t) = α(t) · β(t)。这个操作存在仅因为环境空间是一个群（或如下所述，只有 H 空间）；它以单位处的常数环路作为严格单位，不需要同伦。

 练习 4 是它们交换：

 (α ∗ β) · (γ ∗ δ)  ≈  (α · γ) ∗ (β · δ),证明是一个计算，而不是同伦：在参数 t ≤ 1/2 时，两边的值都为 α(2t) · γ(2t)，在 t ≥ 1/2 时，两边的值都为 β(2t−1) · δ(2t−1)，因为逐点乘积与拼接在 1/2 处的拆分是可交换的。因此，这两个映射在每一点上都是相等的，而 [pointwise_homotopic] (Instance/Top/FundamentalGroupoid.v) 将其提升为一个相对端点的同伦，并且不在任何地方进行平方操作。下面是 [loop_interchange]。练习6然后是Eckmann和Hilton的问题：两个单位运算互换后相同，而留下的唯一运算是交换的并且满足结合律。Theory/EckmannHilton.v 在一个裸集合上证明了这一点；该文件将其实例化在回路的同合集（hom-setoid）上，其`≈` 是相对端点同伦（[Path_Setoid]）。将结论传回到 π₁ 后得到 [pi1_topgroup_abelian]。

 方向性，已经推导并固定。Theory/EckmannHilton.v 在形式上采用其交换律为

 f (g a b) (g c d)  ≈  g (f a c) (f b d),

 所以 f 在左边最后应用，在右边首先应用。与上面显示的规律匹配强制规定

 f := 点对点乘法      g := 拼接。交换后的赋值不是错误的——交换律在交换 f 和 g 的同时并交换其中间的两个参数时是自对偶的，所以交换后的律是 [loop_interchange]，其中 b 和 c 互换，并且以另一种方式实例化抽象定理会得到同样的结论，只不过 f 和 g 的两边交换。上述匹配仅在弱意义上是强制的，即它逐变量读取练习 4 中展示的定律；在此条件下，定理的 f 边结论（[eh_comm]，[eh_assoc]）关于逐点乘法，并且读者想要关于 π₁ 的结论——它在连接下是一个群——作为 g 边的推论 [eh_g_comm] 出现。两者都在下方记录（[loop_mult_comm] 和 [loop_concat_comm]）。假设实际上是什么，以及为什么记录不是 [TopGroup]。根据论证，乘法恰好使用了三次：
 它必须遵循 `≈`，它必须联合连续（以便两个路径的逐点积仍然是路径，两个同伦的逐点积仍然是同伦），并且它在基点处必须有一个严格的双侧单位（以便两个在 e 处的环的逐点积仍然是 e 处的环，并且恒定环是其严格单位）。无论是结合性还是逆元在任何地方都未被使用。下面的记录 [HTopMonoid] 刚好包含这三个要求而无其他内容；
 它是练习题的经典精炼——具有严格单位的 H-空间的基本群是阿贝尔群——并且它是 [pi1_topgroup_abelian] 所陈述的内容。[TopGroup] 然后用一个逆元、它的两个定律及其连续性来扩展它，以便 Mac Lane 命名的对象存在于该树中；[pi1_TopGroup_abelian] 是他的字面陈述，仅一行。披露：通向该定理的路径上没有任何东西消耗逆元、它的任何定律或它的连续性。[tg_inv_cont] 恰好有一个使用者，即 [tg_inv_nbhd]，它重述了它，并且自身不被任何东西使用；[tg_inv_left] 和 [tg_inv_right] 根本没有使用者。它们被保留是因为该练习命名了一个群，而不是因为定理需要一个群。一个伴随的非断言，由于这两个操作在构造上明显不同（一个将在 1/2 分开区间，另一个则不分开）：[loop_mult_concat_agree] 说它们在同伦意义上是一致的，这就是 Eckmann 和 Hilton 的 [eh_ops]，并且这是一个结论，而不是假设。它并没有说两个映射在每一点上都相等，并且这里没有证据能够逐点区分它们——逐点区分将是关于选定代表的陈述，而不是关于 π₁ 的陈述，这也是为什么没有构建任何证据的原因。为什么乘法的连续性是一种证明。Instance/Top.v 并不构建乘积，所以不存在可以进行量化的空间 G × G，也不存在可以被称为连续的箭头 G × G ⟶ G。因此，联合连续性直接体现在双开集合形式中——对于包含 m(x, y) 的每一个开集 V，都存在开集 U 包含 x 和 W 包含 y，使得 m(U × W) ⊆ V——这与 Instance/Top/Homotopy.v 对圆柱体的处理方式相同（其 [htpy_cont] 字段出于正好这个原因而逐点地陈述了矩形条件）。逆映射不受影响：在单变量的情况下，普通的原像形式是可用的，而下面的 [tg_inv_cont] 是 [Continuous G G] 对逆映射展开形式（该常量本身期望一个打包的 [SetoidMorphism]，而 [tg_inv] 故意没有提供）。[tg_inv_nbhd] 用逐点形式重新陈述它，以与乘法保持对称。什么是延迟的，已经披露。（1）这个树中的任何空间都没有非平凡的基本群——Instance/Top/FundamentalGroupoid.v 在它自己的头部中说明了这一点，而且它的两个证据在每个基点处的顶点群都是平凡的——所以下面的证据，加法实数，体现了假设和推导，而不是结论的强度。π₁(ℝ) 是平凡的，因此是阿贝尔群，这个原因与本定理无关。圆，其 π₁ 为 ℤ，其情况将是诚实的测试，需要覆盖空间理论。（2）下面的 [open_of_nbhds] 是关于每个拓扑空间的事实，应放在 Instance/Top.v；它在这里被证明而不是在上游，以保持此文件的改动范围在一个新文件内，并且它是一个上游候选项。(3) 循环空间 Ω(G, e) 并不是作为一个空间构建的（那需要紧-开拓扑，因此需要函数空间，而 Instance/Top.v 并不具备）；构建的是其点上的两个运算，这正是所有练习要求的内容。
*)

(* * ** Topological monoids and topological groups / * ** 拓扑幺半群与拓扑群 *)

(* An H-space with a strict unit, in the exact strength the exercises consume. [htm_mult_cont] is joint continuity in the two-open form forced by the absence of products (header). / 具有严格单位的 H 空间，在练习消耗的精确强度下。[htm_mult_cont] 是在两开放形式下的联合连续性，由产品（标题）的缺失强制。 *)
Record HTopMonoid := {
  htm_space :> TopSpace;

  htm_unit : htm_space;
  htm_mult : htm_space → htm_space → htm_space;

  htm_mult_proper : Proper (equiv ==> equiv ==> equiv) htm_mult;

  htm_unit_left : ∀ x : htm_space, htm_mult htm_unit x ≈ x;
  htm_unit_right : ∀ x : htm_space, htm_mult x htm_unit ≈ x;

  htm_mult_cont : ∀ V : htm_space → Type, IsOpen htm_space V →
    ∀ x y : htm_space, V (htm_mult x y) →
      { U : htm_space → Type &
        ((IsOpen htm_space U) ∧ (U x) ∧
         { W : htm_space → Type &
           ((IsOpen htm_space W) ∧ (W y) ∧
            (∀ x' y' : htm_space,
               U x' → W y' → V (htm_mult x' y')))%type })%type }
}.

(*
 Mac Lane's named object: a group in [Top].  The inverse's continuity is
 stated in the ordinary preimage form, which for a map of one variable is
 available and is literally [Continuous]. 

 --------
 Mac Lane 命名的对象：[Top] 中的一个群。逆映射的连续性以普通原像形式陈述，对于单变量的映射是可用的，并且字面上是 [Continuous]。
*)
Record TopGroup := {
  tg_monoid :> HTopMonoid;

  tg_inv : tg_monoid → tg_monoid;

  tg_inv_proper : Proper (equiv ==> equiv) tg_inv;

  tg_inv_left : ∀ x : tg_monoid,
    htm_mult tg_monoid (tg_inv x) x ≈ htm_unit tg_monoid;
  tg_inv_right : ∀ x : tg_monoid,
    htm_mult tg_monoid x (tg_inv x) ≈ htm_unit tg_monoid;

  tg_inv_cont : ∀ V : tg_monoid → Type,
    IsOpen (htm_space tg_monoid) V →
    IsOpen (htm_space tg_monoid) (fun x => V (tg_inv x))
}.

(*
 The pointwise reading of the inverse's continuity, for symmetry with the
 multiplication's certificate.  Nothing below consumes it; it is here so
 that the two continuity conditions can be compared in one shape. 

 --------
 逆运算连续性的逐点读取，为了与乘法的证明保持对称。下面没有任何东西会使用它；它存在的目的是为了让两个连续性条件可以在同一个形式下进行比较。
*)
Lemma tg_inv_nbhd (G : TopGroup) (V : G → Type)
      (HV : IsOpen (htm_space (tg_monoid G)) V) (x : G) (Hx : V (tg_inv G x)) :
  { U : G → Type &
    ((IsOpen (htm_space (tg_monoid G)) U) ∧ (U x) ∧
     (∀ y : G, U y → V (tg_inv G y)))%type }.
Proof.
  exists (fun z => V (tg_inv G z)).
  split; [ | split ].
  - exact (tg_inv_cont G V HV).
  - exact Hx.
  - intros y Hy; exact Hy.
Qed.

(* * ** A predicate with an open neighbourhood at each of its points is open / * ** 在其每个点都有一个邻域的谓词是开放的 *)

(*
 The union of the neighbourhoods, indexed by the points at which the
 predicate holds.  Radius-free and choice-free: the neighbourhood is DATA,
 supplied by the hypothesis, exactly as the radius is data in
 Instance/Top/Interval.v's [ball_open].  This is a fact about every
 [TopSpace] and is an upstreaming candidate for Instance/Top.v (header,
 deferral 2). 

 --------
 邻域的并集，由谓词成立的点索引。无半径且无选择：邻域是由假设提供的数据，就像在 Instance/Top/Interval.v 的 [ball_open] 中半径是数据一样。这是关于每个 [TopSpace] 的事实，并且是 Instance/Top.v（头文件，延期 2）的上游候选项。
*)
Lemma open_of_nbhds (X : TopSpace) (P : X → Type)
      (H : ∀ x : X, P x →
             { U : X → Type &
               ((IsOpen X U) ∧ (U x) ∧ (∀ y : X, U y → P y))%type }) :
  IsOpen X P.
Proof.
  apply (open_respects X
           (fun x => { w : { z : X & P z } &
                       projT1 (H (projT1 w) (projT2 w)) x })
           P).
  - intro x; split.
    + intros [w Hw].
      exact (snd (snd (projT2 (H (projT1 w) (projT2 w)))) x Hw).
    + intro Px.
      exact ((x; Px); fst (snd (projT2 (H x Px)))).
  - apply open_union.
    intro w.
    exact (fst (projT2 (H (projT1 w) (projT2 w)))).
Qed.

(* * ** The pointwise product of two arrows into a topological monoid / * ** 两个箭头到拓扑幺半群的逐点乘积 *)

(*
 Developed once for an ARBITRARY domain, because it is needed twice: at the
 interval, where it multiplies two paths, and at the square, where it
 multiplies two homotopies.  Nothing in the construction mentions either
 domain. 

 --------
 最初为一个任意的领域开发，因为它需要出现两次：在区间中，它会将两条路径相乘；在平方中，它会将两个同伦相乘。构造中没有提到任何特定的领域。
*)
Section PointwiseProduct.

Context (G : HTopMonoid).
Context {D : TopSpace}.
Context (p q : D ~{Top}~> G).

Definition mult_fun (z : D) : G := htm_mult G (p z) (q z).

Lemma mult_fun_proper : Proper (equiv ==> equiv) mult_fun.
Proof.
  intros z w Hzw.
  apply (htm_mult_proper G); apply proper_morphism; exact Hzw.
Qed.

Definition mult_setoid_map : SetoidMorphism (top_carrier D) (top_carrier G) := {|
  morphism        := mult_fun;
  proper_morphism := mult_fun_proper
|}.

(*
 Continuity.  Given an open V containing the product at z, the certificate
 supplies opens U ∋ p z and W ∋ q z whose product lands in V; the two
 preimages are open by continuity of p and of q, and their intersection is
 the neighbourhood of z that [open_of_nbhds] asks for.  No metric, no
 radius, no reals: the argument is the abstract one. 

 --------
 连续性。给定包含点 z 处乘积的开集 V，该证书提供了包含 p(z) 的开集 U 和包含 q(z) 的开集 W，使得它们的乘积落在 V 中；由于 p 和 q 的连续性，这两个原像是开集，并且它们的交集就是 [open_of_nbhds] 所要求的 z 的邻域。没有度量、没有半径、没有实数：这个论证是抽象的论证。
*)
Lemma mult_open (V : G → Type) (HV : IsOpen (htm_space G) V) :
  IsOpen D (fun z => V (mult_fun z)).
Proof.
  apply open_of_nbhds.
  intros z Hz.
  destruct (htm_mult_cont G V HV (p z) (q z) Hz)
    as [U [HU [Uz [W [HW [Wz Hprod]]]]]].
  exists (fun w : D => U (p w) ∧ W (q w)).
  split; [ | split ].
  - apply open_inter.
    + exact (continuity p U HU).
    + exact (continuity q W HW).
  - split; [ exact Uz | exact Wz ].
  - intros w Hw; exact (Hprod (p w) (q w) (fst Hw) (snd Hw)).
Qed.

Definition mult_arrow : D ~{Top}~> G := {|
  continuous_map := mult_setoid_map;
  continuity     := mult_open
|}.

(* The defining equation, by [reflexivity]: the arrow's value IS the product of the two values. / 由 [reflexivity] 给出的定义方程：箭头的值就是两个值的乘积。 *)
Lemma mult_arrow_eval (z : D) : mult_arrow z ≈ htm_mult G (p z) (q z).
Proof. reflexivity. Qed.

End PointwiseProduct.

Arguments mult_fun G {D} p q z.
Arguments mult_arrow G {D} p q.

(* * ** Pointwise multiplication of loops / * ** 循环的逐点乘法 *)

Section Loops.

Context (G : HTopMonoid).

(* Both endpoint conditions come from the same computation: the value at an endpoint is the product of the two endpoint values, which are both the unit, and the unit is strict. / 两个端点条件都来自同一个计算：端点的值是两个端点值的乘积，这两个端点值都是单位，且单位是严格的。 *)
Lemma loop_mult_src (p q : Path G (htm_unit G) (htm_unit G)) :
  mult_arrow G (path_map p) (path_map q) I_zero ≈ htm_unit G.
Proof.
  transitivity (htm_mult G (htm_unit G) (htm_unit G)).
  - apply (htm_mult_proper G); [ exact (path_src p) | exact (path_src q) ].
  - exact (htm_unit_left G (htm_unit G)).
Qed.

Lemma loop_mult_tgt (p q : Path G (htm_unit G) (htm_unit G)) :
  mult_arrow G (path_map p) (path_map q) I_one ≈ htm_unit G.
Proof.
  transitivity (htm_mult G (htm_unit G) (htm_unit G)).
  - apply (htm_mult_proper G); [ exact (path_tgt p) | exact (path_tgt q) ].
  - exact (htm_unit_left G (htm_unit G)).
Qed.

(* The pointwise product of two loops at the unit, as a loop at the unit. / 两个单位处环的逐点乘积，作为单位处的一个环。 *)
Definition loop_mult (p q : Path G (htm_unit G) (htm_unit G)) :
  Path G (htm_unit G) (htm_unit G) := {|
  path_map := mult_arrow G (path_map p) (path_map q);
  path_src := loop_mult_src p q;
  path_tgt := loop_mult_tgt p q
|}.

Lemma loop_mult_eval (p q : Path G (htm_unit G) (htm_unit G)) (t : Ipt) :
  path_map (loop_mult p q) t ≈ htm_mult G (path_map p t) (path_map q t).
Proof. reflexivity. Qed.

(* * ** Pointwise multiplication respects homotopy / * **点乘符合同伦 *)

(*
 The square is the pointwise product of the two squares, which is
 [mult_arrow] again -- at the square rather than at the interval.  Its four
 edges are the products of the corresponding edges: the bottom and top by
 respectfulness, the two sides because the product of the unit with itself
 is the unit. 

 --------
 该方形是两个方形的逐点乘积，即 [mult_arrow] —— 仍是在方形上而不是在区间上。它的四条边是对应边的乘积：底边和顶边由于相应性，两侧边因为单位与自身的乘积是单位。
*)
Definition loop_mult_respects
           {p p' q q' : Path G (htm_unit G) (htm_unit G)}
           (H1 : PathHomotopy p p') (H2 : PathHomotopy q q') :
  PathHomotopy (loop_mult p q) (loop_mult p' q').
Proof.
  unfold PathHomotopy.
  refine {| ah_map := mult_arrow G (ah_map H1) (ah_map H2) |}.
  - intro t.
    apply (htm_mult_proper G); [ exact (ah_bot H1 t) | exact (ah_bot H2 t) ].
  - intro t.
    apply (htm_mult_proper G); [ exact (ah_top H1 t) | exact (ah_top H2 t) ].
  - intro s.
    transitivity (htm_mult G (htm_unit G) (htm_unit G)).
    + apply (htm_mult_proper G); [ exact (ah_left H1 s) | exact (ah_left H2 s) ].
    + exact (htm_unit_left G (htm_unit G)).
  - intro s.
    transitivity (htm_mult G (htm_unit G) (htm_unit G)).
    + apply (htm_mult_proper G);
        [ exact (ah_right H1 s) | exact (ah_right H2 s) ].
    + exact (htm_unit_left G (htm_unit G)).
Defined.

(* * ** The constant loop is a STRICT unit for pointwise multiplication / * ** 恒定循环是逐点乘法的严格单元 *)

(* Strict at the level of points; the homotopy is then [pointwise_homotopic] and nothing is deformed. / 在点的层面上严格；同伦随后是 [pointwise_homotopic]，且没有任何变形。 *)
Definition loop_mult_unit_left (p : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (const_path (htm_unit G)) p) p.
Proof.
  apply pointwise_homotopic.
  intro t.
  exact (htm_unit_left G (path_map p t)).
Defined.

Definition loop_mult_unit_right (p : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p (const_path (htm_unit G))) p.
Proof.
  apply pointwise_homotopic.
  intro t.
  exact (htm_unit_right G (path_map p t)).
Defined.

(* * ** Mac Lane §II.5 Exercise 4: the interchange law / * ** 马克·莱恩 §II.5 练习 4：交换律 *)

(*
 Both sides split the interval at 1/2 in the same place and agree on each
 half, so they agree at every point.  On the first half both reduce to
 a(2t) · c(2t), on the second to b(2t−1) · d(2t−1). 

 --------
 双方在相同的地方将区间在1/2处分开，并对每一半达成一致，所以他们在每一点上都达成了一致。在前半部分，两者都化简为 a(2t) · c(2t)，在后半部分化简为 b(2t−1) · d(2t−1)。
*)
Theorem loop_interchange (a b c d : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (path_concat a b) (path_concat c d))
               (path_concat (loop_mult a c) (loop_mult b d)).
Proof.
  apply pointwise_homotopic.
  intro t.
  destruct (Rle_dec (ival t) (1/2)) as [Hle | Hnle].
  - transitivity (path_map (loop_mult a c) (I_dbl t)).
    + apply (htm_mult_proper G).
      * apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
      * apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
    + symmetry.
      apply concat_first; [ exact Hle | rewrite I_dbl_eval; Rlin ].
  - apply Rnot_le_lt in Hnle.
    transitivity (path_map (loop_mult b d) (I_dbl' t)).
    + apply (htm_mult_proper G).
      * apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
      * apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
    + symmetry.
      apply concat_second; [ lra | rewrite I_dbl'_eval; Rlin ].
Qed.

(* * ** Mac Lane §II.5 Exercise 6: Eckmann–Hilton at the loops / * ** 马克·莱恩 §II.5 练习 6：环路上的埃克曼–希尔顿 *)

(*
 The seven hypotheses of Theory/EckmannHilton.v, assembled.  The carrier is
 the set of loops at the unit and the setoid is [Path_Setoid], whose `≈` IS
 homotopy rel endpoints; f is pointwise multiplication and g is
 concatenation, in the orientation the header derives.  The two [Proper]
 arguments are supplied as lambdas rather than as instances, because
 [Path_Setoid] is deliberately not registered for resolution
 (Instance/Top/FundamentalGroupoid.v) and the expected type unfolds to
 exactly the shape [loop_mult_respects] and [path_concat_respects]
 already have.

 The g-side unit laws come from the fundamental groupoid's own two unit
 homotopies -- note the sides: [unit_left_homotopy] concatenates the
 CONSTANT loop first, so it is [g_unit_left], and [unit_right_homotopy]
 concatenates it last, so it is [g_unit_right]. 

 --------
 Theory/EckmannHilton.v 的七个假设已组装完毕。载体是单位处的循环集，集合是 [Path_Setoid]，其 `≈` 是端点相对的同伦；f 是逐点乘法，g 是按标题推导方向的串联。两个 [Proper] 参数以 lambda 形式提供，而不是以实例形式提供，因为 [Path_Setoid] 故意未注册以供解析（Instance/Top/FundamentalGroupoid.v），且预期类型展开后正好呈现 [loop_mult_respects] 的形状，而 [path_concat_respects] 已经拥有。 

 g 侧的单位律来自基本群oid自身的两个单位同伦——注意各边：[unit_left_homotopy] 先串联常量循环，因此它是 [g_unit_left]，而 [unit_right_homotopy] 最后串联它，因此它是 [g_unit_right]。
*)

Definition loops_eckmann_hilton :
  (const_path (htm_unit G) ≈ const_path (htm_unit G))
    ∧ (∀ a b, loop_mult a b ≈ path_concat a b)
    ∧ (∀ a b, loop_mult a b ≈ loop_mult b a)
    ∧ (∀ a b c, loop_mult (loop_mult a b) c ≈ loop_mult a (loop_mult b c)) :=
  @eckmann_hilton
    (Path G (htm_unit G) (htm_unit G))
    (Path_Setoid (htm_unit G) (htm_unit G))
    loop_mult (@path_concat G _ _ _)
    (const_path (htm_unit G)) (const_path (htm_unit G))
    (fun p p' E1 q q' E2 => loop_mult_respects E1 E2)
    (fun p p' E1 q q' E2 => path_concat_respects E1 E2)
    loop_mult_unit_left loop_mult_unit_right
    (fun p => unit_left_homotopy p) (fun p => unit_right_homotopy p)
    loop_interchange.

(*
 The three substantive conclusions, read off individually.  Each is the
 corresponding lemma of Theory/EckmannHilton.v at the same seven
 hypotheses; they are restated here so that a consumer need not unfold the
 nested pair. 

 --------
 这三个实质性结论，逐个读取。每个都是在相同七个假设下 Theory/EckmannHilton.v 的对应引理；它们在此重述，以便用户无需拆开嵌套对。
*)

(* The two operations agree up to homotopy. / 这两个操作在同宿条件下是相同的。 *)
Theorem loop_mult_concat_agree (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p q) (path_concat p q).
Proof.
  exact (fst (snd loops_eckmann_hilton) p q).
Qed.

(*
 Pointwise multiplication is commutative up to homotopy (the f-side
 conclusion). 

 --------
 逐点乘法在同伦意义下是交换的（f 侧结论）。
*)
Theorem loop_mult_comm (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult p q) (loop_mult q p).
Proof.
  exact (fst (snd (snd loops_eckmann_hilton)) p q).
Qed.

(* Pointwise multiplication is associative up to homotopy. / 逐点乘法在同伦意义下是结合的。 *)
Theorem loop_mult_assoc (p q r : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (loop_mult (loop_mult p q) r) (loop_mult p (loop_mult q r)).
Proof.
  exact (snd (snd (snd loops_eckmann_hilton)) p q r).
Qed.

(*
 THE LOOP-LEVEL FORM of Exercise 6: concatenation of loops at the unit is
 commutative up to homotopy rel endpoints.  This is the g-side corollary
 [eh_g_comm], and it is the statement π₁ is about -- the fundamental group's
 operation is concatenation, not the pointwise product. 

 --------
 练习 6 的循环层级形式：在单元处的循环连接是终点同伦下的交换的。这是 g 侧的推论 [eh_g_comm]，它正是 π₁ 所涉及的陈述——基本群的运算是连接，而不是逐点乘积。
*)
Theorem loop_concat_comm (p q : Path G (htm_unit G) (htm_unit G)) :
  PathHomotopy (path_concat p q) (path_concat q p).
Proof.
  exact (@eh_g_comm
           (Path G (htm_unit G) (htm_unit G))
           (Path_Setoid (htm_unit G) (htm_unit G))
           loop_mult (@path_concat G _ _ _)
           (const_path (htm_unit G)) (const_path (htm_unit G))
           (fun a a' E1 b b' E2 => loop_mult_respects E1 E2)
           (fun a a' E1 b b' E2 => path_concat_respects E1 E2)
           loop_mult_unit_left loop_mult_unit_right
           (fun a => unit_left_homotopy a) (fun a => unit_right_homotopy a)
           loop_interchange p q).
Qed.

End Loops.

Arguments loop_mult {G} p q.
Arguments loop_interchange {G} a b c d.
Arguments loop_concat_comm {G} p q.

(* * ** The headline: π₁ of a topological group is abelian / * ** 标题：拓扑群的 π₁ 是阿贝尔群 *)

(*
 The group-level statement.  [fundamental_group G e] is the vertex group of
 π(G) at e (Instance/Top/FundamentalGroupoid.v), whose multiplication
 is [hom_monoid]'s -- that is, composition in π(G), which
 Instance/Top/FundamentalGroupoid.v defines as
 [compose q p := path_concat p q].  So [mon_op p q] IS
 [path_concat q p], and commutativity of the group operation is
 [loop_concat_comm] with its two arguments in the other order.

 THE NAME is the one issue #286 pins, and it names Mac Lane's object; the
 theorem is stated over the weaker [HTopMonoid] because that is all the
 proof consumes (header).  [pi1_TopGroup_abelian] just below is Mac Lane's
 literal statement, over a genuine topological group. 

 --------
 群层面的陈述。[fundamental_group G e] 是 π(G) 在 e 处的顶点群（Instance/Top/FundamentalGroupoid.v），其乘法是 [hom_monoid] 的 —— 即 π(G) 中的复合，Instance/Top/FundamentalGroupoid.v 定义为 [compose q p := path_concat p q]。因此 [mon_op p q] 是 [path_concat q p]，并且群操作的交换性是 [loop_concat_comm]，两者参数顺序相反。

 THE NAME 是问题 #286 中提到的唯一问题，它命名了 Mac Lane 的对象；定理陈述在较弱的 [HTopMonoid] 上，因为证明只使用了这些（标题）。下面的 [pi1_TopGroup_abelian] 是 Mac Lane 的字面陈述，在一个真正的拓扑群上。
*)
Theorem pi1_topgroup_abelian (G : HTopMonoid)
        (p q : fundamental_group G (htm_unit G)) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (loop_concat_comm q p).
Qed.

(*
 What the group operation and its unit ARE, recorded by [eq_refl] so that
 the statement above cannot be misread: the multiplication of
 [fundamental_group] is concatenation -- in the order π(G)'s composition
 puts it, the SECOND argument running first -- and its unit is the
 constant loop.  Neither is an artefact of this file: both are read off
 Construction/Deloop.v's [hom_monoid] at
 Instance/Top/FundamentalGroupoid.v. 

 --------
 群运算及其单位是什么，由 [eq_refl] 记录，以便上述陈述不会被误读：[fundamental_group] 的乘法是连接操作——按照 π(G) 的复合顺序，第二个参数先运行——其单位是恒定环路。这两者都不是该文件的人工产物：两者都可以从 Construction/Deloop.v 的 [hom_monoid] 在 Instance/Top/FundamentalGroupoid.v 中读取。
*)
Example pi1_mon_op_is_concat (G : HTopMonoid)
        (p q : fundamental_group G (htm_unit G)) :
  mon_op p q = path_concat q p := eq_refl.

Example pi1_mon_unit_is_const (G : HTopMonoid) :
  @mon_unit (fundamental_group G (htm_unit G)) = const_path (htm_unit G)
  := eq_refl.

(*
 Mac Lane §II.5 Exercise 6 as stated: the fundamental group of a
 topological group, at its unit, is abelian. 

 --------
 Mac Lane §II.5 练习 6 如所述：拓扑群在其单位元处的基本群是阿贝尔群。
*)
Corollary pi1_TopGroup_abelian (G : TopGroup)
          (p q : fundamental_group (tg_monoid G) (htm_unit (tg_monoid G))) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (pi1_topgroup_abelian (tg_monoid G) p q).
Qed.

(** ** Witness: the additive reals / ** 见证：加法实数 *)

(*
 Instance/Top/Presheaf.v's [R_Top] -- the real line with the metric
 topology, over Instance/Top/Interval.v's ball spaces -- carries the
 additive group structure, and both continuity conditions are the ordinary
 ε/2 and ε arguments with the radius carried as data.

 DISCLOSURE (header, deferral 1): π₁(ℝ) is trivial, ℝ being contractible,
 so this witness demonstrates that the hypotheses of [HTopMonoid] and
 [TopGroup] are simultaneously satisfiable by a genuine space -- and that
 the certificate field is dischargeable in practice -- and NOT that the
 conclusion has content at it.  No space in this tree has a nontrivial
 fundamental group. 

 --------
 Instance/Top/Presheaf.v 的  [R_Top] —— 带度量拓扑的实数轴，在 Instance/Top/Interval.v 的球空间之上 —— 具有加法群结构，并且两个连续性条件都是普通的 ε/2 和 ε 论证，并将半径作为数据携带。

 披露（标题，延迟 1）：π₁(ℝ) 是平凡的，因为 ℝ 是可缩的，所以这个例子表明 [HTopMonoid] 和 [TopGroup] 的假设可以同时由一个真实空间满足 —— 并且证书字段在实践中是可处理的 —— 而不是说结论在其中有实际内容。此树中的任何空间都没有非平凡的基本群。
*)

(*
 Instance/Top/Presheaf.v registers [R_equiv_Equivalence] but deliberately
 not [R_Setoid] (its note), so `≈` does not resolve at a bare [R].
 Registering it FILE-LOCALLY is what lets the two [Proper] obligations
 below be stated in the ordinary shape; it is the same setoid the record
 fields ask for, [is_setoid (top_carrier R_Top)] reducing to it. 

 --------
 Instance/Top/Presheaf.v 注册了 [R_equiv_Equivalence]，但故意没有注册 [R_Setoid]（它的注释），所以在裸的 [R] 上 `≈` 无法解析。在文件本地注册它才使得下面两个 [Proper] 义务能够以普通形式陈述；它是记录字段所要求的同构集，[is_setoid (top_carrier R_Top)] 归约到它。
*)
#[local] Existing Instance R_Setoid.

(*
 A metric ball of the real line is open: at any interior point the slack
 radius witnesses openness, radius as data, no choice.  Instance/Top/
 Interval.v's [Rlin] splits absolute values in the GOAL only, and the
 estimate here carries one in a hypothesis, so the triangle inequality is
 applied by name rather than by case analysis; that also avoids adding a
 third copy of Instance/Top/ContinuousRing.v's [RlinH] to the tree. 

 --------
 实数轴上的度量球是开集：在任意内部点处，松弛半径表明其开放性，半径作为数据，无需选择。Instance/Top/Interval.v 的 [Rlin] 只在目标中拆分绝对值，而此处的估计在假设中就包含了一个绝对值，因此应用三角不等式是通过名称而不是通过情况分析；这也避免了在树中添加第三个 Instance/Top/ContinuousRing.v 的 [RlinH] 副本。
*)
Lemma R_ball_open (c d : R) :
  (0 < d)%R → IsOpen R_Top (fun r : R => (Rabs (c - r) < d)%R).
Proof.
  intros Hd r Hr.
  exists (d - Rabs (c - r))%R; split.
  - lra.
  - intros y Hy; simpl in Hy.
    pose proof (Rabs_triang (c - r) (r - y)) as Ht.
    replace (c - r + (r - y))%R with (c - y)%R in Ht by ring.
    lra.
Qed.

Lemma R_plus_proper : Proper (equiv ==> equiv ==> equiv) Rplus.
Proof.
  intros a b Hab c d Hcd.
  assert (Ha : a = b :> R) by exact Hab.
  assert (Hc : c = d :> R) by exact Hcd.
  rewrite Ha, Hc.
  reflexivity.
Qed.

(* Joint continuity of addition, in the two-open form: split the target radius in half between the two factors. / 加法的联合连续性，在两开形式中：将目标半径在两个因子之间平分。 *)
Lemma R_plus_cont (V : R_Top → Type) (HV : IsOpen R_Top V)
      (x y : R_Top) (Hxy : V (Rplus x y)) :
  { U : R_Top → Type &
    ((IsOpen R_Top U) ∧ (U x) ∧
     { W : R_Top → Type &
       ((IsOpen R_Top W) ∧ (W y) ∧
        (∀ x' y' : R_Top, U x' → W y' → V (Rplus x' y')))%type })%type }.
Proof.
  destruct (HV (Rplus x y) Hxy) as [d [Hd Hball]].
  exists (fun u : R => (Rabs (x - u) < d / 2)%R).
  split; [ | split ].
  - apply R_ball_open; lra.
  - replace (x - x)%R with 0%R by ring; rewrite Rabs_R0; lra.
  - exists (fun w : R => (Rabs (y - w) < d / 2)%R).
    split; [ | split ].
    + apply R_ball_open; lra.
    + replace (y - y)%R with 0%R by ring; rewrite Rabs_R0; lra.
    + intros u w Hu Hw.
      apply Hball.
      pose proof (Rabs_triang (x - u) (y - w)) as Ht.
      replace (x - u + (y - w))%R with (x + y - (u + w))%R in Ht by ring.
      simpl; lra.
Qed.

Definition R_TopMonoid : HTopMonoid := {|
  htm_space  := R_Top;
  htm_unit   := 0%R;
  htm_mult   := Rplus;

  htm_mult_proper := R_plus_proper;

  htm_unit_left  := Rplus_0_l;
  htm_unit_right := Rplus_0_r;

  htm_mult_cont := R_plus_cont
|}.

Lemma R_opp_proper : Proper (equiv ==> equiv) Ropp.
Proof.
  intros a b Hab.
  assert (Ha : a = b :> R) by exact Hab.
  rewrite Ha; reflexivity.
Qed.

(*
 Negation is continuous: the same radius works, negation being an
 isometry. 

 --------
 否定是连续的：使用相同的半径即可，因为否定是一个等距变换。
*)
Lemma R_opp_cont (V : R_Top → Type) (HV : IsOpen R_Top V) :
  IsOpen R_Top (fun x : R => V (Ropp x)).
Proof.
  intros x Hx.
  destruct (HV (Ropp x) Hx) as [d [Hd Hball]].
  exists d; split; [ exact Hd | ].
  intros y Hy.
  apply Hball.
  simpl in *.
  replace (- x - - y)%R with (- (x - y))%R by ring.
  rewrite Rabs_Ropp.
  exact Hy.
Qed.

Definition R_TopGroup : TopGroup := {|
  tg_monoid := R_TopMonoid;

  tg_inv := Ropp;

  tg_inv_proper := R_opp_proper;

  tg_inv_left  := Rplus_opp_l;
  tg_inv_right := Rplus_opp_r;

  tg_inv_cont := R_opp_cont
|}.

(* Acceptance: the record's data are the additive ones on the nose, and the pointwise product of two loops is pointwise addition. / 接受：记录的数据正好是可加的，并且两个环的逐点积是逐点相加。 *)
Example R_unit_is_zero : htm_unit R_TopMonoid = 0%R := eq_refl.

Example R_mult_is_plus : htm_mult R_TopMonoid = Rplus := eq_refl.

Example R_inv_is_opp : tg_inv R_TopGroup = Ropp := eq_refl.

Example R_loop_mult_eval
        (p q : Path R_TopMonoid (htm_unit R_TopMonoid) (htm_unit R_TopMonoid))
        (t : Ipt) :
  path_map (loop_mult p q) t ≈ (path_map p t + path_map q t)%R.
Proof. reflexivity. Qed.

(* And the headline instantiated at the reals. / 而这个标题在实数中被实例化。 *)
Corollary pi1_R_abelian
          (p q : fundamental_group R_TopMonoid (htm_unit R_TopMonoid)) :
  mon_op p q ≈ mon_op q p.
Proof.
  exact (pi1_topgroup_abelian R_TopMonoid p q).
Qed.
