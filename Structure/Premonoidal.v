Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Binoidal.Central.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
   * * Premonoidal categories

   nLab: https://ncatlab.org/nlab/show/premonoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Premonoidal_category

   A premonoidal category (Power–Robinson, “Premonoidal categories and
   notions of computation”, Math. Structures Comput. Sci. 7(5), 1997) is a
   binoidal category — Structure/Binoidal.v — together with

   - a unit object [premon_I];
   - unitor isomorphisms  lambda : I ⊗ x ≅ x   ([premon_unit_left])
   rho    : x ⊗ I ≅ x   ([premon_unit_right]);
   - an associator alpha : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)  ([premon_assoc]);

   such that the forward components of lambda, rho and alpha are CENTRAL
   (Structure/Binoidal.v, [central]), each family is natural in every
   variable SEPARATELY, and the triangle and pentagon coherence laws hold.
   The iso orientations and the naturality-square orientations mirror
   Structure/Monoidal.v exactly, so that a monoidal category yields a
   premonoidal one field-for-field (Structure/Premonoidal/Monoidal.v).

   Design of the field set:

   - Naturality is one variable at a time.  In a binoidal category the
   tensor is only separately functorial, so a jointly-natural square in
   the style of Monoidal.v's [to_tensor_assoc_natural] is not the
   primitive notion; the three one-variable associator squares
   ([premon_assoc_natural_left]/[_middle]/[_right]) are.  Remarkably,
   the JOINT square for the interleaved composite [composite_ff'] is
   still derivable from them with no centrality hypothesis at all
   ([premon_joint_assoc_natural] below).

   - Only the forward (to) directions are data.  The from-direction
   centralities follow by [central_iso_from], and the from-direction
   naturality squares follow by conjugating the to-squares with the
   isomorphisms ([premon_square_from]).  Keeping the class minimal
   means fewer obligations for instance builders; the derived lemmas
   below restore the full Monoidal.v-style surface.

   - Centrality of the structural isomorphisms is what separates a
   premonoidal category from a mere “binoidal category with coherent
   isos”: it makes the unitors and associator morphisms of the centre
   Z(C), so that Z(C) becomes a genuine monoidal category
   (Structure/Premonoidal/Centre.v), and it is exactly what the
   one-sided interchange lemmas [composite_ff'_comp_l]/[_r] of
   Structure/Binoidal/Central.v consume.

   The [composite_ff']-phrased translation lemmas at the end of this file
   ([premon_unit_left_natural_ff'], [premon_unit_right_natural_ff'],
   [premon_triangle_ff'], [premon_pentagon_ff'], and the unitor from-forms)
   restate the class fields with identity padding, which is the exact shape
   [Build_Monoidal] needs when every morphism is central
   (Structure/Premonoidal/Monoidal.v) and when the tensor is restricted to
   the centre (Structure/Premonoidal/Centre.v). 

   --------
   * * 前单范畴

   nLab:  https://ncatlab.org/nlab/show/premonoidal+category 
   维基百科:  https://en.wikipedia.org/wiki/Premonoidal_category 

   前单范畴（Power–Robinson，《前单范畴与计算概念》，数学结构计算科学 7(5), 1997）是一个二元范畴 — Structure/Binoidal.v — 并且包含

   - 一个单位对象  [premon_I] ;
   - 单位同构  lambda : I ⊗ x ≅ x   ( [premon_unit_left] )
   rho    : x ⊗ I ≅ x   ( [premon_unit_right] );
   - 结合同构 alpha : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z)  ( [premon_assoc] );使得 λ、ρ 和 α 的前向分量是中心的
   （Structure/Binoidal.v, [central]），每个族在每个变量上都是自然的，且三角形与五边形的相容律成立。
   同构方向和自然性平方的方向完全对应于 Structure/Monoidal.v，因此一个单体范畴可以逐字段地生成一个预单体范畴（Structure/Premonoidal/Monoidal.v）。

   字段集的设计：- 自然性是一次一个变量。在二项范畴中，张量只对每个变量分别是函子性的，因此像 Monoidal.v 中的 [to_tensor_assoc_natural] 风格的联合自然方形并不是基本概念；三个单变量结合子方形（[premon_assoc_natural_left] / [_middle] / [_right]）才是。值得注意的是，交错复合 [composite_ff'] 的联合方形仍然可以从它们推导出来，而完全无需中心性假设（见下方 [premon_joint_assoc_natural]）。- 只有前向（到）方向是数据。来自方向的中心性由 [central_iso_from] 给出，而来自方向的自然性平方通过用同构（[premon_square_from]）对到平方进行共轭得到。保持类的最小化意味着实例构造器的义务更少；下面的推导引理恢复了完整的 Monoidal.v 风格的表面。- 结构同构的中心性是区分 的一个因素
   从一个仅仅具有连贯的“双素范畴”中获得前单半范畴
   iso“：它使中心的酉子态射和结合子态射成为
   Z（C），使得 Z（C） 成为一个真正的幺半范畴
   （结构/前单体/中心.v），它正是
   单侧交换引理 [composite_ff'_comp_l] / [_r]
   Structure/Binoidal/Central.v 消费。本文件末尾的 [composite_ff'] 表达的翻译词条
   （[premon_unit_left_natural_ff']、[premon_unit_right_natural_ff']、
   [premon_triangle_ff']、[premon_pentagon_ff'] 以及单位元的 from-forms）
   使用恒等填充重新声明类字段，这是 [Build_Monoidal] 所需要的精确形状，当每个态射都是中心态射时
   （Structure/Premonoidal/Monoidal.v）以及当张量限制在中心时（Structure/Premonoidal/Centre.v）。
*)

(*
 Effects, interchange, and the premonoidal programme

 nLab:  https://ncatlab.org/nlab/show/premonoidal+category
 nLab:  https://ncatlab.org/nlab/show/Freyd+category
 Paper: Moggi, “Notions of computation and monads”, Information and
 Computation 93(1), 1991
 Paper: Power, Robinson, “Premonoidal categories and notions of
 computation”, Mathematical Structures in Computer Science 7(5),
 1997

 Premonoidal categories keep exactly the monoidal structure that
 survives when morphisms carry computational effects.  A monoidal tensor
 is jointly functorial: the interchange law
 (g₁ ⊗ g₂) ∘ (f₁ ⊗ f₂) ≈ (g₁ ∘ f₁) ⊗ (g₂ ∘ f₂) says that the two sides
 of a tensor proceed independently.  For effectful programs interchange
 breaks down observably — as an illustration, if f prints one message
 and g another, the two execution orders differ, yet interchange against
 identities would equate them.  It follows that a joint tensor of
 morphisms has no canonical meaning; what remains is one-variable
 tensoring ⋉ / ⋊, interleaved into two schedules: [composite_ff'] of
 Structure/Binoidal.v runs the left factor first, and the rival
 interleaving runs the right factor first.  Yet the plumbing — unit,
 unitors, associator — stays effect-free and coherent: centrality of
 the structural maps is what [premon_unit_left_central],
 [premon_unit_right_central] and [premon_assoc_central] assert,
 [premon_triangle] and [premon_pentagon] supply the coherence, and
 together this is exactly enough for a multi-variable context to
 receive a semantics independent of bracketing.

 Power and Robinson introduced the structure for the denotational
 semantics of programming languages, as the monad-free residue of
 Moggi's monadic account of effects (Moggi, “Computational
 lambda-calculus and monads”, LICS 1989): what survives on a Kleisli
 category when the monad is forgotten.  Their motivating theorem: the
 Kleisli category of a strong monad on a symmetric monoidal category
 carries a canonical premonoidal structure — the strength extends the
 tensor separately in each variable — and that structure is monoidal
 precisely when the monad is commutative.  Both halves are in-tree:
 Monad/Kleisli/Premonoidal.v builds the instance, whose two schedules
 are literally the double strengths [dstr] and [dstr'] — which effectful
 factor runs first — and Monad/Kleisli/Commutative.v proves the
 commutative case ([kleisli_all_central], [Kleisli_Monoidal]).

 On this reading centrality is the categorical residue of purity:
 [central] f says the two schedules agree against every partner on
 either side, and in the Kleisli instance this is exactly agreement of
 the two sequencings wherever f is a factor ([kleisli_central_iff]).
 Führmann's hierarchy pure ⇒ thunkable ⇒ central refines the picture
 (Monad/Thunkable.v, after Führmann, “Direct models of the computational
 lambda-calculus”, MFPS XV 1999).  The centre Z(C) is a genuine monoidal
 category ([Centre_Monoidal], Structure/Premonoidal/Centre.v), and per
 nLab the centre construction provides a right adjoint to the inclusion
 of monoidal categories into premonoidal ones; a monoidal category is
 precisely a premonoidal one in which every morphism is central
 (Structure/Premonoidal/Monoidal.v, [Monoidal_Premonoidal] and
 [Premonoidal_Monoidal]).  This premonoidal centre is distinct from the
 Drinfeld centre of Structure/Monoidal/Drinfeld.v, which is built from
 half-braidings on a monoidal base.

 The downstream uses cluster around call-by-value.  A Freyd category is
 an identity-on-objects functor from a category of values to a
 premonoidal category of computations, landing in the centre (Power,
 Thielecke, “Closed Freyd- and κ-categories”, ICALP 1999; per nLab the
 name honours Peter Freyd's 1989 work on axiomatic domain theory).  When
 the value inclusion has a right adjoint, the computation category is
 the Kleisli category of the induced strong monad, so closed Freyd
 categories and strong monads are interconvertible; yet Freyd categories
 also make sense for first-order languages with no object of
 computations.  Structure/Premonoidal/Freyd.v formalizes the effectful
 weakening ([EffectfulFunctor], [Freyd]).  Further afield: Selinger's
 control categories pair cartesian-closed with premonoidal structure to
 interpret the λμ-calculus (Selinger, “Control categories and duality:
 on the categorical semantics of the lambda-mu calculus”, MSCS 11(2),
 2001); Benton and Hyland generalize traces to symmetric premonoidal
 categories and Conway operators to Freyd categories, motivated by value
 recursion (Benton, Hyland, “Traced premonoidal categories”, RAIRO-ITA
 37(4), 2003); Hughes-style arrows correspond to Freyd categories per
 nLab (Jacobs, Heunen, Hasuo, JFP 19(3–4), 2009); and a strict
 premonoidal category is a monoid in Cat under the funny tensor product
 (nLab), the round trip proved over (StrictCat, □) in
 Instance/StrictCat/Premonoid.v. 

 --------
 效果、互换性与前单态程序

 nLab：https://ncatlab.org/nlab/show/premonoidal+category 
 nLab：https://ncatlab.org/nlab/show/Freyd+category 
 论文：Moggi，《计算和单子概念》，信息与计算 93(1), 1991
 论文：Power, Robinson，《前单态范畴和计算概念》，计算机科学中的数学结构 7(5), 1997前单范畴精确保留了在态射携带计算效应时仍然存在的幺半群结构。一个幺半群张量是联合函子性的：交换律
 (g₁ ⊗ g₂) ∘ (f₁ ⊗ f₂) ≈ (g₁ ∘ f₁) ⊗ (g₂ ∘ f₂) 表明张量的两边是独立进行的。对于带效应的程序，交换在可观察上会失效——例如，如果 f 打印一条消息而 g 打印另一条消息，那么两种执行顺序会不同，但针对恒等映射的交换会将它们等同。因此，态射的联合张量没有规范意义；剩下的是单变量张量 ⋉ / ⋊，交错成两个调度：Structure/Binoidal.v 中的 [composite_ff'] 先运行左因子，而对立的交错则先运行右因子。然而，管道——单位、一致器、结合器——仍然保持无影响且连贯：结构映射的中心性正是 [premon_unit_left_central]、[premon_unit_right_central] 和 [premon_assoc_central] 所断言的，[premon_triangle] 和 [premon_pentagon] 提供了连贯性，而这些加在一起正好足够让多变量上下文接收与括号无关的语义。Power 和 Robinson 引入了用于编程语言指称语义的结构，作为 Moggi 对效应的单子描述（Moggi，《计算 λ 演算与单子》，LICS 1989）的无单子残余：在忘记单子之后在 Kleisli 范畴上残存的部分。他们的动机定理是：在对称单模范畴上的强单子的 Kleisli 范畴具有一个典型的前单模结构——强度在每个变量中单独扩展了张量——而且当且仅当单子是交换的时，该结构才是单模的。两部分都在代码树中：
 Monad/Kleisli/Premonoidal.v 构建了实例，其两个调度实际上是双重强度 [dstr] 和 [dstr'] —— 哪个效果因子先运行 —— 而 Monad/Kleisli/Commutative.v 证明了可交换情况（[kleisli_all_central]，[Kleisli_Monoidal]）。在这种解读下，中心性是纯性的范畴残留：
 [central] f 说两个调度在任一方的每个伙伴上都一致，在 Kleisli 实例中，这正是当 f 是一个因子时两个序列的一致性（[kleisli_central_iff]）。Führmann 的层次结构 pure ⇒ thunkable ⇒ central 精炼了这一图景（Monad/Thunkable.v，参照 Führmann, “计算 λ 演算的直接模型”, MFPS XV 1999）。中心 Z(C) 是一个真正的单体范畴（[Centre_Monoidal]，Structure/Premonoidal/Centre.v），根据 nLab，中心构造为单体范畴包含进前单体范畴提供了右伴随；一个单体范畴恰好是每个态射都是中心态射的前单体范畴（Structure/Premonoidal/Monoidal.v, [Monoidal_Premonoidal] 和 [Premonoidal_Monoidal]）。这个前单元中心不同于 Structure/Monoidal/Drinfeld.v 的 Drinfeld 中心，后者是由单元基上的半交错构建的。下游使用集中于按值调用。Freyd范畴是从值范畴到计算的前单范畴的一个对象恒等函子，落在中心（Power, Thielecke, “Closed Freyd- and κ-categories”, ICALP 1999；根据nLab，该名称是为了纪念Peter Freyd 1989年的公理化域理论工作）。当值的包含具有右伴随时，计算范畴是由此产生的强幺半范畴的Kleisli范畴，因此闭Freyd范畴和强幺半范畴是可互换的；然而，Freyd范畴对于没有计算对象的一阶语言也有意义。Structure/Premonoidal/Freyd.v形式化了效应削弱（[EffectfulFunctor], [Freyd]）。进一步研究：Selinger 的控制范畴将笛卡尔闭范畴与预单范畴结构配对，以解释 λμ 演算（Selinger，《控制范畴与对偶性：论 λμ 演算的范畴语义》，MSCS 11(2), 2001）；Benton 和 Hyland 将迹推广到对称预单范畴，并将 Conway 算子推广到 Freyd 范畴，其动机是值递归（Benton, Hyland，《迹的预单范畴》，RAIRO-ITA 37(4), 2003）；Hughes 风格的箭头根据 nLab 对应于 Freyd 范畴（Jacobs, Heunen, Hasuo, JFP 19(3–4), 2009）；严格预单范畴是在 Cat 下的幽默张量积下的一个幺半群（nLab），在 Instance/StrictCat/Premonoid.v 中对 (StrictCat, □) 的往返已经被证明。
*)

Section Premonoidal.

Context {C : Category}.
Context `{@Binoidal C}.

(*
 Section-local object-level tensor, mirroring the section notation of
 Structure/Binoidal.v.  The global ⊗ lives in two scopes (objects and,
 via [composite_ff'], morphisms); since morphism_scope is opened on top
 of object_scope, an unscoped section notation is needed for ⊗ to mean
 the OBJECT tensor inside the field types below.  Morphism-level
 interleaved tensoring is always written [composite_ff'] in this file. 

 --------
 段局部对象级张量，镜像 Structure/Binoidal.v 的段记法。全局 ⊗ 存在于两个作用域（对象以及通过 [composite_ff'] 的态射）；由于 morphism_scope 在 object_scope 之上被打开，所以需要一种无作用域的段记法来使 ⊗ 表示下面字段类型中的对象张量。态射级交错张量在此文件中总是写作 [composite_ff']。
*)
Local Notation "x ⊗ y" := (tensor x y)
  (at level 30, right associativity).

(*
 Conjugating a commuting square by isomorphisms on both vertical edges:
 from   g ∘ to i ≈ to j ∘ f   we get   f ∘ from i ≈ from j ∘ g.
 Instantiated below with the unitors and the associator, this converts
 every to-direction naturality field into its from-direction form, so the
 inverse squares need not be part of the class data. 

 --------
 通过对两个垂直边进行同构共轭：
 从   g ∘ to i ≈ to j ∘ f   我们得到   f ∘ from i ≈ from j ∘ g。
 下文通过使用单元子和结合子实例化，这将每个 to-方向的自然性域转换为其 from-方向形式，因此逆平方不需要成为类数据的一部分。
*)
Lemma premon_square_from {a b c d : C} (i : a ≅ b) (j : c ≅ d)
      (f : a ~> c) (g : b ~> d) :
  g ∘ to i ≈ to j ∘ f →
  f ∘ from i ≈ from j ∘ g.
Proof.
  intros sq.
  symmetry.
  rewrite <- (id_right g).
  rewrite <- (iso_to_from i).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (from j) g (to i)).
  rewrite sq.
  rewrite (comp_assoc (from j) (to j) f).
  rewrite (iso_from_to j).
  now rewrite id_left.
Qed.

(*
 The premonoidal structure proper.  Field orientations follow
 Structure/Monoidal.v L48-94: the isos point I ⊗ x → x, x ⊗ I → x and
 (x ⊗ y) ⊗ z → x ⊗ (y ⊗ z); the naturality squares put the tensored
 morphism after the structural map on the right-hand side; triangle and
 pentagon are verbatim transcriptions with the joint bimap replaced by
 the separate tensorings ⋉ / ⋊ of Structure/Binoidal.v. 

 --------
 预单oidal结构本身。场方向遵循Structure/Monoidal.v L48-94：同构点 I ⊗ x → x, x ⊗ I → x 和 (x ⊗ y) ⊗ z → x ⊗ (y ⊗ z)；自然性图将张量化的态射放在右侧的结构映射之后；三角形和五边形是逐字转录，将联合双映射替换为Structure/Binoidal.v中的单独张量 ⋉ / ⋊。
*)
Class Premonoidal := {
  premon_I : C;

  premon_unit_left  {x} : premon_I ⊗ x ≅ x;                 (* lambda *)
  premon_unit_right {x} : x ⊗ premon_I ≅ x;                 (* rho *)
  premon_assoc {x y z} : (x ⊗ y) ⊗ z ≅ x ⊗ (y ⊗ z);         (* alpha *)

  (* The forward structural maps are central; the from-directions are derived below via [central_iso_from]. / 前向结构映射是核心；以下通过 [central_iso_from] 推导出方向。 *)
  premon_unit_left_central  {x} : central (to (@premon_unit_left x));
  premon_unit_right_central {x} : central (to (@premon_unit_right x));
  premon_assoc_central {x y z} : central (to (@premon_assoc x y z));

  (* Naturality, one variable at a time. For the unitors there is a single variable; for the associator there are three squares, one for each tensor position. / 自然性，一次处理一个变量。对于单位子，有一个变量；对于结合子，有三个方块，每个张量位置一个。 *)
  premon_unit_left_natural {x y} (g : x ~> y) :
    g ∘ to premon_unit_left
      << premon_I ⊗ x ~~> y >>
    to premon_unit_left ∘ (premon_I ⋊ g);

  premon_unit_right_natural {x y} (g : x ~> y) :
    g ∘ to premon_unit_right
      << x ⊗ premon_I ~~> y >>
    to premon_unit_right ∘ (g ⋉ premon_I);

  premon_assoc_natural_left {x y z w} (g : x ~> y) :
    (g ⋉ (z ⊗ w)) ∘ to premon_assoc
      << (x ⊗ z) ⊗ w ~~> y ⊗ (z ⊗ w) >>
    to premon_assoc ∘ ((g ⋉ z) ⋉ w);

  premon_assoc_natural_middle {x z w y} (h : z ~> w) :
    (x ⋊ (h ⋉ y)) ∘ to premon_assoc
      << (x ⊗ z) ⊗ y ~~> x ⊗ (w ⊗ y) >>
    to premon_assoc ∘ ((x ⋊ h) ⋉ y);

  premon_assoc_natural_right {x y z w} (i : z ~> w) :
    (x ⋊ (y ⋊ i)) ∘ to premon_assoc
      << (x ⊗ y) ⊗ z ~~> x ⊗ (y ⊗ w) >>
    to premon_assoc ∘ ((x ⊗ y) ⋊ i);

  (* Coherence: triangle (unitors against the associator, across the unit) and pentagon (the two reassociations of a fourfold tensor agree). / 相干性：三角形（单位子对结合子，在单位的作用下）和五边形（四重张量的两种重新结合方式一致）。 *)
  premon_triangle {x y} :
    to premon_unit_right ⋉ y
      << (x ⊗ premon_I) ⊗ y ~~> x ⊗ y >>
    (x ⋊ to premon_unit_left) ∘ to premon_assoc;

  premon_pentagon {x y z w} :
    (x ⋊ to premon_assoc) ∘ to premon_assoc ∘ (to premon_assoc ⋉ w)
      << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
    to premon_assoc ∘ to premon_assoc
}.

Context `{Premonoidal}.

(*
   * ** From-direction centrality

   The inverse of a central isomorphism is central
   (Structure/Binoidal/Central.v, [central_iso_from]), so the inverse
   structural maps are central as well. 

   --------
   * ** 从方向中心性

   一个中心同构的逆是中心的
   (Structure/Binoidal/Central.v,  [central_iso_from])，因此逆结构映射也是中心的。
*)

Lemma premon_unit_left_central_from {x} :
  central (from (@premon_unit_left _ x)).
Proof. apply central_iso_from, premon_unit_left_central. Qed.

Lemma premon_unit_right_central_from {x} :
  central (from (@premon_unit_right _ x)).
Proof. apply central_iso_from, premon_unit_right_central. Qed.

Lemma premon_assoc_central_from {x y z} :
  central (from (@premon_assoc _ x y z)).
Proof. apply central_iso_from, premon_assoc_central. Qed.

(*
   * ** From-direction naturality

   Each to-square conjugates to the corresponding from-square via
   [premon_square_from]; the orientations mirror Monoidal.v's
   [from_unit_left_natural] etc. 

   --------
   * ** 来向自然性

   每个目标格通过 [premon_square_from] 与对应的出发格结合；其方向与 Monoidal.v 的 [from_unit_left_natural] 等相对应。
*)

Lemma premon_unit_left_natural_from {x y} (g : x ~> y) :
  (premon_I ⋊ g) ∘ from premon_unit_left
    << x ~~> premon_I ⊗ y >>
  from premon_unit_left ∘ g.
Proof. apply premon_square_from, premon_unit_left_natural. Qed.

Lemma premon_unit_right_natural_from {x y} (g : x ~> y) :
  (g ⋉ premon_I) ∘ from premon_unit_right
    << x ~~> y ⊗ premon_I >>
  from premon_unit_right ∘ g.
Proof. apply premon_square_from, premon_unit_right_natural. Qed.

Lemma premon_assoc_natural_left_from {x y z w} (g : x ~> y) :
  ((g ⋉ z) ⋉ w) ∘ from premon_assoc
    << x ⊗ (z ⊗ w) ~~> (y ⊗ z) ⊗ w >>
  from premon_assoc ∘ (g ⋉ (z ⊗ w)).
Proof. apply premon_square_from, premon_assoc_natural_left. Qed.

Lemma premon_assoc_natural_middle_from {x z w y} (h : z ~> w) :
  ((x ⋊ h) ⋉ y) ∘ from premon_assoc
    << x ⊗ (z ⊗ y) ~~> (x ⊗ w) ⊗ y >>
  from premon_assoc ∘ (x ⋊ (h ⋉ y)).
Proof. apply premon_square_from, premon_assoc_natural_middle. Qed.

Lemma premon_assoc_natural_right_from {x y z w} (i : z ~> w) :
  ((x ⊗ y) ⋊ i) ∘ from premon_assoc
    << x ⊗ (y ⊗ z) ~~> (x ⊗ y) ⊗ w >>
  from premon_assoc ∘ (x ⋊ (y ⋊ i)).
Proof. apply premon_square_from, premon_assoc_natural_right. Qed.

(*
   * ** Joint naturality of the associator, without centrality

   In a binoidal category the interleaved tensor [composite_ff' f f']
   (written f ⊗ g in the global morphism scope) is in general functorial
   only up to a centrality hypothesis, and the two interleavings of a
   pair of morphisms in general disagree.  Nevertheless, the associator
   is natural against [composite_ff'] JOINTLY in all three variables,
   with NO centrality hypothesis: decompose each [composite_ff'] into
   its ⋊-then-⋉ factors, expand the outer tensorings of composites by
   functoriality, and push alpha through the three one-variable squares;
   both sides land on the same fully right-associated word

   alpha ∘ ((y ⊗ w) ⋊ i) ∘ ((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u).

   The reason no interchange is needed: in [composite_ff' g (composite_ff'
   h i) ∘ alpha] the three factors are already stacked in the order
   right-position, middle-position, left-position, which is exactly the
   order in which the three one-variable squares consume them, and each
   square permutes a factor past alpha without ever swapping two
   non-structural factors.

   This lemma is the engine behind Structure/Premonoidal/Monoidal.v's
   [Premonoidal_Monoidal] (where it discharges [to_tensor_assoc_natural]
   once every morphism is central) and, at `1-projections, behind the
   monoidal structure of the centre in Structure/Premonoidal/Centre.v. 

   --------
   * ** 结合子在不依赖中心性下的联合自然性

   在双诺伊达类别中，交错张量 [composite_ff' f f']（在全局态射作用域中写作 f ⊗ g）通常仅在中心性假设下具有函子性，而且一对态射的两种交错方式通常不一致。尽管如此，结合子在三个变量上对 [composite_ff'] 仍然是联合自然的，并且不依赖中心性假设：将每个 [composite_ff'] 分解为其 ⋊-然后-⋉ 因子，通过函子性展开组合的外层张量，并将 α 推过三个单变量方框；两边都落在相同的完全右结合的表达式上

   alpha ∘ ((y ⊗ w) ⋊ i) ∘ ((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u)。不需要交换的原因：在 [composite_ff' g (composite_ff' h i) ∘ alpha] 中，这三个因子已经按照右位置、中位置、左位置的顺序堆叠，这正是三个单变量平方使用它们的顺序，并且每个平方都会把一个因子通过 alpha 进行置换，而从不交换两个非结构因子。

   这个引理是 Structure/Premonoidal/Monoidal.v 中 [Premonoidal_Monoidal] 的核心（当每个态射都是中心态射时，它一次性处理 [to_tensor_assoc_natural]），并且在 `1-投影 情况下，是 Structure/Premonoidal/Centre.v 中中心的幺半群结构背后的原因。
*)

Lemma premon_joint_assoc_natural {x y z w u v}
      (g : x ~> y) (h : z ~> w) (i : u ~> v) :
  composite_ff' g (composite_ff' h i) ∘ to premon_assoc
    << (x ⊗ z) ⊗ u ~~> y ⊗ (w ⊗ v) >>
  to premon_assoc ∘ composite_ff' (composite_ff' g h) i.
Proof.
  unfold composite_ff'.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  (* left-position square: (g ⋉ (z ⊗ u)) ∘ alpha ≈ alpha ∘ ((g ⋉ z) ⋉ u) / 左侧方形: (g ⋉ (z ⊗ u)) ∘ alpha ≈ alpha ∘ ((g ⋉ z) ⋉ u) *)
  transitivity
    ((y ⋊ (w ⋊ i))
       ∘ ((y ⋊ (h ⋉ u)) ∘ (to premon_assoc ∘ ((g ⋉ z) ⋉ u)))).
  { apply compose_respects; [reflexivity|].
    apply compose_respects; [reflexivity|].
    apply premon_assoc_natural_left. }
  (* middle-position square: (y ⋊ (h ⋉ u)) ∘ alpha ≈ alpha ∘ ((y ⋊ h) ⋉ u) / 中间位置方块: (y ⋊ (h ⋉ u)) ∘ alpha ≈ alpha ∘ ((y ⋊ h) ⋉ u) *)
  transitivity
    ((y ⋊ (w ⋊ i))
       ∘ (to premon_assoc ∘ (((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u)))).
  { apply compose_respects; [reflexivity|].
    rewrite !comp_assoc.
    apply compose_respects; [|reflexivity].
    apply premon_assoc_natural_middle. }
  (* right-position square: (y ⋊ (w ⋊ i)) ∘ alpha ≈ alpha ∘ ((y ⊗ w) ⋊ i) / 右位置方： (y ⋊ (w ⋊ i)) ∘ alpha ≈ alpha ∘ ((y ⊗ w) ⋊ i) *)
  rewrite comp_assoc.
  transitivity
    ((to premon_assoc ∘ ((y ⊗ w) ⋊ i))
       ∘ (((y ⋊ h) ⋉ u) ∘ ((g ⋉ z) ⋉ u))).
  { apply compose_respects; [|reflexivity].
    apply premon_assoc_natural_right. }
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

Lemma premon_joint_assoc_natural_from {x y z w u v}
      (g : x ~> y) (h : z ~> w) (i : u ~> v) :
  composite_ff' (composite_ff' g h) i ∘ from premon_assoc
    << x ⊗ (z ⊗ u) ~~> (y ⊗ w) ⊗ v >>
  from premon_assoc ∘ composite_ff' g (composite_ff' h i).
Proof. apply premon_square_from, premon_joint_assoc_natural. Qed.

(*
   * ** Translation to [composite_ff'] form

   The unitor naturality squares and the coherence laws, restated with
   identity padding through [composite_ff'] (via [composite_id_left] /
   [composite_id_right] of Structure/Binoidal/Central.v).  With the
   tensor bifunctor of an all-central or centre-restricted premonoidal
   category defined by [fmap := composite_ff'], these are literally the
   [Build_Monoidal] fields of Structure/Monoidal.v. 

   --------
   * ** 翻译为 [composite_ff'] 形式

   单位元自然性方阵和相合律，通过 [composite_ff'] 以恒等填充重新表述（通过 Structure/Binoidal/Central.v 的 [composite_id_left] / [composite_id_right]）。使用由 [fmap := composite_ff'] 定义的全中心或中心限制前单范畴的张量双函子，这些在 Structure/Monoidal.v 中实际上是 [Build_Monoidal] 字段。
*)

Lemma premon_unit_left_natural_ff' {x y} (g : x ~> y) :
  g ∘ to premon_unit_left
    << premon_I ⊗ x ~~> y >>
  to premon_unit_left ∘ composite_ff' (id[premon_I]) g.
Proof.
  rewrite composite_id_left.
  apply premon_unit_left_natural.
Qed.

Lemma premon_unit_right_natural_ff' {x y} (g : x ~> y) :
  g ∘ to premon_unit_right
    << x ⊗ premon_I ~~> y >>
  to premon_unit_right ∘ composite_ff' g (id[premon_I]).
Proof.
  rewrite composite_id_right.
  apply premon_unit_right_natural.
Qed.

Lemma premon_unit_left_natural_from_ff' {x y} (g : x ~> y) :
  composite_ff' (id[premon_I]) g ∘ from premon_unit_left
    << x ~~> premon_I ⊗ y >>
  from premon_unit_left ∘ g.
Proof.
  rewrite composite_id_left.
  apply premon_unit_left_natural_from.
Qed.

Lemma premon_unit_right_natural_from_ff' {x y} (g : x ~> y) :
  composite_ff' g (id[premon_I]) ∘ from premon_unit_right
    << x ~~> y ⊗ premon_I >>
  from premon_unit_right ∘ g.
Proof.
  rewrite composite_id_right.
  apply premon_unit_right_natural_from.
Qed.

Lemma premon_triangle_ff' {x y} :
  composite_ff' (to premon_unit_right) (id[y])
    << (x ⊗ premon_I) ⊗ y ~~> x ⊗ y >>
  composite_ff' (id[x]) (to premon_unit_left) ∘ to premon_assoc.
Proof.
  rewrite composite_id_left, composite_id_right.
  apply premon_triangle.
Qed.

Lemma premon_pentagon_ff' {x y z w} :
  composite_ff' (id[x]) (to premon_assoc)
      ∘ to premon_assoc
      ∘ composite_ff' (to premon_assoc) (id[w])
    << ((x ⊗ y) ⊗ z) ⊗ w ~~> x ⊗ (y ⊗ (z ⊗ w)) >>
  to premon_assoc ∘ to premon_assoc.
Proof.
  rewrite composite_id_left, composite_id_right.
  apply premon_pentagon.
Qed.

End Premonoidal.
