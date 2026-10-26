Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.

Generalizable All Variables.

Reserved Infix "~~>" (at level 90, right associativity).
Reserved Infix "~~~>" (at level 90, right associativity).
Reserved Infix "∘∘" (at level 40, left associativity).
Reserved Infix "∘∘∘" (at level 40, left associativity).

(** Bicategory / 双范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/bicategory
   Wikipedia: https://en.wikipedia.org/wiki/Bicategory

   A bicategory (a weak 2-category) has 0-cells (objects), 1-cells between
   0-cells, and 2-cells between parallel 1-cells. For each pair of 0-cells the
   1-cells and 2-cells form a hom-category `bicat x y` (objects are 1-cells,
   morphisms are 2-cells, `∘∘` is vertical composition). Horizontal
   composition `hcompose` is a functor of these hom-categories, associative
   and unital only up to coherent 2-isomorphism: an associator α and left/right
   unitors λ, ρ, subject to the pentagon and triangle coherence laws.

   Notation map: in the verbatim nLab definition below, → is `~>` (a 1-cell)
   and ⇒ is `~~>` (a 2-cell); here `~~~>` is also a 2-cell, `∘∘` is vertical
   2-cell composition and `∘∘∘` is horizontal 1-cell composition.

   STATUS: this development supplies a complete bicategory. Beyond the hom-
   categories `bicat x y` and the horizontal-composition functor `hcompose`, the
   class now carries the associator `hassoc`, the left/right unitors
   `hunit_left`/`hunit_right` (as 2-isomorphisms in the hom-categories), their
   naturality squares, and the triangle and pentagon coherence laws — exactly
   the fields mirroring `Structure/Monoidal.v` under the dictionary
   tensor ↔ hcompose, I ↔ bi1id, λ ↔ hunit_left, ρ ↔ hunit_right,
   α ↔ hassoc. The derived horizontal 2-cell operation `hcomp2` (Godement
   whiskering) is the functorial action of `hcompose` on a pair of 2-cells, and
   is what the coherence laws are stated through.

--------
nLab: https://ncatlab.org/nlab/show/bicategory
   Wikipedia: https://en.wikipedia.org/wiki/Bicategory

   双范畴 (bicategory)（弱 2-范畴）有 0-胞（对象）、0-胞之间的 1-胞、以及平行 1-胞
   之间的 2-胞。对每对 0-胞，1-胞与 2-胞形成 hom-范畴 `bicat x y`（对象是 1-胞，
   态射是 2-胞，`∘∘` 是垂直复合）。水平复合 `hcompose` 是这些 hom-范畴的函子，
   仅在连贯 2-同构下结合与有单位：结合子 α 与左/右单位子 λ、ρ，服从五边形与三角形
   连贯定律。

   记号对照：下文 verbatim nLab 定义中，→ 是 `~>`（1-胞），⇒ 是 `~~>`（2-胞）；
   此处 `~~~>` 也是 2-胞，`∘∘` 是垂直 2-胞复合，`∘∘∘` 是水平 1-胞复合。

   状态：本开发提供完整双范畴。除 hom-范畴 `bicat x y` 与水平复合函子 `hcompose` 外，
   类现携带结合子 `hassoc`、左/右单位子 `hunit_left`/`hunit_right`（作为 hom-范畴中的
   2-同构）、其自然性方块，以及三角形与五边形连贯定律——恰是在词典
   tensor ↔ hcompose、I ↔ bi1id、λ ↔ hunit_left、ρ ↔ hunit_right、α ↔ hassoc 下镜像
   `Structure/Monoidal.v` 的字段。派生的水平 2-胞运算 `hcomp2`（Godement whiskering）
   是 `hcompose` 对一对 2-胞的函子作用，连贯定律经其陈述。
*)

(*
Why weaken a 2-category: examples, coherence, and the monad slogan

   nLab:      https://ncatlab.org/nlab/show/bicategory
   Wikipedia: https://en.wikipedia.org/wiki/Bicategory
   Paper: Bénabou, J., “Introduction to bicategories”, Reports of the
          Midwest Category Seminar, LNM 47, Springer 1967, pp. 1-77
   Paper: Kelly, G.M., Street, R., “Review of the elements of
          2-categories”, LNM 420, Springer 1974, pp. 75-103
   Paper: Mac Lane, S., Paré, R., “Coherence for bicategories and indexed
          categories”, J. Pure Appl. Algebra 37, 1985, pp. 59-80

   The notion is due to Bénabou (1967).  A strict 2-category demands that
   horizontal composition of 1-cells be associative and unital on the
   nose, and almost none of the naturally occurring 2-dimensional
   structures meet that demand.  When composition is given by a universal
   construction — pullback of spans, tensor of bimodules, coend of
   profunctors — the result is determined only up to canonical
   isomorphism, so [hcompose] is associative and unital up to a coherent
   invertible 2-cell rather than on the nose.  A [Bicategory] keeps such
   examples honest by recording the associator [hassoc] and the unitors
   [hunit_left], [hunit_right] as data, and constraining them by the two
   coherence laws [hcoherence_pentagon] and [hcoherence_triangle], so that
   every reasonable diagram of associators and unitors commutes.  This
   was, per nLab, the earliest such notion and remains the one in most
   common use.

   The one-object case is exactly a monoidal category.  Read at a single
   [bi0cell], with [bi1id] as the unit and [hcompose] as the tensor, the
   bicategory axioms are the monoidal coherence axioms; this delooping is
   why the [Bicategory] class was shaped to mirror Structure/Monoidal.v
   field for field (the dictionary in the header above), and
   Theory/Bicategory/OneObject.v realizes the correspondence by projecting
   the monoidal data into a one-object bicategory (nLab; Wikipedia).

   Cat is the archetypal strict example — categories, functors, natural
   transformations — realized in Instance/Cat/Bicategory.v, where the
   hom-category [bicat] C D is definitionally the functor category on C
   and D.  The motivating weak examples lie elsewhere.  Span(C) over a
   category with pullbacks is, as the header of Construction/Span/Category.v
   notes, literally a bicategory, and quotienting by apex-iso recovers a
   strict 1-category (with Span(Set) subsuming Rel); its pushout mirror
   Cospan(C) is in Construction/Cospan/Category.v; bimodules over rings are
   what nLab calls the prototype for many similar examples; and profunctors
   compose by a coend, whose unit and associator laws are developed in
   Construction/Profunctor/Laws.v.

   The headline payoff, observed in the same 1967 paper, is a slogan: a
   small category is a monad in the bicategory of spans of sets.  A monad
   on a set A₀ in Span(Set) is a span A₀ ← A₁ → A₀ (objects, morphisms,
   source and target) with a multiplication A₁ ×_{A₀} A₁ → A₁
   (composition) and a unit A₀ → A₁ (identities), and its monad axioms are
   the category axioms.  Varying the ambient bicategory specializes the
   slogan: a monad in Prof is a promonad, the categorical content of
   Hughes's arrows and the setting for profunctor optics (Milewski,
   “Promonads, Arrows, and Einstein Notation for Profunctors”, 2019;
   Clarke et al., “Profunctor Optics, a Categorical Update”, arXiv 2020).
   More broadly, a bicategory is where composition given by a universal
   construction is modeled without asserting a strict equality it does not
   have.

   Adjunctions internal to a bicategory, and the mates correspondence —
   the bijection of 2-cells they induce — are the 2-categorical toolkit
   for lifts, transports, and Beck-Chevalley squares (Kelly, Street
   1974); the in-tree development gives internal adjunctions in
   Theory/Bicategory/Adjunction.v, the Kelly-Street mates calculus in
   Theory/Bicategory/Mates.v, pseudofunctors (the weak 2-functors) in
   Theory/Bicategory/Pseudofunctor.v, and lax transformations and
   modifications in Theory/Bicategory/Lax.v and
   Theory/Bicategory/Modification.v, with a bicategorical adjunction in
   Cat shown to coincide with F ⊣ U in
   Instance/Cat/Bicategory/Adjunction.v.  The coherence theorem (Mac Lane,
   Paré 1985) shows every bicategory biequivalent to a strict 2-category,
   even though the naturally occurring examples are presented weakly;
   Theory/DoubleCategory.v cross-refers to the [hassoc] orientation used
   here.

--------
为什么削弱二范畴：例子、一致性与幺半群口号

nLab：https://ncatlab.org/nlab/show/bicategory
维基百科：https://en.wikipedia.org/wiki/Bicategory
论文：Bénabou, J., 《双范畴导论》，中西部范畴研讨会报告，LNM 47，Springer 1967，第 1-77 页
论文：Kelly, G.M., Street, R., 《二范畴元素综述》，LNM 420，Springer 1974，第 75-103 页
论文：Mac Lane, S., Paré, R., 《双范畴与指标范畴的相合性》，纯粹与应用代数杂志 37, 1985，第 59-80 页

这一概念源于 Bénabou（1967）。严格的 2-范畴要求 1-态射的水平复合在字面上是结合的并且有单位的，而几乎没有自然出现的二维结构能够满足这一要求。当复合由一个普适构造给出时——如跨度的拉回、双模的张量、Profunctor 的余端——其结果仅在典型同构下确定，因此 [hcompose] 是结合的并且有单位的，但只是通过一个连贯的可逆 2-态射，而不是字面上的。[Bicategory] 通过记录结合子 [hassoc] 和单位态射 [hunit_left]、[hunit_right] 作为数据，并通过两个相容律 [hcoherence_pentagon] 和 [hcoherence_triangle] 约束它们，从而保持这些例子的严格性，使每一个合理的结合子和单位态射的图都是交换的。据 nLab，这一概念是最早提出的此类概念，并且仍然是最常用的。

单对象情况正好是一个幺半范畴。读取为单个 [bi0cell]，以 [bi1id] 作为单位，[hcompose] 作为张量，二范畴公理就是幺半范畴的相干公理；这种去环化就是为什么 [Bicategory] 类被设计成逐字段地镜像 Structure/Monoidal.v（上方头部的字典），并且 Theory/Bicategory/OneObject.v 通过将幺半范畴的数据投射到单对象二范畴来实现对应关系（nLab；Wikipedia）。

Cat 是典型的严格示例——范畴、函子、自然变换——在 Instance/Cat/Bicategory.v 中得以实现，其中同态范畴 [bicat] C D 在定义上就是 C 和 D 上的函子范畴。激励的弱示例则在其他地方。对于具有拉回的范畴 C，上的 Span(C) 正如 Construction/Span/Category.v 的标题所述，实际上是一个双范畴，通过 apex-iso 的商可以恢复一个严格的一范畴（Span(Set) 包含 Rel）；它的推挤镜 Cospan(C) 位于 Construction/Cospan/Category.v；环上的双模是 nLab 所称的许多类似示例的原型；而二函子通过一个共端来复合，其单位和结合律在 Construction/Profunctor/Laws.v 中得以发展。

在同一篇1967年的论文中观察到的主要结论是一个口号：一个小范畴是在集合跨度双范畴中的一个幺半范畴。在 Span(Set) 中，集合 A₀ 上的一个幺半范畴是一个跨度 A₀ ← A₁ → A₀（对象、态射、起点和终点），带有一个乘法 A₁ ×_{A₀} A₁ → A₁（组合）和一个单位 A₀ → A₁（恒等元），其幺半范畴公理即为范畴公理。改变所处的环境双范畴会使这个口号具体化：Prof 中的幺半范畴是一个前幺半范畴，即 Hughes 箭头的范畴内容，也是前函子光学（profunctor optics）的应用背景（Milewski，《Promonads, Arrows, and Einstein Notation for Profunctors》，2019；Clarke 等，《Profunctor Optics, a Categorical Update》，arXiv 2020）。更广义地说，双范畴是一种在其中通过一个普遍构造给出的组合被建模而无需断言它没有的严格相等性的结构。

双范畴内部的伴随，以及伴随对应——它们引起的 2-胞的双射——是 2-范畴工具箱，用于提升、迁移和 Beck-Chevalley 方形 (Kelly, Street 1974)；in-tree 开发给出了 Theory/Bicategory/Adjunction.v 中的内部伴随，Theory/Bicategory/Mates.v 中的 Kelly-Street 伴随演算，Theory/Bicategory/Pseudofunctor.v 中的伪函子（弱 2-函子），以及 Theory/Bicategory/Lax.v 和 Theory/Bicategory/Modification.v 中的松变换和修饰，其中 Cat 中的双范畴伴随被证明与 Instance/Cat/Bicategory/Adjunction.v 中的 F ⊣ U 一致。相干性定理 (Mac Lane, Paré 1985) 显示每个双范畴同双等价于严格 2-范畴，尽管自然出现的例子是弱形式呈现的；Theory/DoubleCategory.v 交叉引用了此处使用的 [hassoc] 方向。
*)

(*
From https://ncatlab.org/nlab/show/bicategory#detailedDefn :

{In the following text, → matches ~> in this library, and ⇒ matches ~~>}

A bicategory B consists of

- a collection Ob[B] of objects or 0-cells,
- for each object a and object b,
  a collection B(a,b) or Hom[B](a,b)
  of morphisms or 1-cells a → b, and
- for each object a, object b, morphism f:a → b, and morphism g:a → b,
  a collection B(f,g) or 2Hom[B](f,g)
  of 2-morphisms or 2-cells f ⇒ g or f ⇒ g:a → b,

equipped with

- for each object a,
  an identity 1[a]:a → a or id[a]:a → a,
- for each a,b,c, f:a → b, and g:b → c,
  a composite f;g: a → c or g ∘ f:a → c,
- for each f:a → b,
  an identity or 2-identity 1[f]:f ⇒ f or Id[f]:f → f,
- for each f,g,h:a → b, η:f ⇒ g, and θ:g ⇒ h,
  a vertical composite θ ∙ η:f ⇒ h,
- for each a,b,c, f,g:a → b, h:b → c, and η:f ⇒ g,
  a left whiskering h ⊲ η:h ∘ f ⇒ h ∘ g,
- for each a,b,c, f:a → b, g,h:b → c, and η:g ⇒ h,
  a right whiskering η ⊳ f:g ∘ f ⇒ h ∘ f,
- for each f:a → b,
  a left unitor λ[f]:id[b] ∘ f ⇒ f,
  and an inverse left unitor λ⁻¹[f]:f ⇒ id[b] ∘ f,
- for each f:a → b,
  a right unitor ρ[f]:f ∘ id[a] ⇒ f
  and an inverse right unitor ρ⁻¹[f]:f ⇒ f ∘ id[a], and
- for each a →[f] b →[g] c →[h] d,
  an associator α[h,g,f]:(h ∘ g) ∘ f ⇒ h ∘ (g ∘ f)
  and an inverse associator α⁻¹[h,g,f]: h ∘ (g ∘ f) ⇒ (h ∘ g) ∘ f,

such that

- for each η:f ⇒ g:a → b,
  the vertical composites η ∙ Id[f] and Id[g] ∙ η both equal η,
- for each f ⇒[η] g ⇒[θ] h ⇒[ι] i:a → b,
  the vertical composites ι ∙ (θ ∙ η) and (ι ∙ θ) ∙ η are equal,
- for each a →[f] b →[g] c,
  the whiskerings Id[g] ⊳ f and g ⊲ Id[f]; both equal Id[g ∘ f],
- for each f ⇒[η] g ⇒[θ] h:a → b and i:b → c,
  the vertical composite (i ⊲ θ) ∙ (i ⊲ η) equals the whiskering i ⊲ (θ ∙ η),
- for each f:a → b and g ⇒[η] h ⇒[θ] i:b → c,
  the vertical composite (θ ⊳ f) ∙ (η ⊲ f) equals the whiskering (θ ∙ η) ⊳ f,
- for each η:f ⇒ g:a → b,
  the vertical composites λ[g] ∙ (id[b] ⊲ η) and η ∙ λ[f] are equal,
- for each η:f ⇒ g:a → b,
  the vertical composites ρ[g] ∙ (η ⊳ id[a]) and η ∙ ρ[f] are equal,
- for each a →[f] b →[g] c and η:h ⇒ i:c → d,
  the vertical composites α⁻¹[i,g,f] ∙ (η ⊳ (g ∘ f))
  and ((η ⊳ g) ⊳ f) ∙ α⁻¹[h,g,f] are equal,
- for each f:a → b, η:g ⇒ h:b → c, and i:c → d,
  the vertical composites α⁻¹[i,h,f] ∙ (i ⊲ (η ⊳ f))
  and ((i ⊲ η) ⊳ f) ∙ α⁻¹[i,g,f] are equal,
- for each η:f ⇒ g:a → b and b →[h] c →[i] d,
  the vertical composites α⁻¹[i,h,g] ∙ (i ⊲ (h ⊲ η))
  and ((i ∘ h) ⊲ η) ∙ α⁻¹[i,h,f] are equal,
- for each η:f ⇒ g:a → b and θ:h ⇒ i:b → c,
  the vertical composites (i ⊲ η) ∙ (θ ⊳ f) and (θ ⊳ g) ∙ (h ⊲ η) are equal,
- for each f:a → b,
  the vertical composites λ[f] ∙ λ⁻¹[f]:f ⇒ f
  and λ⁻¹[f] ∙ λ[f]:id[b] ∘ f ⇒ id[b] ∘ f
  equal the appropriate identity 2-morphisms,
- for each f:a → b,
  the vertical composites ρ[f] ∙ ρ⁻¹[f]:f ⇒ f
  and ρ⁻¹[f] ∙ ρ[f]:f ∘ id[a] ⇒ f ∘ id[a]
  equal the appropriate identity 2-morphisms,
- for each a →[f] b →[g] c →[h] d,
  the vertical composites α⁻¹[h,g,f] ∙ α[h,g,f]:(h ∘ g) ∘ f ⇒ (h ∘ g) ∘ f
  and α[h,g,f] ∙ α⁻¹[h,g,f]:h ∘ (g ∘ f) ⇒ h ∘ (g ∘ f)
  equal the appropriate identity 2-morphisms,
- for each a →[f] b →[g] c,
  the vertical composite (ρ[g] ⊳ f) ∙ α⁻¹[g,id[b],f]
  equals the whiskering g ⊲ λ[f], and
- for each a →[f] b →[g] c →[h] d →[i] e,
  the vertical composites ((α⁻¹[i,h,g] ⊳ f) ∙ α⁻¹[i,h∘g,f]) ∙ (i ⊲ α⁻¹[h,g,f])
  and α⁻¹[i∘h,g,f] ∙ α⁻¹[i,h,g∘f] are equal.

--------
来自 https://ncatlab.org/nlab/show/bicategory#detailedDefn ：

{在下面的文本中，→ 匹配此库中的 ~>，⇒ 匹配 ~~>}

双范畴 B 包括

- 对象或 0 单元格的 Ob[B] 集合，
 - 对于每个对象 a 和对象 b，
 集合 B(a,b) 或 Hom[B](a,b)
 态射或 1-cell a → b，以及
 - 对于每个对象 a、对象 b，态射 f:a → b 和态射 g:a → b，
 集合 B(f,g) 或 2Hom[B](f,g)
 2-态射或 2-细胞 f ⇒ g 或 f ⇒ g:a → b，

配备有

- 对于每个对象a，
 恒等 1[a]:a → a 或 id[a]:a → a，
 - 对于每个 a、b、c、f:a → b 和 g:b → c，
 复合 f;g: a → c 或 g ∘ f:a → c，
 - 对于每个 f:a → b，
 一个恒等式或 2-恒等式 1[f]:f ⇒ f 或 Id[f]:f → f，
 - 对于每个 f,g,h:a → b, η:f ⇒ g 和 θ:g ⇒ h，
 垂直复合 θ ∙ η:f ⇒ h，
 - 对于每个 a,b,c, f,g:a → b, h:b → c 和 η:f ⇒ g，
 a 左晶须 h ⊲ η:h ∘ f ⇒ h ∘ g,
 - 对于每个 a,b,c, f:a → b, g,h:b → c 和 η:g ⇒ h，
 右晶须 η ⊳ f:g ∘ f ⇒ h ∘ f,
 - 对于每个 f:a → b，
 左单位 λ[f]:id[b] ∘ f ⇒ f,
 和一个逆左单位 λ⁻1[f]:f ⇒ id[b] ∘ f，
 - 对于每个 f:a → b，
 右单位 ρ[f]:f ∘ id[a] ⇒ f
 和逆右单位 ρ⁻1[f]:f ⇒ f ∘ id[a]，以及
 - 对于每个 a →[f] b →[g] c →[h] d，
 关联器 α[h,g,f]:(h ∘ g) ∘ f ⇒ h ∘ (g ∘ f)
 和逆关联子 α⁻1[h,g,f]： h ∘ (g ∘ f) ⇒ (h ∘ g) ∘ f，

这样

- 对于每个 η:f ⇒ g:a → b，
 垂直复合 η ∙ Id[f] 和 Id[g] ∙ η 均等于 η，
 - 对于每个 f ⇒[η] g ⇒[θ] h ⇒[ι] i:a → b，
 垂直复合 ι ∙ (θ ∙ η) 和 (ι ∙ θ) ∙ η 相等，
 - 对于每个 a →[f] b →[g] c，
 晶须 Id[g] ⊳ f 和 g ⊲ Id[f]； 两者都等于 Id[g ∘ f]，
 - 对于每个 f ⇒[η] g ⇒[θ] h:a → b 和 i:b → c，
 垂直复合 (i ⊲ θ) ∙ (i ⊲ η) 等于晶须 i ⊲ (θ ∙ η)，
 - 对于每个 f:a → b 和 g ⇒[η] h ⇒[θ] i:b → c，
 垂直复合 (θ ⊳ f) ∙ (η ⊲ f) 等于晶须 (θ ∙ η) ⊳ f，
 - 对于每个 η:f ⇒ g:a → b，
 垂直复合 λ[g] ∙ (id[b] ⊲ η) 和 η ∙ λ[f] 相等，
 - 对于每个 η:f ⇒ g:a → b，
 垂直复合 ρ[g] ∙ (η ⊳ id[a]) 和 η ∙ ρ[f] 相等，
 - 对于每个 a →[f] b →[g] c 和 η:h ⇒ i:c → d，
 垂直复合 α⁻1[i,g,f] ∙ (η ⊳ (g ∘ f))
 和 ((η ⊳ g) ⊳ f) ∙ α⁻1[h,g,f] 相等，
 - 对于每个 f:a → b、 η:g ⇒ h:b → c 和 i:c → d，
 垂直复合 α⁻1[i,h,f] ∙ (i ⊲ (η ⊳ f))
 和 ((i ⊲ η) ⊳ f) ∙ α⁻1[i,g,f] 相等，
 - 对于每个 η:f ⇒ g:a → b 和 b →[h] c →[i] d，
 垂直复合 α⁻1[i,h,g] ∙ (i ⊲ (h ⊲ η))
 和 ((i ∘ h) ⊲ η) ∙ α⁻¹[i,h,f] 相等，
 - 对于每个 η:f ⇒ g:a → b 和 θ:h ⇒ i:b → c，
 垂直复合 (i ⊲ η) ∙ (θ ⊳ f) 和 (θ ⊳ g) ∙ (h ⊲ η) 相等，
 - 对于每个 f:a → b，
 垂直复合 λ[f] ∙ λ⁻¹[f]:f ⇒ f
 和 λ⁻1[f] ∙ λ[f]:id[b] ∘ f ⇒ id[b] ∘ f
 等于适当的恒等式 2-态射，
 - 对于每个 f:a → b，
 垂直复合材料 ρ[f] ∙ ρ⁻¹[f]:f ⇒ f
 和 ρ⁻1[f] ∙ ρ[f]:f ∘ id[a] ⇒ f ∘ id[a]
 等于适当的恒等式 2-态射，
 - 对于每个 a →[f] b →[g] c →[h] d，
 垂直复合 α⁻1[h,g,f] ∙ α[h,g,f]:(h ∘ g) ∘ f ⇒ (h ∘ g) ∘ f
 和 α[h,g,f] ∙ α⁻1[h,g,f]:h ∘ (g ∘ f) ⇒ h ∘ (g ∘ f)
 等于适当的恒等式 2-态射，
 - 对于每个 a →[f] b →[g] c，
 垂直复合 (ρ[g] ⊳ f) ∙ α⁻¹[g,id[b],f]
 等于晶须 g ⊲ λ[f]，并且
 - 对于每个 a →[f] b →[g] c →[h] d →[i] e，
 垂直复合材料 ((α⁻1[i,h,g] ⊳ f) ∙ α⁻1[i,h∘g,f]) ∙ (i ⊲ α⁻1[h,g,f])
 和 α⁻1[i∘h,g,f] ∙ α⁻1[i,h,g∘f] 相等。
*)

Class Bicategory := {
  bi0cell : Type;                       (* collection of 0-cells (objects) / 0-胞（对象）的集合 *)

  bi1uhom := Type : Type;               (* universe of 1-cell collections / 单细胞集合的宇宙 *)
  bi1cell : bi0cell → bi0cell → bi1uhom (* 1-cells a ~~> b / 1-胞 a ~~> b *)
    where "a ~~> b" := (bi1cell a b);

  bi2uhom := Type : Type;               (* universe of 2-cell collections / 由双细胞集合构成的宇宙 *)
  bi2cell {x y : bi0cell} (f g : bi1cell x y) : bi2uhom  (* 2-cells f ~~~> g / 2-胞 f ~~~> g *)
    where "f ~~~> g" := (bi2cell f g);

  bi1id {x : bi0cell} : x ~~> x;        (* identity 1-cell on a 0-cell / 0-胞上的1-胞恒等 *)

  bi2homset {x y : bi0cell} : ∀ X Y : bi1cell x y, Setoid (@bi2cell x y X Y);
                                        (* 2-cells form a hom-setoid (≈) / 2-胞形成一个同态集(≈) *)

  bi2id {x y : bi0cell} {a : bi1cell x y} : a ~~~> a;  (* identity 2-cell on a 1-cell / 1-胞上的2-胞恒等 *)

  vcompose {x y : bi0cell} {a b c : bi1cell x y}      (* vertical 2-cell composition / 垂直双胞结构 *)
           (f : b ~~~> c) (g : a ~~~> b) : a ~~~> c
    where "f ∘∘ g" := (vcompose f g);

  vcompose_respects x y a b c :         (* vertical composition respects ≈ / 垂直构图尊重 ≈ *)
    Proper (equiv ==> equiv ==> equiv) (@vcompose x y a b c);

  bi2id_left  {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : bi2id ∘∘ f ≈ f;
                                        (* left unit law for vertical composition / 垂直组合的左单位律 *)
  bi2id_right {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : f ∘∘ bi2id ≈ f;
                                        (* right unit law for vertical composition / 垂直组合的右单位律 *)

  vcompose_assoc {x y : bi0cell} {a b c d : bi1cell x y}  (* associativity of vertical comp. / 垂直组合的结合性 *)
                 (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    f ∘∘ (g ∘∘ h) ≈ (f ∘∘ g) ∘∘ h;
  vcompose_assoc_sym {x y : bi0cell} {a b c d : bi1cell x y}  (* dual form (built-in duality) / 双重形式（内置二元性） *)
                     (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    (f ∘∘ g) ∘∘ h ≈ f ∘∘ (g ∘∘ h);

  bicat (x y : bi0cell) : Category := {|  (* hom-category B(x,y): 1-cells / 2-cells / 同态范畴 B(x,y)：1-态 / 2-态 *)
    obj              := @bi1cell x y;
    hom              := @bi2cell x y;
    homset           := @bi2homset x y;
    id               := @bi2id x y;
    compose          := @vcompose x y;
    compose_respects := @vcompose_respects x y;
    id_left          := @bi2id_left x y;
    id_right         := @bi2id_right x y;
    comp_assoc       := @vcompose_assoc x y;
    comp_assoc_sym   := @vcompose_assoc_sym x y;
  |};

  hcompose {x y z : bi0cell} : bicat y z ∏ bicat x y ⟶ bicat x z
    where "f ∘∘∘ g" := (hcompose (f, g));  (* horizontal composition functor / 水平组合函子 *)

  (*
The horizontal composite of two 2-cells (Godement whiskering), obtained as
     the functorial action of `hcompose` on the pair. This is a manifest field:
     it is a definition, not new data, so it computes to the underlying
     bifunctor's `fmap`. All the coherence laws below are phrased through it.

--------
两个 2-胞腔的水平合成（Godement 打毛），通过 `hcompose` 对该对的函子作用得到。这是一个显式字段：它是一个定义，而不是新的数据，因此它计算为基础双函子的 `fmap`。下面的所有相容性法则都是通过它表述的。
*)
  hcomp2 {x y z : bi0cell} {g g' : bicat y z} {f f' : bicat x y}
         (θ : g ~{bicat y z}~> g') (η : f ~{bicat x y}~> f') :
    (g ∘∘∘ f) ~{bicat x z}~> (g' ∘∘∘ f')
    := @fmap _ _ (@hcompose x y z) (g, f) (g', f') (θ, η);

  (*
The coherence 2-isomorphisms of a bicategory, living in the hom-categories
     `bicat _ _` and mirroring the unitors and associator of a monoidal
     category (`Structure/Monoidal.v`), with tensor ↔ hcompose, I ↔ bi1id.

--------
二范畴的相干二同态，存在于同态范畴 `bicat _ _` 中，并反映了单范畴 (`Structure/Monoidal.v`) 的幺元子和结合子，其中张量 ↔ hcompose，I ↔ bi1id。
*)

  hunit_left  {x y : bi0cell} (f : bicat x y) :   (* left  unitor λ[f] / 左单元 λ[f] *)
    (bi1id ∘∘∘ f) ≅[bicat x y] f;
  hunit_right {x y : bi0cell} (f : bicat x y) :   (* right unitor ρ[f] / 右单位器 ρ[f] *)
    (f ∘∘∘ bi1id) ≅[bicat x y] f;
  hassoc {w x y z : bi0cell}                      (* associator α[h,g,f] / 结合子 α[h,g,f] *)
         (h : bicat y z) (g : bicat x y) (f : bicat w x) :
    ((h ∘∘∘ g) ∘∘∘ f) ≅[bicat w z] (h ∘∘∘ (g ∘∘∘ f));

  (*
The unitors and the associator are natural in their 1-cell arguments; each
     square is the horizontal-composition analogue of the monoidal naturality
     of λ, ρ and α (the `to`-direction; the `from`-direction follows since these
     are isomorphisms).

--------
单位器和结合器在它们的 1-胞元参数中是自然的；每个方形是 λ、ρ 和 α 的单体自然性的水平组合类比（`to` 方向；由于它们是同构，`from` 方向也随之成立）。
*)

  hunit_left_natural {x y : bi0cell} {f f' : bicat x y}
                     (η : f ~{bicat x y}~> f') :
    η ∘∘ to (hunit_left f) ≈ to (hunit_left f') ∘∘ hcomp2 (bi2id (a:=bi1id)) η;
  hunit_right_natural {x y : bi0cell} {f f' : bicat x y}
                      (η : f ~{bicat x y}~> f') :
    η ∘∘ to (hunit_right f) ≈ to (hunit_right f') ∘∘ hcomp2 η (bi2id (a:=bi1id));
  hassoc_natural {w x y z : bi0cell}
      {h h' : bicat y z} {g g' : bicat x y} {f f' : bicat w x}
      (θ : h ~{bicat y z}~> h') (γ : g ~{bicat x y}~> g') (η : f ~{bicat w x}~> f') :
    hcomp2 θ (hcomp2 γ η) ∘∘ to (hassoc h g f)
      ≈ to (hassoc h' g' f') ∘∘ hcomp2 (hcomp2 θ γ) η;

  (*
The two coherence laws: the triangle relates the unitors to the associator
     across `bi1id`, and the pentagon makes the two reassociations of a fourfold
     horizontal composite agree. Endpoints mirror `Monoidal.triangle_identity`
     and `Monoidal.pentagon_identity` exactly.

--------
两个相干律：三角形将单位子与结合子在 `bi1id` 上联系起来，五边形使四重水平复合的两次重关联一致。端点准确地对应 `Monoidal.triangle_identity` 和 `Monoidal.pentagon_identity`。
*)

  hcoherence_triangle {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
    hcomp2 (to (hunit_right g)) (bi2id (a:=f))
      ≈ hcomp2 (bi2id (a:=g)) (to (hunit_left f)) ∘∘ to (hassoc g bi1id f);
  hcoherence_pentagon {v w x y z : bi0cell}
      (k : bicat y z) (h : bicat x y) (g : bicat w x) (f : bicat v w) :
    hcomp2 (bi2id (a:=k)) (to (hassoc h g f))
      ∘∘ to (hassoc k (h ∘∘∘ g) f)
      ∘∘ hcomp2 (to (hassoc k h g)) (bi2id (a:=f))
      ≈ to (hassoc k h (g ∘∘∘ f)) ∘∘ to (hassoc (k ∘∘∘ h) g f)
}.
#[export] Existing Instance bi2homset.
#[export] Existing Instance vcompose_respects.

(*
Smart constructor for [Bicategory], mirroring [Build_Category']: it takes
   every field except `vcompose_assoc_sym` and supplies that symmetric form
   automatically as `symmetry (vcompose_assoc …)`. This is “what symmetry
   permits” — the dual orientation of vertical associativity carries no extra
   content — and keeps duality definitional exactly as in [Category]. Intended
   for use with `unshelve refine`, leaving the coherence obligations as goals.

--------
[Bicategory] 的智能构造函数，类似于 [Build_Category']：它接受除了 `vcompose_assoc_sym` 之外的每个字段，并自动将该对称形式作为 `symmetry (vcompose_assoc …)` 提供。这是“对称所允许的”——垂直结合的双重方向不包含额外内容——并且保持双重性定义与 [Category] 完全相同。旨在与 `unshelve refine` 一起使用，将一致性义务作为目标保留。
*)
Definition Build_Bicategory'
    bi0cell bi1cell bi2cell bi1id bi2homset bi2id
    vcompose vcompose_respects bi2id_left bi2id_right vcompose_assoc
    hcompose hunit_left hunit_right hassoc
    hunit_left_natural hunit_right_natural hassoc_natural
    hcoherence_triangle hcoherence_pentagon :=
  @Build_Bicategory bi0cell bi1cell bi2cell bi1id bi2homset bi2id
    vcompose vcompose_respects bi2id_left bi2id_right vcompose_assoc
    (fun x y a b c d f g h => symmetry (vcompose_assoc x y a b c d f g h))
    hcompose hunit_left hunit_right hassoc
    hunit_left_natural hunit_right_natural hassoc_natural
    hcoherence_triangle hcoherence_pentagon.
