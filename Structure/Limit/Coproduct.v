Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(* * * Indexed coproducts, as indexed products in the opposite category / * * 指数余积，作为对偶范畴中的指数积 *)

(*
 nLab:      https://ncatlab.org/nlab/show/coproduct
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 An [A]-indexed coproduct of a family [f : A → C] is an object [p] together
 with a family of injections [inj a : f a ~> p] that is universal: every
 competing family [iota a : f a ~> c] factors through the injections by a
 unique mediating map [u : p ~> c] with [u ∘ inj a ≈ iota a] for every [a].
 That is precisely the [A]-indexed product of [f] read in [C^op], and this
 file takes it as the definition.  Two files in the tree already dualize
 this way, by two different mechanisms.  Structure/Cocartesian.v states
 the idea -- "To be cocartesian is just to be cartesian in the opposite
 category" -- and realizes it with a NOTATION pair, [Notation "'Cocartesian'
 C" := (@Cartesian (C^op))].  [Comonad] instead uses a
 [Definition], [Comonad := @Monad (C^op) (M^op)] at Theory/Monad.v,
 with [Existing Class Comonad] declared separately in the API module at
 Comonad/Core.v.  This file follows the second, splitting [Definition]
 from [Existing Class] in exactly that way; see below for why.

 WHAT IS NEW HERE AND WHAT IS NOT.  No constant below carries a proof
 obligation.  Each is a definitional re-reading, at [C^op], of a constant of
 Structure/Limit/Product.v:

 [IsIndexedCoproduct f p inj]    is  [@IsIndexedProduct (C^op) A f p inj]
 [icoprod f L]                   is  [@iprod (C^op) A f L]
 [icoprod_inj f L]               is  [@iprod_proj (C^op) A f L]
 [icoprod_ump f L]               is  [@iprod_ump (C^op) A f L]
 [colimit_is_indexed_coproduct]  is  [@limit_is_indexed_product (C^op)]
 [HasIndexedCoproducts C]        is  [@HasIndexedProducts (C^op)]

 What the file adds is the covariant reading.  [icoprod_desc] and the three
 [indexed_coproduct*] accessors state the universal property with arrows in
 [C] rather than [C^op]; [Build_IsIndexedCoproduct] and
 [Build_HasIndexedCoproducts] let a caller supply the data in that same
 covariant form.  Each is its product counterpart applied at [C^op] with no
 step beyond [C^op]'s definitional unfolding of [hom], [compose] and
 [homset] (Construction/Opposite.v).

 [HasIndexedCoproducts] is a [Definition] with [Existing Class] declared
 immediately after, rather than a [Class] of its own.  Typeclass resolution
 keys on the head constant of a goal and does not look through the
 unfolding, so without the declaration a coproduct witness in scope would
 not be found for the implicit argument of the accessors below.  That is
 the reasoning recorded at Comonad/Core.v for [Comonad], the
 [Definition]-plus-[Existing Class] precedent this file follows.  (One
 difference: [Comonad]'s two halves are deliberately kept in separate files,
 the definition in Theory/Monad.v and the class declaration in the API
 module, so that library-wide class resolution is not imposed on the bare
 definition.  Here there is only one file, so both sit together.)

 COLIMIT PRESENTATION.  [icoprod] and its companions read a [Limit] of the
 discrete diagram taken IN [C^op], namely
 [Limit (@DiscreteCat_Functor A (C^op) f)] -- not a [Colimit] in the sense
 of Structure/Limit.v, which sets [Colimit F := Limit (F^op)] and so
 indexes over [(DiscreteCat A)^op].  The hom from [x] to [y] is [x = y] in
 [DiscreteCat A] (Instance/Discrete.v) and [y = x] in its opposite
 (Construction/Opposite.v), and Coq does not identify the two categories:
 [eq_refl : (DiscreteCat A)^op = DiscreteCat A] is rejected, "cannot unify".
 (Checked outside the tree, so that the [make todo] scan stays clean.)  A
 translation between the two shapes is not given here, and no consumer in
 this development calls for one.

 STATUS: axiom-free, and free of new proof: the first inhabitant is
 [Sets_HasIndexedCoproducts] in Instance/Sets/Products.v, audited by the
 Makefile's [print-assumptions] target.  No finiteness is assumed -- [A] is
 an arbitrary [Type] -- but the ambient category may constrain the universe
 [A] lives at; see the header of Instance/Sets/Products.v for exactly what
 that constraint comes to at [Sets]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/coproduct 
 维基百科:  https://en.wikipedia.org/wiki/Coproduct一个 [A] 索引的 [f : A → C] 家族的余积是一个对象 [p]，以及一族注入 [inj a : f a ~> p]，它具有普遍性：每一个竞争性家族 [iota a : f a ~> c] 都通过唯一的中介映射 [u : p ~> c] 因注入而分解，且对每个 [a] 都满足 [u ∘ inj a ≈ iota a]。那正是 [C^op] 中的 [f] 的 [A] 索引的积，并且本文件以此作为定义。树中的两个文件已经以两种不同的机制对其进行了对偶化。Structure/Cocartesian.v 表述了这一想法——“要成为余积，仅仅是在对偶范畴中成为积”——并且通过一对符号实现了它，[Notation "'Cocartesian' C" := (@Cartesian (C^op))]。[Comonad] 取而代之的是使用 [Definition]、[Comonad := @Monad (C^op) (M^op)] 于 Theory/Monad.v 中，同时 [Existing Class Comonad] 在 Comonad/Core.v 的 API 模块中单独声明。该文件遵循第二种方式，将 [Definition] 从 [Existing Class] 中完全以这种方式拆分；如下所示说明原因。

 这里的新内容和非新内容。下面没有常量带有证明义务。每一个都是在 [C^op] 中对 Structure/Limit/Product.v 中常量的定义性重新释读：

 [IsIndexedCoproduct f p inj]     是   [@IsIndexedProduct (C^op) A f p inj] 
 [icoprod f L]                    是   [@iprod (C^op) A f L] 
 [icoprod_inj f L]                是   [@iprod_proj (C^op) A f L] 
 [icoprod_ump f L]                是   [@iprod_ump (C^op) A f L] 
 [colimit_is_indexed_coproduct]   是   [@limit_is_indexed_product (C^op)] 
 [HasIndexedCoproducts C]         是   [@HasIndexedProducts (C^op)]该文件增加了协变读取功能。[icoprod_desc] 和三个 [indexed_coproduct*] 访问器通过 [C] 中的箭头而不是 [C^op] 来描述泛性质；[Build_IsIndexedCoproduct] 和 [Build_HasIndexedCoproducts] 允许调用者以相同的协变形式提供数据。每个都是其在 [C^op] 上应用的积的对应项，并且没有超出 [C^op] 对 [hom]、[compose] 和 [homset]（Construction/Opposite.v）的定义展开步骤。[HasIndexedCoproducts] 是一个 [Definition]，并且在其之后立即声明了 [Existing Class]，而不是拥有自己的 [Class]。类型类的解析是基于目标的头常量，并不会透过展开去查看，所以如果没有该声明，作用域中的协同积见证将无法被找到作为下面访问器的隐式参数。这就是在 Comonad/Core.v 中记录的 [Comonad] 的推理，这个文件遵循了 [Definition] 加上 [Existing Class] 的先例。（一个区别是：[Comonad] 的两个部分被故意保存在不同的文件中，Theory/Monad.v 中为定义，API 模块中为类声明，这样库范围的类解析不会强加于纯定义上。这里只有一个文件，所以它们在一起。）余极限表示。[icoprod]及其相关项读取在[C^op]中离散图的[Limit]，即[Limit (@DiscreteCat_Functor A (C^op) f)]——不是Structure/Limit.v意义下的[Colimit]，它设定[Colimit F := Limit (F^op)]并因此在[(DiscreteCat A)^op]上索引。从[x]到[y]的态射在[DiscreteCat A]（Instance/Discrete.v）中是[x = y]，而在其对偶（Construction/Opposite.v）中是[y = x]，且Coq不会将这两个范畴识别为相同：[eq_refl : (DiscreteCat A)^op = DiscreteCat A]被拒绝，‘无法统一’。（在树外检查，以保持[make todo]扫描的整洁。）此处没有给出这两种形状之间的转换，并且在此开发中没有消费者调用该转换。状态：无公理，并且没有新的证明：第一个元素是 Instance/Sets/Products.v 中的 [Sets_HasIndexedCoproducts]，由 Makefile 的 [print-assumptions] 目标审核。没有假设有限性——[A] 是任意的 [Type]——但环境类别可能限制 [A] 所在的宇宙；请参见 Instance/Sets/Products.v 的头部，了解该约束在 [Sets] 时具体是怎样的。
*)

Definition IsIndexedCoproduct {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) : Type :=
  @IsIndexedProduct (C^op) A f p inj.

Definition icoprod_desc {C : Category} {A : Type} {f : A → C} {p : C}
  {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj)
  {c : C} (iota : ∀ a : A, f a ~> c) :
  ∃! u : p ~> c, ∀ a : A, u ∘ inj a ≈ iota a :=
  @iprod_desc (C^op) A f p inj H c iota.

Definition Build_IsIndexedCoproduct {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p)
  (desc : ∀ (c : C) (iota : ∀ a : A, f a ~> c),
            ∃! u : p ~> c, ∀ a : A, u ∘ inj a ≈ iota a) :
  IsIndexedCoproduct f p inj :=
  @Build_IsIndexedProduct (C^op) A f p inj desc.

Definition icoprod {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) : C :=
  @iprod (C^op) A f L.

Definition icoprod_inj {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) (a : A) : f a ~> icoprod f L :=
  @iprod_proj (C^op) A f L a.

Definition icoprod_ump {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f))
  (c : C) (iota : ∀ a : A, f a ~> c) :
  ∃! u : icoprod f L ~> c, ∀ a : A, u ∘ icoprod_inj f L a ≈ iota a :=
  @iprod_ump (C^op) A f L c iota.

Definition colimit_is_indexed_coproduct {C : Category} {A : Type} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) :
  IsIndexedCoproduct f (icoprod f L) (icoprod_inj f L) :=
  @limit_is_indexed_product (C^op) A f L.

Definition HasIndexedCoproducts (C : Category) : Type :=
  @HasIndexedProducts (C^op).

Existing Class HasIndexedCoproducts.

Definition Build_HasIndexedCoproducts {C : Category}
  (cobj : ∀ A : Type, (A → C) → C)
  (cinj : ∀ (A : Type) (f : A → C) (a : A), f a ~> cobj A f)
  (cump : ∀ (A : Type) (f : A → C),
            IsIndexedCoproduct f (cobj A f) (cinj A f)) :
  HasIndexedCoproducts C :=
  @Build_HasIndexedProducts (C^op) cobj cinj cump.

Section IndexedCoproductAPI.

Context {C : Category}.
Context {H : HasIndexedCoproducts C}.

Definition indexed_coproduct {A : Type} (f : A → C) : C :=
  @indexed_product (C^op) H A f.

Definition indexed_coproduct_inj {A : Type} (f : A → C) (a : A) :
  f a ~> indexed_coproduct f :=
  @indexed_product_proj (C^op) H A f a.

Definition indexed_coproduct_ump {A : Type} (f : A → C) :
  IsIndexedCoproduct f (indexed_coproduct f) (indexed_coproduct_inj f) :=
  @indexed_product_ump (C^op) H A f.

End IndexedCoproductAPI.
