Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(*
   * * Base change: reindexing coloured PROPs along a colour function 

   --------
   * * 基变换：沿颜色函数重新索引彩色 PROP
*)

(*
 nLab: https://ncatlab.org/nlab/show/base+change
 nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 A function [f : Colour → Colour'] between colour sets induces a
 monoid homomorphism [map f : list Colour → list Colour'] between the
 free monoids of colour words, and along it two constructions:

 1.  RESTRICTION OF SCALARS ([ColouredPROP_restrict]): every coloured
 PROP [P] over [Colour'] becomes a coloured PROP over [Colour] on
 the SAME underlying category, by reading the object
 correspondence through [map f]:

 cprop_of_list cs := cprop_of_list (map f cs).

 Only the object-naming data changes; the category, its strict
 and symmetric monoidal structures, and their coherence are
 carried over verbatim, so the [cprop_monoidal_coherence] field
 — the fragile one, per the discussion in [Construction/PROP.v]
 — is P's own proof, untouched.  The unit condition holds
 because [map f [] ≡ []] is definitional, and the tensor
 condition is P's own [cprop_tensor_app] composed with the image
 of [map_app f cs ds : map f (cs ++ ds) = map f cs ++ map f ds]
 — the one genuinely propositional seam in the whole
 construction (stdlib's [map_app] is opaque).

 2.  THE BASE-CHANGE FUNCTOR ([BaseChangeF]): a signature morphism
 OVER [f] — a boundary-reindexing generator map

 h : ∀ cs ds, S cs ds → S' (map f cs) (map f ds)

 ([CSigMap]) — induces a strict symmetric monoidal functor
 [CFreeCat S ⟶ CFreeCat S'] between the free coloured PROPs,
 acting on objects by [map f] and sending each generator [g] to
 [CT_gen (h _ _ g)].

 ** Design: the functor is built THROUGH the universal property

 Rather than writing a fresh term-recursion and re-proving the
 19-case [CTermEq] soundness induction, [BaseChangeF] is one
 instantiation of the free coloured PROP's universal property
 ([Construction/ColouredPROP/Universal.v]): the target of the
 interpretation is the RESTRICTION of [FreeColouredPROP S' C'dec]
 along [f].  In that restriction the hom-set
 [⟦cs⟧ ~> ⟦ds⟧] IS [CTerm S' (map f cs) (map f ds)] on the nose, so
 the valuation [basechange_val := fun _ _ g => CT_gen (h _ _ g)]
 typechecks with no casts, and [CInterpF] delivers the functor
 together with its entire monoidal tower — [CInterpF_Monoidal] /
 [CInterpF_Strict] / [CInterpF_Braided] / [CInterpF_Symmetric] /
 [CInterpF_SymmetricStrict] instantiate to the [BaseChangeF_*]
 records below — and, downstream, its functoriality laws come from
 the uniqueness theorem [cinterp_unique] (see
 [Construction/ColouredPROP/BaseChange/Laws.v]) rather than from
 fresh inductions.

 Because [cinterp] COMPUTES on constructors, the functor's action is
 definitional where it matters: objects go to [map f cs], generators
 to [CT_gen (h _ _ g)], identities to identities and composites to
 composites, each machine-checked by an [eq_refl] [Example] below.

 ** The strictness comparisons are NOT all reflexivity

 [strict_pure_obj] of [BaseChangeF_Strict] is [eq_refl] (the unit
 colour word is fixed by [map f] definitionally), but
 [strict_ap_obj cs ds] is the [map_app]-shaped composite

 eq_trans eq_refl (f_equal (fun ks => ks) (eq_sym (map_app f cs ds)))

 and CANNOT be [eq_refl]: for variable [cs], the colour words
 [map f cs ++ map f ds] and [map f (cs ++ ds)] are propositionally
 but not definitionally equal.  This is exactly the seam that the
 [hom_cast]-conjugated functoriality statements of
 [BaseChange/Laws.v] have to thread, so it is pinned here by
 [Example]s at its source.

 ** Deciders (D2 discipline)

 Two colour deciders circulate, one per colour type: [Cdec] for
 [Colour] (naming the source's shared [Monoidal] record
 [CFreeCat_Monoidal S Cdec]) and [C'dec] for [Colour'] (naming the
 target's, and supplying the [ObjDecEq] side condition of the
 universal property).  Per the D2 discipline of
 [Construction/ColouredPROP/Instance.v], both are explicit
 arguments, and each instance site should pass the ONE canonical
 decider of its colour type.

 Design alternative (not developed): a computing [C_base_map]
 Fixpoint on [CTerm] with cast-conjugated braid and tensor clauses
 would also yield the functor, at the cost of a fresh 19-case
 transport soundness induction mirroring [CT_map_CTermEq] of
 [Construction/ColouredPROP/Relabel.v].  The via-universal-property
 route delivers everything below without it, so the fixpoint form
 is left undeveloped. 

 --------
 nLab:  https://ncatlab.org/nlab/show/base+change 
 nLab:  https://ncatlab.org/nlab/show/restriction+of+scalars 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 Wikipedia:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 一个在颜色集合之间的函数  [f : Colour → Colour']  会诱导出一个在颜色词自由幺半群之间的幺半群同态  [map f : list Colour → list Colour'] ，以及沿着它的两个构造：

 1.  标量限制（RESTRICTION OF SCALARS）（[ColouredPROP_restrict]）：每一个在  [Colour']  上的带颜色PROP  [P]  都会变为在  [Colour]  上的带颜色PROP，使用相同的基础范畴，通过  [map f]  读取对象对应关系：

 cprop_of_list cs := cprop_of_list (map f cs).只有对象命名的数据发生变化；类别及其严格且对称的幺半群结构及其相干性都被照搬，因此 [cprop_monoidal_coherence] 字段——根据 [Construction/PROP.v] 的讨论，这是脆弱的——是 P 自己的证明，没有被修改。单位条件成立，因为 [map f [] ≡ []] 是定义性的，并且张量条件是 P 自己的 [cprop_tensor_app] 与 [map_app f cs ds : map f (cs ++ ds) = map f cs ++ map f ds] 的像组成的——这是整个构造中唯一真正命题性的缝隙（stdlib 的 [map_app] 是不透明的）。

 2. 基变换函子 ([BaseChangeF])：一个在 [f] 上的签名态射——一个边界重索引生成器映射

 h : ∀ cs ds, S cs ds → S' (map f cs) (map f ds)([CSigMap]) — 诱导一个严格的对称幺半范畴函子 [CFreeCat S ⟶ CFreeCat S']，在自由有色PROP之间，
 作用于对象通过 [map f]，并将每个生成元 [g] 映射到 [CT_gen (h _ _ g)]。

 ** 设计：该函子是通过泛性质构建的与其重新编写一个新的术语递归并重新证明 19 情况的 [CTermEq] 完整性归纳，不如 [BaseChangeF] 是自由有色 PROP 的普遍性质（[Construction/ColouredPROP/Universal.v]）的一次实例：解释的目标是沿 [f] 的 [FreeColouredPROP S' C'dec] 的限制。在该限制中，同态集 [⟦cs⟧ ~> ⟦ds⟧] 恰好是 [CTerm S' (map f cs) (map f ds)]，因此估值 [basechange_val := fun _ _ g => CT_gen (h _ _ g)] 类型检查无需强制转换，并且 [CInterpF] 提供了函子及其完整的单体塔 — [CInterpF_Monoidal] / [CInterpF_Strict] / [CInterpF_Braided] / [CInterpF_Symmetric] / [CInterpF_SymmetricStrict] 对应于下面的 [BaseChangeF_*] 记录 — 并且，在下游，其函子性定律来自唯一性定理 [cinterp_unique]（见 [Construction/ColouredPROP/BaseChange/Laws.v]），而不是来自新的归纳法。因为 [cinterp] 在构造函数上进行计算，所以函子在关键地方的作用是定义性的：对象映射到 [map f cs]，生成元映射到 [CT_gen (h _ _ g)]，恒等映射到恒等，组合映射到组合，每一个都由下面的 [eq_refl] [Example] 机器检查。

 ** 严格性比较并非全部是自反性

 [strict_pure_obj] 的 [BaseChangeF_Strict] 是 [eq_refl]（单位颜色词由 [map f] 定义地固定），但是 [strict_ap_obj cs ds] 是 [map_app] 形状的组合

 eq_trans eq_refl (f_equal (fun ks => ks) (eq_sym (map_app f cs ds)))并且不能是 [eq_refl]：对于变量 [cs]，颜色词 [map f cs ++ map f ds] 和 [map f (cs ++ ds)] 在命题上相等，但在定义上不相等。这正是 [BaseChange/Laws.v] 的 [hom_cast] 共轭函子性陈述必须穿越的缝隙，因此在其来源处被 [Example] 固定。

 ** 决策器（D2 规则）

 有两种颜色决策器循环，每种颜色类型一个：[Cdec] 对应 [Colour]（命名源的共享 [Monoidal] 记录 [CFreeCat_Monoidal S Cdec]），而 [C'dec] 对应 [Colour']（命名目标的，并提供泛性质的 [ObjDecEq] 边缘条件）。根据 [Construction/ColouredPROP/Instance.v] 的 D2 规则，两者都是显式参数，每个实例位置都应传递其颜色类型的唯一标准决策器。替代设计（未开发）：在 [CTerm] 上的计算 [C_base_map] 定点，带有共轭编织和张量子句，也将产生函子，但代价是需要一个新的 19 案例传输健全性归纳，类似于 [CT_map_CTermEq] 的 [Construction/ColouredPROP/Relabel.v]。通过普遍性质的方式可以在不使用它的情况下传递下面的一切，因此定点形式保持未开发状态。
*)

(*
   * ** The free coloured PROP's braiding, on the strict path

   For the free coloured PROP the coherence between the strict and
   symmetric [Monoidal] paths is [eq_refl]
   ([FreeColouredPROP_coherence_is_refl]), so the [transport_braid]
   re-indexing inside [cstrict_braid] is the identity and the
   strict-path braiding is the [CT_braid] constructor ON THE NOSE.
   This is the fact that makes braid-square hypotheses against free
   targets ([CSymmetricStrict] competitors in [BaseChange/Laws.v])
   definitionally transparent.  Machine-checked here, over an
   arbitrary signature and decider. 

   --------
   * ** 自由着色 PROP 在严格路径上的缠绕

   对于自由着色 PROP，严格路径与对称路径之间的相干性是 [eq_refl]（[FreeColouredPROP_coherence_is_refl]），因此在 [cstrict_braid] 内部的 [transport_braid] 重新索引是恒等的，严格路径的缠绕是 [CT_braid] 构造器本身的。这个事实使得针对自由目标（[BaseChange/Laws.v] 中的 [CSymmetricStrict] 竞争者）的缠绕平方假设在定义上是透明的。在这里，它已被机器检查过，适用于任意签名和判定器。
*)

Example free_cstrict_braid {Colour : Type} (S : CSignature Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  (cs ds : list Colour) :
  cstrict_braid (FreeColouredPROP S Cdec) cs ds = CT_braid cs ds := eq_refl.

Section BaseChange.

Context {Colour Colour' : Type}.
Context (f : Colour -> Colour').
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (C'dec : forall c d : Colour', {c = d} + {c <> d}).

(*
   * ** 1. Restriction of scalars

   The [ColouredPROP Colour] induced on a [ColouredPROP Colour'] by
   reading colour words through [map f].  The underlying category and
   all monoidal structure are [P]'s own — only [cprop_of_list] and
   the two object-equality fields change.  An explicit
   [Build_ColouredPROP] application: [Colour] occurs in no field
   type, so a record literal could not infer it.

   Since the underlying category is untouched, the side-condition
   instances of [Construction/Quotient.v] carry over on the nose: any
   [HomEqProp P] IS a [HomEqProp (ColouredPROP_restrict P)], and any
   [ObjDecEq P] an [ObjDecEq (ColouredPROP_restrict P)] — the classes
   mention only the category, which is judgmentally the same — so no
   new instances are declared here. 

   --------
   * ** 1. 标量的限制

   通过 [map f] 读取颜色词在 [ColouredPROP Colour'] 上引入的 [ColouredPROP Colour]。底层范畴和所有单体结构都是 [P] 自己的——只有 [cprop_of_list] 和两个对象等式字段发生变化。一个显式的 [Build_ColouredPROP] 应用：[Colour] 在任何字段类型中都不会出现，因此记录字面量无法推断它。

   由于底层范畴未被修改，[Construction/Quotient.v] 的附加条件实例会原样携带：任何 [HomEqProp P] 是 [HomEqProp (ColouredPROP_restrict P)]，任何 [ObjDecEq P] 是 [ObjDecEq (ColouredPROP_restrict P)]——这些类只提到范畴，而范畴在判断上是相同的——因此这里不声明新的实例。
*)

Definition ColouredPROP_restrict (P : ColouredPROP Colour') :
  ColouredPROP Colour :=
  Build_ColouredPROP Colour
    (cprop_cat P)
    (cprop_strict P)
    (cprop_symmetric P)

    (*
 The coherence between the two [Monoidal] paths is [P]'s own
 proof: both paths project through the untouched structures. 

 --------
 两个 [Monoidal] 路径之间的一致性是 [P] 自身的证明：两个路径都通过未被触碰的结构投影。
*)
    (@cprop_monoidal_coherence Colour' P)

    (*
 Objects: colour words over [Colour], read through [map f]. 

 --------
 对象：颜色词在 [Colour] 上，通读 [map f]。
*)
    (fun cs : list Colour => @cprop_of_list Colour' P (map f cs))

    (*
 [map f [] ≡ []] is definitional, so the unit condition is [P]'s
 own field at the empty word. 

 --------
 [map f [] ≡ []] 是定义性的，因此单位条件是 [P] 在空字上的自身域。
*)
    (@cprop_unit_nil Colour' P)

    (*
 The tensor condition: [P]'s own strictness at the image words,
 composed with the [cprop_of_list]-image of the (propositional)
 monoid-homomorphism law of [map f]. 

 --------
 张量条件：[P] 在图像词上的自身严格性，与[cprop_of_list] 对[map f] 的（命题）幺半群同态定律的图像组合。
*)
    (fun cs ds : list Colour =>
       eq_trans (@cprop_tensor_app Colour' P (map f cs) (map f ds))
                (f_equal (@cprop_of_list Colour' P)
                         (eq_sym (map_app f cs ds)))).

(*
   * Machine-checked: the restriction changes only the object naming. 

   --------
   * 机器检查：该限制仅更改对象命名。
*)

Example ColouredPROP_restrict_cat (P : ColouredPROP Colour') :
  cprop_cat (ColouredPROP_restrict P) = cprop_cat P := eq_refl.

Example ColouredPROP_restrict_of_list (P : ColouredPROP Colour')
  (cs : list Colour) :
  cprop_of_list (ColouredPROP := ColouredPROP_restrict P) cs
  = cprop_of_list (ColouredPROP := P) (map f cs) := eq_refl.

Example ColouredPROP_restrict_unit (P : ColouredPROP Colour') :
  @cprop_unit_nil Colour (ColouredPROP_restrict P)
  = @cprop_unit_nil Colour' P := eq_refl.

(*
   * A restricted wire is the wire of the image colour ([map f [c]]
   computes to [[f c]]). 

   --------
   * 受限导线是图像颜色的导线（[map f [c]] 计算为 [[f c]]）。
*)
Example ColouredPROP_restrict_wire (P : ColouredPROP Colour') (c : Colour) :
  wire (P := ColouredPROP_restrict P) c = wire (P := P) (f c) := eq_refl.

(*
   * ** 2. Signature morphisms over a colour function

   The base-change analogue of [CSubSig] ([Construction/ColouredPROP/
   Signature.v]): where a signature relabelling ([CSubSig]) preserves
   boundaries on the nose, a [CSigMap] REINDEXES them through
   [map f].  The identity and composition of such maps involve
   transports along [map_id] / [map_map] and live with the
   functoriality laws in [BaseChange/Laws.v]. 

   --------
   * ** 2. 关于颜色函数的签名态射

   [CSubSig] 的基变换类似物 ([Construction/ColouredPROP/Signature.v]): 当一个签名重标记 ([CSubSig]) 精确保留边界时，[CSigMap] 会通过 [map f] 对其重新索引。这类映射的恒等和复合涉及沿 [map_id] / [map_map] 的传输，并符合 [BaseChange/Laws.v] 中的函子律。
*)

Definition CSigMap (S : CSignature Colour) (S' : CSignature Colour') : Type :=
  forall cs ds : list Colour, S cs ds -> S' (map f cs) (map f ds).

Context (S : CSignature Colour).
Context (S' : CSignature Colour').
Context (h : CSigMap S S').

(*
   * ** 3. The base-change functor, through the universal property

   The interpretation target: the free coloured PROP on [S'],
   restricted along [f].  Its hom-sets at restricted objects are
   [CTerm S' (map f cs) (map f ds)] ON THE NOSE, so the generator
   valuation needs no casts. 

   --------
   * ** 3. 基变换函子，通过泛性质

   解释目标：在 [S'] 上的自由彩色 PROP，
   沿 [f] 限制。它在受限对象上的 Hom 集
   是 [CTerm S' (map f cs) (map f ds)] 的原样，因此生成元
   赋值不需要类型转换。
*)

Definition basechange_target : ColouredPROP Colour :=
  ColouredPROP_restrict (FreeColouredPROP S' C'dec).

Definition basechange_val : CValuation basechange_target S :=
  fun (cs ds : list Colour) (g : S cs ds) => CT_gen (h cs ds g).

(*
   * The functor: [CInterpF] at the restricted target.  The
   side-condition instances are the free category's own
   ([CFreeCat_HomEqProp] / [CFreeCat_ObjDecEq], carried over across
   the restriction per the note above); [ObjDecEq] is
   [C'dec]-conditional and therefore passed explicitly (D2).  The
   stated target category [CFreeCat S'] is judgmentally
   [cprop_cat basechange_target], so the ascription pins the functor
   at the type its consumers want. 

   --------
   * 函子：在受限目标上的 [CInterpF]。  
   侧条件实例是自由范畴自身的（[CFreeCat_HomEqProp] / [CFreeCat_ObjDecEq]，按照上述注释在限制中传递）；  
   [ObjDecEq] 是 [C'dec] 条件的，因此需要显式传递（D2）。  
   所述目标范畴 [CFreeCat S'] 在判定上是 [cprop_cat basechange_target]，因此这个注明将函子固定在其使用者所需的类型上。
*)

Definition BaseChangeF : CFreeCat S ⟶ CFreeCat S' :=
  @CInterpF Colour S basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(*
   * Machine-checked: the action of [BaseChangeF] is definitional on
   objects, generators, identities, and composites ([cinterp]
   computes; [id] and [compose] of [CFreeCat S'] are [CT_id] and
   [CT_comp]).  Braids and tensors map to their cast-conjugated
   images — the [cbraid_hom] / [ctensor_hom] combinators of
   [Construction/ColouredPROP/Interp.v] at [basechange_target] — and
   are handled by the cast algebra of [BaseChange/Laws.v]. 

   --------
   * 机器检查：[BaseChangeF] 的动作在对象、生成元、恒等映射和复合上是定义性的（[cinterp] 计算；[id] 和 [compose] 的 [CFreeCat S'] 是 [CT_id] 和 [CT_comp]）。编结和张量映射到它们的类共轭像——[Construction/ColouredPROP/Interp.v] 在 [basechange_target] 的 [cbraid_hom] / [ctensor_hom] 组合子——并由 [BaseChange/Laws.v] 的类代数处理。
*)

Example BaseChangeF_fobj (cs : list Colour) :
  fobj[BaseChangeF] cs = map f cs := eq_refl.

Example BaseChangeF_gen {cs ds : list Colour} (g : S cs ds) :
  fmap[BaseChangeF] (CT_gen g) = CT_gen (h cs ds g) := eq_refl.

(*
 Named after [CInterpF_fmap_id] / [CInterpF_fmap_comp] of
 [Universal.v] (these are their instances at [basechange_target]);
 the short names [BaseChangeF_id] / [BaseChangeF_comp] are reserved
 for the pseudofunctoriality theorems of [BaseChange/Laws.v]. 

 --------
 以 [CInterpF_fmap_id] / [CInterpF_fmap_comp] 的名字命名，来自 [Universal.v]（它们在 [basechange_target] 的实例）；短名称 [BaseChangeF_id] / [BaseChangeF_comp] 保留给 [BaseChange/Laws.v] 的伪函子定理。
*)
Example BaseChangeF_fmap_id (cs : list Colour) :
  fmap[BaseChangeF] (CT_id cs) = CT_id (map f cs) := eq_refl.

Example BaseChangeF_fmap_comp {cs ds es : list Colour}
  (u : CTerm S ds es) (t : CTerm S cs ds) :
  fmap[BaseChangeF] (CT_comp u t)
  = CT_comp (fmap[BaseChangeF] u) (fmap[BaseChangeF] t) := eq_refl.

(*
   * ** 4. The strict symmetric monoidal packaging, for free

   Each record below is the corresponding [CInterpF_*] packaging of
   [Construction/ColouredPROP/Universal.v] at [basechange_target],
   re-typed at the target's own monoidal tower — legitimate because
   the restriction leaves the structures untouched, so
   [MPc basechange_target] is judgmentally [CFreeCat_Monoidal S'
   C'dec], and likewise for the braided and symmetric records.  Both
   [Monoidal] instances in each type are THE shared records of their
   respective colour types (see the D2 WARNING in
   [Construction/ColouredPROP/Instance.v]). 

   --------
   * ** 4. 严格对称单体包装，免费提供

   每条记录如下，是  
   [Construction/ColouredPROP/Universal.v] 在 [basechange_target] 的对应 [CInterpF_*] 包装，  
   在目标自身的单体塔上重新输入 — 这是合法的，因为  
   限制不会改变结构，所以 [MPc basechange_target] 在判断上是 [CFreeCat_Monoidal S' C'dec]，对于编织和对称记录也是如此。每种类型中的两个 [Monoidal] 实例是各自颜色类型的共享记录（参见 [Construction/ColouredPROP/Instance.v] 中的 D2 警告）。
*)

Definition BaseChangeF_Monoidal :
  @MonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec) BaseChangeF :=
  @CInterpF_Monoidal Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

Definition BaseChangeF_Strict :
  @StrictMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec) BaseChangeF :=
  @CInterpF_Strict Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(** Machine-checked: the unit comparison is reflexivity... / 机器检查：单位比较是自反性... *)
Example BaseChangeF_strict_pure_obj_is_refl :
  @strict_pure_obj _ _ _ _ BaseChangeF BaseChangeF_Strict = eq_refl
  := eq_refl.

(*
   * ...but the tensor comparison is the restriction's
   [cprop_tensor_app] — the [map_app]-shaped composite, NOT [eq_refl]
   (which would be ill-typed here: [map f cs ++ map f ds] and
   [map f (cs ++ ds)] differ definitionally for variable [cs]).
   First the comparison is pinned to the class field verbatim
   (mirroring [CInterpF_strict_ap_obj_is_cprop_tensor_app]), then the
   field's shape is exposed: through the free instance the
   [eq_trans]'s first leg collapses to [eq_refl] and [cprop_of_list]
   to the identity function, leaving [map_app] as the sole residue. 

   --------
   * ...但是张量比较是限制的 [cprop_tensor_app] —— [map_app] 形状的复合，而不是 [eq_refl]（在这里会类型错误：[map f cs ++ map f ds] 和 [map f (cs ++ ds)] 对变量 [cs] 的定义不同）。
   首先比较被固定到类字段逐字（镜像 [CInterpF_strict_ap_obj_is_cprop_tensor_app]），然后暴露字段的形状：通过自由实例，[eq_trans] 的第一条腿坍缩为 [eq_refl]，[cprop_of_list] 坍缩为恒等函数，只留下 [map_app] 作为唯一残余。
*)

Example BaseChangeF_strict_ap_obj_is_tensor_app (cs ds : list Colour) :
  @strict_ap_obj _ _ _ _ BaseChangeF BaseChangeF_Strict cs ds
  = @cprop_tensor_app Colour basechange_target cs ds := eq_refl.

Example basechange_tensor_app_shape (cs ds : list Colour) :
  @cprop_tensor_app Colour basechange_target cs ds
  = eq_trans eq_refl
      (f_equal (fun ks : list Colour' => ks) (eq_sym (map_app f cs ds)))
  := eq_refl.

Definition BaseChangeF_Braided :
  @BraidedMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Braided S Cdec) (CFreeCat_Braided S' C'dec) BaseChangeF :=
  @CInterpF_Braided Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(*
   * Machine-checked: because the free target's monoidal coherence is
   [eq_refl], the [MonoidalFunctor_transport] inside
   [CInterpF_Braided] is the identity, so the braided record's
   underlying strong structure IS [BaseChangeF_Monoidal] — one shared
   tensor comparison across the whole tower, on the nose. 

   --------
   * 机器检查：因为自由目标的幺半群一致性是  
   [eq_refl]，[CInterpF_Braided] 内的 [MonoidalFunctor_transport] 是恒等，所以编织记录的  
   基础强结构就是 [BaseChangeF_Monoidal] — 整个塔中共享的一个张量比较，完全一致。
*)
Example BaseChangeF_Braided_is_strong :
  @braided_is_strong _ _ _ _ BaseChangeF BaseChangeF_Braided
  = BaseChangeF_Monoidal := eq_refl.

(*
   * A braided monoidal functor between symmetric monoidal categories
   IS a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
   definition, not a class); supplied explicitly, as the alias does
   not participate in instance resolution. 

   --------
   * 对称幺半范畴之间的编织幺半函子
   是对称幺半函子（[SymmetricMonoidalFunctor] 是一个
   定义，而不是一个类）；需要显式提供，因为别名不参与实例解析。
*)
Definition BaseChangeF_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Symmetric S Cdec) (CFreeCat_Symmetric S' C'dec) BaseChangeF :=
  BaseChangeF_Braided.

(*
   * The braid-compatibility square over the strict-path braiding — the
   hypothesis-pack form that the uniqueness theorem
   ([cinterp_unique]) consumes.  [BaseChange/Laws.v] instantiates the
   functoriality arguments with exactly this witness. 

   --------
   * 严格路径编织上的编织兼容性方阵——唯一性定理（[cinterp_unique]）所使用的假设包形式。[BaseChange/Laws.v] 用正好这个实例化了函子性论证。
*)
Definition BaseChangeF_SymmetricStrict :
  CSymmetricStrict S Cdec basechange_target BaseChangeF BaseChangeF_Monoidal :=
  @CInterpF_SymmetricStrict Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(*
   * The target-side instance of [free_cstrict_braid], through the
   restriction: the strict-path braiding of [basechange_target] is
   the [CT_braid] constructor of [CTerm S'] on the nose (the
   restriction carries [P]'s coherence verbatim, and the free
   coherence is [eq_refl]). 

   --------
   * [free_cstrict_braid] 的目标端实例，通过限制：[basechange_target] 的严格路径编织正好是 [CTerm S'] 的 [CT_braid] 构造函数（该限制原封不动地携带了 [P] 的一致性，且自由一致性为 [eq_refl]）。
*)
Example basechange_cstrict_braid (xs ys : list Colour') :
  cstrict_braid basechange_target xs ys = CT_braid xs ys := eq_refl.

End BaseChange.

Arguments ColouredPROP_restrict {Colour Colour'} f P : assert.
Arguments CSigMap {Colour Colour'} f S S' : assert.
Arguments basechange_target {Colour Colour'} f C'dec S' : assert.
(*
 [basechange_val] keeps its auto-generated argument status
 ({Colour Colour'} f C'dec S S' h, then the [CValuation] binders):
 its type unfolds to a ∀, so the boundary words and the generator
 ride along as trailing arguments. 

 --------
 [basechange_val] 保持其自动生成的参数状态（({Colour Colour'} f C'dec S S' h，然后是 [CValuation] 绑定器)：它的类型展开为 ∀，因此边界词和生成器会作为尾随参数随之出现。
*)
Arguments BaseChangeF {Colour Colour'} f C'dec S S' h : assert.
Arguments BaseChangeF_Monoidal {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Strict {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Braided {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Symmetric {Colour Colour'} f Cdec C'dec S S' h : assert.
(*
 [BaseChangeF_SymmetricStrict] keeps its auto-generated argument
 status: its type [CSymmetricStrict ...] is a definitionally
 unfolding ∀, so the constant carries the boundary binders [cs ds]
 as trailing arguments (compare [CInterpF_SymmetricStrict] in
 [Construction/ColouredPROP/Universal.v]). 

 --------
 [BaseChangeF_SymmetricStrict] 保持其自动生成的参数状态：其类型 [CSymmetricStrict ...] 是一个定义性展开的 ∀，因此该常量将边界绑定器 [cs ds] 作为尾随参数（比较 [CInterpF_SymmetricStrict] 在 [Construction/ColouredPROP/Universal.v] 中）。
*)

(*
   * ** Discussion: functoriality and further structure

   Base change is (pseudo)functorial in [f]: along the identity
   colour function it is the identity up to the [map_id] transports,
   and along a composite [g ∘ f] it agrees with the composite of the
   base changes up to the [map_map] transports.  Both statements are
   necessarily [hom_cast]-conjugated — [map_id] and [map_map] are
   propositional, not definitional — and both are consequences of the
   uniqueness half of the universal property rather than fresh
   inductions; they live in [Construction/ColouredPROP/BaseChange/
   Laws.v], together with the subset-restriction specialisation
   (base change along [proj1_sig]) and the descent of base change to
   presented coloured PROPs. 

   --------
   * ** 讨论：函子性及进一步结构

   基变换在  [f] 中是（伪）函子性的：沿恒等颜色函数，它在  [map_id]  传输下是恒等的；沿复合  [g ∘ f] ，它与基变换的复合在  [map_map]  传输下相符合。两个陈述都必然是  [hom_cast] -共轭的——[map_id] 和 [map_map] 是命题性的，而非定义性的——并且两者都是由泛性性质的一半唯一性推论得出的，而非新的归纳；它们存在于 [Construction/ColouredPROP/BaseChange/Laws.v] 中，同时还有子集-限制的特化（沿 [proj1_sig] 的基变换）以及基变换在呈现的彩色 PROP 上的下降。
*)
