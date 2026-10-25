Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(*
   * * Transport infrastructure for the free coloured PROP

   The free coloured PROP needs to talk about morphisms between
   objects whose colour words are PROPOSITIONALLY but not
   DEFINITIONALLY equal — e.g. [cs ++ []] and [cs], or
   [(x ++ y) ++ z] and [x ++ (y ++ z)].  List concatenation [app] is
   left-strict but not right-strict in Coq (exactly the asymmetry of
   [Nat.add] in the one-sorted donor [Construction/PROP/Cast.v]), so
   these boundary equations do not reduce definitionally and must be
   transported across.

   [CT_cast e] is the identity term, transported across an equality
   [e] of colour words.  Together with the associated rewrite lemmas
   it lets the Monoidal instance on [CFreeCat S] package up the
   structural isomorphisms (unitors, associator) for the cases where
   the boundary equality is not [eq_refl].

   This file merges the three cast-layer donors of the one-sorted
   spine into one:

   - the [T_cast] kit of [Construction/PROP/Cast.v] (UIP-free core
   plus the decidability-conditional UIP layer);
   - the tensor-cast fusion lemmas of
   [Construction/PROP/CastTensor.v];
   - the structural isomorphisms of
   [Construction/PROP/Structural.v].

   Deviation from the donor, by design: [nat] has the canonical
   decider [Nat.eq_dec], so the donor's UIP layer was unconditional.
   An arbitrary [Colour : Type] carries no such decider, so here
   every UIP-dependent lemma threads a colour-equality decider
   [Cdec] as an EXPLICIT argument, and uses
   [UIP_dec (list_eq_dec Cdec)] on colour words.  The UIP-free core
   (inverse laws, composition, naturality, tensor fusion) needs no
   decidability at all. 

   --------
   * * 自由彩色 PROP 的传输基础设施

   自由彩色 PROP 需要讨论那些颜色词在命题上相等但在定义上不相等的对象之间的同态 —— 例如 [cs ++ [] 和 [cs]，或者 [(x ++ y) ++ z] 和 [x ++ (y ++ z)]。列表连接 [app] 在 Coq 中是左严格但不是右严格的（正好是单一类型捐赠者 [Construction/PROP/Cast.v] 中 [Nat.add] 的不对称性），因此这些边界方程在定义上不能化简，必须被传输过去。

   [CT_cast e] 是恒等项，被传输到颜色词的一个相等 [e] 上。结合相关的重写引理，它使得 [CFreeCat S] 上的单体实例可以封装结构同构（单位元同构、结合律同构）用于边界相等不为 [eq_refl] 的情况。该文件将单分类脊柱的三个类型转换层捐赠者合并为一个：

   - [T_cast] 套件来自 [Construction/PROP/Cast.v]（UIP 免费核心加上可判定性条件的 UIP 层）；
   - [Construction/PROP/CastTensor.v] 的张量类型转换融合引理；
   - [Construction/PROP/Structural.v] 的结构同构。

   与捐赠者的偏差，按设计：[nat] 拥有规范判定器 [Nat.eq_dec]，因此捐赠者的 UIP 层是无条件的。任意 [Colour : Type] 不携带此类判定器，因此在这里，每个依赖 UIP 的引理都以显式参数方式穿入颜色等式判定器 [Cdec]，并在颜色词上使用 [UIP_dec (list_eq_dec Cdec)]。UIP 免费核心（逆律、组合、自然性、张量融合）完全不需要可判定性。
*)

(*
   * ** The cast term

   Identity, transported across [e : cs = ds].  Kept transparent (a
   plain [Definition] in [match] form): downstream files compute
   with it, and the structural isomorphisms below are built from it
   definitionally. 

   --------
   * ** 类型转换术语

   身份，通过 [e : cs = ds] 传输。保持透明（在 [match] 形式下为普通 [Definition]）：下游文件使用它进行计算，并且下面的结构同构是基于它定义构建的。
*)
Definition CT_cast {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) : CTerm S cs ds :=
  match e in _ = k return CTerm S cs k with
  | eq_refl => CT_id cs
  end.

(** Cast at [eq_refl] is the literal identity. / 在 [eq_refl] 的强制类型转换是字面上的身份。 *)
Lemma CT_cast_refl {Colour : Type} {S : CSignature Colour}
  (cs : list Colour) :
  @CT_cast Colour S cs cs eq_refl = CT_id cs.
Proof. reflexivity. Qed.

(*
   * Composing two casts gives a cast along the transitive equation. 

   --------
   * 组合两个类型转换会得到沿传递等式的类型转换。
*)
Lemma CT_cast_compose {Colour : Type} {S : CSignature Colour}
  {cs ds es : list Colour} (e1 : cs = ds) (e2 : ds = es) :
  CTermEq S (CT_comp (CT_cast e2) (CT_cast e1)) (CT_cast (eq_trans e1 e2)).
Proof.
  destruct e1, e2.
  cbn.
  apply CTE_id_left.
Qed.

(*
   * NOTE (donor divergence): the coloured [CT_cast_inv] is the
   TARGET-side cancellation — what the donor
   (Construction/PROP/Cast.v) calls [T_cast_inv_sym] — and
   [CT_cast_inv_sym] the SOURCE-side one.  Ports of mono-sorted
   proofs must swap the pair; see also the header of Braided.v,
   which compensates for this flip. 

   --------
   * 注意（供体差异）：带颜色的 [CT_cast_inv] 是目标端的消去——供体（Construction/PROP/Cast.v）称为 [T_cast_inv_sym]——而 [CT_cast_inv_sym] 是源端的。单类型证明的端口必须交换这对；另请参见 Braided.v 的头部，它弥补了这种翻转。
*)

(*
   * Casting along [e] after casting along [eq_sym e] is the identity
   on the TARGET word [ds]. 

   --------
   * 沿着 [e] 的类型转换在沿着 [eq_sym e] 的类型转换之后，在目标词 [ds] 上是恒等的。
*)
Lemma CT_cast_inv {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) :
  CTermEq S (CT_comp (CT_cast e) (CT_cast (eq_sym e))) (CT_id ds).
Proof.
  destruct e.
  cbn.
  apply CTE_id_left.
Qed.

(*
   * Casting along [eq_sym e] after casting along [e] is the identity
   on the SOURCE word [cs]. 

   --------
   * 沿着 [eq_sym e] 的转型在沿着 [e] 的转型之后，在源词 [cs] 上是恒等的。
*)
Lemma CT_cast_inv_sym {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) :
  CTermEq S (CT_comp (CT_cast (eq_sym e)) (CT_cast e)) (CT_id cs).
Proof.
  destruct e.
  cbn.
  apply CTE_id_left.
Qed.

(*
   * Instantiation helper mirrored from the one-sorted donor
   (Construction/PROP/Cast.v): the hypothesis [Hfg] is the conclusion
   universally quantified over the boundary equation, so this lemma
   is a bare instantiation at [e] with no proof content of its own,
   and it is stated for endo-boundaries only.  It is NOT what
   discharges the Monoidal coherence obligations: the naturality
   squares of the unitors and the associator are proved in Monoidal.v
   via [CT_cast_id] / [CT_cast_irrelevant] (UIP on colour words,
   hence [Cdec]-conditional) together with Monoidal.v's [ceq_rect_*]
   transport bridges.  Kept for donor parity. 

   --------
   * 实例化助手镜像自单类型捐赠者
   (Construction/PROP/Cast.v)：假设 [Hfg] 是在边界方程上普遍量化的结论，因此这个引理
   只是 [e] 的一个纯实例化，本身没有证明内容，
   并且它仅适用于自边界。它不是用于解除单体范畴一致性义务的内容：单位元和结合子的自然性方块通过 [CT_cast_id] / [CT_cast_irrelevant]（颜色词上的 UIP，因此 [Cdec]-条件性）以及 Monoidal.v 的 [ceq_rect_*] 传输桥在 Monoidal.v 中被证明。保留以保持与捐赠者的一致性。
*)
Lemma CT_cast_natural {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds)
  (f : CTerm S cs cs) (g : CTerm S ds ds)
  (Hfg : forall (q : cs = ds),
           CTermEq S (CT_comp (CT_cast q) f)
                     (CT_comp g (CT_cast q))) :
  CTermEq S (CT_comp (CT_cast e) f) (CT_comp g (CT_cast e)).
Proof. apply Hfg. Qed.

(*
   * Degenerate naturality at [eq_refl]: a [CT_cast eq_refl] is
   [CT_id], so it commutes with any morphism trivially. 

   --------
   * 在 [eq_refl] 上的简并自然性：一个[CT_cast eq_refl]是
   [CT_id] ，因此它与任意态射都平凡地交换。
*)
Lemma CT_cast_natural_refl {Colour : Type} {S : CSignature Colour}
  {cs : list Colour} (f : CTerm S cs cs) :
  CTermEq S (CT_comp (CT_cast eq_refl) f) (CT_comp f (CT_cast eq_refl)).
Proof.
  cbn.
  apply CTE_trans with f.
  - apply CTE_id_left.
  - apply CTE_sym, CTE_id_right.
Qed.

(*
   * ** Transport bridges for strict-PROP equations

   The strict right-unit, associativity, hexagon, and unit-braid
   axioms in [CTermEq] are stated in [eq_rect] transport form (over
   [app_nil_r] and [app_assoc]).  Below we expose small helpers for
   use when downstream proofs need to work with both ends of the
   transport. 

   --------
   * ** 严格 PROP 方程的传输桥

   [CTermEq] 中的严格右单位、结合律、六边形和单位编织公理
   以 [eq_rect] 的传输形式陈述（在 [app_nil_r] 和 [app_assoc] 上）。下面我们展示一些小工具，便于后续证明中需要同时处理传输两端的情况。
*)

(*
   * Transport-spelling bridge: the [eq_rect] transport of a term
   along [e : cs = ds] over the codomain index equals the [match]
   (dependent pattern-match) spelling of the same transport.  Both
   sides are [CT_cast e] applied to [t]; this lemma just lets a
   proof switch between the [eq_rect] form used in [CTermEq]'s
   strict-PROP axioms and the [match] form used by [CT_cast].

   This is the standard "destruct the eq_rect" pattern.  This lemma
   and [CT_term_eq_rect_r_refl] below are exported kit with no
   in-tree consumer yet: the naturality proofs in Monoidal.v
   destruct their quantified boundary equations via the
   [ceq_rect_*] transport bridges instead. 

   --------
   * 传输拼写桥：沿着 [e : cs = ds] 在余域索引上的 [eq_rect] 项的传输等于相同传输的 [match]（依赖模式匹配）拼写。两边都是应用于 [t] 的 [CT_cast e]；这个引理只是让证明在 [CTermEq] 的严格 PROP 公理中使用的 [eq_rect] 形式和 [CT_cast] 使用的 [match] 形式之间切换。

   这是标准的“拆解 eq_rect”模式。这个引理以及下面的 [CT_term_eq_rect_r_refl] 被导出为工具包，但尚未有树内使用者：Monoidal.v 中的自然性证明通过 [ceq_rect_*] 传输桥拆解其量化边界方程。
*)
Lemma CT_term_eq_rect_destruct {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) (t : CTerm S cs cs) :
  eq_rect cs (fun k => CTerm S cs k) t ds e
  = match e in _ = k return CTerm S cs k with
    | eq_refl => t
    end.
Proof. destruct e; reflexivity. Qed.

(*
   * Dual: an [eq_rect_r] transport on the domain index reduces at
   [eq_refl] to the term itself.  More general transport shapes
   require a [destruct e] in context. 

   --------
   * 对偶：在域索引上的 [eq_rect_r] 传输在 [eq_refl] 处简化为该项本身。更一般的传输形状需要在上下文中使用 [destruct e] 。
*)
Lemma CT_term_eq_rect_r_refl {Colour : Type} {S : CSignature Colour}
  {cs : list Colour} (t : CTerm S cs cs) :
  eq_rect_r (fun k => CTerm S k cs) t (@eq_refl _ cs) = t.
Proof. reflexivity. Qed.

(*
   * ** [CT_cast] interaction with [CT_tens]

   Bridge lemmas that the Monoidal instance on [CFreeCat S] will
   need to discharge naturality of the structural isomorphisms.
   [CT_tens] concatenates two boundary words; [CT_cast] rewrites a
   single boundary along a propositional equation.  The lemmas below
   all reduce the cast away by [destruct]-ing the boundary equation,
   after which the goal is closed by a primitive tensor/identity
   constructor of [CTermEq] ([CTE_tens_id], [CTE_id_left], or
   [CTE_id_right]).  None of them needs colour decidability. 

   --------
   * ** [CT_cast] 与 [CT_tens] 的交互

   桥接引理说明 [CFreeCat S] 上的单体实例需要处理结构同构的自然性。 
   [CT_tens] 将两个边界词连接在一起；[CT_cast] 根据命题等式重写单个边界。以下引理
   都通过 [destruct] 对边界等式进行操作来消除类型转换，
   之后目标由 [CTermEq]（[CTE_tens_id]、[CTE_id_left] 或 [CTE_id_right]）的原始张量/恒等构造子闭合。 
   它们都不需要颜色可判定性。
*)

(*
   * Tensoring an identity with a cast on the right factor equals a
   single cast along the [++]-congruenced boundary equation.

   [(id_cs ⊕c CT_cast e) ≈ CT_cast (f_equal (cs ++ _) e)]

   The right-hand boundary equation [cs ++ a = cs ++ b] is [e]
   congruenced by left-concatenation of [cs]; at [eq_refl] it
   reduces to [eq_refl] and the goal becomes [CTE_tens_id]. 

   --------
   * 对右因子进行张量化的恒等式等于沿 [++] 同余边界方程的单一转换。

   [(id_cs ⊕c CT_cast e) ≈ CT_cast (f_equal (cs ++ _) e)]

   右侧边界方程 [cs ++ a = cs ++ b] 与 [e] 同余，通过左连接 [cs]；在 [eq_refl] 处，它简化为 [eq_refl]，目标变为 [CTE_tens_id]。
*)
Lemma CT_tens_id_cast_left {Colour : Type} {S : CSignature Colour}
  {cs a b : list Colour} (e : a = b) :
  CTermEq S (CT_tens (CT_id cs) (CT_cast e))
            (CT_cast (f_equal (fun ks => cs ++ ks) e)).
Proof.
  destruct e.
  cbn.
  apply CTE_tens_id.
Qed.

(*
   * Symmetric variant: cast on the LEFT, identity on the RIGHT. 

   --------
   * 对称变体：在左侧进行投射，在右侧保持不变。
*)
Lemma CT_tens_cast_id_right {Colour : Type} {S : CSignature Colour}
  {a b ns : list Colour} (e : a = b) :
  CTermEq S (CT_tens (CT_cast e) (CT_id ns))
            (CT_cast (f_equal (fun ks => ks ++ ns) e)).
Proof.
  destruct e.
  cbn.
  apply CTE_tens_id.
Qed.

(*
   * Tensor preserves identities: [id_cs ⊕c id_ds ≈ id_(cs ++ ds)].
   This is just the primitive [CTE_tens_id] constructor restated as
   a named lemma (no cast involved).  Together with the two
   [eq_refl]-collapse lemmas below ([CT_comp_cast_tens_left] and
   [CT_comp_tens_cast_right]) it is exported kit with no in-tree
   consumer yet. 

   --------
   * 张量保持恒等式：[id_cs ⊕c id_ds ≈ id_(cs ++ ds)]。
   这只是原始的[CTE_tens_id]构造函数重新表述为一个命名引理（不涉及类型转换）。连同下面的两个[eq_refl]折叠引理（[CT_comp_cast_tens_left]和[CT_comp_tens_cast_right]），它被导出为一个套件，但目前树内还没有使用者。
*)
Lemma CT_tens_id_id {Colour : Type} {S : CSignature Colour}
  (cs ds : list Colour) :
  CTermEq S (CT_tens (CT_id cs) (CT_id ds)) (CT_id (cs ++ ds)).
Proof. apply CTE_tens_id. Qed.

(*
   * Composing a trivial [CT_cast eq_refl] (which is [CT_id]) onto a
   tensor is the identity operation.  [CT_cast eq_refl] reduces to
   [CT_id (ds1 ++ ds2)], so the composite collapses by left
   identity. 

   --------
   * 将一个平凡的 [CT_cast eq_refl]（即 [CT_id]）作用到张量上是恒等操作。[CT_cast eq_refl] 简化为 [CT_id (ds1 ++ ds2)]，因此复合通过左恒等式而消减。
*)
Lemma CT_comp_cast_tens_left {Colour : Type} {S : CSignature Colour}
  {cs1 ds1 cs2 ds2 : list Colour}
  (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
  CTermEq S (CT_comp (CT_cast eq_refl) (CT_tens f g))
            (CT_tens f g).
Proof. cbn. apply CTE_id_left. Qed.

(*
   * Dual: post-composing a trivial [CT_cast eq_refl] on the input
   side of a tensor collapses by right identity. 

   --------
   * 双重：在张量的输入端对一个微不足道的 [CT_cast eq_refl] 进行后合成会通过右单位元塌缩。
*)
Lemma CT_comp_tens_cast_right {Colour : Type} {S : CSignature Colour}
  {cs1 ds1 cs2 ds2 : list Colour}
  (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
  CTermEq S (CT_comp (CT_tens f g) (CT_cast eq_refl))
            (CT_tens f g).
Proof. cbn. apply CTE_id_right. Qed.

(*
   * ** The UIP layer: proof irrelevance of boundary casts

   Proof-irrelevance for colour-word casts: any two proofs [e1 e2]
   of [cs = ds] give equal cast terms.

   A colour type with decidable equality gives decidable equality on
   colour words by [list_eq_dec], hence Uniqueness of Identity
   Proofs (UIP) on [list Colour] without any axioms — proved by
   [Eqdep_dec.UIP_dec (list_eq_dec Cdec)].  This lets us replace one
   proof of a boundary equation by another inside [CT_cast].

   The decider [Cdec] is threaded as an EXPLICIT argument rather
   than assumed globally: the UIP-free core
   above stays available for arbitrary colour types, and every
   downstream file states exactly which of its results are
   decidability-conditional.  Downstream instance sites must fix ONE
   canonical [Cdec] per colour type, since different deciders give
   different (albeit provably equal) cast-irrelevance proofs. 

   --------
   * ** UIP 层：边界类型转换的证明无关性

   颜色词转换的证明无关性：任何两个  [e1 e2]  对  [cs = ds]  的证明都会给出相等的类型转换项。

   具有可判定相等性的颜色类型通过  [list_eq_dec]  在颜色词上给出了可判定相等性，因此在  [list Colour]  上无需任何公理即可获得身份证明的唯一性（UIP）——由  [Eqdep_dec.UIP_dec (list_eq_dec Cdec)]  证明。这允许我们在  [CT_cast]  中将边界方程的一个证明替换为另一个。决策器 [Cdec] 被作为显式参数传递，而不是全局假定：上述无 UIP 核心仍然可用于任意颜色类型，并且每个下游文件都会确切说明其结果中哪些是可判定性条件的。下游实例位置必须为每种颜色类型固定一个规范的 [Cdec]，因为不同的决策器会给出不同的（尽管可证明相等的）类型转换无关性证明。
*)
Lemma CT_cast_irrelevant {Colour : Type} {S : CSignature Colour}
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  {cs ds : list Colour} (e1 e2 : cs = ds) :
  CT_cast (S := S) e1 = CT_cast (S := S) e2.
Proof.
  rewrite (UIP_dec (list_eq_dec Cdec) e1 e2).
  reflexivity.
Qed.

(*
   * Special case: any cast along an equation of [cs = cs] is the
   identity, because [eq_refl cs] is the canonical proof of
   [cs = cs] and [CT_cast eq_refl = CT_id cs] reduces
   definitionally. 

   --------
   * 特殊情况：沿着 [cs = cs] 的任何类型转换都是恒等变换，因为 [eq_refl cs] 是 [cs = cs] 的标准证明，并且 [CT_cast eq_refl = CT_id cs] 在定义上可以化简。
*)
Lemma CT_cast_id {Colour : Type} {S : CSignature Colour}
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  {cs : list Colour} (e : cs = cs) :
  CT_cast (S := S) e = CT_id cs.
Proof.
  rewrite (CT_cast_irrelevant Cdec e eq_refl).
  reflexivity.
Qed.

(* * * Structural isomorphisms for the free coloured PROP / * * 自由彩色 PROP 的结构同构 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 nLab: https://ncatlab.org/nlab/show/associator
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/Coherence_condition

 Package the three structural maps of a monoidal category — left
 unitor, right unitor, associator — as isomorphisms in [CFreeCat S]
 using [CT_cast].

 "Structural" here is the monoidal-coherence sense (the unitors and
 associator of nLab/Mac Lane), not the permutation sense: a
 coloured PROP also has the symmetric structural maps built from
 braids and identities (see [CT_braid] in Signature.v), which are a
 separate family.

 The boundary equations are pure [list] facts:

 [app_nil_l cs]    : [] ++ cs = cs                  (left unit)
 [app_nil_r cs]    : cs ++ [] = cs                  (right unit)
 [app_assoc x y z] : x ++ (y ++ z) = (x ++ y) ++ z  (associator)

 Because [app] is left-strict in Coq, the left-unit boundary
 EQUATION [[] ++ cs = cs] holds definitionally; but [app_nil_l] is
 a Qed-opaque stdlib proof, so the left unitor's cast is a stuck
 [match] that does NOT reduce to [CT_id] by computation (it is
 eliminated via [CT_cast_id] under [Cdec] in Monoidal.v, exactly
 like the right unitor's and associator's genuinely propositional
 casts).  Note the stdlib orientation of [app_assoc] (right-to-left
 reassociation, same as [Nat.add_assoc]), so the associator's [to]
 is the [eq_sym] cast.

 The isomorphisms are built with explicit [Build_Isomorphism]
 applications: the two inverse-law fields are exactly
 [CT_cast_inv] / [CT_cast_inv_sym] instances, since composition in
 [CFreeCat S] is [CT_comp], identity is [CT_id], and the
 hom-equivalence is [CTermEq S], all definitionally. 

 --------
 nLab：https://ncatlab.org/nlab/show/monoidal+category
 nLab：https://ncatlab.org/nlab/show/associator
 维基百科：https://en.wikipedia.org/wiki/Monoidal_category
 维基百科：https://en.wikipedia.org/wiki/Coherence_condition

 将单含类范畴的三种结构映射——左幺元同构、右幺元同构、结合子——作为 [CFreeCat S] 中的同构进行打包，使用 [CT_cast]。

 这里的“结构性”是指单含一致性的意义（nLab/Mac Lane 的幺元同构和结合子），而不是排列的意义：彩色 PROP 还具有由编织和恒等映射构建的对称结构映射（参见 Signature.v 中的 [CT_braid]），它们是一个独立的族群。

 边界方程是纯粹的 [list] 事实：

 [app_nil_l cs] : [] ++ cs = cs                  （左幺元）
 [app_nil_r cs] : cs ++ [] = cs                  （右幺元）
 [app_assoc x y z] : x ++ (y ++ z) = (x ++ y) ++ z  （结合子）因为 [app] 在 Coq 中是左严格的，所以左单位边界方程 [[] ++ cs = cs 在定义上成立；但 [app_nil_l] 是一个 Qed-opaque 的标准库证明，所以左单位子的类型转换是一个卡住的 [match]，它不能通过计算简化为 [CT_id]（它是在 Monoidal.v 中通过 [Cdec] 下的 [CT_cast_id] 消去的，就像右单位子和结合子的真正命题类型转换一样）。注意 [app_assoc] 的标准库方向（从右到左的重新结合，与 [Nat.add_assoc] 相同），所以结合子的 [to] 是 [eq_sym] 类型转换。同构是通过显式的 [Build_Isomorphism] 应用构建的：两个逆律域正好是 [CT_cast_inv] / [CT_cast_inv_sym] 实例，因为在 [CFreeCat S] 中的复合是 [CT_comp]，恒等映射是 [CT_id]，并且同源等价是 [CTermEq S]，所有这些都是按定义的。
*)

(*
   * Left unitor [[] ++ cs ≅ cs] in [CFreeCat S].  The boundary
   equation [[] ++ cs = cs] is definitional, but [app_nil_l] is a
   Qed-opaque stdlib proof, so [CT_cast (app_nil_l cs)] is a stuck
   [match], not [CT_id cs]; Monoidal.v eliminates it with
   [CT_cast_id] under [Cdec].  (The proof term is deliberately kept
   as [app_nil_l]: Instance.v compares these structural maps by the
   same proof term.) 

   --------
   * 左单位元 [[] ++ cs ≅ cs] 在 [CFreeCat S] 中。边界方程 [[] ++ cs = cs] 是定义性的，但是 [app_nil_l] 是一个 Qed-opaque 标准库证明，因此 [CT_cast (app_nil_l cs)] 是一个卡住的 [match]，而不是 [CT_id cs]；Monoidal.v 在 [Cdec] 下用 [CT_cast_id] 消除了它。（证明项被刻意保持为 [app_nil_l]：Instance.v 通过相同的证明项比较这些结构映射。）
*)
Definition CFreeCat_unit_left {Colour : Type} (S : CSignature Colour)
  (cs : list Colour) :
  @Isomorphism (CFreeCat S) ([] ++ cs) cs :=
  @Build_Isomorphism (CFreeCat S) ([] ++ cs) cs
    (CT_cast (app_nil_l cs))
    (CT_cast (eq_sym (app_nil_l cs)))
    (CT_cast_inv (app_nil_l cs))
    (CT_cast_inv_sym (app_nil_l cs)).

(*
   * Right unitor [cs ++ [] ≅ cs] in [CFreeCat S].  [app_nil_r] is
   propositional, not definitional, so the cast is along a
   non-trivial equation. 

   --------
   * 右单位元 [cs ++ [] ≅ cs] 在 [CFreeCat S] 中。[app_nil_r] 是命题性的，而不是定义性的，所以类型转换沿着一个非平凡的方程进行。
*)
Definition CFreeCat_unit_right {Colour : Type} (S : CSignature Colour)
  (cs : list Colour) :
  @Isomorphism (CFreeCat S) (cs ++ []) cs :=
  @Build_Isomorphism (CFreeCat S) (cs ++ []) cs
    (CT_cast (app_nil_r cs))
    (CT_cast (eq_sym (app_nil_r cs)))
    (CT_cast_inv (app_nil_r cs))
    (CT_cast_inv_sym (app_nil_r cs)).

(*
   * Associator [(x ++ y) ++ z ≅ x ++ (y ++ z)] in [CFreeCat S].
   Likewise propositional via [app_assoc].  Oriented
   [to : (x ++ y) ++ z ~> x ++ (y ++ z)], matching the nLab
   associator α : (A⊗B)⊗C → A⊗(B⊗C); with the stdlib orientation of
   [app_assoc] this makes [to] the [eq_sym] cast. 

   --------
   * 结合子 [(x ++ y) ++ z ≅ x ++ (y ++ z)] 在 [CFreeCat S] 中。  
   同样通过 [app_assoc] 提出命题。定向 [to : (x ++ y) ++ z ~> x ++ (y ++ z)]，与 nLab 结合子 α : (A⊗B)⊗C → A⊗(B⊗C) 相匹配；使用 [app_assoc] 的标准库方向，这使得 [to] 成为 [eq_sym] 的转换。
*)
Definition CFreeCat_tensor_assoc {Colour : Type} (S : CSignature Colour)
  (x y z : list Colour) :
  @Isomorphism (CFreeCat S) ((x ++ y) ++ z) (x ++ (y ++ z)) :=
  @Build_Isomorphism (CFreeCat S) ((x ++ y) ++ z) (x ++ (y ++ z))
    (CT_cast (eq_sym (app_assoc x y z)))
    (CT_cast (app_assoc x y z))
    (CT_cast_inv_sym (app_assoc x y z))
    (CT_cast_inv (app_assoc x y z)).

Arguments CFreeCat_unit_left {Colour} S cs : assert.
Arguments CFreeCat_unit_right {Colour} S cs : assert.
Arguments CFreeCat_tensor_assoc {Colour} S x y z : assert.
