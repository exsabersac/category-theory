Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
(*
 [Category.Instance.Fun] is Required transitively (its [Fun] category
 hosts the tensor-comparison isomorphism below) but deliberately NOT
 Imported: its bracket notation [C, D] is grammatically incompatible
 with the singleton list notation [c] of [ListNotations], which the
 wire-datum corollary needs.  The one use site writes the qualified
 [@Category.Instance.Fun.Fun] instead. 

 --------
 [Category.Instance.Fun] 是传递性必需的（它的 [Fun] 类别承载了下面的张量比较同构），但故意未导入：它的括号符号 [C, D] 在语法上与 [ListNotations] 的单元素列表符号 [c] 不兼容，而这正是 wire-datum 推论所需要的。唯一的使用位置改为写出了限定的 [@Category.Instance.Fun.Fun]。
*)
Require Category.Instance.Fun.
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
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Construction.ColouredPROP.Interp.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * The universal property of the free coloured PROP / * * 自由着色PROP的普遍性质 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 Given a coloured signature [S], a coloured PROP [P], and a valuation
 [v] of the generators, this file packages the interpretation
 [cinterp : CTerm S cs ds → (⟦cs⟧ ~{P}~> ⟦ds⟧)] of
 [Construction/ColouredPROP/Interp.v] into a functor
 [CInterpF : CFreeCat S ⟶ P] and equips it with the full
 strict-symmetric-monoidal structure, then proves it UNIQUE among
 such functors: the free coloured PROP [FreeColouredPROP S Cdec] is
 initial among coloured PROPs that are equipped with an
 [S]-valuation and satisfy two side conditions on the target [P]:
 decidable object equality ([ObjDecEq], powering the axiom-free UIP
 on [obj P]) and a [Prop] reflection of the hom equivalence
 ([HomEqProp], powering [CInterpF]'s respectfulness field
 [cinterp_sound]).  The free instance provides both by construction
 ([CFreeCat_HomEqProp] / [CFreeCat_ObjDecEq] in [Instance.v]).  The
 [Proof using] lines witness the split: uniqueness ([cinterp_unique]
 and its corollaries) needs only [ObjDecEq]; [HomEqProp] enters only
 through [CInterpF] itself.

 This file is the many-sorted mirror of
 [Construction/PROP/Universal.v] (the one-sorted donor), with
 [list Colour] replacing [nat], [++] replacing [+], [[]] replacing
 [0], and the boundary equations [app_nil_l] / [app_nil_r] /
 [app_assoc] replacing [Nat.add_0_l] / [Nat.add_0_r] /
 [Nat.add_assoc].  The generic transport of monoidal-functor
 structure across a [Monoidal] equality — [MonoidalFunctor_transport]
 — is REUSED BY IMPORT from the donor: it is stated over arbitrary
 categories [C D], so it applies verbatim to [CFreeCat S] and the
 category underlying a coloured PROP (the same import-not-clone
 discipline as the [BraidTransport] kit of
 [Construction/ColouredPROP/Interp.v]).

 The strictness comparisons of [CInterpF] ride the coloured-PROP
 class fields VERBATIM: [strict_pure_obj] is [cprop_unit_nil] and
 [strict_ap_obj] is [cprop_tensor_app] (machine-checked by
 [Example]s below), so the universal property really is stated
 against the strict object equalities every coloured PROP carries.

 ** Design note: how “strict symmetric monoidal functor” is phrased

 A coloured PROP carries two [Monoidal] structures on the same
 category — the strict path [MPc P] and the braided/symmetric path
 [MBc P] — related only by the propositional equality
 [cprop_monoidal_coherence].  The classes [StrictMonoidalFunctor]
 (of [Functor/Structure/Monoidal/Strict.v], at [MPc P]) and
 [BraidedMonoidalFunctor] (of [Functor/Structure/Monoidal/Braided.v],
 at [MBc P]) therefore carry INDEPENDENT [MonoidalFunctor] fields
 over propositionally-different target monoidals, and a hypothesis
 pack made of one instance of each would be underdetermined (nothing
 would relate their two tensor comparisons).  Uniqueness is instead
 phrased against ONE [StrictMonoidalFunctor] plus [CSymmetricStrict]:
 the braid compatibility square over that SAME [ap_iso], with the
 braiding re-indexed to the strict path by [cstrict_braid] (the
 transport of [Interp.v]).  For competitors arriving with a genuine
 [BraidedMonoidalFunctor], the converse bridge
 [CSymmetricStrict_of_Braided] converts (given the agreement of the
 two tensor comparisons across the coherence transport), and
 [CInterpF_Braided] / [CInterpF_Symmetric] deliver [CInterpF] itself
 in those two classes via the match-based
 [MonoidalFunctor_transport].

 ** Uniqueness

 [cinterp_unique] pins any [CSymmetricStrict] competitor [G] that
 agrees with [v] on generators: the object agreement is a family
 [Hobj : ∀ cs, G cs = ⟦cs⟧] of Leibniz equalities, and the morphism
 agreement is phrased by conjugating with [hom_cast] along it.  The
 theorem holds for an ARBITRARY such family — axiom-free UIP on
 [obj P] (the [ObjDecEq] class) makes any two proofs of the same
 object equality interchangeable; [Cdec] enters only to STATE the
 competitor's source structure (a [StrictMonoidalFunctor] typed at
 [CFreeCat_Monoidal S Cdec], so the statement and its [Proof using]
 name it), while the proof never case-splits on colours — all UIP
 is routed through [obj P], as in [Interp.v] — and the corollary
 [cinterp_unique_from_wires] derives
 the whole family from the single-wire data [G [c] = ⟦[c]⟧] via the
 [G_obj] fixpoint, peeling one typed wire at a time.
 [cinterp_unique2] is the resulting agreement of any two
 competitors.  The existence half is named as well:
 [CInterpF_extends_valuation] records (by [eq_refl]) that [CInterpF]
 extends the valuation, and [CInterpF_interp_unique_self]
 instantiates the hypothesis pack of [cinterp_unique] at [CInterpF]
 itself, with [Hobj := eq_refl].

 The named coherence lemmas of section 2 ([cinterp_ap_natural],
 [cinterp_monoidal_unit_left/right], [cinterp_monoidal_assoc],
 [cinterp_braid_ap]) are deliberately standalone: their statements
 are purely target-side, so
 [Construction/ColouredPROP/Presentation/Universal.v] reuses them
 verbatim for the presented coloured PROP. 

 --------
 nLab：https://ncatlab.org/nlab/show/PROP
 nLab：https://ncatlab.org/nlab/show/free+category
 维基百科：https://en.wikipedia.org/wiki/PROP_(category_theory)给定一个有色签名 [S]，一个有色 PROP [P]，以及生成元的赋值 [v]，本文件将 [Construction/ColouredPROP/Interp.v] 的解释 [cinterp : CTerm S cs ds → (⟦cs⟧ ~{P}~> ⟦ds⟧)] 封装到一个函子 [CInterpF : CFreeCat S ⟶ P] 中，并为其配备完整的严格对称单对象结构，然后证明在这样的函子中它是唯一的：自由有色 PROP [FreeColouredPROP S Cdec] 在配备了 [S] 赋值且在目标 [P] 上满足两个附加条件的有色 PROP 中是初始的：可判定的对象等式（[ObjDecEq]，为 [obj P] 上无公理 UIP 提供支持）以及同态等价的 [Prop] 反射（[HomEqProp]，为 [CInterpF] 的尊重性字段 [cinterp_sound] 提供支持）。自由实例通过构造同时提供这两者（[CFreeCat_HomEqProp] / [CFreeCat_ObjDecEq] 在 [Instance.v] 中）。[Proof using] 行见证了分裂：唯一性（[cinterp_unique] 及其推论）只需要 [ObjDecEq]；[HomEqProp] 仅通过 [CInterpF] 进入。

 这个文件是 [Construction/PROP/Universal.v]（单一类型源）的多类型镜像，其中 [list Colour] 替代了 [nat]，[++] 替代了 [+]，[[]] 替代了 [0]，并且边界方程 [app_nil_l] / [app_nil_r] / [app_assoc] 替代了 [Nat.add_0_l] / [Nat.add_0_r] / [Nat.add_assoc]。 单体函子结构在 [Monoidal] 相等条件下的通用传输——[MonoidalFunctor_transport]——是从源直接引用（REUSED BY IMPORT）的：它在任意范畴 [C D] 上陈述，因此可逐字应用于 [CFreeCat S] 以及彩色 PROP 所在的范畴（与 [BraidTransport] 工具包 [Construction/ColouredPROP/Interp.v] 相同的导入而非克隆的规则）。[CInterpF] 对彩色 PROP 的类字段的严格性比较按原文：[strict_pure_obj] 是 [cprop_unit_nil]，[strict_ap_obj] 是 [cprop_tensor_app]（由下面的 [Example] 机器检查），因此通用性质确实是针对每个彩色 PROP 所携带的严格对象等式陈述的。

 ** 设计注：'严格对称单体范畴函子' 的表述方式一个带色的 PROP 在同一范畴上携带两个 [Monoidal] 结构——严格路径 [MPc P] 和编织/对称路径 [MBc P]——仅通过命题等式 [cprop_monoidal_coherence] 相关。类 [StrictMonoidalFunctor] （在 [MPc P] 上的 [Functor/Structure/Monoidal/Strict.v] 的类）和 [BraidedMonoidalFunctor] （在 [MBc P] 上的 [Functor/Structure/Monoidal/Braided.v] 的类）因此在命题不同的目标幺半群上携带独立的 [MonoidalFunctor] 场，而由每个实例组成的假设包将是欠定的（没有任何东西将它们的两个张量比较联系起来）。唯一性反而是针对一个 [StrictMonoidalFunctor] 加 [CSymmetricStrict] 来表达的：在同一个 [ap_iso] 上的编织兼容正方形，其中编织通过 [cstrict_braid] 被重新索引到严格路径（ZW66WZZ 的迁移）。对于携带真实 [BraidedMonoidalFunctor] 到达的竞争者，逆桥 [CSymmetricStrict_of_Braided] 会转换（在两个张量比较在相干传输上达成一致的情况下），并且 [CInterpF_Braided] / [CInterpF_Symmetric] 通过基于匹配的 [MonoidalFunctor_transport] 在这两个类别中提供 [CInterpF] 本身。

 ** 唯一性[cinterp_unique] 钉住任何 [CSymmetricStrict] 竞争者 [G]，其在发电机上的观点与 [v] 一致：对象的一致性是一族 [Hobj : ∀ cs, G cs = ⟦cs⟧] 莱布尼茨等式，而态射的一致性则通过沿其使用 [hom_cast] 的共轭来表述。该定理对任意这样的族都成立——在 [obj P]（[ObjDecEq] 类）上无公理 UIP 使得同一对象相等的任意两个证明可以互换；[Cdec] 仅用于陈述竞争者的源结构（一个在 [CFreeCat_Monoidal S Cdec] 上类型化的 [StrictMonoidalFunctor]，因此陈述及其 [Proof using] 名称是什么），而证明从不在颜色上分情况——所有 UIP 都通过 [obj P] 路由，如在 [Interp.v] 中——并且推论 [cinterp_unique_from_wires] 从单线数据 [G [c] = ⟦[c]⟧] 通过 [G_obj] 不动点推导出整个族，一次剥离一根类型化的线。[cinterp_unique2] 是任意两个竞争者达成的结果一致性。存在部分也被命名为：
 [CInterpF_extends_valuation] 记录（由  [eq_refl] ）表明  [CInterpF] 
 扩展了评估，而  [CInterpF_interp_unique_self] 
 在  [CInterpF] 本身实例化了  [cinterp_unique] 的假设包，并且使用了  [Hobj := eq_refl] 。

 第2节的命名一致性引理（ [cinterp_ap_natural] ，
 [cinterp_monoidal_unit_left/right] ，  [cinterp_monoidal_assoc] ，
 [cinterp_braid_ap] ）是刻意独立的：它们的陈述
 完全是目标端的，因此 [Construction/ColouredPROP/Presentation/Universal.v] 
 原样重用了它们用于所展示的彩色 PROP。
*)

Section CUniversal.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (P : ColouredPROP Colour).
Context {HP : @HomEqProp P}.
Context {OD : @ObjDecEq P}.
Context (v : CValuation P S).

Notation "⟦ cs ⟧" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧").

(*
   * ** 1. The interpretation functor

   Objects go to [cprop_of_list]; morphisms go through [cinterp].
   Respectfulness is exactly the soundness theorem of [Interp.v], and
   the functor laws hold by computation, because [cinterp] reduces on
   the [CT_id] and [CT_comp] constructors. 

   --------
   * ** 1. 解释函子

   对象映射到 [cprop_of_list]；态射通过 [cinterp] 映射。
   保持性恰好是 [Interp.v] 的正确性定理，并且函子定律通过计算成立，因为 [cinterp] 在 [CT_id] 和 [CT_comp] 构造子上可以化简。
*)

Lemma CInterpF_fmap_id (cs : list Colour) :
  cinterp P S v (CT_id cs) ≈ id[⟦cs⟧].
Proof. reflexivity. Qed.

Lemma CInterpF_fmap_comp {cs ds es : list Colour}
  (f : CTerm S ds es) (g : CTerm S cs ds) :
  cinterp P S v (CT_comp f g) ≈ cinterp P S v f ∘ cinterp P S v g.
Proof. reflexivity. Qed.

(*
 Built with an explicit [Build_Functor] so that the source and target
 categories are pinned (the [QuotientProj] discipline of
 [Construction/Quotient.v]); a bare record literal would try to infer
 them from the field values, which live in [list Colour] and [P]. 

 --------
 使用显式的 [Build_Functor] 构建，以便源类别和目标类别被固定（[QuotientProj] 的 [Construction/Quotient.v] 纪律）；一个裸记录字面量会尝试从字段值推断它们，这些字段值位于 [list Colour] 和 [P] 中。
*)
Definition CInterpF : CFreeCat S ⟶ P :=
  Build_Functor (CFreeCat S) P
    (@cprop_of_list Colour P)
    (fun cs ds t => cinterp P S v t)
    (fun cs ds s t Hst => cinterp_sound P S v Hst)
    CInterpF_fmap_id
    (fun cs ds es f g => CInterpF_fmap_comp f g).

(*
   * Machine-checked: [CInterpF] EXTENDS the valuation — every generator
   is sent to its assigned morphism, definitionally.  Together with
   [CInterpF_interp_unique_self] below, this is the existence half of
   the universal property in named form. 

   --------
   * 机器检查：[CInterpF] 扩展了估值——每个生成元都被发送到其定义上的态射。结合下面的 [CInterpF_interp_unique_self]，这是以命名形式表示的泛性质的存在部分。
*)
Example CInterpF_extends_valuation (cs ds : list Colour) (g : S cs ds) :
  fmap[CInterpF] (CT_gen g) = v cs ds g := eq_refl.

(*
   * ** 2. Named coherence lemmas

   Every statement is purely target-side (only [P]-morphisms appear),
   so [Presentation/Universal.v] can reuse them for the presented
   coloured PROP, whose structural maps are the very same [CT_cast]
   terms.

   The [_general] lemmas quantify over the object equalities: after
   destructing them, the single non-destructible residue is aligned
   with the canonical strict equality by [obj_uip] (axiom-free UIP on
   [obj P], from [ObjDecEq]).  As everywhere in the coloured spine,
   proof irrelevance is routed through the TARGET's objects; the
   colour decider [Cdec] plays no role in this section. 

   --------
   * ** 2. 命名一致性引理

   每个陈述都是纯粹的目标端（只出现 [P] -态射），因此 [Presentation/Universal.v] 可以将它们重新用于所展示的彩色 PROP，其结构映射正是相同的 [CT_cast] 项。

   [_general] 引理量化在对象等式之上：在对它们进行析构后，唯一不可析构的残余与 [obj_uip] 的典型严格等式对齐（来自 [ObjDecEq] 的 [obj P] 上无公理 UIP）。就像彩色脊索中的各处一样，证明无关性通过 TARGET 的对象来实现；彩色判定器 [Cdec] 在本节中不起作用。
*)

(*
   * Naturality of the tensor-comparison cast against [cinterp]: the
   conjugating cast of [⊞c] cancels its inverse. 

   --------
   * 相对于 [cinterp] 的张量比较转换的自然性：[⊞c] 的共轭转换抵消了它的逆。
*)
Lemma cinterp_ap_natural {m n m' n' : list Colour}
  (f : CTerm S m m') (g : CTerm S n n') :
  cinterp P S v (CT_tens f g) ∘ id_cast (@cprop_tensor_app Colour P m n)
    ≈ id_cast (@cprop_tensor_app Colour P m' n')
        ∘ (cinterp P S v f ⨂[MPc P] cinterp P S v g).
Proof.
  cbn [cinterp].
  unfold ctensor_hom.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(** The inverse-direction square, by flipping across the casts. / 反向平方，通过跨模具翻转。 *)
Lemma cinterp_ap_natural_from {m n m' n' : list Colour}
  (f : CTerm S m m') (g : CTerm S n n') :
  (cinterp P S v f ⨂[MPc P] cinterp P S v g)
      ∘ id_cast (eq_sym (@cprop_tensor_app Colour P m n))
    ≈ id_cast (eq_sym (@cprop_tensor_app Colour P m' n'))
        ∘ cinterp P S v (CT_tens f g).
Proof.
  apply cid_cast_flip.
  apply cinterp_ap_natural.
Qed.

(*
   * General left-unit coherence: with every comparison an [id_cast],
   the left-unitality square collapses to the strict unitor. 

   --------
   * 一般左单位一致性：每次比较都有一个[id_cast]，
   左单位性方格坍缩为严格酉子。
*)
Lemma cto_unit_left_cast_general {u w s : P}
  (eu : @I P (MPc P) = u) (e : (u ⨂[MPc P] w)%object = s) (d : s = w) :
  to (@unit_left P (MPc P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id_cast eu ⨂[MPc P] id[w]).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_left_obj w)).
  rewrite !id_right.
  symmetry; apply cstrict_unitl_cast.
Qed.

(** General right-unit coherence. / 一般右单元一致性。 *)
Lemma cto_unit_right_cast_general {u w s : P}
  (eu : @I P (MPc P) = u) (e : (w ⨂[MPc P] u)%object = s) (d : s = w) :
  to (@unit_right P (MPc P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id[w] ⨂[MPc P] id_cast eu).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_right_obj w)).
  rewrite !id_right.
  symmetry; apply cstrict_unitr_cast.
Qed.

(** General associativity coherence. / 一般结合性一致性。 *)
Lemma cto_assoc_cast_general {a b c ab bc u w : P}
  (eab : (a ⨂[MPc P] b)%object = ab)
  (ebc : (b ⨂[MPc P] c)%object = bc)
  (eu : (ab ⨂[MPc P] c)%object = u)
  (ew : (a ⨂[MPc P] bc)%object = w)
  (d : u = w) :
  id_cast d ∘ id_cast eu ∘ (id_cast eab ⨂[MPc P] id[c])
    ≈ id_cast ew ∘ (id[a] ⨂[MPc P] id_cast ebc)
        ∘ to (@tensor_assoc P (MPc P) a b c).
Proof using OD P.
  destruct eab, ebc, eu, ew.
  rewrite !id_cast_refl.
  rewrite !bimap_id_id.
  rewrite (obj_uip d (strict_assoc_obj a b c)).
  rewrite !id_right, !id_left.
  apply cstrict_assoc_cast.
Qed.

(*
   * The left-unitality field of [MonoidalFunctor] at [CInterpF].  The
   boundary equation [[] ++ x = x] holds definitionally ([app] is
   left-strict), but [app_nil_l] is an opaque stdlib proof of it, so
   the cast is carried explicitly. 

   --------
   * 在  [CInterpF]  处的  [MonoidalFunctor]  的左幺元性域。边界方程  [[]  ++ x = x] 是定义上的（[app] 是左严格的），但 [app_nil_l] 是对此的一个不透明的标准库证明，因此类型转换是显式进行的。
*)
Lemma cinterp_monoidal_unit_left (x : list Colour) :
  to (@unit_left P (MPc P) ⟦x⟧)
    ≈ cinterp P S v (CT_cast (app_nil_l x))
        ∘ id_cast (@cprop_tensor_app Colour P [] x)
        ∘ (id_cast (@cprop_unit_nil Colour P) ⨂[MPc P] id[⟦x⟧]).
Proof using OD P S v.
  rewrite cinterp_CT_cast.
  unfold chcast.
  apply cto_unit_left_cast_general.
Qed.

(*
   * The right-unitality field of [MonoidalFunctor] at [CInterpF]. 

   --------
   * 在  [CInterpF] 处的  [MonoidalFunctor]  的右单位性场。
*)
Lemma cinterp_monoidal_unit_right (x : list Colour) :
  to (@unit_right P (MPc P) ⟦x⟧)
    ≈ cinterp P S v (CT_cast (app_nil_r x))
        ∘ id_cast (@cprop_tensor_app Colour P x [])
        ∘ (id[⟦x⟧] ⨂[MPc P] id_cast (@cprop_unit_nil Colour P)).
Proof using OD P S v.
  rewrite cinterp_CT_cast.
  unfold chcast.
  apply cto_unit_right_cast_general.
Qed.

(*
   * The associativity field of [MonoidalFunctor] at [CInterpF].
   Recall the stdlib orientation of [app_assoc] (right-to-left
   reassociation), so the source associator's [to] is the [eq_sym]
   cast — the orientation fixed once in [Cast.v]. 

   --------
   *  [MonoidalFunctor] 在 [CInterpF] 的结合性字段。
   回想 [app_assoc] 的标准库方向（从右到左重结合），所以源结合子的 [to] 是 [eq_sym] 类型转换 —— 方向在 [Cast.v] 中固定一次。
*)
Lemma cinterp_monoidal_assoc (x y z : list Colour) :
  cinterp P S v (CT_cast (eq_sym (app_assoc x y z)))
      ∘ id_cast (@cprop_tensor_app Colour P (x ++ y) z)
      ∘ (id_cast (@cprop_tensor_app Colour P x y) ⨂[MPc P] id[⟦z⟧])
    ≈ id_cast (@cprop_tensor_app Colour P x (y ++ z))
        ∘ (id[⟦x⟧] ⨂[MPc P] id_cast (@cprop_tensor_app Colour P y z))
        ∘ to (@tensor_assoc P (MPc P) ⟦x⟧ ⟦y⟧ ⟦z⟧).
Proof using OD P S v.
  rewrite cinterp_CT_cast.
  unfold chcast.
  apply cto_assoc_cast_general.
Qed.

(*
   * The braid-compatibility square of [cinterp] against the target's
   strict-path braiding [cstrict_braid]. 

   --------
   * [cinterp] 对目标的严格路径编织 [cstrict_braid] 的编织兼容性方阵。
*)
Lemma cinterp_braid_ap (cs ds : list Colour) :
  cinterp P S v (CT_braid cs ds)
      ∘ id_cast (@cprop_tensor_app Colour P cs ds)
    ≈ id_cast (@cprop_tensor_app Colour P ds cs)
        ∘ cstrict_braid P ⟦cs⟧ ⟦ds⟧.
Proof.
  cbn [cinterp].
  unfold cbraid_hom.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(*
   * ** 3. The strong and strict monoidal structure on [CInterpF]

   The tensor comparison is the [cprop_tensor_app] cast, packaged as
   a natural isomorphism in the functor category. 

   --------
   * ** 3. 在  [CInterpF] 上的强且严格的单oidal 结构

   张量比较是  [cprop_tensor_app] 的转换，封装为函子范畴中的自然同构。
*)

Definition CInterpF_ap_dom : CFreeCat S ∏ CFreeCat S ⟶ P :=
  @tensor P (MPc P) ◯ CInterpF ∏⟶ CInterpF.

Definition CInterpF_ap_cod : CFreeCat S ∏ CFreeCat S ⟶ P :=
  CInterpF ◯ @tensor (CFreeCat S) (CFreeCat_Monoidal S Cdec).

Definition CInterpF_ap_to : CInterpF_ap_dom ⟹ CInterpF_ap_cod :=
  @Build_Transform' (CFreeCat S ∏ CFreeCat S) P
    CInterpF_ap_dom CInterpF_ap_cod
    (fun mn => id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    (fun x y f => cinterp_ap_natural (fst f) (snd f)).

Definition CInterpF_ap_from : CInterpF_ap_cod ⟹ CInterpF_ap_dom :=
  @Build_Transform' (CFreeCat S ∏ CFreeCat S) P
    CInterpF_ap_cod CInterpF_ap_dom
    (fun mn => id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn))))
    (fun x y f => cinterp_ap_natural_from (fst f) (snd f)).

(*
   * The two composites are the identity transformation, componentwise.
   (In the functor category the identity's component at [mn] is
   [fmap id], which on each side reduces to a tensor of identities.) 

   --------
   * 这两个复合是逐分量的恒等变换。
   （在函子范畴中，恒等变换在 [mn] 处的分量是 [fmap id]， 在每一边都约简为恒等映射的张量。）
*)
Lemma CInterpF_ap_to_from (mn : CFreeCat S ∏ CFreeCat S) :
  id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
      ∘ id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    ≈ cinterp P S v (CT_tens (CT_id (fst mn)) (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [cinterp].
  apply ctensor_hom_id.
Qed.

Lemma CInterpF_ap_from_to (mn : CFreeCat S ∏ CFreeCat S) :
  id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
      ∘ id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
    ≈ (cinterp P S v (CT_id (fst mn)) ⨂[MPc P] cinterp P S v (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [cinterp].
  apply bimap_id_id.
Qed.

(*
 The functor-category isomorphism is an explicit [Build_Isomorphism]
 application, pinning the ambient category to the functor category
 [Fun (CFreeCat S ∏ CFreeCat S) P] (a record literal would leave it
 to inference; see the import note at the top for why the category
 is written in qualified form rather than bracket notation). 

 --------
 函子范畴同构是一个显式的 [Build_Isomorphism] 应用，将环境范畴固定为函子范畴 [Fun (CFreeCat S ∏ CFreeCat S) P]（使用记录字面量会将其留给推断；见顶部的导入说明了解为何该范畴以限定形式而非括号符号表示）。
*)
Definition CInterpF_ap_iso :
  @Isomorphism (@Category.Instance.Fun.Fun (CFreeCat S ∏ CFreeCat S) P)
    CInterpF_ap_dom CInterpF_ap_cod :=
  @Build_Isomorphism (@Category.Instance.Fun.Fun (CFreeCat S ∏ CFreeCat S) P)
    CInterpF_ap_dom CInterpF_ap_cod
    CInterpF_ap_to CInterpF_ap_from
    CInterpF_ap_to_from CInterpF_ap_from_to.

(*
   * The strong monoidal structure.  All proof fields are the named
   lemmas of section 2; the derived-iso data fields are casts. 

   --------
   * 强单体结构。所有证明字段都是第2节的命名引理；派生同构数据字段是类型转换。
*)
Definition CInterpF_Monoidal :
  @MonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec) (MPc P)
    CInterpF :=
  @Build_MonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec) (MPc P)
    CInterpF
    (id_cast_iso (@cprop_unit_nil Colour P))
    CInterpF_ap_iso
    (fun x : list Colour => @unit_left P (MPc P) ⟦x⟧)
    (fun x : list Colour =>
       iso_compose
         (id_cast_iso (f_equal (@cprop_of_list Colour P)
                               (eq_sym (app_nil_r x))))
         (@unit_right P (MPc P) ⟦x⟧))
    (fun x y z : list Colour =>
       id_cast_iso
         (eq_trans
            (f_equal (fun u : P => (u ⨂[MPc P] ⟦z⟧)%object)
                     (@cprop_tensor_app Colour P x y))
            (eq_trans (@cprop_tensor_app Colour P (x ++ y) z)
                      (f_equal (@cprop_of_list Colour P)
                               (eq_sym (app_assoc x y z))))))
    cinterp_monoidal_unit_left
    cinterp_monoidal_unit_right
    cinterp_monoidal_assoc.

(*
   * The comparisons ARE the coloured PROP's strictness equalities,
   verbatim. 

   --------
   * 这些比较严格来说就是彩色道具的严格相等关系，逐字对应。
*)
Lemma CInterpF_strict_pure_iso_id :
  to (@pure_iso _ _ _ _ CInterpF CInterpF_Monoidal)
    ≈ match @cprop_unit_nil Colour P in _ = T return @I P (MPc P) ~{P}~> T
      with eq_refl => id end.
Proof. reflexivity. Qed.

Lemma CInterpF_strict_ap_iso_id (x y : list Colour) :
  to (@ap_iso _ _ _ _ CInterpF CInterpF_Monoidal x y)
    ≈ match @cprop_tensor_app Colour P x y in _ = T
            return ((CInterpF x ⨂[MPc P] CInterpF y)%object ~{P}~> T)
      with eq_refl => id end.
Proof. reflexivity. Qed.

Definition CInterpF_Strict :
  @StrictMonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec) (MPc P)
    CInterpF :=
  @Build_StrictMonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec)
    (MPc P) CInterpF
    CInterpF_Monoidal
    (@cprop_unit_nil Colour P)                     (* the class field / 类字段 *)
    (fun x y : list Colour => @cprop_tensor_app Colour P x y)  (* ditto *)
    CInterpF_strict_pure_iso_id
    CInterpF_strict_ap_iso_id.

(*
   * Machine-checked: the strict object comparisons of [CInterpF_Strict]
   are the coloured-PROP class fields themselves. 

   --------
   * 机器检查：[CInterpF_Strict] 的严格对象比较是彩色-PROP 类字段本身。
*)
Example CInterpF_strict_pure_obj_is_cprop_unit_nil :
  @strict_pure_obj _ _ _ _ CInterpF CInterpF_Strict
  = @cprop_unit_nil Colour P := eq_refl.

Example CInterpF_strict_ap_obj_is_cprop_tensor_app (x y : list Colour) :
  @strict_ap_obj _ _ _ _ CInterpF CInterpF_Strict x y
  = @cprop_tensor_app Colour P x y := eq_refl.

(*
   * ** 4. Symmetry

   [CSymmetricStrict G MG] is the braid-compatibility square of a
   monoidal functor [G] over ITS OWN tensor comparison, with the
   target braiding re-indexed to the strict path by [cstrict_braid].
   See the header for why uniqueness is phrased against this bundle
   rather than against the two independent functor classes of
   [Functor/Structure/Monoidal/Strict.v] and
   [Functor/Structure/Monoidal/Braided.v]. 

   --------
   * ** 4. 对称性

   [CSymmetricStrict G MG] 是一个单体函子 [G] 在其自身张量比较下的编辫兼容方格，其目标编辫通过 [cstrict_braid] 重索引到严格路径。
   参见标题，了解为何唯一性是相对于这个束而不是相对于两个独立的函子类 [Functor/Structure/Monoidal/Strict.v] 和 [Functor/Structure/Monoidal/Braided.v] 来表述的。
*)

Definition CSymmetricStrict (G : CFreeCat S ⟶ P)
  (MG : @MonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec) (MPc P) G) :
  Type :=
  ∀ cs ds : list Colour,
    fmap[G] (CT_braid cs ds) ∘ to (@ap_iso _ _ _ _ G MG cs ds)
      ≈ to (@ap_iso _ _ _ _ G MG ds cs) ∘ cstrict_braid P (G cs) (G ds).

Lemma CInterpF_SymmetricStrict : CSymmetricStrict CInterpF CInterpF_Monoidal.
Proof.
  intros cs ds.
  exact (cinterp_braid_ap cs ds).
Qed.

(*
   * *** Bridges to the braided/symmetric functor classes of
   [Functor/Structure/Monoidal/Braided.v]

   The braid square at the transported functor is the braid square at
   the original functor against the transported braid family; both
   lemmas destruct a VARIABLE [Monoidal] equality, so the concrete
   [cprop_monoidal_coherence] is never eliminated in a goal — the
   same quarantine discipline as [Interp.v]. 

   --------
   * *** 连接到 [Functor/Structure/Monoidal/Braided.v] 的编织/对称函子类  

   在被传送的函子上，编织平方就是在原始函子上针对被传送的编织族的编织平方；两个引理都分解了一个 VARIABLE [Monoidal] 等式，因此具体的 [cprop_monoidal_coherence] 在目标中从不被消去 — 与 [Interp.v] 相同的隔离纪律。
*)

Lemma CSymmetricStrict_square_transport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : CFreeCat S ⟶ P)
  (MG : @MonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec) N1 G)
  (b : braid_family N2) (x y : list Colour) :
  fmap[G] (CT_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y) →
  fmap[G] (CT_braid x y)
      ∘ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
    ≈ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) y x)
        ∘ b (G x) (G y).
Proof.
  revert b; destruct e; intros b H.
  exact H.
Qed.

(*
   * The converse direction: a braid square at the transported functor
   comes back to one at the original, against the transported braid. 

   --------
   * 相反方向：传递函子上的编织平方会回到原来的一个，对抗传递的编织。
*)
Lemma CSymmetricStrict_untransport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : CFreeCat S ⟶ P)
  (MG : @MonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec) N1 G)
  (MG' : @MonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec) N2 G)
  (b : braid_family N2)
  (Hap : ∀ x y : list Colour,
     to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
       ≈ to (@ap_iso _ _ _ _ G MG' x y))
  (Hsq : ∀ x y : list Colour,
     fmap[G] (CT_braid x y) ∘ to (@ap_iso _ _ _ _ G MG' x y)
       ≈ to (@ap_iso _ _ _ _ G MG' y x) ∘ b (G x) (G y)) :
  ∀ x y : list Colour,
    fmap[G] (CT_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y).
Proof.
  revert MG' b Hap Hsq; destruct e; intros MG' b Hap Hsq x y.
  simpl in Hap.
  rewrite (Hap x y), (Hap y x).
  exact (Hsq x y).
Qed.

(*
   * The braid square of [CInterpF] against the SYMMETRIC-path braiding,
   obtained by transporting [CInterpF_SymmetricStrict] across the
   coherence.  Standalone so that the [BraidedMonoidalFunctor] record
   below is an explicit constructor application. 

   --------
   * 在对称路径编织下，[CInterpF] 的编织平方，通过将 [CInterpF_SymmetricStrict] 在一致性上运输得到。独立存在，以便下面的 [BraidedMonoidalFunctor] 记录是一个显式的构造器应用。
*)
Lemma CInterpF_Braided_compat (x y : list Colour) :
  fmap[CInterpF] (CT_braid x y)
      ∘ to (@ap_iso _ _ _ _ CInterpF
              (MonoidalFunctor_transport (@cprop_monoidal_coherence Colour P)
                 CInterpF_Monoidal) x y)
    ≈ to (@ap_iso _ _ _ _ CInterpF
            (MonoidalFunctor_transport (@cprop_monoidal_coherence Colour P)
               CInterpF_Monoidal) y x)
        ∘ @braid P (@symmetric_is_braided P (@cprop_symmetric Colour P))
            (CInterpF x) (CInterpF y).
Proof.
  exact (CSymmetricStrict_square_transport
           (@cprop_monoidal_coherence Colour P)
           CInterpF CInterpF_Monoidal
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@cprop_symmetric Colour P))
                a b)
           x y (CInterpF_SymmetricStrict x y)).
Qed.

(*
   * [CInterpF] as a [BraidedMonoidalFunctor]: the underlying
   strong structure is [CInterpF_Monoidal] transported across the
   coherence, and the braid square is [CInterpF_SymmetricStrict]. 

   --------
   *  [CInterpF] 作为  [BraidedMonoidalFunctor] ：其底层的强结构是  [CInterpF_Monoidal] ，通过相干性进行传递，且编结平方是  [CInterpF_SymmetricStrict] 。
*)
Definition CInterpF_Braided :
  @BraidedMonoidalFunctor (CFreeCat S) P (CFreeCat_Braided S Cdec)
    (@symmetric_is_braided P (@cprop_symmetric Colour P)) CInterpF :=
  @Build_BraidedMonoidalFunctor (CFreeCat S) P (CFreeCat_Braided S Cdec)
    (@symmetric_is_braided P (@cprop_symmetric Colour P)) CInterpF
    (MonoidalFunctor_transport (@cprop_monoidal_coherence Colour P)
       CInterpF_Monoidal)
    CInterpF_Braided_compat.

(*
   * [SymmetricMonoidalFunctor] is a [Definition] alias in
   [Functor/Structure/Monoidal/Braided.v], so the instance is
   supplied explicitly rather than by class search. 

   --------
   * [SymmetricMonoidalFunctor] 是 [Definition] 在 [Functor/Structure/Monoidal/Braided.v] 中的别名，因此实例是显式提供的，而不是通过类搜索获取的。
*)
Definition CInterpF_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat S) P (CFreeCat_Symmetric S Cdec)
    (@cprop_symmetric Colour P) CInterpF := CInterpF_Braided.

(*
   * Competitors arriving with a [BraidedMonoidalFunctor]
   convert to [CSymmetricStrict], given that their two tensor
   comparisons agree across the coherence transport. 

   --------
   * 竞争者携带 [BraidedMonoidalFunctor] 到达 
   转换为 [CSymmetricStrict]，假设它们的两个张量比较在相干传输中一致。
*)
Corollary CSymmetricStrict_of_Braided
  (G : CFreeCat S ⟶ P)
  (SG : @StrictMonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec)
          (MPc P) G)
  (BG : @BraidedMonoidalFunctor (CFreeCat S) P (CFreeCat_Braided S Cdec)
          (@symmetric_is_braided P (@cprop_symmetric Colour P)) G)
  (Hap : ∀ x y : list Colour,
     to (@ap_iso _ _ _ _ G
           (MonoidalFunctor_transport (@cprop_monoidal_coherence Colour P)
              (@strict_functor_is_monoidal _ _ _ _ G SG)) x y)
       ≈ to (@ap_iso _ _ _ _ G (@braided_is_strong _ _ _ _ G BG) x y)) :
  CSymmetricStrict G SG.
Proof.
  exact (CSymmetricStrict_untransport (@cprop_monoidal_coherence Colour P) G
           (@strict_functor_is_monoidal _ _ _ _ G SG)
           (@braided_is_strong _ _ _ _ G BG)
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@cprop_symmetric Colour P))
                a b)
           Hap
           (fun x y => @braid_compat _ _ _ _ G BG x y)).
Qed.

(*
   * ** 5. Uniqueness

   The cast toolbox is the transport kit of
   [Construction/Quotient.v] — sliding a cast across an equation
   ([comp_cast_shift]), fusing nested cast conjugations
   ([id_cast_conj_fuse]), identifying conjugations along different
   proofs of the same object equalities ([id_cast_conj_irr], UIP on
   [obj P]), and round-tripping [hom_cast]s ([hom_cast_roundtrip]) —
   plus its monoidal extension [cbimap_hom_cast] from
   [Construction/ColouredPROP/Interp.v]. 

   --------
   * ** 5. 唯一性

   cast 工具箱是 [Construction/Quotient.v] 的运输工具包——在方程上滑动一个 cast ([comp_cast_shift])，融合嵌套的 cast 共轭 ([id_cast_conj_fuse])，识别相同对象等式不同证明中的共轭 ([id_cast_conj_irr], [obj P] 上的 UIP)，以及往返 [hom_cast] ([hom_cast_roundtrip])——加上它从 [Construction/ColouredPROP/Interp.v] 扩展出的单幺半群 [cbimap_hom_cast] 。
*)

Section CUniqueness.

Context (G : CFreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec)
                (MPc P) G).
Context (HB : CSymmetricStrict G SG).
Context (Hobj : ∀ cs : list Colour, G cs = ⟦cs⟧).
Context (Hgen : ∀ cs ds (g : S cs ds),
  fmap[G] (CT_gen g)
    ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds)) (v cs ds g)).

(*
   * The tensor comparison of [SG], spelled as an [id_cast]. 

   --------
   * 张量比较 [SG]，被拼写为 [id_cast]。
*)
Lemma CG_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ G SG x y). Qed.

(*
   * Naturality of [SG]'s tensor comparison at a pair of terms. 

   --------
   * [SG] 在一对项上的张量比较的自然性。
*)
Lemma CG_ap_natural {m1 m2 n1 n2 : list Colour}
  (f : CTerm S m1 n1) (g : CTerm S m2 n2) :
  fmap[G] (CT_tens f g)
      ∘ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
              m1 m2)
    ≈ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
            n1 n2)
        ∘ (fmap[G] f ⨂[MPc P] fmap[G] g).
Proof.
  exact (naturality
           (to (@ap_functor_iso _ _ _ _ G
                  (@strict_functor_is_monoidal _ _ _ _ G SG)))
           (m1, m2) (n1, n2) (f, g)).
Qed.

(*
   * Main uniqueness: any strict symmetric competitor agreeing with [v]
   on generators agrees with [cinterp] on every term, up to the
   [hom_cast] conjugation along the object family [Hobj].  The proof
   is a structural induction on terms; thanks to UIP on [obj P], it
   works for an ARBITRARY family [Hobj], with no coherence hypothesis
   relating its members. 

   --------
   * 主要独特性：任何在生成元上与  [v]  严格对称的竞争者，在每一项上都与  [cinterp]  一致，最多只差沿对象族  [Hobj]  的  [hom_cast]  共轭。证明是对项的结构归纳；由于  [obj P]  上的 UIP，它对任意家族  [Hobj]  都成立，而无需关于其成员的相干性假设。
*)
Theorem cinterp_unique : ∀ cs ds (t : CTerm S cs ds),
  fmap[G] t
    ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds)) (cinterp P S v t).
Proof using Cdec G HB Hgen Hobj OD P S SG v.
  intros cs ds t.
  induction t as [k | bm bn | cm cn cp tg IHg tf IHf
                  | m1 n1 m2 n2 tf IHf tg IHg | gm gn gs].
  - (* CT_id *)
    cbn [cinterp].
    rewrite hom_cast_id.
    exact (@fmap_id (CFreeCat S) P G k).
  - (* CT_braid *)
    cbn [cinterp].
    unfold cbraid_hom.
    assert (Hb : fmap[G] (CT_braid bm bn)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG bn bm)
                  ∘ cstrict_braid P (G bm) (G bn)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG bm bn))).
    { apply comp_cast_shift.
      rewrite <- !CG_ap_cast.
      apply HB. }
    rewrite Hb.
    rewrite (cstrict_braid_cast P (eq_sym (Hobj bm)) (eq_sym (Hobj bn))).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* CT_comp *)
    cbn [cinterp].
    rewrite <- (hom_cast_comp (eq_sym (Hobj cm)) (eq_sym (Hobj cn))
                  (eq_sym (Hobj cp))).
    rewrite <- IHg, <- IHf.
    exact (@fmap_comp (CFreeCat S) P G cm cn cp tg tf).
  - (* CT_tens *)
    cbn [cinterp].
    unfold ctensor_hom.
    assert (Ht : fmap[G] (CT_tens tf tg)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG n1 n2)
                  ∘ (fmap[G] tf ⨂[MPc P] fmap[G] tg)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG m1 m2))).
    { apply comp_cast_shift.
      rewrite <- !CG_ap_cast.
      apply CG_ap_natural. }
    rewrite Ht.
    rewrite IHf, IHg.
    rewrite (cbimap_hom_cast P).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* CT_gen *)
    apply Hgen.
Qed.

End CUniqueness.

(*
   * *** Existence, machine-checked against the hypothesis pack

   [CInterpF] itself — with its strict structure [CInterpF_Strict],
   its braid square [CInterpF_SymmetricStrict], and the object family
   [Hobj := eq_refl] (its object action is [cprop_of_list] on the
   nose) — satisfies the hypotheses of [cinterp_unique]: the
   generator agreement is [CInterpF_extends_valuation] up to trivial
   casts, and instantiating the theorem at [CInterpF] typechecks.
   This is the named witness that the mediating functor of the
   existence half is itself pinned by the uniqueness half. 

   --------
   * *** 存在性，经机器验证与假设包一致

   [CInterpF] 本身 — 具有其严格结构 [CInterpF_Strict]，
   它的编织平方 [CInterpF_SymmetricStrict]，以及对象族
   [Hobj := eq_refl]（其对象作用是 [cprop_of_list] 于
   鼻子上）— 满足 [cinterp_unique] 的假设：生成元一致性为 [CInterpF_extends_valuation]，最多经过平凡转换，并且在 [CInterpF] 处实例化定理可以通过类型检查。
   这是命名的见证，表明存在性半部分的中介函子本身被唯一性半部分固定。
*)

Example CInterpF_generator_agreement (cs ds : list Colour) (g : S cs ds) :
  fmap[CInterpF] (CT_gen g)
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦cs⟧)) (eq_sym (@eq_refl _ ⟦ds⟧))
               (v cs ds g).
Proof. reflexivity. Qed.

Example CInterpF_interp_unique_self (cs ds : list Colour)
  (t : CTerm S cs ds) :
  fmap[CInterpF] t
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦cs⟧)) (eq_sym (@eq_refl _ ⟦ds⟧))
               (cinterp P S v t).
Proof using Cdec HP OD P S v.
  exact (cinterp_unique CInterpF CInterpF_Strict CInterpF_SymmetricStrict
           (fun ks : list Colour => eq_refl) CInterpF_generator_agreement
           cs ds t).
Qed.

(*
   * *** Uniqueness from single-wire object data

   The object family [Hobj] can be synthesised from the single-wire
   data [H1 : ∀ c, G [c] = ⟦[c]⟧] — the coloured analogue of the
   one-sorted donor's single datum [G 1 = ⟦1⟧].  Nil-arity agreement
   is [strict_pure_obj] against [cprop_unit_nil], and cons agreement
   peels one typed wire off with [strict_ap_obj] against
   [cprop_tensor_app], using the definitional fact
   [[c] ⨂ cs' = [c] ++ cs' = c :: cs'] on the free side. 

   --------
   * *** 单线对象数据的唯一性

   对象族 [Hobj] 可以从单线数据 [H1 : ∀ c, G [c] = ⟦ [c] ⟧] 合成——它是单排序捐赠者单一数据 [G 1 = [H1 : ∀ c, G [c]] 的彩色类比。零元性一致性是 [strict_pure_obj] 对 [cprop_unit_nil]，而 cons 一致性通过 [strict_ap_obj] 对 [cprop_tensor_app] 剥离一根类型化的线，使用自由端上的定义事实 [[c] ⨂ cs' = [c] ++ cs' = c :: cs']。
*)

Section CUniquenessFromWires.

Context (G : CFreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec)
                (MPc P) G).
Context (HB : CSymmetricStrict G SG).
Context (H1 : ∀ c : Colour, G [c] = ⟦[c]⟧).

Fixpoint G_obj (cs : list Colour) : G cs = ⟦cs⟧ :=
  match cs with
  | [] => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                   (@cprop_unit_nil Colour P)
  | c :: cs' =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG [c] cs'))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MPc P] b)%object)
                     (H1 c) (G_obj cs'))
           (@cprop_tensor_app Colour P [c] cs'))
  end.

Corollary cinterp_unique_from_wires
  (Hgen : ∀ cs ds (g : S cs ds),
     fmap[G] (CT_gen g)
       ≈ hom_cast (eq_sym (G_obj cs)) (eq_sym (G_obj ds)) (v cs ds g)) :
  ∀ cs ds (t : CTerm S cs ds),
    fmap[G] t ≈ hom_cast (eq_sym (G_obj cs)) (eq_sym (G_obj ds))
                         (cinterp P S v t).
Proof using Cdec G H1 HB OD P S SG v.
  exact (cinterp_unique G SG HB G_obj Hgen).
Qed.

End CUniquenessFromWires.

(*
   * *** Agreement of competitors

   Any two strict symmetric functors that agree with [v] on the
   generators agree with each other on every term, after re-indexing
   both to the canonical objects. 

   --------
   * *** 竞争者的一致性

   任何两个在生成元上与 [v] 一致的严格对称函子，在将两者重新索引到标准对象后，在每一个项上都彼此一致。
*)

Corollary cinterp_unique2
  (G1 : CFreeCat S ⟶ P)
  (SG1 : @StrictMonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec)
           (MPc P) G1)
  (HB1 : CSymmetricStrict G1 SG1)
  (Hobj1 : ∀ cs : list Colour, G1 cs = ⟦cs⟧)
  (Hgen1 : ∀ cs ds (g : S cs ds),
     fmap[G1] (CT_gen g)
       ≈ hom_cast (eq_sym (Hobj1 cs)) (eq_sym (Hobj1 ds)) (v cs ds g))
  (G2 : CFreeCat S ⟶ P)
  (SG2 : @StrictMonoidalFunctor (CFreeCat S) P (CFreeCat_Monoidal S Cdec)
           (MPc P) G2)
  (HB2 : CSymmetricStrict G2 SG2)
  (Hobj2 : ∀ cs : list Colour, G2 cs = ⟦cs⟧)
  (Hgen2 : ∀ cs ds (g : S cs ds),
     fmap[G2] (CT_gen g)
       ≈ hom_cast (eq_sym (Hobj2 cs)) (eq_sym (Hobj2 ds)) (v cs ds g)) :
  ∀ cs ds (t : CTerm S cs ds),
    hom_cast (Hobj1 cs) (Hobj1 ds) (fmap[G1] t)
      ≈ hom_cast (Hobj2 cs) (Hobj2 ds) (fmap[G2] t).
Proof using Cdec OD P S v.
  intros cs ds t.
  rewrite (cinterp_unique G1 SG1 HB1 Hobj1 Hgen1 cs ds t).
  rewrite (cinterp_unique G2 SG2 HB2 Hobj2 Hgen2 cs ds t).
  now rewrite !hom_cast_roundtrip.
Qed.

End CUniversal.

Arguments CInterpF {Colour} S P {HP OD} v : assert.
Arguments CSymmetricStrict {Colour} S Cdec P G MG : assert.
