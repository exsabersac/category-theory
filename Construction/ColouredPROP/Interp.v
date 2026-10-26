Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.PROP.Interp.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(*
   * * Interpreting free coloured-PROP terms in an arbitrary coloured PROP 

   --------
   * * 在任意有色 PROP 中解释自由有色-PROP 项
*)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 Given a coloured signature [S] and a coloured PROP [P], a
 [CValuation] assigns to every generator [g : S cs ds] a morphism
 [⟦cs⟧ ~{P}~> ⟦ds⟧].  This file defines the induced interpretation
 [cinterp : CTerm S cs ds → (⟦cs⟧ ~{P}~> ⟦ds⟧)] and proves it SOUND
 for the equational theory [CTermEq] of
 [Construction/ColouredPROP/TermEq.v]: [CTermEq]-equal terms have
 equivalent interpretations.  This is the morphism-level content of
 the free coloured PROP's universal property; the functor packaging
 lives in the successor file [Construction/ColouredPROP/Universal.v].

 This file is the many-sorted mirror of [Construction/PROP/Interp.v]
 (the one-sorted donor), with [list Colour] replacing [nat], [++]
 replacing [+], [[]] replacing [0], and the boundary equations
 [app_nil_r] / [app_assoc] replacing [Nat.add_0_r] / [Nat.add_assoc].
 The development is organised in three layers:

 1.  [BraidTransport] — the coherence quarantine — is REUSED BY
 IMPORT from [Construction/PROP/Interp.v]: its section is
 generic over an arbitrary [Context {C : Category}], so
 [braid_family], [transport_braid] and the six
 [transport_braid_*] law transporters apply verbatim to the
 category underlying a coloured PROP.  A coloured PROP carries
 two [Monoidal] structures on the same category — the strict
 path [strict_is_monoidal cprop_strict] and the symmetric path
 [braided_is_monoidal (symmetric_is_braided cprop_symmetric)] —
 related by the propositional equality
 [cprop_monoidal_coherence]; the braiding and its laws live on
 the symmetric path, the strictness equalities [cprop_unit_nil]
 / [cprop_tensor_app] on the strict path.  Every transporter
 destructs a VARIABLE equality between two [Monoidal] records,
 so the transport reduces definitionally; the concrete coherence
 proof of [P] is eliminated here (at [cstrict_braid] and its six
 law images below) and, independently, in the MP/MB mediation of
 [Construction/ColouredPROP/Supply.v] ([ctensor_app_b] /
 [cunit_nil_b]) — the only place in the coloured-PROP
 development that matches on it directly.

 2.  The coloured-PROP-target kit — [cstrict_braid] (the transported
 braiding), cast/bimap interaction lemmas, the strict structural
 maps as [id_cast]s with their naturality restated as
 cast-sliding, the [⟦·⟧]-level combinators [chcast], [⊞c]
 ([ctensor_hom]) and [cbraid_hom], and the K-lemmas K1–K12
 giving the strict symmetric monoidal laws of [⊞c]/[cbraid_hom]
 at [list Colour]-indexed objects.  The UIP-flavoured lemmas
 require decidable object equality ([ObjDecEq P], axiom-free UIP
 via [Eqdep_dec]); note that NO decidability of [Colour] itself
 is needed anywhere in this file — where the one-sorted donor
 invoked UIP on [nat] via [Nat.eq_dec], the coloured kit works
 with proof irrelevance on the OBJECTS of the target [P]
 ([obj_uip] / [id_cast_irr] of [Construction/Quotient.v]).

 3.  [CValuation], [cinterp], and soundness.  [CTermEq] is
 [Prop]-valued while the hom equivalence [≈] of an abstract
 target is [Type]-valued, so the induction lands in the
 [Prop]-reflection [heq] of a [HomEqProp] instance and
 round-trips through [heq_intro] / [heq_elim] (see
 [Construction/Quotient.v]).  The induction covers every one of
 the nineteen [CTermEq] constructors.

 Naming: every definition and lemma here is [c]-prefixed so this
 file can be imported alongside the one-sorted
 [Construction/PROP/Interp.v] without collision. 

 --------
 nLab：https://ncatlab.org/nlab/show/PROP
 nLab：https://ncatlab.org/nlab/show/free+category
 维基百科：https://en.wikipedia.org/wiki/PROP_(category_theory)

 给定一个有色签名[S]和一个有色PROP [P]，[CValuation]将每个生成元[g : S cs ds]分配一个态射[⟦cs⟧ ~{P}~> ⟦ds⟧]。此文件定义了诱导的解释[cinterp : CTerm S cs ds → (⟦cs⟧ ~{P}~> ⟦ds⟧)]并证明它在[CTermEq]的方程理论下是正确的：[Construction/ColouredPROP/TermEq.v]：[CTermEq]-相等的项具有等价的解释。这是自由有色PROP的普遍性质在态射层面的内容；函子封装存在于后续文件[Construction/ColouredPROP/Universal.v]中。此文件是 [Construction/PROP/Interp.v]（单排序捐赠者）的多排序镜像，其中 [list Colour] 替换了 [nat]，[++] 替换了 [+]，[[] 替换了 [0]，边界方程 [app_nil_r] / [app_assoc] 替换了 [Nat.add_0_r] / [Nat.add_assoc]。该开发组织为三层：1. [BraidTransport] — 一致性隔离 — 被从 [Construction/PROP/Interp.v] 导入重复使用：它的部分是对任意 [Context {C : Category}] 的通用，因此 [braid_family]、[transport_braid] 和六个 [transport_braid_*] 法律传递器逐字适用于有色 PROP 所基于的范畴。有色 PROP 在同一范畴上携带两个 [Monoidal] 结构——严格路径 [strict_is_monoidal cprop_strict] 和对称路径 [braided_is_monoidal (symmetric_is_braided cprop_symmetric)]——通过命题等式 [cprop_monoidal_coherence] 相关联；交换作用及其定律存在于对称路径上，严格性等式 [cprop_unit_nil] / [cprop_tensor_app] 存在于严格路径上。每个传输器都会破坏两个 [Monoidal] 记录之间的 VARIABLE 相等性，因此传输定义上被简化；[P] 的具体一致性证明在此（在 [cstrict_braid] 及其下面的六个法则映像中）被消除，并且在 [Construction/ColouredPROP/Supply.v] 的 MP/MB 调解中（[ctensor_app_b] / [cunit_nil_b]）也是如此——这是彩色-PROP 开发中唯一直接匹配它的地方。2. 彩色-PROP-目标套件 —— [cstrict_braid]（传输的编织）、投射/二重映射交互引理、严格结构映射作为 [id_cast] 并将其自然性重新表述为投射滑动、[⟦·⟧] 级组合子 [chcast]、[⊞c]（[ctensor_hom]）和 [cbraid_hom]，以及 K 引理 K1–K12，给出了 [⊞c] / [cbraid_hom] 在 [list Colour] 索引对象上的严格对称单子律。UIP 风格的引理
 需要可判定的对象相等性（[ObjDecEq P]，通过 [Eqdep_dec] 的无公理 UIP）；请注意，在此文件的任何地方都不需要 [Colour] 本身的可判定性——其中单排序捐赠者通过 [Nat.eq_dec] 在 [nat] 上调用了 UIP，彩色工具包则在目标 [P] 的对象上使用了证明无关性（[obj_uip] / [id_cast_irr] 的 [Construction/Quotient.v]）。3. [CValuation]、[cinterp] 和健全性。[CTermEq] 是 [Prop] 值的，而抽象目标的同伦等价 [≈] 是 [Type] 值的，所以归纳落在 [HomEqProp] 实例的 [Prop] 反射 [heq] 中，并通过 [heq_intro] / [heq_elim] 进行往返（见 [Construction/Quotient.v]）。归纳覆盖了十九个 [CTermEq] 构造器中的每一个。

 命名：这里的每一个定义和引理都是以 [c] 为前缀，这样该文件就可以与单类型 [Construction/PROP/Interp.v] 一起导入而不会冲突。
*)

(** ** The coloured-PROP-target kit / ** 彩色-PROP-靶标套件 *)

Section CInterp.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).

(*
   * The coloured-PROP-object [⟦cs⟧], as in
   [Construction/ColouredPROP.v] (whose notation is section-local
   there and must be re-declared per file). 

   --------
   * 彩色-PROP-对象 [⟦cs⟧]，如同 [Construction/ColouredPROP.v] （其表示法在该节是局部的，且必须在每个文件中重新声明）。
*)
Notation "⟦ cs ⟧" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧").

(*
   * The two [Monoidal] paths through a coloured PROP: the strict one
   and the braided/symmetric one.  Everything downstream is phrased
   at [MPc]; the braid is imported from [MBc] by [transport_braid]. 

   --------
   * 两个经过上色 PROP 的 [Monoidal] 路径：严格路径和编织/对称路径。下游的所有内容都用 [MPc] 表达；编织由 [transport_braid] 从 [MBc] 导入。
*)
Definition MPc : @Monoidal P :=
  @strict_is_monoidal P (@cprop_strict Colour P).
Definition MBc : @Monoidal P :=
  @braided_is_monoidal P
    (@symmetric_is_braided P (@cprop_symmetric Colour P)).

(*
   * The braiding of [P], re-indexed to the strict monoidal path.  This
   definition and the six [cstrict_braid_*] lemmas following it are
   the only places in this file that mention
   [cprop_monoidal_coherence], and none of them destructs it: each
   merely passes the concrete coherence proof to a [BraidTransport]
   lemma imported from [Construction/PROP/Interp.v], which eliminates
   only its VARIABLE equality.  The rest of this file never touches
   the coherence again.  The same discipline governs the rest of the
   coloured-PROP development, with one deliberate exception: the
   MP/MB mediation of [Construction/ColouredPROP/Supply.v] destructs
   the concrete proof directly in [ctensor_app_b] / [cunit_nil_b]. 

   --------
   * [P] 的编织，重新索引到严格单体路径。这个定义以及随后的六个 [cstrict_braid_*] 引理是本文件中唯一提到 [cprop_monoidal_coherence] 的地方，并且没有一个破坏它：每个只是将具体的一致性证明传递给从 [Construction/PROP/Interp.v] 导入的 [BraidTransport] 引理，它只消除了其变量（VARIABLE）等式。本文件的其余部分再也没有触碰过该一致性。相同的规则也适用于彩色-PROP 的开发，其间有一个有意的例外：[Construction/ColouredPROP/Supply.v] 的 MP/MB 调解会在 [ctensor_app_b] / [cunit_nil_b] 中直接破坏具体的证明。
*)
Definition cstrict_braid : braid_family MPc :=
  transport_braid (@cprop_monoidal_coherence Colour P)
    (fun x y : P =>
       @braid P (@symmetric_is_braided P (@cprop_symmetric Colour P)) x y).

(*
   * Naturality of [cstrict_braid], in the transposed square form of
   [bimap_braid] ([Structure/Monoidal/Symmetric.v]). 

   --------
   * [cstrict_braid] 的自然性，在 [bimap_braid]（[Structure/Monoidal/Symmetric.v]）的转置方形形式中。
*)
Lemma cstrict_braid_swap {x y z w : P} (f : x ~> z) (g : y ~> w) :
  (g ⨂[MPc] f) ∘ cstrict_braid x y ≈ cstrict_braid z w ∘ (f ⨂[MPc] g).
Proof.
  apply (transport_braid_swap (@cprop_monoidal_coherence Colour P) _
           (fun a b c d f' g' => @bimap_braid P _ a b c d f' g')).
Qed.

(** [cstrict_braid] is an involution. / [cstrict_braid] 是一个自反运算。 *)
Lemma cstrict_braid_invol (x y : P) :
  cstrict_braid y x ∘ cstrict_braid x y ≈ id.
Proof.
  apply (transport_braid_invol (@cprop_monoidal_coherence Colour P) _
           (fun a b => @braid_invol P _ a b)).
Qed.

(** The first hexagon at [MPc]. / 第一个六边形在 [MPc] 。 *)
Lemma cstrict_braid_hex (x y z : P) :
  to (@tensor_assoc P MPc y z x) ∘ cstrict_braid x ((y ⨂[MPc] z)%object)
     ∘ to (@tensor_assoc P MPc x y z)
    ≈ (id[y] ⨂[MPc] cstrict_braid x z) ∘ to (@tensor_assoc P MPc y x z)
        ∘ (cstrict_braid x y ⨂[MPc] id[z]).
Proof.
  apply (transport_braid_hex (@cprop_monoidal_coherence Colour P) _
           (fun a b c => @hexagon_identity P _ a b c)).
Qed.

(** The second hexagon at [MPc]. / 第二个六边形在 [MPc] 。 *)
Lemma cstrict_braid_hex_sym (x y z : P) :
  from (@tensor_assoc P MPc z x y) ∘ cstrict_braid ((x ⨂[MPc] y)%object) z
     ∘ from (@tensor_assoc P MPc x y z)
    ≈ (cstrict_braid x z ⨂[MPc] id[y]) ∘ from (@tensor_assoc P MPc x z y)
        ∘ (id[x] ⨂[MPc] cstrict_braid y z).
Proof.
  apply (transport_braid_hex_sym (@cprop_monoidal_coherence Colour P) _
           (fun a b c => @hexagon_identity_sym P _ a b c)).
Qed.

(*
   * The unitor coherences at [MPc] (Joyal–Street Prop. 2.1, imported
   from [Structure/Monoidal/Braided/Proofs.v] and transported). 

   --------
   * 单位器在 [MPc] 处的一致性（Joyal–Street 命题 2.1，从 [Structure/Monoidal/Braided/Proofs.v] 导入并迁移）。
*)
Lemma cstrict_braid_unit_left (x : P) :
  to (@unit_left P MPc x) ∘ cstrict_braid x (@I P MPc)
    ≈ to (@unit_right P MPc x).
Proof.
  apply (transport_braid_unit_left (@cprop_monoidal_coherence Colour P) _
           (fun a => @braid_unit_left P _ a)).
Qed.

Lemma cstrict_braid_unit_right (x : P) :
  to (@unit_right P MPc x) ∘ cstrict_braid (@I P MPc) x
    ≈ to (@unit_left P MPc x).
Proof.
  apply (transport_braid_unit_right (@cprop_monoidal_coherence Colour P) _
           (fun a => @braid_unit_right P _ a)).
Qed.

(*
   * *** Casts and the tensor bifunctor

   Every strict structural map is an [id_cast], and every boundary
   cast interacts with [⨂[MPc]] by [f_equal]-images.  Each proof
   destructs the equality and closes with a bifunctor law. 

   --------
   * *** 类型转换和张量双函子

   每个严格的结构映射都是一个 [id_cast]，每个边界类型转换通过 [f_equal]-像与 [⨂[MPc] 交互。每个证明都会析构等式并以双函子定律结束。
*)

(*
   * A transparent pairing of object equalities through the tensor.
   The stdlib's [f_equal2] is opaque, so a cast along it would be
   stuck even at [eq_refl]; this local combinator reduces. 

   --------
   * 通过张量透明地配对对象等式。
   标准库的 [f_equal2] 是不透明的，因此沿它进行类型转换即使在 [eq_refl] 处也会卡住；这个局部组合子可以简化该过程。
*)
Definition ctensor_obj_eq {a a' b b' : P} (e : a = a') (e' : b = b') :
  (a ⨂[MPc] b)%object = (a' ⨂[MPc] b')%object :=
  match e in _ = u return ((a ⨂[MPc] b)%object = (u ⨂[MPc] b')%object) with
  | eq_refl =>
      match e' in _ = v
        return ((a ⨂[MPc] b)%object = (a ⨂[MPc] v)%object)
      with
      | eq_refl => eq_refl
      end
  end.

(** A tensor of casts is the cast along the paired equality. / 张量的转换是沿着配对等式的转换。 *)
Lemma cbimap_cast {a a' b b' : P} (e : a = a') (e' : b = b') :
  (id_cast e ⨂[MPc] id_cast e') ≈ id_cast (ctensor_obj_eq e e').
Proof.
  destruct e, e'.
  exact (@bimap_id_id P P P (@tensor P MPc) a b).
Qed.

(*
   * A cast in the left tensorand extracts as a whole-tensor cast. 

   --------
   * 左张量的转换被提取为整体张量转换。
*)
Lemma cbimap_cast_l {a a' x y : P} (e : a = a') (g : x ~> y) :
  (id_cast e ⨂[MPc] g)
    ≈ id_cast (f_equal (fun u : P => (u ⨂[MPc] y)%object) e)
        ∘ (id[a] ⨂[MPc] g).
Proof. destruct e; cat. Qed.

(*
   * A cast in the right tensorand extracts as a whole-tensor cast. 

   --------
   * 在正确的张量项上进行的类型转换会作为整体张量类型转换被提取。
*)
Lemma cbimap_cast_r {x y b b' : P} (g : x ~> y) (e : b = b') :
  (g ⨂[MPc] id_cast e)
    ≈ id_cast (f_equal (fun v : P => (y ⨂[MPc] v)%object) e)
        ∘ (g ⨂[MPc] id[b]).
Proof. destruct e; cat. Qed.

(*
   * Tensoring an identity with a cast IS a cast.  Like [cbimap_cast]
   through [cbimap_cast_r] above, these two are exported cast/tensor
   kit with no in-tree consumer yet; the current proofs reach the
   same effects through the slide lemmas and the [_general] forms
   below. 

   --------
   * 用张量操作将一个恒等式与一个类型转换结合是一个类型转换。就像上面通过 [cbimap_cast] 到 [cbimap_cast_r] 的情况，这两个是已导出的类型转换/张量工具包，但在树内还没有使用者；当前的证明通过滑动引理和下面的 [_general] 形式达到相同的效果。
*)
Lemma cbimap_cast_id_l {a x y : P} (e : x = y) :
  (id[a] ⨂[MPc] id_cast e)
    ≈ id_cast (f_equal (fun v : P => (a ⨂[MPc] v)%object) e).
Proof.
  destruct e.
  exact (@bimap_id_id P P P (@tensor P MPc) a x).
Qed.

Lemma cbimap_cast_id_r {a x y : P} (e : x = y) :
  (id_cast e ⨂[MPc] id[a])
    ≈ id_cast (f_equal (fun u : P => (u ⨂[MPc] a)%object) e).
Proof.
  destruct e.
  exact (@bimap_id_id P P P (@tensor P MPc) x a).
Qed.

(*
   * A tensor of [hom_cast]s is the [hom_cast] along the paired object
   equalities ([ctensor_obj_eq]).  This is the monoidal extension of
   the [hom_cast] kit of [Construction/Quotient.v]; it is consumed by
   the tens case of the uniqueness proof in [Universal.v]. 

   --------
   * 一个 [hom_cast] 的张量是沿着成对对象等式 ([ctensor_obj_eq]) 的 [hom_cast]。这是 [Construction/Quotient.v] 的 [hom_cast] 工具包的幺半群扩展；它被 [Universal.v] 中唯一性证明的张量情况所使用。
*)
Lemma cbimap_hom_cast {a b c d a' b' c' d' : P}
  (ea : a = a') (eb : b = b') (ec : c = c') (ed : d = d')
  (f : a ~> c) (g : b ~> d) :
  (hom_cast ea ec f ⨂[MPc] hom_cast eb ed g)
    ≈ hom_cast (ctensor_obj_eq ea eb) (ctensor_obj_eq ec ed)
               (f ⨂[MPc] g).
Proof. destruct ea, eb, ec, ed; reflexivity. Qed.

(*
   * [cstrict_braid] re-indexes along object equalities by [hom_cast].
   Consumed by the uniqueness proof of [Universal.v], whose braid
   case re-indexes a competitor's [cstrict_braid (G cs) (G ds)] to
   the canonical [cstrict_braid ⟦cs⟧ ⟦ds⟧] along the object
   agreement.  (The hexagon lemmas K9/K10 below do not need it: they
   quantify over the strictness equalities in the
   [cbraid_hex_*_general] forms instead.) 

   --------
   * [cstrict_braid] 按照对象等式通过 [hom_cast] 重新索引。
   被 [Universal.v] 的唯一性证明所使用，其编织情况
   按照对象一致性将竞争者的 [cstrict_braid (G cs) (G ds)]
   重新索引到规范的 [cstrict_braid ⟦cs⟧ ⟦ds⟧]。（下面的六边形引理 K9/K10 不需要它：它们
   对 [cbraid_hex_*_general] 形式中的严格等式进行量化。）
*)
Lemma cstrict_braid_cast {x x' y y' : P} (e1 : x = x') (e2 : y = y') :
  cstrict_braid x' y'
    ≈ hom_cast (ctensor_obj_eq e1 e2) (ctensor_obj_eq e2 e1)
               (cstrict_braid x y).
Proof. destruct e1, e2; reflexivity. Qed.

(*
   * Flipping a cast-naturality square across the inverse casts. 

   --------
   * 在逆向转换上翻转一个类型自然性的转换方块。
*)
Lemma cid_cast_flip {a b a' b' : P} (e1 : a = a') (e2 : b = b')
  (p : a ~> b) (q : a' ~> b') :
  q ∘ id_cast e1 ≈ id_cast e2 ∘ p →
  p ∘ id_cast (eq_sym e1) ≈ id_cast (eq_sym e2) ∘ q.
Proof.
  destruct e1, e2; simpl; intros Hq.
  rewrite id_right in Hq; rewrite id_left in Hq.
  rewrite id_right, id_left.
  symmetry; exact Hq.
Qed.

(*
   * Composing two cast-conjugated morphisms cancels the middle casts. 

   --------
   * 将两个类型转换后结合的态射组合，会消去中间的类型转换。
*)
Lemma cconj_compose {x y z x' y' z' : P}
  (e1 : x = x') (e2 : y = y') (e3 : z = z')
  (f : y ~> z) (g : x ~> y) :
  (id_cast e3 ∘ f ∘ id_cast (eq_sym e2))
     ∘ (id_cast e2 ∘ g ∘ id_cast (eq_sym e1))
    ≈ id_cast e3 ∘ (f ∘ g) ∘ id_cast (eq_sym e1).
Proof. destruct e1, e2, e3; cat. Qed.

(*
   * *** The strict structural maps as casts, with sliding naturality

   In a strict monoidal category the associator and unitors ARE the
   transported identities; their naturality squares become “slides”
   that move a cast past a tensor of morphisms. 

   --------
   * *** 严格的结构映射如同类型转换，具有滑动的自然性

   在严格的单结类中，结合子和单位子就是传递的恒等映射；它们的自然性方形变成“滑动”，将类型转换移过态射的张量。
*)

(*
   * The strict comparison fields, restated through [id_cast]. 

   --------
   * 严格的比较字段，通过 [id_cast] 重述。
*)
Lemma cstrict_assoc_cast (x y z : P) :
  id_cast (strict_assoc_obj x y z) ≈ to (@tensor_assoc P MPc x y z).
Proof. symmetry; apply strict_assoc_to. Qed.

Lemma cstrict_unitl_cast (x : P) :
  id_cast (strict_unit_left_obj x) ≈ to (@unit_left P MPc x).
Proof. symmetry; apply strict_unit_left_to. Qed.

Lemma cstrict_unitr_cast (x : P) :
  id_cast (strict_unit_right_obj x) ≈ to (@unit_right P MPc x).
Proof. symmetry; apply strict_unit_right_to. Qed.

(** Associator slide. / 联想器幻灯片。 *)
Lemma cstrict_assoc_slide {x y z x' y' z' : P}
  (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  (f ⨂[MPc] (g ⨂[MPc] h)) ∘ id_cast (strict_assoc_obj x y z)
    ≈ id_cast (strict_assoc_obj x' y' z') ∘ ((f ⨂[MPc] g) ⨂[MPc] h).
Proof.
  rewrite !cstrict_assoc_cast.
  apply to_tensor_assoc_natural.
Qed.

(** Left-unitor slide. / 左幺元滑动。 *)
Lemma cstrict_unitl_slide {x y : P} (g : x ~> y) :
  g ∘ id_cast (strict_unit_left_obj x)
    ≈ id_cast (strict_unit_left_obj y) ∘ (id[@I P MPc] ⨂[MPc] g).
Proof.
  rewrite !cstrict_unitl_cast.
  apply to_unit_left_natural.
Qed.

(** Right-unitor slide. / 右单位元滑动。 *)
Lemma cstrict_unitr_slide {x y : P} (g : x ~> y) :
  g ∘ id_cast (strict_unit_right_obj x)
    ≈ id_cast (strict_unit_right_obj y) ∘ (g ⨂[MPc] id[@I P MPc]).
Proof.
  rewrite !cstrict_unitr_cast.
  apply to_unit_right_natural.
Qed.

(** *** The [⟦·⟧]-level combinators / *** [⟦·⟧] 级组合子 *)

(** A boundary cast: the identity transported along [⟦e⟧]. / 边界作用：沿 [⟦e⟧] 传递的身份。 *)
Definition chcast {cs ds : list Colour} (e : cs = ds) : ⟦cs⟧ ~{P}~> ⟦ds⟧ :=
  @id_cast (cprop_cat P) ⟦cs⟧ ⟦ds⟧ (f_equal (@cprop_of_list Colour P) e).

(*
   * [chcast]s compose and cancel — with no proof irrelevance needed:
   each lemma destructs its boundary equation.  Of these, the
   soundness induction below consumes [chcast_inv_r]; [chcast_trans]
   and [chcast_inv_l] complete the algebra as exported kit with no
   in-tree consumer yet.  Proof IRRELEVANCE of [chcast] ([chcast_irr]
   / [chcast_loop]) needs decidable object equality on [P] and lives
   below the [ObjDecEq] hypothesis — where the one-sorted donor used
   UIP on [nat] outright, an arbitrary [Colour] carries no decider,
   and the coloured kit routes irrelevance through the TARGET's
   objects instead. 

   --------
   * [chcast] 进行组合和取消 —— 不需要无关性的证明：每个引理都会破坏其边界方程。在这些中，下面的健全性归纳使用了 [chcast_inv_r]；[chcast_trans] 和 [chcast_inv_l] 作为导出的工具包完成代数，但目前还没有树内使用者。[chcast]（[chcast_irr] / [chcast_loop]）的证明无关性需要在 [P] 上可判定的对象相等性，并存在于 [ObjDecEq] 假设之下 —— 其中单排序的捐赠者直接在 [nat] 上使用了 UIP，任意的 [Colour] 没有携带判定器，而彩色工具包则通过目标对象来传递无关性。
*)
Lemma chcast_trans {cs ds es : list Colour} (e1 : cs = ds) (e2 : ds = es) :
  chcast e2 ∘ chcast e1 ≈ chcast (eq_trans e1 e2).
Proof. destruct e1, e2; cat. Qed.

Lemma chcast_inv_l {cs ds : list Colour} (e : cs = ds) :
  chcast (eq_sym e) ∘ chcast e ≈ id.
Proof. destruct e; cat. Qed.

Lemma chcast_inv_r {cs ds : list Colour} (e : cs = ds) :
  chcast e ∘ chcast (eq_sym e) ≈ id.
Proof. destruct e; cat. Qed.

(*
   * Parallel composition at [⟦·⟧]-indexed objects: tensor at [MPc],
   conjugated by the [cprop_tensor_app] strictness casts. 

   --------
   * 在 [⟦·⟧] 索引的对象上的平行组合：在 [MPc] 的张量，由 [cprop_tensor_app] 严格性转换共轭。
*)
Definition ctensor_hom {a b c d : list Colour}
  (f : ⟦a⟧ ~{P}~> ⟦b⟧) (g : ⟦c⟧ ~{P}~> ⟦d⟧) : ⟦a ++ c⟧ ~{P}~> ⟦b ++ d⟧ :=
  id_cast (cprop_tensor_app b d) ∘ (f ⨂[MPc] g)
    ∘ id_cast (eq_sym (cprop_tensor_app a c)).

Infix "⊞c" := ctensor_hom (at level 30, right associativity).

(** The block braiding at [⟦·⟧]-indexed objects. / [⟦·⟧] 索引对象的块状编发。 *)
Definition cbraid_hom (cs ds : list Colour) : ⟦cs ++ ds⟧ ~{P}~> ⟦ds ++ cs⟧ :=
  id_cast (cprop_tensor_app ds cs) ∘ cstrict_braid ⟦cs⟧ ⟦ds⟧
    ∘ id_cast (eq_sym (cprop_tensor_app cs ds)).

(*
   * *** The K-kit, part one: bifunctor and braid laws of [⊞c]

   K1–K5 need no proof-irrelevance: the [cprop_tensor_app] casts
   cancel pairwise by [cconj_compose] and the core laws are those of
   [⨂[MPc]] and [cstrict_braid]. 

   --------
   * *** K-工具包，第一部分：[⊞c] 的双函子与编织律

   K1–K5 不需要证明无关性：[cprop_tensor_app] 的投射通过 [cconj_compose] 成对抵消，核心定律是 [⨂[MPc] 和 [cstrict_braid] 的定律。
*)

(** K1: [⊞c] preserves identities. / K1：[⊞c] 保留身份。 *)
Lemma ctensor_hom_id (cs ds : list Colour) :
  id[⟦cs⟧] ⊞c id[⟦ds⟧] ≈ id[⟦cs ++ ds⟧].
Proof.
  unfold ctensor_hom.
  rewrite bimap_id_id.
  rewrite id_right.
  apply id_cast_inv_r.
Qed.

(*
   * K2: [⊞c] preserves composition (middle-four interchange). 

   --------
   * K2：[⊞c] 保持组合（中间四项交换）。
*)
Lemma ctensor_hom_comp {a b c d j k : list Colour}
  (f : ⟦b⟧ ~{P}~> ⟦c⟧) (f' : ⟦a⟧ ~{P}~> ⟦b⟧)
  (g : ⟦j⟧ ~{P}~> ⟦k⟧) (g' : ⟦d⟧ ~{P}~> ⟦j⟧) :
  (f ∘ f') ⊞c (g ∘ g') ≈ (f ⊞c g) ∘ (f' ⊞c g').
Proof.
  unfold ctensor_hom.
  rewrite cconj_compose.
  now rewrite bimap_comp.
Qed.

(** K3: [⊞c] respects the hom equivalence. / K3: [⊞c] 尊重同调等价。 *)
#[export] Instance ctensor_hom_respects {a b c d : list Colour} :
  Proper (equiv ==> equiv ==> equiv) (@ctensor_hom a b c d).
Proof.
  proper.
  unfold ctensor_hom.
  now rewrite X, X0.
Qed.

(** K4: [cbraid_hom] is an involution. / K4: [cbraid_hom] 是一个自反变换。 *)
Lemma cbraid_hom_invol (cs ds : list Colour) :
  cbraid_hom ds cs ∘ cbraid_hom cs ds ≈ id[⟦cs ++ ds⟧].
Proof.
  unfold cbraid_hom.
  rewrite cconj_compose.
  rewrite cstrict_braid_invol.
  rewrite id_right.
  apply id_cast_inv_r.
Qed.

(** K5: naturality of [cbraid_hom] against [⊞c]. / K5：[cbraid_hom] 相对于 [⊞c] 的自然性。 *)
Lemma cbraid_hom_swap {m1 n1 m2 n2 : list Colour}
  (f : ⟦m1⟧ ~{P}~> ⟦n1⟧) (g : ⟦m2⟧ ~{P}~> ⟦n2⟧) :
  (g ⊞c f) ∘ cbraid_hom m1 m2 ≈ cbraid_hom n1 n2 ∘ (f ⊞c g).
Proof.
  unfold ctensor_hom, cbraid_hom.
  rewrite !cconj_compose.
  now rewrite cstrict_braid_swap.
Qed.

(*
   * *** The K-kit, part two: strict unit and associativity laws

   K6–K12 identify casts along DIFFERENT proofs of the same object
   equality, so they need uniqueness of identity proofs on [obj P] —
   axiom-free, via decidable object equality ([ObjDecEq], from
   [Construction/Quotient.v]).

   Each law is first proved in a fully general, object-level form
   that quantifies over the strictness equalities: destructing the
   quantified equalities makes the transports definitional, and the
   single non-destructible residue (a unit- or associativity-shaped
   loop) is aligned to the canonical strict equality by [obj_uip].
   The [⟦·⟧]-level K-lemma is then an instantiation.  These
   [_general] forms never compute on the boundary index type, which
   is why they transfer from the one-sorted donor with name
   substitution only. 

   --------
   * *** K-套件，第二部分：严格单位和结合律  

   K6–K12 识别沿不同证明的相同对象的类型转换，因此它们需要在 [obj P] 上的身份证明的唯一性——无公理，通过可判定的对象相等性（[ObjDecEq]，来自 [Construction/Quotient.v]）。  

   每条定律首先以完全一般的对象级形式证明，该形式对严格相等进行量化：析构量化的相等性使得传输成为定义性的，而单个不可析构的残余（单位或结合形状的循环）通过 [obj_uip] 与规范严格相等对齐。然后 [⟦·⟧] 级别的 K-引理是一种具体实例。这些 [_general] 形式从不在边界索引类型上计算，这就是为什么它们可以只通过名称替换从单一排序的供体转移过来。
*)

Context {OD : @ObjDecEq P}.

(*
   * [chcast] is proof-irrelevant in its boundary equation: both casts
   transport along object equalities of [P], which are unique under
   [ObjDecEq].  No decidability of [Colour] is involved. 

   --------
   * [chcast] 在其边界方程中是与证明无关的：两个类型转换沿着 [P] 的对象相等传输，而在 [ObjDecEq] 下它们是唯一的。[Colour] 的可判定性不涉及其中。
*)
Lemma chcast_irr {cs ds : list Colour} (e1 e2 : cs = ds) :
  chcast e1 = chcast e2.
Proof using OD P.
  unfold chcast.
  apply id_cast_irr.
Qed.

Lemma chcast_loop {cs : list Colour} (e : cs = cs) : chcast e = id.
Proof using OD P.
  unfold chcast.
  apply id_cast_loop.
Qed.

(** General left-unit absorption at [MPc]. / 在 [MPc] 的一般左单位吸收。 *)
Lemma ctensor_unit_left_general {u x y : P} (eu : @I P MPc = u)
  (f : x ~> y)
  (e1 : (u ⨂[MPc] x)%object = x) (e2 : (u ⨂[MPc] y)%object = y) :
  id_cast e2 ∘ (id[u] ⨂[MPc] f) ∘ id_cast (eq_sym e1) ≈ f.
Proof using OD P.
  destruct eu.
  unfold MPc.
  rewrite (obj_uip e1 (strict_unit_left_obj x)).
  rewrite (obj_uip e2 (strict_unit_left_obj y)).
  rewrite <- cstrict_unitl_slide.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_r.
  apply id_right.
Qed.

(*
   * K6: tensoring with [id ⟦[]⟧] on the left is the identity (the
   boundary equation [[] ++ a = a] holds definitionally, exactly as
   [0 + a = a] did in the one-sorted donor). 

   --------
   * K6：在左侧与 [id ⟦[] ⟧ 张量化是恒等（边界方程 [[] ++ a = a] 定义上成立，就像 [0 + a = a] 在单排序捐赠者中所做的一样）。
*)
Lemma ctensor_hom_idnil_left {a b : list Colour} (f : ⟦a⟧ ~{P}~> ⟦b⟧) :
  id[⟦[]⟧] ⊞c f ≈ f.
Proof using OD P.
  unfold ctensor_hom.
  apply (ctensor_unit_left_general (@cprop_unit_nil Colour P) f
           (cprop_tensor_app [] a) (cprop_tensor_app [] b)).
Qed.

(*
   * General right-unit absorption at [MPc], with mediating casts for
   the propositional boundary equation [a ++ [] = a]. 

   --------
   * 在 [MPc] 处进行一般的右单位吸收，同时为命题边界方程 [a ++ [] = a 提供中介投影。
*)
Lemma ctensor_unit_right_general {u x y x' y' : P} (eu : @I P MPc = u)
  (f : x ~> y)
  (e1 : (x ⨂[MPc] u)%object = x') (e2 : (y ⨂[MPc] u)%object = y')
  (d1 : x' = x) (d2 : y' = y) :
  id_cast e2 ∘ (f ⨂[MPc] id[u]) ∘ id_cast (eq_sym e1)
    ≈ id_cast (eq_sym d2) ∘ f ∘ id_cast d1.
Proof using OD P.
  destruct eu, d1, d2.
  unfold MPc.
  rewrite (obj_uip e1 (strict_unit_right_obj _)).
  rewrite (obj_uip e2 (strict_unit_right_obj _)).
  rewrite <- cstrict_unitr_slide.
  rewrite <- (comp_assoc f (id_cast (strict_unit_right_obj x'))
                (id_cast (eq_sym (strict_unit_right_obj x')))).
  rewrite id_cast_inv_r.
  cat.
Qed.

(*
   * K7: tensoring with [id ⟦[]⟧] on the right is the identity up to
   the [chcast]s along [a ++ [] = a]. 

   --------
   * K7：在右侧用  [id ⟦[] ⟧] 做张量运算，相当于恒等式，最高到沿着  [a ++ [] = a 的  [chcast] s。
*)
Lemma ctensor_hom_idnil_right {a b : list Colour} (f : ⟦a⟧ ~{P}~> ⟦b⟧) :
  f ⊞c id[⟦[]⟧]
    ≈ chcast (eq_sym (app_nil_r b)) ∘ f ∘ chcast (app_nil_r a).
Proof using OD P.
  unfold ctensor_hom, chcast.
  rewrite (id_cast_irr
             (f_equal (@cprop_of_list Colour P) (eq_sym (app_nil_r b)))
             (eq_sym (f_equal (@cprop_of_list Colour P) (app_nil_r b)))).
  apply (ctensor_unit_right_general (@cprop_unit_nil Colour P) f
           (cprop_tensor_app a []) (cprop_tensor_app b [])
           (f_equal (@cprop_of_list Colour P) (app_nil_r a))
           (f_equal (@cprop_of_list Colour P) (app_nil_r b))).
Qed.

(*
   * General strict associativity of the conjugated tensor at [MPc]. 

   --------
   * 在 [MPc] 处共轭张量的一般严格结合性。
*)
Lemma ctensor_assoc_general {x y z x' y' z' u u' v v' w w' s s' : P}
  (f : x ~> x') (g : y ~> y') (h : z ~> z')
  (exy : (x ⨂[MPc] y)%object = u) (exy' : (x' ⨂[MPc] y')%object = u')
  (eyz : (y ⨂[MPc] z)%object = v) (eyz' : (y' ⨂[MPc] z')%object = v')
  (eu : (u ⨂[MPc] z)%object = w) (eu' : (u' ⨂[MPc] z')%object = w')
  (ev : (x ⨂[MPc] v)%object = s) (ev' : (x' ⨂[MPc] v')%object = s')
  (d : w = s) (d' : w' = s') :
  id_cast d'
      ∘ (id_cast eu'
           ∘ ((id_cast exy' ∘ (f ⨂[MPc] g) ∘ id_cast (eq_sym exy)) ⨂[MPc] h)
           ∘ id_cast (eq_sym eu))
    ≈ (id_cast ev'
         ∘ (f ⨂[MPc] (id_cast eyz' ∘ (g ⨂[MPc] h) ∘ id_cast (eq_sym eyz)))
         ∘ id_cast (eq_sym ev))
        ∘ id_cast d.
Proof using OD P.
  destruct exy, exy', eyz, eyz', eu, eu', ev, ev'.
  unfold MPc.
  rewrite (obj_uip d (strict_assoc_obj x y z)).
  rewrite (obj_uip d' (strict_assoc_obj x' y' z')).
  rewrite !id_cast_refl.
  rewrite !id_left, !id_right.
  symmetry.
  apply cstrict_assoc_slide.
Qed.

(*
   * K8: [⊞c] is associative up to the [chcast]s along [app_assoc]. 

   --------
   * K8：[⊞c] 在 [app_assoc] 上对 [chcast] 是结合的。
*)
Lemma ctensor_hom_assoc {a b c d j k : list Colour}
  (f : ⟦a⟧ ~{P}~> ⟦b⟧) (g : ⟦c⟧ ~{P}~> ⟦d⟧) (h : ⟦j⟧ ~{P}~> ⟦k⟧) :
  chcast (eq_sym (app_assoc b d k)) ∘ ((f ⊞c g) ⊞c h)
    ≈ (f ⊞c (g ⊞c h)) ∘ chcast (eq_sym (app_assoc a c j)).
Proof using OD P.
  unfold ctensor_hom, chcast.
  apply (ctensor_assoc_general f g h
           (cprop_tensor_app a c) (cprop_tensor_app b d)
           (cprop_tensor_app c j) (cprop_tensor_app d k)
           (cprop_tensor_app (a ++ c) j) (cprop_tensor_app (b ++ d) k)
           (cprop_tensor_app a (c ++ j)) (cprop_tensor_app b (d ++ k))
           (f_equal (@cprop_of_list Colour P) (eq_sym (app_assoc a c j)))
           (f_equal (@cprop_of_list Colour P) (eq_sym (app_assoc b d k)))).
Qed.

(*
   * The [eq_sym] cast in the reversed-match spelling used by
   [strict_assoc_from] ([Structure/Monoidal/Strict.v]). 

   --------
   * [eq_sym] 在 [strict_assoc_from] ([Structure/Monoidal/Strict.v]) 使用的反向匹配拼写中出现。
*)
Lemma cid_cast_sym_match {a b : P} (e : a = b) :
  id_cast (eq_sym e) = match e in _ = T return (T ~> a) with
                       | eq_refl => id
                       end.
Proof using P. destruct e; reflexivity. Qed.

(** The inverse associator as a cast. / 作为类型转换的逆结合子。 *)
Lemma cstrict_assoc_cast_from (x y z : P) :
  id_cast (eq_sym (strict_assoc_obj x y z))
    ≈ from (@tensor_assoc P MPc x y z).
Proof using P.
  rewrite cid_cast_sym_match.
  symmetry; apply strict_assoc_from.
Qed.

(*
   * The first hexagon, with every structural map spelled as a cast. 

   --------
   * 第一个六边形，每个结构图都被拼写成一个铸件。
*)
Lemma cstrict_braid_hex_cast (x y z : P) :
  id_cast (strict_assoc_obj y z x)
     ∘ cstrict_braid x ((y ⨂[MPc] z)%object)
     ∘ id_cast (strict_assoc_obj x y z)
    ≈ (id[y] ⨂[MPc] cstrict_braid x z)
        ∘ id_cast (strict_assoc_obj y x z)
        ∘ (cstrict_braid x y ⨂[MPc] id[z]).
Proof using P.
  rewrite !cstrict_assoc_cast.
  apply cstrict_braid_hex.
Qed.

(** The second hexagon, in cast form. / 第二个六边形，铸造形式。 *)
Lemma cstrict_braid_hex_sym_cast (x y z : P) :
  id_cast (eq_sym (strict_assoc_obj z x y))
     ∘ cstrict_braid ((x ⨂[MPc] y)%object) z
     ∘ id_cast (eq_sym (strict_assoc_obj x y z))
    ≈ (cstrict_braid x z ⨂[MPc] id[y])
        ∘ id_cast (eq_sym (strict_assoc_obj x z y))
        ∘ (id[x] ⨂[MPc] cstrict_braid y z).
Proof using P.
  rewrite !cstrict_assoc_cast_from.
  apply cstrict_braid_hex_sym.
Qed.

(** General right-hexagon decomposition of the conjugated braid. / 共轭辫的一般右六边形分解。 *)
Lemma cbraid_hex_right_general {x y z v a1 a2 q r b1 b2 t1 t2 c1 c2 : P}
  (eyz : (y ⨂[MPc] z)%object = v)
  (exv : (x ⨂[MPc] v)%object = a1) (evx : (v ⨂[MPc] x)%object = a2)
  (ezx : (z ⨂[MPc] x)%object = q) (exz : (x ⨂[MPc] z)%object = r)
  (eyq : (y ⨂[MPc] q)%object = b1) (eyr : (y ⨂[MPc] r)%object = b2)
  (exy : (x ⨂[MPc] y)%object = t1) (eyx : (y ⨂[MPc] x)%object = t2)
  (et1z : (t1 ⨂[MPc] z)%object = c1) (et2z : (t2 ⨂[MPc] z)%object = c2)
  (D1 : a2 = b1) (D2 : c2 = b2) (D3 : a1 = c1) :
  id_cast D1 ∘ (id_cast evx ∘ cstrict_braid x v ∘ id_cast (eq_sym exv))
    ≈ ((id_cast eyq
          ∘ (id[y] ⨂[MPc]
               (id_cast ezx ∘ cstrict_braid x z ∘ id_cast (eq_sym exz)))
          ∘ id_cast (eq_sym eyr))
         ∘ id_cast D2)
        ∘ ((id_cast et2z
              ∘ ((id_cast eyx ∘ cstrict_braid x y ∘ id_cast (eq_sym exy))
                   ⨂[MPc] id[z])
              ∘ id_cast (eq_sym et1z))
             ∘ id_cast D3).
Proof using OD P.
  destruct eyz, exv, evx, ezx, exz, eyq, eyr, exy, eyx, et1z, et2z.
  unfold MPc.
  rewrite (obj_uip D1 (strict_assoc_obj y z x)).
  rewrite (obj_uip D2 (strict_assoc_obj y x z)).
  rewrite (obj_uip D3 (eq_sym (strict_assoc_obj x y z))).
  rewrite !id_cast_refl.
  rewrite !id_left, !id_right.
  assert (HX := cstrict_braid_hex_cast x y z).
  unfold MPc in HX.
  symmetry.
  rewrite comp_assoc.
  rewrite <- HX.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_r.
  rewrite id_right.
  reflexivity.
Qed.

(*
   * K9: the right hexagon at [⟦·⟧]-indexed objects, in the transport
   spelling produced by interpreting [CTE_braid_hex_right]. 

   --------
   * K9：在传输拼写中通过解释 [CTE_braid_hex_right] 生成的，位于 [⟦·⟧] 索引对象的右六边形。
*)
Lemma cbraid_hom_hex_r (m n p : list Colour) :
  chcast (eq_sym (app_assoc n p m)) ∘ cbraid_hom m (n ++ p)
    ≈ ((id[⟦n⟧] ⊞c cbraid_hom m p) ∘ chcast (eq_sym (app_assoc n m p)))
        ∘ ((cbraid_hom m n ⊞c id[⟦p⟧]) ∘ chcast (app_assoc m n p)).
Proof using OD P.
  unfold ctensor_hom, cbraid_hom, chcast.
  apply (cbraid_hex_right_general
           (cprop_tensor_app n p)
           (cprop_tensor_app m (n ++ p)) (cprop_tensor_app (n ++ p) m)
           (cprop_tensor_app p m) (cprop_tensor_app m p)
           (cprop_tensor_app n (p ++ m)) (cprop_tensor_app n (m ++ p))
           (cprop_tensor_app m n) (cprop_tensor_app n m)
           (cprop_tensor_app (m ++ n) p) (cprop_tensor_app (n ++ m) p)
           (f_equal (@cprop_of_list Colour P) (eq_sym (app_assoc n p m)))
           (f_equal (@cprop_of_list Colour P) (eq_sym (app_assoc n m p)))
           (f_equal (@cprop_of_list Colour P) (app_assoc m n p))).
Qed.

(** General left-hexagon decomposition of the conjugated braid. / 共轭辫的一般左六边形分解。 *)
Lemma cbraid_hex_left_general {x y z v a1 q r b1 t1 c1 c2 w1 w2 s2 : P}
  (exy : (x ⨂[MPc] y)%object = t1)
  (eyz : (y ⨂[MPc] z)%object = v)
  (et1z : (t1 ⨂[MPc] z)%object = c1) (ezt1 : (z ⨂[MPc] t1)%object = c2)
  (exv : (x ⨂[MPc] v)%object = a1)
  (exz : (x ⨂[MPc] z)%object = r) (ezx : (z ⨂[MPc] x)%object = q)
  (eqy : (q ⨂[MPc] y)%object = w2) (ery : (r ⨂[MPc] y)%object = w1)
  (ezy : (z ⨂[MPc] y)%object = s2) (exs2 : (x ⨂[MPc] s2)%object = b1)
  (D1 : a1 = c1) (D2 : b1 = w1) (D3 : w2 = c2) :
  (id_cast ezt1 ∘ cstrict_braid t1 z ∘ id_cast (eq_sym et1z)) ∘ id_cast D1
    ≈ (id_cast D3
         ∘ ((id_cast eqy
               ∘ ((id_cast ezx ∘ cstrict_braid x z ∘ id_cast (eq_sym exz))
                    ⨂[MPc] id[y])
               ∘ id_cast (eq_sym ery))
              ∘ id_cast D2))
        ∘ (id_cast exs2
             ∘ (id[x] ⨂[MPc]
                  (id_cast ezy ∘ cstrict_braid y z ∘ id_cast (eq_sym eyz)))
             ∘ id_cast (eq_sym exv)).
Proof using OD P.
  destruct exy, eyz, et1z, ezt1, exv, exz, ezx, eqy, ery, ezy, exs2.
  unfold MPc.
  rewrite (obj_uip D1 (eq_sym (strict_assoc_obj x y z))).
  rewrite (obj_uip D2 (eq_sym (strict_assoc_obj x z y))).
  rewrite (obj_uip D3 (strict_assoc_obj z x y)).
  rewrite !id_cast_refl.
  rewrite !id_left, !id_right.
  assert (HX := cstrict_braid_hex_sym_cast x y z).
  unfold MPc in HX.
  symmetry.
  rewrite <- comp_assoc.
  rewrite <- HX.
  rewrite !comp_assoc.
  rewrite id_cast_inv_r.
  rewrite id_left.
  reflexivity.
Qed.

(*
   * K10: the left hexagon at [⟦·⟧]-indexed objects, in the transport
   spelling produced by interpreting [CTE_braid_hex_left]. 

   --------
   * K10：在运输拼写中通过解释 [CTE_braid_hex_left] 生成的 [⟦·⟧] 索引对象中的左六边形。
*)
Lemma cbraid_hom_hex_l (m n p : list Colour) :
  cbraid_hom (m ++ n) p ∘ chcast (app_assoc m n p)
    ≈ (chcast (eq_sym (app_assoc p m n))
         ∘ ((cbraid_hom m p ⊞c id[⟦n⟧]) ∘ chcast (app_assoc m p n)))
        ∘ (id[⟦m⟧] ⊞c cbraid_hom n p).
Proof using OD P.
  unfold ctensor_hom, cbraid_hom, chcast.
  apply (cbraid_hex_left_general
           (cprop_tensor_app m n) (cprop_tensor_app n p)
           (cprop_tensor_app (m ++ n) p) (cprop_tensor_app p (m ++ n))
           (cprop_tensor_app m (n ++ p))
           (cprop_tensor_app m p) (cprop_tensor_app p m)
           (cprop_tensor_app (p ++ m) n) (cprop_tensor_app (m ++ p) n)
           (cprop_tensor_app p n) (cprop_tensor_app m (p ++ n))
           (f_equal (@cprop_of_list Colour P) (app_assoc m n p))
           (f_equal (@cprop_of_list Colour P) (app_assoc m p n))
           (f_equal (@cprop_of_list Colour P) (eq_sym (app_assoc p m n)))).
Qed.

(** The braids against the unit object, as casts. / 辫子围绕单位对象，就像投射一样。 *)
Lemma cstrict_braid_unit_l_core (x : P) :
  cstrict_braid x (@I P MPc)
    ≈ id_cast (eq_sym (strict_unit_left_obj x))
        ∘ id_cast (strict_unit_right_obj x).
Proof using P.
  symmetry.
  rewrite cstrict_unitr_cast.
  rewrite <- cstrict_braid_unit_left.
  rewrite <- cstrict_unitl_cast.
  rewrite comp_assoc.
  rewrite id_cast_inv_l.
  rewrite id_left.
  reflexivity.
Qed.

Lemma cstrict_braid_unit_r_core (x : P) :
  cstrict_braid (@I P MPc) x
    ≈ id_cast (eq_sym (strict_unit_right_obj x))
        ∘ id_cast (strict_unit_left_obj x).
Proof using P.
  symmetry.
  rewrite cstrict_unitl_cast.
  rewrite <- cstrict_braid_unit_right.
  rewrite <- cstrict_unitr_cast.
  rewrite comp_assoc.
  rewrite id_cast_inv_l.
  rewrite id_left.
  reflexivity.
Qed.

(*
   * General unit-braid collapse: the braid against a unit-equal object
   is a pure cast, so a cast-conjugated copy of it is the identity. 

   --------
   * 一般单位编织坍塌：对一个单位等价对象的编织是一个纯铸，因此其铸共轭副本是恒等映射。
*)
Lemma cbraid_unit_general_l {u x q r : P} (eu : @I P MPc = u)
  (eux : (u ⨂[MPc] x)%object = q) (exu : (x ⨂[MPc] u)%object = r)
  (d : r = q) :
  id_cast d ∘ (id_cast exu ∘ cstrict_braid u x ∘ id_cast (eq_sym eux))
    ≈ id[q].
Proof using OD P.
  destruct eu, eux, exu.
  rewrite (obj_uip d (eq_trans (strict_unit_right_obj x)
                               (eq_sym (strict_unit_left_obj x)))).
  rewrite !id_cast_refl.
  rewrite id_left, id_right.
  rewrite cstrict_braid_unit_r_core.
  rewrite comp_assoc.
  rewrite !id_cast_trans.
  rewrite id_cast_loop.
  reflexivity.
Qed.

Lemma cbraid_unit_general_r {u x q r : P} (eu : @I P MPc = u)
  (eux : (u ⨂[MPc] x)%object = q) (exu : (x ⨂[MPc] u)%object = r)
  (d : x = r) (dq : x = q) :
  (id_cast eux ∘ cstrict_braid x u ∘ id_cast (eq_sym exu)) ∘ id_cast d
    ≈ id_cast dq.
Proof using OD P.
  destruct eu, eux, exu.
  rewrite (obj_uip d (eq_sym (strict_unit_right_obj x))).
  rewrite (obj_uip dq (eq_sym (strict_unit_left_obj x))).
  rewrite !id_cast_refl.
  rewrite id_left, id_right.
  rewrite cstrict_braid_unit_l_core.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_r.
  rewrite id_right.
  reflexivity.
Qed.

(*
   * K11: the braid of [[]] past [n] collapses to the identity. 

   --------
   * K11：[[]] 经过[n] 的辫子坍缩为单位元。
*)
Lemma cbraid_hom_unit_l (n : list Colour) :
  chcast (app_nil_r n) ∘ cbraid_hom [] n ≈ id[⟦n⟧].
Proof using OD P.
  unfold cbraid_hom, chcast.
  apply (cbraid_unit_general_l (@cprop_unit_nil Colour P)
           (cprop_tensor_app [] n) (cprop_tensor_app n [])
           (f_equal (@cprop_of_list Colour P) (app_nil_r n))).
Qed.

(*
   * K12: the braid of [n] past [[]] collapses to the identity. 

   --------
   * K12：[n] 过去的 [[] ] 的辫子坍缩为单位元。
*)
Lemma cbraid_hom_unit_r (n : list Colour) :
  cbraid_hom n [] ∘ chcast (eq_sym (app_nil_r n)) ≈ id[⟦n⟧].
Proof using OD P.
  unfold cbraid_hom, chcast.
  rewrite (id_cast_irr
             (f_equal (@cprop_of_list Colour P) (eq_sym (app_nil_r n)))
             (eq_sym (f_equal (@cprop_of_list Colour P) (app_nil_r n)))).
  transitivity (id_cast (@eq_refl _ ⟦n⟧ : ⟦n⟧ = ⟦[] ++ n⟧)).
  - apply (cbraid_unit_general_r (@cprop_unit_nil Colour P)
             (cprop_tensor_app [] n) (cprop_tensor_app n [])
             (eq_sym (f_equal (@cprop_of_list Colour P) (app_nil_r n)))
             (@eq_refl _ ⟦n⟧ : ⟦n⟧ = ⟦[] ++ n⟧)).
  - reflexivity.
Qed.

(* * *** Valuations and the interpretation of terms / * *** 估值与术语的解释 *)

Context (S : CSignature Colour).

(*
   * A valuation assigns a target morphism to every generator. 

   --------
   * 一个赋值会给每个生成元分配一个目标态射。
*)
Definition CValuation : Type :=
  ∀ cs ds : list Colour, S cs ds → (⟦cs⟧ ~{P}~> ⟦ds⟧).

Context (v : CValuation).

(*
   * The interpretation of a raw term, by structural recursion:
   identity wires to identities, block braids to [cbraid_hom],
   sequential composition to [∘], parallel composition to [⊞c], and
   generators through the valuation.  [cinterp] COMPUTES on
   constructors — e.g. [cinterp (CT_comp g f)] is definitionally
   [cinterp g ∘ cinterp f] — so the functor laws of the packaging
   file [Universal.v] hold by reflexivity. 

   --------
   * 通过结构递归对原始项的解释：  
   将 identity 线路映射到 identities，将 block braids 映射到 [cbraid_hom]，  
   将顺序组合映射到 [∘]，将并行组合映射到 [⊞c]，  
   将生成元通过赋值映射。[cinterp] 对构造子进行计算——例如，[cinterp (CT_comp g f)] 在定义上是 [cinterp g ∘ cinterp f]——  
   因此打包文件 [Universal.v] 的函子律通过自反性成立。
*)
Fixpoint cinterp {cs ds : list Colour} (t : CTerm S cs ds) :
  ⟦cs⟧ ~{P}~> ⟦ds⟧ :=
  match t in CTerm _ cs' ds' return ⟦cs'⟧ ~{P}~> ⟦ds'⟧ with
  | CT_id ks      => id
  | CT_braid a b  => cbraid_hom a b
  | CT_comp g f   => cinterp g ∘ cinterp f
  | CT_tens f g   => cinterp f ⊞c cinterp g
  | CT_gen g      => v _ _ g
  end.

(*
   * Casts interpret to casts — a Leibniz equality, by [e]-elimination. 

   --------
   * 将解释转换为类型转换——一个莱布尼茨等式，由 [e] 消去。
*)
Lemma cinterp_CT_cast {cs ds : list Colour} (e : cs = ds) :
  cinterp (CT_cast e) = chcast e.
Proof using P. destruct e; reflexivity. Qed.

(*
   * ** Transport bridges

   The strict-PROP axioms of [CTermEq] carry their boundary
   mismatches as [eq_rect] transports; under [cinterp] a codomain
   transport becomes a post-composed [chcast] and a domain transport
   a pre-composed one. 

   --------
   * ** 传输桥梁

   [CTermEq] 的严格-PROP 公理将它们的边界不匹配作为 [eq_rect] 传输；在 [cinterp] 下，余域传输变为后组合的 [chcast]，而域传输则变为前组合的。
*)

Lemma cinterp_eq_rect_cod {a b b' : list Colour} (e : b = b')
  (t : CTerm S a b) :
  cinterp (eq_rect b (fun k : list Colour => CTerm S a k) t b' e)
    ≈ chcast e ∘ cinterp t.
Proof using P. destruct e; cat. Qed.

Lemma cinterp_eq_rect_dom {a a' b : list Colour} (e : a = a')
  (t : CTerm S a b) :
  cinterp (eq_rect a (fun k : list Colour => CTerm S k b) t a' e)
    ≈ cinterp t ∘ chcast (eq_sym e).
Proof using P. destruct e; cat. Qed.

Lemma cinterp_eq_rect_r_dom {a a' b : list Colour} (e : a' = a)
  (t : CTerm S a b) :
  cinterp (eq_rect_r (fun k : list Colour => CTerm S k b) t e)
    ≈ cinterp t ∘ chcast e.
Proof using P. destruct e; cat. Qed.

(*
   * *** Soundness

   [CTermEq] is [Prop]-valued and the hom equivalence of the abstract
   target is [Type]-valued, so the induction eliminates into the
   [Prop]-reflection [heq] of a [HomEqProp] instance (the
   [Quotient.v] kit) and round-trips through [heq_intro] /
   [heq_elim].  Every one of the nineteen [CTermEq] constructors is
   covered. 

   --------
   * *** 健全性

   [CTermEq] 是 [Prop] 值的，并且抽象目标的同伦等价是 [Type] 值的，所以归纳消除进入 [Prop]-反射的 [heq] 的 [HomEqProp] 实例（[Quotient.v] 套件），并通过 [heq_intro] / [heq_elim] 往返。十九个 [CTermEq] 构造函数中的每一个都被覆盖。
*)

Context {HP : @HomEqProp P}.

Lemma cinterp_sound_heq {cs ds : list Colour} {s t : CTerm S cs ds} :
  CTermEq S s t → heq (cinterp s) (cinterp t).
Proof using HP OD P S v.
  intros HT.
  induction HT.
  - (* CTE_refl *)
    apply heq_intro; reflexivity.
  - (* CTE_sym *)
    apply heq_intro; symmetry; exact (heq_elim IHHT).
  - (* CTE_trans / CTE_转 *)
    apply heq_intro.
    rewrite (heq_elim IHHT1).
    exact (heq_elim IHHT2).
  - (* CTE_comp_cong / CTE_复合_并发 *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHHT1), (heq_elim IHHT2).
  - (* CTE_tens_cong / CTE_张力电容 *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHHT1), (heq_elim IHHT2).
  - (* CTE_id_left / CTE_id_左 *)
    apply heq_intro; cbn [cinterp]; apply id_left.
  - (* CTE_id_right / CTE_id_右 *)
    apply heq_intro; cbn [cinterp]; apply id_right.
  - (* CTE_assoc / CTE_关联 *)
    apply heq_intro; cbn [cinterp]; symmetry; apply comp_assoc.
  - (* CTE_tens_id / CTE_张力编号 *)
    apply heq_intro; cbn [cinterp]; apply ctensor_hom_id.
  - (* CTE_interchange / CTE_互换 *)
    apply heq_intro; cbn [cinterp]; symmetry; apply ctensor_hom_comp.
  - (* CTE_braid_invol / CTE_辫子_参与 *)
    apply heq_intro; cbn [cinterp]; apply cbraid_hom_invol.
  - (* CTE_braid_natural / CTE_自然编织 *)
    apply heq_intro; cbn [cinterp]; apply cbraid_hom_swap.
  - (* CTE_tens_id0_left / CTE_张力_id0_左 *)
    apply heq_intro; cbn [cinterp]; apply ctensor_hom_idnil_left.
  - (* CTE_tens_id0_right / CTE_张力_id0_右 *)
    apply heq_intro.
    rewrite cinterp_eq_rect_cod, cinterp_eq_rect_r_dom.
    cbn [cinterp].
    rewrite ctensor_hom_idnil_right.
    rewrite !comp_assoc.
    rewrite chcast_inv_r.
    now rewrite id_left.
  - (* CTE_tens_assoc / CTE_张量关联 *)
    apply heq_intro.
    rewrite cinterp_eq_rect_cod, cinterp_eq_rect_r_dom.
    cbn [cinterp].
    apply ctensor_hom_assoc.
  - (* CTE_braid_hex_left / CTE_左侧六边形编织 *)
    apply heq_intro.
    cbn [cinterp].
    rewrite cinterp_eq_rect_cod.
    rewrite !cinterp_eq_rect_dom.
    cbn [cinterp].
    rewrite (chcast_irr (eq_sym (eq_sym (app_assoc m n p)))
                        (app_assoc m n p)).
    rewrite (chcast_irr (eq_sym (eq_sym (app_assoc m p n)))
                        (app_assoc m p n)).
    apply cbraid_hom_hex_l.
  - (* CTE_braid_hex_right / CTE_右侧六边形编织 *)
    apply heq_intro.
    cbn [cinterp].
    rewrite cinterp_eq_rect_cod.
    rewrite !cinterp_eq_rect_dom.
    cbn [cinterp].
    rewrite (chcast_irr (eq_sym (eq_sym (app_assoc m n p)))
                        (app_assoc m n p)).
    apply cbraid_hom_hex_r.
  - (* CTE_braid_unit_left / CTE_左侧编织单元 *)
    apply heq_intro.
    rewrite cinterp_eq_rect_cod.
    cbn [cinterp].
    apply cbraid_hom_unit_l.
  - (* CTE_braid_unit_right / CTE_右侧编织单元 *)
    apply heq_intro.
    rewrite cinterp_eq_rect_dom.
    cbn [cinterp].
    apply cbraid_hom_unit_r.
Qed.

(** Soundness, in the target's own hom equivalence. / 稳健性，在目标自身的同余等价中。 *)
Theorem cinterp_sound {cs ds : list Colour} {s t : CTerm S cs ds} :
  CTermEq S s t → cinterp s ≈ cinterp t.
Proof using HP OD P S v.
  intros HT.
  exact (heq_elim (cinterp_sound_heq HT)).
Qed.

End CInterp.

Arguments CValuation {Colour} P S : assert.
Arguments cinterp {Colour} P S v {cs ds} t : assert.
