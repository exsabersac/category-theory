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
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Cast.

From Coq Require Import Arith.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(*
   * * Interpreting free-PROP terms in an arbitrary PROP 

   --------
   * * 在任意 PROP 中解释 free-PROP 项
*)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 Given a signature [S] and a PROP [P], a [Valuation] assigns to every
 generator [g : S m n] a morphism [⟦m⟧ ~{P}~> ⟦n⟧].  This file defines
 the induced interpretation [interp : Term S m n → (⟦m⟧ ~{P}~> ⟦n⟧)]
 and proves it SOUND for the equational theory [TermEq] of
 [Construction/PROP/TermEq.v]: [TermEq]-equal terms have equivalent
 interpretations.  This is the morphism-level content of the free
 PROP's universal property; the functor packaging lives in the
 successor file [Construction/PROP/Universal.v].

 The development is organised in three layers:

 1.  [BraidTransport] — the coherence quarantine.  A PROP carries two
 [Monoidal] structures on the same category: the strict path
 [strict_is_monoidal prop_strict] and the symmetric path
 [braided_is_monoidal (symmetric_is_braided prop_symmetric)],
 related by the propositional equality [prop_monoidal_coherence].
 The braiding and its laws live on the symmetric path, while the
 strictness equalities [prop_unit_zero] / [prop_tensor_plus] live
 on the strict path.  [transport_braid] moves the braid family
 across the coherence equality, and the [transport_braid_*]
 lemmas move each braid law with it.  Every lemma destructs a
 VARIABLE equality between two [Monoidal] records, so the
 transport reduces definitionally; the concrete coherence proof
 of [P] is eliminated here and NOWHERE ELSE downstream.

 2.  The PROP-target kit — [strict_braid] (the transported braiding),
 cast/bimap interaction lemmas, the strict structural maps as
 [id_cast]s with their naturality restated as cast-sliding, the
 [⟦·⟧]-level combinators [hcast], [⊞] ([prop_tensor_hom]) and
 [prop_braid], and the K-lemmas K1–K12 giving the strict
 symmetric monoidal laws of [⊞]/[prop_braid] at [nat]-indexed
 objects.  The UIP-flavoured lemmas require decidable object
 equality ([ObjDecEq P], axiom-free UIP via [Eqdep_dec]).

 3.  [Valuation], [interp], and soundness.  [TermEq] is [Prop]-valued
 while the hom equivalence [≈] of an abstract target is
 [Type]-valued, so the induction lands in the [Prop]-reflection
 [heq] of a [HomEqProp] instance and round-trips through
 [heq_intro] / [heq_elim] (see [Construction/Quotient.v]).  The
 induction covers every one of the nineteen [TermEq]
 constructors. 

 --------
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 给定一个签名 [S] 和一个 PROP [P]，[Valuation] 将每个生成元 [g : S m n] 分配一个态射 [⟦m⟧ ~{P}~> ⟦n⟧]。此文件定义了诱导的解释 [interp : Term S m n → (⟦m⟧ ~{P}~> ⟦n⟧)]，并证明它对于 [TermEq] 的方程理论是可靠的：[Construction/PROP/TermEq.v] 中相等的项具有等价的解释。这是自由 PROP 的普遍性质在态射层面的内容；封装函子位于后续文件 [Construction/PROP/Universal.v] 中。

 发展过程组织为三层：1. [BraidTransport] — 相干隔离。一个 PROP 在同一范畴上携带两个 [Monoidal] 结构：严格路径 [strict_is_monoidal prop_strict] 和对称路径 [braided_is_monoidal (symmetric_is_braided prop_symmetric)]，它们通过命题等式 [prop_monoidal_coherence] 关联。编织及其定律存在于对称路径上，而严格性等式 [prop_unit_zero] / [prop_tensor_plus] 存在于严格路径上。[transport_braid] 将编织族沿相干等式移动，而 [transport_braid_*] 引理则随之移动每个编织定律。每个引理都会析构两个 [Monoidal] 记录之间的 VARIABLE 等式，因此传输在定义上归约；[P] 的具体相干证明在此处被消除，并且在下游的任何其他地方都不会出现。2. PROP-目标套件 — [strict_braid]（已传输的编织），投射/双映射交互引理，严格结构映射作为 [id_cast]，并将其自然性重新表述为投射滑动，[⟦·⟧] 级组合子 [hcast]、[⊞]（[prop_tensor_hom]）和 [prop_braid]，以及 K-引理 K1–K12 给出 [⊞] / [prop_braid] 在 [nat] 索引对象上的严格对称单体律。UIP 风格的引理需要可判定的对象相等性（[ObjDecEq P]，通过 [Eqdep_dec] 无公理 UIP）。3. [Valuation]、[interp] 和健全性。[TermEq] 是 [Prop] 值的，而抽象目标的同伦等价 [≈] 是 [Type] 值的，因此归纳落在 [Prop] 反射的 [heq] 一个 [HomEqProp] 实例中，并通过 [heq_intro] / [heq_elim] 往返（见 [Construction/Quotient.v]）。归纳覆盖了十九个 [TermEq] 构造函数中的每一个。
*)

(*
   * ** Transporting a braid family across a [Monoidal] equality

   The equality [coh : M1 = M2] relates two monoidal structures on the
   SAME category.  A braid family at [M2] transports to one at [M1] by
   dependent elimination; each braid law transports along, by
   destructing [coh].  All statements quantify over the braid family
   and the law, so the destruct is over a variable equality and the
   lemmas are proof-irrelevant in the concrete coherence used. 

   --------
   * ** 在 [Monoidal] 等式下传输编织族

   等式 [coh : M1 = M2] 连接了同一范畴上的两个幺半群结构。在 [M2] 的一个编织族可以通过依赖消元传输到 [M1]；每个编织律通过析构 [coh] 而被传输。所有陈述都是对编织族和律的量化，因此析构作用于一个变量等式，并且在使用的具体相干性中引理是证明无关的。
*)

Section BraidTransport.

Context {C : Category}.

(** A doubly indexed family of braid-shaped morphisms at [M]. / 在 [M] 上的双索引编织状态射族。 *)
Definition braid_family (M : @Monoidal C) : Type :=
  ∀ x y : C, ((x ⨂[M] y)%object ~{C}~> (y ⨂[M] x)%object).

(*
   * Transport a braid family backwards across [coh : M1 = M2]. 

   --------
   * 将一个辫子族向后运送穿过 [coh : M1 = M2]。
*)
Definition transport_braid {M1 M2 : @Monoidal C} (coh : M1 = M2) :
  braid_family M2 → braid_family M1 :=
  match coh in _ = M return braid_family M → braid_family M1 with
  | eq_refl => fun b => b
  end.

(*
   * Naturality (in the transposed [bimap_braid] form) transports. 

   --------
   * 自然性（在移调后的 [bimap_braid] 形式中）传输。
*)
Lemma transport_braid_swap {M1 M2 : @Monoidal C} (coh : M1 = M2) :
  ∀ b : braid_family M2,
  (∀ x y z w (f : x ~> z) (g : y ~> w),
     (g ⨂[M2] f) ∘ b x y ≈ b z w ∘ (f ⨂[M2] g)) →
  ∀ x y z w (f : x ~> z) (g : y ~> w),
    (g ⨂[M1] f) ∘ transport_braid coh b x y
      ≈ transport_braid coh b z w ∘ (f ⨂[M1] g).
Proof. destruct coh; intros b Hb; exact Hb. Qed.

(** The involution law transports. / 内卷法则传输。 *)
Lemma transport_braid_invol {M1 M2 : @Monoidal C} (coh : M1 = M2) :
  ∀ b : braid_family M2,
  (∀ x y, b y x ∘ b x y ≈ id) →
  ∀ x y, transport_braid coh b y x ∘ transport_braid coh b x y ≈ id.
Proof. destruct coh; intros b Hb; exact Hb. Qed.

(** The first hexagon transports. / 第一个六边形传送。 *)
Lemma transport_braid_hex {M1 M2 : @Monoidal C} (coh : M1 = M2) :
  ∀ b : braid_family M2,
  (∀ x y z,
     to (@tensor_assoc C M2 y z x) ∘ b x ((y ⨂[M2] z)%object)
        ∘ to (@tensor_assoc C M2 x y z)
       ≈ (id[y] ⨂[M2] b x z) ∘ to (@tensor_assoc C M2 y x z)
           ∘ (b x y ⨂[M2] id[z])) →
  ∀ x y z,
    to (@tensor_assoc C M1 y z x)
       ∘ transport_braid coh b x ((y ⨂[M1] z)%object)
       ∘ to (@tensor_assoc C M1 x y z)
      ≈ (id[y] ⨂[M1] transport_braid coh b x z)
          ∘ to (@tensor_assoc C M1 y x z)
          ∘ (transport_braid coh b x y ⨂[M1] id[z]).
Proof. destruct coh; intros b Hb; exact Hb. Qed.

(** The second hexagon transports. / 第二个六边形传送。 *)
Lemma transport_braid_hex_sym {M1 M2 : @Monoidal C} (coh : M1 = M2) :
  ∀ b : braid_family M2,
  (∀ x y z,
     from (@tensor_assoc C M2 z x y) ∘ b ((x ⨂[M2] y)%object) z
        ∘ from (@tensor_assoc C M2 x y z)
       ≈ (b x z ⨂[M2] id[y]) ∘ from (@tensor_assoc C M2 x z y)
           ∘ (id[x] ⨂[M2] b y z)) →
  ∀ x y z,
    from (@tensor_assoc C M1 z x y)
       ∘ transport_braid coh b ((x ⨂[M1] y)%object) z
       ∘ from (@tensor_assoc C M1 x y z)
      ≈ (transport_braid coh b x z ⨂[M1] id[y])
          ∘ from (@tensor_assoc C M1 x z y)
          ∘ (id[x] ⨂[M1] transport_braid coh b y z).
Proof. destruct coh; intros b Hb; exact Hb. Qed.

(** The unitor coherence [λ ∘ β ≈ ρ] transports. / 单位器相干性 [λ ∘ β ≈ ρ] 传输。 *)
Lemma transport_braid_unit_left {M1 M2 : @Monoidal C} (coh : M1 = M2) :
  ∀ b : braid_family M2,
  (∀ x, to (@unit_left C M2 x) ∘ b x (@I C M2) ≈ to (@unit_right C M2 x)) →
  ∀ x, to (@unit_left C M1 x) ∘ transport_braid coh b x (@I C M1)
         ≈ to (@unit_right C M1 x).
Proof. destruct coh; intros b Hb; exact Hb. Qed.

(** The mirror unitor coherence [ρ ∘ β ≈ λ] transports. / 镜子统一器相干 [ρ ∘ β ≈ λ] 传输。 *)
Lemma transport_braid_unit_right {M1 M2 : @Monoidal C} (coh : M1 = M2) :
  ∀ b : braid_family M2,
  (∀ x, to (@unit_right C M2 x) ∘ b (@I C M2) x ≈ to (@unit_left C M2 x)) →
  ∀ x, to (@unit_right C M1 x) ∘ transport_braid coh b (@I C M1) x
         ≈ to (@unit_left C M1 x).
Proof. destruct coh; intros b Hb; exact Hb. Qed.

End BraidTransport.

(** ** The PROP-target kit / ** PROP-靶标试剂盒 *)

Section PROPTarget.

Context (P : PROP).

Open Scope nat_scope.

(*
   * The PROP-object [⟦n⟧], as in [Construction/PROP.v] (whose notation
   is section-local there and must be re-declared per file). 

   --------
   * PROP 对象 [⟦n⟧]，如 [Construction/PROP.v]（其符号在章节中是局部的，并且必须在每个文件中重新声明）。
*)
Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(*
   * The two [Monoidal] paths through a PROP: the strict one and the
   braided/symmetric one.  Everything downstream is phrased at [MP];
   the braid is imported from [MB] by [transport_braid]. 

   --------
   * PROP中的两个[Monoidal]路径：严格路径和编织/对称路径。下游的所有内容都用[MP]表达；编织由[transport_braid]从[MB]引入。
*)
Definition MP : @Monoidal P := @strict_is_monoidal P (@prop_strict P).
Definition MB : @Monoidal P :=
  @braided_is_monoidal P (@symmetric_is_braided P (@prop_symmetric P)).

(*
   * The braiding of [P], re-indexed to the strict monoidal path.  This
   definition and the six [strict_braid_*] lemmas following it are the
   only places in this file that mention [prop_monoidal_coherence],
   and none of them destructs it: each merely passes the concrete
   coherence proof to a [BraidTransport] lemma above, which eliminates
   only its VARIABLE equality.  The rest of this file never touches
   the coherence again, and the successor files keep the same
   discipline ([Universal.v] passes it, whole, to its own match-based
   transports). 

   --------
   * [P] 的编织，重新索引到严格单体路径。这个定义以及紧随其后的六个 [strict_braid_*] 引理是本文件中唯一提到 [prop_monoidal_coherence] 的地方，而且没有一个会破坏它：每一个只是将具体的一致性证明传递给上面的 [BraidTransport] 引理，它只消除了其变量等式。本文件的其余部分再也不涉及该一致性，而后继文件保持相同的规范（[Universal.v] 将其完整地传递给自身基于匹配的传输函数）。
*)
Definition strict_braid : braid_family MP :=
  transport_braid (@prop_monoidal_coherence P)
    (fun x y : P => @braid P (@symmetric_is_braided P (@prop_symmetric P)) x y).

(*
   * Naturality of [strict_braid], in the transposed square form of
   [bimap_braid] ([Structure/Monoidal/Symmetric.v]). 

   --------
   * [strict_braid] 的自然性，在 [bimap_braid]（[Structure/Monoidal/Symmetric.v]）的转置方形形式中。
*)
Lemma strict_braid_swap {x y z w : P} (f : x ~> z) (g : y ~> w) :
  (g ⨂[MP] f) ∘ strict_braid x y ≈ strict_braid z w ∘ (f ⨂[MP] g).
Proof.
  apply (transport_braid_swap (@prop_monoidal_coherence P) _
           (fun a b c d f' g' => @bimap_braid P _ a b c d f' g')).
Qed.

(** [strict_braid] is an involution. / [strict_braid] 是一个自反运算。 *)
Lemma strict_braid_invol (x y : P) :
  strict_braid y x ∘ strict_braid x y ≈ id.
Proof.
  apply (transport_braid_invol (@prop_monoidal_coherence P) _
           (fun a b => @braid_invol P _ a b)).
Qed.

(** The first hexagon at [MP]. / 第一个六边形在 [MP] 。 *)
Lemma strict_braid_hex (x y z : P) :
  to (@tensor_assoc P MP y z x) ∘ strict_braid x ((y ⨂[MP] z)%object)
     ∘ to (@tensor_assoc P MP x y z)
    ≈ (id[y] ⨂[MP] strict_braid x z) ∘ to (@tensor_assoc P MP y x z)
        ∘ (strict_braid x y ⨂[MP] id[z]).
Proof.
  apply (transport_braid_hex (@prop_monoidal_coherence P) _
           (fun a b c => @hexagon_identity P _ a b c)).
Qed.

(** The second hexagon at [MP]. / 第二个六边形在 [MP] 。 *)
Lemma strict_braid_hex_sym (x y z : P) :
  from (@tensor_assoc P MP z x y) ∘ strict_braid ((x ⨂[MP] y)%object) z
     ∘ from (@tensor_assoc P MP x y z)
    ≈ (strict_braid x z ⨂[MP] id[y]) ∘ from (@tensor_assoc P MP x z y)
        ∘ (id[x] ⨂[MP] strict_braid y z).
Proof.
  apply (transport_braid_hex_sym (@prop_monoidal_coherence P) _
           (fun a b c => @hexagon_identity_sym P _ a b c)).
Qed.

(*
   * The unitor coherences at [MP] (Joyal–Street Prop. 2.1, imported
   from [Structure/Monoidal/Braided/Proofs.v] and transported). 

   --------
   * 单位器在 [MP] 处的一致性（Joyal–Street 命题 2.1，从 [Structure/Monoidal/Braided/Proofs.v] 导入并迁移）。
*)
Lemma strict_braid_unit_left (x : P) :
  to (@unit_left P MP x) ∘ strict_braid x (@I P MP)
    ≈ to (@unit_right P MP x).
Proof.
  apply (transport_braid_unit_left (@prop_monoidal_coherence P) _
           (fun a => @braid_unit_left P _ a)).
Qed.

Lemma strict_braid_unit_right (x : P) :
  to (@unit_right P MP x) ∘ strict_braid (@I P MP) x
    ≈ to (@unit_left P MP x).
Proof.
  apply (transport_braid_unit_right (@prop_monoidal_coherence P) _
           (fun a => @braid_unit_right P _ a)).
Qed.

(*
   * *** Casts and the tensor bifunctor

   Every strict structural map is an [id_cast], and every arity cast
   interacts with [⨂[MP]] by [f_equal]-images.  Each proof destructs
   the equality and closes with a bifunctor law. 

   --------
   * *** 类型转换与张量双函子

   每个严格结构映射都是一个 [id_cast]，每个元数类型转换
   都通过 [f_equal]-像与 [⨂[MP] ] 交互。每个证明分解
   等式并以双函子定律结束。
*)

(*
   * A transparent pairing of object equalities through the tensor.
   The stdlib's [f_equal2] is opaque, so a cast along it would be
   stuck even at [eq_refl]; this local combinator reduces. 

   --------
   * 通过张量透明地配对对象等式。
   标准库的 [f_equal2] 是不透明的，因此沿它进行类型转换即使在 [eq_refl] 处也会卡住；这个局部组合子可以简化该过程。
*)
Definition tensor_obj_eq {a a' b b' : P} (e : a = a') (e' : b = b') :
  (a ⨂[MP] b)%object = (a' ⨂[MP] b')%object :=
  match e in _ = u return ((a ⨂[MP] b)%object = (u ⨂[MP] b')%object) with
  | eq_refl =>
      match e' in _ = v
        return ((a ⨂[MP] b)%object = (a ⨂[MP] v)%object)
      with
      | eq_refl => eq_refl
      end
  end.

(** A tensor of casts is the cast along the paired equality. / 张量的转换是沿着配对等式的转换。 *)
Lemma bimap_cast {a a' b b' : P} (e : a = a') (e' : b = b') :
  (id_cast e ⨂[MP] id_cast e') ≈ id_cast (tensor_obj_eq e e').
Proof.
  destruct e, e'.
  exact (@bimap_id_id P P P (@tensor P MP) a b).
Qed.

(*
   * A cast in the left tensorand extracts as a whole-tensor cast. 

   --------
   * 左张量的转换被提取为整体张量转换。
*)
Lemma bimap_cast_l {a a' x y : P} (e : a = a') (g : x ~> y) :
  (id_cast e ⨂[MP] g)
    ≈ id_cast (f_equal (fun u : P => (u ⨂[MP] y)%object) e)
        ∘ (id[a] ⨂[MP] g).
Proof. destruct e; cat. Qed.

(*
   * A cast in the right tensorand extracts as a whole-tensor cast. 

   --------
   * 在正确的张量项上进行的类型转换会作为整体张量类型转换被提取。
*)
Lemma bimap_cast_r {x y b b' : P} (g : x ~> y) (e : b = b') :
  (g ⨂[MP] id_cast e)
    ≈ id_cast (f_equal (fun v : P => (y ⨂[MP] v)%object) e)
        ∘ (g ⨂[MP] id[b]).
Proof. destruct e; cat. Qed.

(*
   * Tensoring an identity with a cast IS a cast.  Like [bimap_cast]
   through [bimap_cast_r] above, these two are exported cast/tensor
   kit with no in-tree consumer yet; the current proofs reach the
   same effects through the slide lemmas and the [_general] forms
   below. 

   --------
   * 用张量操作将一个恒等映射与一个类型转换结合就是一个类型转换。就像上面的 [bimap_cast] 到 [bimap_cast_r]，这两个是导出的类型转换/张量工具包，目前还没有在树内的使用者；当前的证明通过滑动引理和下面的 [_general] 形式达到相同的效果。
*)
Lemma bimap_cast_id_l {a x y : P} (e : x = y) :
  (id[a] ⨂[MP] id_cast e)
    ≈ id_cast (f_equal (fun v : P => (a ⨂[MP] v)%object) e).
Proof.
  destruct e.
  exact (@bimap_id_id P P P (@tensor P MP) a x).
Qed.

Lemma bimap_cast_id_r {a x y : P} (e : x = y) :
  (id_cast e ⨂[MP] id[a])
    ≈ id_cast (f_equal (fun u : P => (u ⨂[MP] a)%object) e).
Proof.
  destruct e.
  exact (@bimap_id_id P P P (@tensor P MP) x a).
Qed.

(*
   * A tensor of [hom_cast]s is the [hom_cast] along the paired object
   equalities ([tensor_obj_eq]).  This is the monoidal extension of
   the [hom_cast] kit of [Construction/Quotient.v]; it is consumed by
   the uniqueness proof of [Universal.v]. 

   --------
   * [hom_cast] 的张量是沿着配对对象的 [hom_cast] 相等 ([tensor_obj_eq])。这是 [Construction/Quotient.v] 的 [hom_cast] 工具包的幺半扩展；它被 [Universal.v] 的唯一性证明所使用。
*)
Lemma bimap_hom_cast {a b c d a' b' c' d' : P}
  (ea : a = a') (eb : b = b') (ec : c = c') (ed : d = d')
  (f : a ~> c) (g : b ~> d) :
  (hom_cast ea ec f ⨂[MP] hom_cast eb ed g)
    ≈ hom_cast (tensor_obj_eq ea eb) (tensor_obj_eq ec ed)
               (f ⨂[MP] g).
Proof. destruct ea, eb, ec, ed; reflexivity. Qed.

(*
   * [strict_braid] re-indexes along object equalities by [hom_cast].
   Consumed by the uniqueness proof of [Universal.v], whose braid
   case re-indexes a competitor's [strict_braid (G m) (G n)] to the
   canonical [strict_braid ⟦m⟧ ⟦n⟧] along the object agreement.  (The
   hexagon lemmas K9/K10 below do not need it: they quantify over the
   strictness equalities in the [braid_hex_*_general] forms
   instead.) 

   --------
   * [strict_braid] 按照对象相等通过 [hom_cast] 重新索引。
   被 [Universal.v] 的唯一性证明所使用，其编织情况沿对象一致性将竞争者的 [strict_braid (G m) (G n)] 重新索引为规范的 [strict_braid ⟦m⟧ ⟦n⟧]。（下面的六边形引理 K9/K10 不需要它：它们量化的是 [braid_hex_*_general] 形式中的严格相等。）
*)
Lemma strict_braid_cast {x x' y y' : P} (e1 : x = x') (e2 : y = y') :
  strict_braid x' y'
    ≈ hom_cast (tensor_obj_eq e1 e2) (tensor_obj_eq e2 e1)
               (strict_braid x y).
Proof. destruct e1, e2; reflexivity. Qed.

(*
   * Flipping a cast-naturality square across the inverse casts. 

   --------
   * 在逆向转换上翻转一个类型自然性的转换方块。
*)
Lemma id_cast_flip {a b a' b' : P} (e1 : a = a') (e2 : b = b')
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
Lemma conj_compose {x y z x' y' z' : P}
  (e1 : x = x') (e2 : y = y') (e3 : z = z')
  (f : y ~> z) (g : x ~> y) :
  (id_cast e3 ∘ f ∘ id_cast (eq_sym e2))
     ∘ (id_cast e2 ∘ g ∘ id_cast (eq_sym e1))
    ≈ id_cast e3 ∘ (f ∘ g) ∘ id_cast (eq_sym e1).
Proof. destruct e1, e2, e3; cat. Qed.

(*
   * *** The strict structural maps as casts, with sliding naturality

   In a strict monoidal category the associator and unitors ARE the
   transported identities; their naturality squares become "slides"
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
Lemma strict_assoc_cast (x y z : P) :
  id_cast (strict_assoc_obj x y z) ≈ to (@tensor_assoc P MP x y z).
Proof. symmetry; apply strict_assoc_to. Qed.

Lemma strict_unitl_cast (x : P) :
  id_cast (strict_unit_left_obj x) ≈ to (@unit_left P MP x).
Proof. symmetry; apply strict_unit_left_to. Qed.

Lemma strict_unitr_cast (x : P) :
  id_cast (strict_unit_right_obj x) ≈ to (@unit_right P MP x).
Proof. symmetry; apply strict_unit_right_to. Qed.

(** Associator slide. / 联想器幻灯片。 *)
Lemma strict_assoc_slide {x y z x' y' z' : P}
  (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  (f ⨂[MP] (g ⨂[MP] h)) ∘ id_cast (strict_assoc_obj x y z)
    ≈ id_cast (strict_assoc_obj x' y' z') ∘ ((f ⨂[MP] g) ⨂[MP] h).
Proof.
  rewrite !strict_assoc_cast.
  apply to_tensor_assoc_natural.
Qed.

(** Left-unitor slide. / 左幺元滑动。 *)
Lemma strict_unitl_slide {x y : P} (g : x ~> y) :
  g ∘ id_cast (strict_unit_left_obj x)
    ≈ id_cast (strict_unit_left_obj y) ∘ (id[@I P MP] ⨂[MP] g).
Proof.
  rewrite !strict_unitl_cast.
  apply to_unit_left_natural.
Qed.

(** Right-unitor slide. / 右单位元滑动。 *)
Lemma strict_unitr_slide {x y : P} (g : x ~> y) :
  g ∘ id_cast (strict_unit_right_obj x)
    ≈ id_cast (strict_unit_right_obj y) ∘ (g ⨂[MP] id[@I P MP]).
Proof.
  rewrite !strict_unitr_cast.
  apply to_unit_right_natural.
Qed.

(** *** The [⟦·⟧]-level combinators / *** [⟦·⟧] 级组合子 *)

(** An arity cast: the identity transported along [⟦e⟧]. / 一个元数转换：沿着 [⟦e⟧] 传输的恒等式。 *)
Definition hcast {m n : nat} (e : m = n) : ⟦m⟧ ~{P}~> ⟦n⟧ :=
  id_cast (f_equal (@prop_of_nat P) e).

(*
   * [hcast]s compose, cancel, and are proof-irrelevant.  Irrelevance
   here is UIP on [nat] (via [Nat.eq_dec]) — no [ObjDecEq] needed.
   Of these, the soundness induction below consumes [hcast_inv_r]
   and [hcast_irr]; [hcast_trans], [hcast_inv_l] and [hcast_loop]
   complete the algebra as exported kit with no in-tree consumer
   yet. 

   --------
   * [hcast] 可以组合、取消，并且与证明无关。这里的无关性是在 [nat] 上的 UIP（通过 [Nat.eq_dec]）——不需要 [ObjDecEq]。在这些中，下面的正确性归纳使用了 [hcast_inv_r] 和 [hcast_irr]；[hcast_trans]、[hcast_inv_l] 和 [hcast_loop] 完成了作为导出工具包的代数，目前还没有在代码树中被使用。
*)
Lemma hcast_trans {m n p : nat} (e1 : m = n) (e2 : n = p) :
  hcast e2 ∘ hcast e1 ≈ hcast (eq_trans e1 e2).
Proof. destruct e1, e2; cat. Qed.

Lemma hcast_inv_l {m n : nat} (e : m = n) :
  hcast (eq_sym e) ∘ hcast e ≈ id.
Proof. destruct e; cat. Qed.

Lemma hcast_inv_r {m n : nat} (e : m = n) :
  hcast e ∘ hcast (eq_sym e) ≈ id.
Proof. destruct e; cat. Qed.

Lemma hcast_irr {m n : nat} (e1 e2 : m = n) : hcast e1 = hcast e2.
Proof. rewrite (UIP_dec Nat.eq_dec e1 e2); reflexivity. Qed.

Lemma hcast_loop {n : nat} (e : n = n) : hcast e = id.
Proof. rewrite (UIP_dec Nat.eq_dec e eq_refl); reflexivity. Qed.

(*
   * Parallel composition at [⟦·⟧]-indexed objects: tensor at [MP],
   conjugated by the [prop_tensor_plus] strictness casts. 

   --------
   * 在 [⟦·⟧] 索引对象上的并行组合：在 [MP] 上的张量，由 [prop_tensor_plus] 严格性转换共轭。
*)
Definition prop_tensor_hom {a b c d : nat}
  (f : ⟦a⟧ ~{P}~> ⟦b⟧) (g : ⟦c⟧ ~{P}~> ⟦d⟧) : ⟦a + c⟧ ~{P}~> ⟦b + d⟧ :=
  id_cast (prop_tensor_plus b d) ∘ (f ⨂[MP] g)
    ∘ id_cast (eq_sym (prop_tensor_plus a c)).

Infix "⊞" := prop_tensor_hom (at level 30, right associativity).

(** The block braiding at [⟦·⟧]-indexed objects. / [⟦·⟧] 索引对象的块状编发。 *)
Definition prop_braid (m n : nat) : ⟦m + n⟧ ~{P}~> ⟦n + m⟧ :=
  id_cast (prop_tensor_plus n m) ∘ strict_braid ⟦m⟧ ⟦n⟧
    ∘ id_cast (eq_sym (prop_tensor_plus m n)).

(*
   * *** The K-kit, part one: bifunctor and braid laws of [⊞]

   K1–K5 need no proof-irrelevance: the [prop_tensor_plus] casts
   cancel pairwise by [conj_compose] and the core laws are those of
   [⨂[MP]] and [strict_braid]. 

   --------
   * *** K-工具包，第一部分：[⊞] 的双函子与编织律

   K1–K5 不需要证明无关性：[prop_tensor_plus] 的强制通过 [conj_compose] 成对抵消，核心律是 [⨂[MP] 和 [strict_braid] 的律。
*)

(** K1: [⊞] preserves identities. / K1：[⊞] 保留身份。 *)
Lemma tensor_hom_id (m n : nat) : id[⟦m⟧] ⊞ id[⟦n⟧] ≈ id[⟦m + n⟧].
Proof.
  unfold prop_tensor_hom.
  rewrite bimap_id_id.
  rewrite id_right.
  apply id_cast_inv_r.
Qed.

(*
   * K2: [⊞] preserves composition (middle-four interchange). 

   --------
   * K2: [⊞] 保持组合（中间四项交换）。
*)
Lemma tensor_hom_comp {a b c d j k : nat}
  (f : ⟦b⟧ ~{P}~> ⟦c⟧) (f' : ⟦a⟧ ~{P}~> ⟦b⟧)
  (g : ⟦j⟧ ~{P}~> ⟦k⟧) (g' : ⟦d⟧ ~{P}~> ⟦j⟧) :
  (f ∘ f') ⊞ (g ∘ g') ≈ (f ⊞ g) ∘ (f' ⊞ g').
Proof.
  unfold prop_tensor_hom.
  rewrite conj_compose.
  now rewrite bimap_comp.
Qed.

(** K3: [⊞] respects the hom equivalence. / K3: [⊞] 尊重同态等价。 *)
#[export] Instance tensor_hom_respects {a b c d : nat} :
  Proper (equiv ==> equiv ==> equiv) (@prop_tensor_hom a b c d).
Proof.
  proper.
  unfold prop_tensor_hom.
  now rewrite X, X0.
Qed.

(** K4: [prop_braid] is an involution. / K4: [prop_braid] 是一个自反变换。 *)
Lemma prop_braid_invol (m n : nat) :
  prop_braid n m ∘ prop_braid m n ≈ id[⟦m + n⟧].
Proof.
  unfold prop_braid.
  rewrite conj_compose.
  rewrite strict_braid_invol.
  rewrite id_right.
  apply id_cast_inv_r.
Qed.

(** K5: naturality of [prop_braid] against [⊞]. / K5：[prop_braid] 相对于 [⊞] 的自然性。 *)
Lemma prop_braid_swap {m1 n1 m2 n2 : nat}
  (f : ⟦m1⟧ ~{P}~> ⟦n1⟧) (g : ⟦m2⟧ ~{P}~> ⟦n2⟧) :
  (g ⊞ f) ∘ prop_braid m1 m2 ≈ prop_braid n1 n2 ∘ (f ⊞ g).
Proof.
  unfold prop_tensor_hom, prop_braid.
  rewrite !conj_compose.
  now rewrite strict_braid_swap.
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
   The [⟦·⟧]-level K-lemma is then an instantiation. 

   --------
   * *** K-工具包，第二部分：严格的单位律和结合律

   K6–K12 在同一对象的不同证明路径中识别类型转换，因此它们需要在 [obj P] 上的身份证明唯一性——
   无公理，通过可判定对象相等性（[ObjDecEq]，来自 [Construction/Quotient.v]）。

   每条定律首先在完全一般的对象层形式下被证明，该形式量化严格相等性：解构量化相等性使得传输成为定义性操作，而
   唯一不可解构的剩余部分（一个单位或结合形状的循环）通过 [obj_uip] 对齐到典型的严格相等性。
   然后 [⟦·⟧] 级别的 K-引理是一个实例化。
*)

Context {OD : @ObjDecEq P}.

(** General left-unit absorption at [MP]. / 在 [MP] 的一般左单位吸收。 *)
Lemma tensor_unit_left_general {u x y : P} (eu : @I P MP = u)
  (f : x ~> y)
  (e1 : (u ⨂[MP] x)%object = x) (e2 : (u ⨂[MP] y)%object = y) :
  id_cast e2 ∘ (id[u] ⨂[MP] f) ∘ id_cast (eq_sym e1) ≈ f.
Proof using OD P.
  destruct eu.
  unfold MP.
  rewrite (obj_uip e1 (strict_unit_left_obj x)).
  rewrite (obj_uip e2 (strict_unit_left_obj y)).
  rewrite <- strict_unitl_slide.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_r.
  apply id_right.
Qed.

(*
   * K6: tensoring with [id ⟦0⟧] on the left is the identity (the arity
   equation [0 + a = a] holds definitionally). 

   --------
   * K6：在左侧与  [id [id ⟦0⟧]]  做张量积是恒等的（算子等式  [0 + a = a]  在定义上成立）。
*)
Lemma tensor_hom_id0_left {a b : nat} (f : ⟦a⟧ ~{P}~> ⟦b⟧) :
  id[⟦0⟧] ⊞ f ≈ f.
Proof using OD P.
  unfold prop_tensor_hom.
  apply (tensor_unit_left_general (@prop_unit_zero P) f
           (prop_tensor_plus 0 a) (prop_tensor_plus 0 b)).
Qed.

(*
   * General right-unit absorption at [MP], with mediating casts for
   the propositional arity equation [a + 0 = a]. 

   --------
   * 在 [MP] 处进行一般的右单元吸收，同时对命题元数方程 [a + 0 = a] 进行中介投射。
*)
Lemma tensor_unit_right_general {u x y x' y' : P} (eu : @I P MP = u)
  (f : x ~> y)
  (e1 : (x ⨂[MP] u)%object = x') (e2 : (y ⨂[MP] u)%object = y')
  (d1 : x' = x) (d2 : y' = y) :
  id_cast e2 ∘ (f ⨂[MP] id[u]) ∘ id_cast (eq_sym e1)
    ≈ id_cast (eq_sym d2) ∘ f ∘ id_cast d1.
Proof using OD P.
  destruct eu, d1, d2.
  unfold MP.
  rewrite (obj_uip e1 (strict_unit_right_obj _)).
  rewrite (obj_uip e2 (strict_unit_right_obj _)).
  rewrite <- strict_unitr_slide.
  rewrite <- (comp_assoc f (id_cast (strict_unit_right_obj x'))
                (id_cast (eq_sym (strict_unit_right_obj x')))).
  rewrite id_cast_inv_r.
  cat.
Qed.

(*
   * K7: tensoring with [id ⟦0⟧] on the right is the identity up to the
   [hcast]s along [a + 0 = a]. 

   --------
   * K7：在右侧与 [id [id ⟦0⟧]] 张量化是恒等的，直到沿着 [a + 0 = a] 的 [hcast]。
*)
Lemma tensor_hom_id0_right {a b : nat} (f : ⟦a⟧ ~{P}~> ⟦b⟧) :
  f ⊞ id[⟦0⟧]
    ≈ hcast (eq_sym (Nat.add_0_r b)) ∘ f ∘ hcast (Nat.add_0_r a).
Proof using OD P.
  unfold prop_tensor_hom, hcast.
  rewrite (id_cast_irr
             (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r b)))
             (eq_sym (f_equal (@prop_of_nat P) (Nat.add_0_r b)))).
  apply (tensor_unit_right_general (@prop_unit_zero P) f
           (prop_tensor_plus a 0) (prop_tensor_plus b 0)
           (f_equal (@prop_of_nat P) (Nat.add_0_r a))
           (f_equal (@prop_of_nat P) (Nat.add_0_r b))).
Qed.

(*
   * General strict associativity of the conjugated tensor at [MP]. 

   --------
   * 在 [MP] 处共轭张量的一般严格结合性。
*)
Lemma tensor_assoc_general {x y z x' y' z' u u' v v' w w' s s' : P}
  (f : x ~> x') (g : y ~> y') (h : z ~> z')
  (exy : (x ⨂[MP] y)%object = u) (exy' : (x' ⨂[MP] y')%object = u')
  (eyz : (y ⨂[MP] z)%object = v) (eyz' : (y' ⨂[MP] z')%object = v')
  (eu : (u ⨂[MP] z)%object = w) (eu' : (u' ⨂[MP] z')%object = w')
  (ev : (x ⨂[MP] v)%object = s) (ev' : (x' ⨂[MP] v')%object = s')
  (d : w = s) (d' : w' = s') :
  id_cast d'
      ∘ (id_cast eu'
           ∘ ((id_cast exy' ∘ (f ⨂[MP] g) ∘ id_cast (eq_sym exy)) ⨂[MP] h)
           ∘ id_cast (eq_sym eu))
    ≈ (id_cast ev'
         ∘ (f ⨂[MP] (id_cast eyz' ∘ (g ⨂[MP] h) ∘ id_cast (eq_sym eyz)))
         ∘ id_cast (eq_sym ev))
        ∘ id_cast d.
Proof using OD P.
  destruct exy, exy', eyz, eyz', eu, eu', ev, ev'.
  unfold MP.
  rewrite (obj_uip d (strict_assoc_obj x y z)).
  rewrite (obj_uip d' (strict_assoc_obj x' y' z')).
  rewrite !id_cast_refl.
  rewrite !id_left, !id_right.
  symmetry.
  apply strict_assoc_slide.
Qed.

(*
   * K8: [⊞] is associative up to the [hcast]s along [Nat.add_assoc]. 

   --------
   * K8：[⊞] 在 [Nat.add_assoc] 上对 [hcast] 是结合的。
*)
Lemma tensor_hom_assoc {a b c d j k : nat}
  (f : ⟦a⟧ ~{P}~> ⟦b⟧) (g : ⟦c⟧ ~{P}~> ⟦d⟧) (h : ⟦j⟧ ~{P}~> ⟦k⟧) :
  hcast (eq_sym (Nat.add_assoc b d k)) ∘ ((f ⊞ g) ⊞ h)
    ≈ (f ⊞ (g ⊞ h)) ∘ hcast (eq_sym (Nat.add_assoc a c j)).
Proof using OD P.
  unfold prop_tensor_hom, hcast.
  apply (tensor_assoc_general f g h
           (prop_tensor_plus a c) (prop_tensor_plus b d)
           (prop_tensor_plus c j) (prop_tensor_plus d k)
           (prop_tensor_plus (a + c) j) (prop_tensor_plus (b + d) k)
           (prop_tensor_plus a (c + j)) (prop_tensor_plus b (d + k))
           (f_equal (@prop_of_nat P) (eq_sym (Nat.add_assoc a c j)))
           (f_equal (@prop_of_nat P) (eq_sym (Nat.add_assoc b d k)))).
Qed.

(*
   * The [eq_sym] cast in the reversed-match spelling used by
   [strict_assoc_from] ([Structure/Monoidal/Strict.v]). 

   --------
   * [eq_sym] 在 [strict_assoc_from] ([Structure/Monoidal/Strict.v]) 使用的反向匹配拼写中出现。
*)
Lemma id_cast_sym_match {a b : P} (e : a = b) :
  id_cast (eq_sym e) = match e in _ = T return (T ~> a) with
                       | eq_refl => id
                       end.
Proof using P. destruct e; reflexivity. Qed.

(** The inverse associator as a cast. / 作为类型转换的逆结合子。 *)
Lemma strict_assoc_cast_from (x y z : P) :
  id_cast (eq_sym (strict_assoc_obj x y z))
    ≈ from (@tensor_assoc P MP x y z).
Proof using P.
  rewrite id_cast_sym_match.
  symmetry; apply strict_assoc_from.
Qed.

(*
   * The first hexagon, with every structural map spelled as a cast. 

   --------
   * 第一个六边形，每个结构图都被拼写成一个铸件。
*)
Lemma strict_braid_hex_cast (x y z : P) :
  id_cast (strict_assoc_obj y z x)
     ∘ strict_braid x ((y ⨂[MP] z)%object)
     ∘ id_cast (strict_assoc_obj x y z)
    ≈ (id[y] ⨂[MP] strict_braid x z)
        ∘ id_cast (strict_assoc_obj y x z)
        ∘ (strict_braid x y ⨂[MP] id[z]).
Proof using P.
  rewrite !strict_assoc_cast.
  apply strict_braid_hex.
Qed.

(** The second hexagon, in cast form. / 第二个六边形，铸造形式。 *)
Lemma strict_braid_hex_sym_cast (x y z : P) :
  id_cast (eq_sym (strict_assoc_obj z x y))
     ∘ strict_braid ((x ⨂[MP] y)%object) z
     ∘ id_cast (eq_sym (strict_assoc_obj x y z))
    ≈ (strict_braid x z ⨂[MP] id[y])
        ∘ id_cast (eq_sym (strict_assoc_obj x z y))
        ∘ (id[x] ⨂[MP] strict_braid y z).
Proof using P.
  rewrite !strict_assoc_cast_from.
  apply strict_braid_hex_sym.
Qed.

(** General right-hexagon decomposition of the conjugated braid. / 共轭辫的一般右六边形分解。 *)
Lemma braid_hex_right_general {x y z v a1 a2 q r b1 b2 t1 t2 c1 c2 : P}
  (eyz : (y ⨂[MP] z)%object = v)
  (exv : (x ⨂[MP] v)%object = a1) (evx : (v ⨂[MP] x)%object = a2)
  (ezx : (z ⨂[MP] x)%object = q) (exz : (x ⨂[MP] z)%object = r)
  (eyq : (y ⨂[MP] q)%object = b1) (eyr : (y ⨂[MP] r)%object = b2)
  (exy : (x ⨂[MP] y)%object = t1) (eyx : (y ⨂[MP] x)%object = t2)
  (et1z : (t1 ⨂[MP] z)%object = c1) (et2z : (t2 ⨂[MP] z)%object = c2)
  (D1 : a2 = b1) (D2 : c2 = b2) (D3 : a1 = c1) :
  id_cast D1 ∘ (id_cast evx ∘ strict_braid x v ∘ id_cast (eq_sym exv))
    ≈ ((id_cast eyq
          ∘ (id[y] ⨂[MP]
               (id_cast ezx ∘ strict_braid x z ∘ id_cast (eq_sym exz)))
          ∘ id_cast (eq_sym eyr))
         ∘ id_cast D2)
        ∘ ((id_cast et2z
              ∘ ((id_cast eyx ∘ strict_braid x y ∘ id_cast (eq_sym exy))
                   ⨂[MP] id[z])
              ∘ id_cast (eq_sym et1z))
             ∘ id_cast D3).
Proof using OD P.
  destruct eyz, exv, evx, ezx, exz, eyq, eyr, exy, eyx, et1z, et2z.
  unfold MP.
  rewrite (obj_uip D1 (strict_assoc_obj y z x)).
  rewrite (obj_uip D2 (strict_assoc_obj y x z)).
  rewrite (obj_uip D3 (eq_sym (strict_assoc_obj x y z))).
  rewrite !id_cast_refl.
  rewrite !id_left, !id_right.
  assert (HX := strict_braid_hex_cast x y z).
  unfold MP in HX.
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
   spelling produced by interpreting [TE_braid_hex_right]. 

   --------
   * K9：在传输拼写中通过解释 [TE_braid_hex_right] 生成的，位于 [⟦·⟧] 索引对象的右六边形。
*)
Lemma prop_braid_hex_r (m n p : nat) :
  hcast (eq_sym (Nat.add_assoc n p m)) ∘ prop_braid m (n + p)
    ≈ ((id[⟦n⟧] ⊞ prop_braid m p) ∘ hcast (eq_sym (Nat.add_assoc n m p)))
        ∘ ((prop_braid m n ⊞ id[⟦p⟧]) ∘ hcast (Nat.add_assoc m n p)).
Proof using OD P.
  unfold prop_tensor_hom, prop_braid, hcast.
  apply (braid_hex_right_general
           (prop_tensor_plus n p)
           (prop_tensor_plus m (n + p)) (prop_tensor_plus (n + p) m)
           (prop_tensor_plus p m) (prop_tensor_plus m p)
           (prop_tensor_plus n (p + m)) (prop_tensor_plus n (m + p))
           (prop_tensor_plus m n) (prop_tensor_plus n m)
           (prop_tensor_plus (m + n) p) (prop_tensor_plus (n + m) p)
           (f_equal (@prop_of_nat P) (eq_sym (Nat.add_assoc n p m)))
           (f_equal (@prop_of_nat P) (eq_sym (Nat.add_assoc n m p)))
           (f_equal (@prop_of_nat P) (Nat.add_assoc m n p))).
Qed.

(** General left-hexagon decomposition of the conjugated braid. / 共轭辫的一般左六边形分解。 *)
Lemma braid_hex_left_general {x y z v a1 q r b1 t1 c1 c2 w1 w2 s2 : P}
  (exy : (x ⨂[MP] y)%object = t1)
  (eyz : (y ⨂[MP] z)%object = v)
  (et1z : (t1 ⨂[MP] z)%object = c1) (ezt1 : (z ⨂[MP] t1)%object = c2)
  (exv : (x ⨂[MP] v)%object = a1)
  (exz : (x ⨂[MP] z)%object = r) (ezx : (z ⨂[MP] x)%object = q)
  (eqy : (q ⨂[MP] y)%object = w2) (ery : (r ⨂[MP] y)%object = w1)
  (ezy : (z ⨂[MP] y)%object = s2) (exs2 : (x ⨂[MP] s2)%object = b1)
  (D1 : a1 = c1) (D2 : b1 = w1) (D3 : w2 = c2) :
  (id_cast ezt1 ∘ strict_braid t1 z ∘ id_cast (eq_sym et1z)) ∘ id_cast D1
    ≈ (id_cast D3
         ∘ ((id_cast eqy
               ∘ ((id_cast ezx ∘ strict_braid x z ∘ id_cast (eq_sym exz))
                    ⨂[MP] id[y])
               ∘ id_cast (eq_sym ery))
              ∘ id_cast D2))
        ∘ (id_cast exs2
             ∘ (id[x] ⨂[MP]
                  (id_cast ezy ∘ strict_braid y z ∘ id_cast (eq_sym eyz)))
             ∘ id_cast (eq_sym exv)).
Proof using OD P.
  destruct exy, eyz, et1z, ezt1, exv, exz, ezx, eqy, ery, ezy, exs2.
  unfold MP.
  rewrite (obj_uip D1 (eq_sym (strict_assoc_obj x y z))).
  rewrite (obj_uip D2 (eq_sym (strict_assoc_obj x z y))).
  rewrite (obj_uip D3 (strict_assoc_obj z x y)).
  rewrite !id_cast_refl.
  rewrite !id_left, !id_right.
  assert (HX := strict_braid_hex_sym_cast x y z).
  unfold MP in HX.
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
   spelling produced by interpreting [TE_braid_hex_left]. 

   --------
   * K10：在运输拼写中通过解释 [TE_braid_hex_left] 生成的 [⟦·⟧] 索引对象中的左六边形。
*)
Lemma prop_braid_hex_l (m n p : nat) :
  prop_braid (m + n) p ∘ hcast (Nat.add_assoc m n p)
    ≈ (hcast (eq_sym (Nat.add_assoc p m n))
         ∘ ((prop_braid m p ⊞ id[⟦n⟧]) ∘ hcast (Nat.add_assoc m p n)))
        ∘ (id[⟦m⟧] ⊞ prop_braid n p).
Proof using OD P.
  unfold prop_tensor_hom, prop_braid, hcast.
  apply (braid_hex_left_general
           (prop_tensor_plus m n) (prop_tensor_plus n p)
           (prop_tensor_plus (m + n) p) (prop_tensor_plus p (m + n))
           (prop_tensor_plus m (n + p))
           (prop_tensor_plus m p) (prop_tensor_plus p m)
           (prop_tensor_plus (p + m) n) (prop_tensor_plus (m + p) n)
           (prop_tensor_plus p n) (prop_tensor_plus m (p + n))
           (f_equal (@prop_of_nat P) (Nat.add_assoc m n p))
           (f_equal (@prop_of_nat P) (Nat.add_assoc m p n))
           (f_equal (@prop_of_nat P) (eq_sym (Nat.add_assoc p m n)))).
Qed.

(** The braids against the unit object, as casts. / 辫子围绕单位对象，就像投射一样。 *)
Lemma strict_braid_unit_l_core (x : P) :
  strict_braid x (@I P MP)
    ≈ id_cast (eq_sym (strict_unit_left_obj x))
        ∘ id_cast (strict_unit_right_obj x).
Proof using P.
  symmetry.
  rewrite strict_unitr_cast.
  rewrite <- strict_braid_unit_left.
  rewrite <- strict_unitl_cast.
  rewrite comp_assoc.
  rewrite id_cast_inv_l.
  rewrite id_left.
  reflexivity.
Qed.

Lemma strict_braid_unit_r_core (x : P) :
  strict_braid (@I P MP) x
    ≈ id_cast (eq_sym (strict_unit_right_obj x))
        ∘ id_cast (strict_unit_left_obj x).
Proof using P.
  symmetry.
  rewrite strict_unitl_cast.
  rewrite <- strict_braid_unit_right.
  rewrite <- strict_unitr_cast.
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
Lemma braid_unit_general_l {u x q r : P} (eu : @I P MP = u)
  (eux : (u ⨂[MP] x)%object = q) (exu : (x ⨂[MP] u)%object = r)
  (d : r = q) :
  id_cast d ∘ (id_cast exu ∘ strict_braid u x ∘ id_cast (eq_sym eux))
    ≈ id[q].
Proof using OD P.
  destruct eu, eux, exu.
  rewrite (obj_uip d (eq_trans (strict_unit_right_obj x)
                               (eq_sym (strict_unit_left_obj x)))).
  rewrite !id_cast_refl.
  rewrite id_left, id_right.
  rewrite strict_braid_unit_r_core.
  rewrite comp_assoc.
  rewrite !id_cast_trans.
  rewrite id_cast_loop.
  reflexivity.
Qed.

Lemma braid_unit_general_r {u x q r : P} (eu : @I P MP = u)
  (eux : (u ⨂[MP] x)%object = q) (exu : (x ⨂[MP] u)%object = r)
  (d : x = r) (dq : x = q) :
  (id_cast eux ∘ strict_braid x u ∘ id_cast (eq_sym exu)) ∘ id_cast d
    ≈ id_cast dq.
Proof using OD P.
  destruct eu, eux, exu.
  rewrite (obj_uip d (eq_sym (strict_unit_right_obj x))).
  rewrite (obj_uip dq (eq_sym (strict_unit_left_obj x))).
  rewrite !id_cast_refl.
  rewrite id_left, id_right.
  rewrite strict_braid_unit_l_core.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_r.
  rewrite id_right.
  reflexivity.
Qed.

(*
   * K11: the braid of [0] past [n] collapses to the identity. 

   --------
   * K11：[0] 经过 [n] 的编织塌缩为单位元。
*)
Lemma prop_braid_unit_l (n : nat) :
  hcast (Nat.add_0_r n) ∘ prop_braid 0 n ≈ id[⟦n⟧].
Proof using OD P.
  unfold prop_braid, hcast.
  apply (braid_unit_general_l (@prop_unit_zero P)
           (prop_tensor_plus 0 n) (prop_tensor_plus n 0)
           (f_equal (@prop_of_nat P) (Nat.add_0_r n))).
Qed.

(*
   * K12: the braid of [n] past [0] collapses to the identity. 

   --------
   * K12：[n] 经过 [0] 的编织塌缩为单位元。
*)
Lemma prop_braid_unit_r (n : nat) :
  prop_braid n 0 ∘ hcast (eq_sym (Nat.add_0_r n)) ≈ id[⟦n⟧].
Proof using OD P.
  unfold prop_braid, hcast.
  rewrite (id_cast_irr
             (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r n)))
             (eq_sym (f_equal (@prop_of_nat P) (Nat.add_0_r n)))).
  transitivity (id_cast (@eq_refl _ ⟦n⟧ : ⟦n⟧ = ⟦0 + n⟧)).
  - apply (braid_unit_general_r (@prop_unit_zero P)
             (prop_tensor_plus 0 n) (prop_tensor_plus n 0)
             (eq_sym (f_equal (@prop_of_nat P) (Nat.add_0_r n)))
             (@eq_refl _ ⟦n⟧ : ⟦n⟧ = ⟦0 + n⟧)).
  - reflexivity.
Qed.

(* * *** Valuations and the interpretation of terms / * *** 估值与术语的解释 *)

Context (S : Signature).

(*
   * A valuation assigns a target morphism to every generator. 

   --------
   * 一个赋值会给每个生成元分配一个目标态射。
*)
Definition Valuation : Type :=
  ∀ m n : nat, S m n → (⟦m⟧ ~{P}~> ⟦n⟧).

Context (v : Valuation).

(*
   * The interpretation of a raw term, by structural recursion:
   identities to identities, block braids to [prop_braid], sequential
   composition to [∘], parallel composition to [⊞], and generators
   through the valuation.  [interp] COMPUTES on constructors — e.g.
   [interp (T_comp g f)] is definitionally [interp g ∘ interp f] — so
   the functor laws of the packaging file [Universal.v] hold by
   reflexivity. 

   --------
   * 原始项的解释，通过结构递归：  
   恒等映射到恒等，块编织映射到  [prop_braid] ，顺序组合映射到  [∘] ，并行组合映射到  [⊞] ，生成元通过估值映射。  [interp] 在构造器上进行计算——例如  
   [interp (T_comp g f)] 在定义上等于 [interp g ∘ interp f] ——因此打包文件 [Universal.v] 的函子定律通过自反性成立。
*)
Fixpoint interp {m n : nat} (t : Term S m n) : ⟦m⟧ ~{P}~> ⟦n⟧ :=
  match t in Term _ m' n' return ⟦m'⟧ ~{P}~> ⟦n'⟧ with
  | T_id k      => id
  | T_braid a b => prop_braid a b
  | T_comp g f  => interp g ∘ interp f
  | T_tens f g  => interp f ⊞ interp g
  | T_gen g     => v _ _ g
  end.

(*
   * Casts interpret to casts — a Leibniz equality, by [e]-elimination. 

   --------
   * 将解释转换为类型转换——一个莱布尼茨等式，由 [e] 消去。
*)
Lemma interp_T_cast {a b : nat} (e : a = b) :
  interp (T_cast e) = hcast e.
Proof using P. destruct e; reflexivity. Qed.

(*
   * ** Transport bridges

   The strict-PROP axioms of [TermEq] carry their arity mismatches as
   [eq_rect] transports; under [interp] a codomain transport becomes a
   post-composed [hcast] and a domain transport a pre-composed one. 

   --------
   * ** 传输桥

   [TermEq] 的严格 PROP 公理将它们的元数不匹配作为 [eq_rect] 传输；在 [interp] 下，余域传输变为后组合的 [hcast]，而定义域传输变为前组合的 [hcast]。
*)

Lemma interp_eq_rect_cod {a b b' : nat} (e : b = b') (t : Term S a b) :
  interp (eq_rect b (fun k : nat => Term S a k) t b' e)
    ≈ hcast e ∘ interp t.
Proof using P. destruct e; cat. Qed.

Lemma interp_eq_rect_dom {a a' b : nat} (e : a = a') (t : Term S a b) :
  interp (eq_rect a (fun k : nat => Term S k b) t a' e)
    ≈ interp t ∘ hcast (eq_sym e).
Proof using P. destruct e; cat. Qed.

Lemma interp_eq_rect_r_dom {a a' b : nat} (e : a' = a) (t : Term S a b) :
  interp (eq_rect_r (fun k : nat => Term S k b) t e)
    ≈ interp t ∘ hcast e.
Proof using P. destruct e; cat. Qed.

(*
   * *** Soundness

   [TermEq] is [Prop]-valued and the hom equivalence of the abstract
   target is [Type]-valued, so the induction eliminates into the
   [Prop]-reflection [heq] of a [HomEqProp] instance (the [Quotient.v]
   kit) and round-trips through [heq_intro] / [heq_elim].  Every one
   of the nineteen [TermEq] constructors is covered. 

   --------
   * *** 健全性

   [TermEq] 是 [Prop] 值的，并且抽象目标的同态等价是 [Type] 值的，所以归纳消解为 [HomEqProp] 实例（[Quotient.v] 工具包）的 [Prop] 反射 [heq]，并通过 [heq_intro] / [heq_elim] 往返。十九个 [TermEq] 构造函数中的每一个都被涵盖。
*)

Context {HP : HomEqProp P}.

Lemma interp_sound_heq {m n : nat} {s t : Term S m n} :
  TermEq S s t → heq (interp s) (interp t).
Proof using HP OD P S v.
  intros HT.
  induction HT.
  - (* TE_refl *)
    apply heq_intro; reflexivity.
  - (* TE_sym *)
    apply heq_intro; symmetry; exact (heq_elim IHHT).
  - (* TE_trans *)
    apply heq_intro.
    rewrite (heq_elim IHHT1).
    exact (heq_elim IHHT2).
  - (* TE_comp_cong / TE_复合_会聚 *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHHT1), (heq_elim IHHT2).
  - (* TE_tens_cong / TE_张力_从 *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHHT1), (heq_elim IHHT2).
  - (* TE_id_left / TE_id_左 *)
    apply heq_intro; cbn [interp]; apply id_left.
  - (* TE_id_right / TE_id_右 *)
    apply heq_intro; cbn [interp]; apply id_right.
  - (* TE_assoc *)
    apply heq_intro; cbn [interp]; symmetry; apply comp_assoc.
  - (* TE_tens_id / TE_张力_编号 *)
    apply heq_intro; cbn [interp]; apply tensor_hom_id.
  - (* TE_interchange / TE_交换 *)
    apply heq_intro; cbn [interp]; symmetry; apply tensor_hom_comp.
  - (* TE_braid_invol / TE_编织_卷入 *)
    apply heq_intro; cbn [interp]; apply prop_braid_invol.
  - (* TE_braid_natural / TE_天然编织 *)
    apply heq_intro; cbn [interp]; apply prop_braid_swap.
  - (* TE_tens_id0_left / TE_张力_id0_左 *)
    apply heq_intro; cbn [interp]; apply tensor_hom_id0_left.
  - (* TE_tens_id0_right / TE_张力_id0_右 *)
    apply heq_intro.
    rewrite interp_eq_rect_cod, interp_eq_rect_r_dom.
    cbn [interp].
    rewrite tensor_hom_id0_right.
    rewrite !comp_assoc.
    rewrite hcast_inv_r.
    now rewrite id_left.
  - (* TE_tens_assoc / TE_张力_关联 *)
    apply heq_intro.
    rewrite interp_eq_rect_cod, interp_eq_rect_r_dom.
    cbn [interp].
    apply tensor_hom_assoc.
  - (* TE_braid_hex_left / TE_编织_六边形_左 *)
    apply heq_intro.
    cbn [interp].
    rewrite interp_eq_rect_cod.
    rewrite !interp_eq_rect_dom.
    cbn [interp].
    rewrite (hcast_irr (eq_sym (eq_sym (Nat.add_assoc m n p)))
                       (Nat.add_assoc m n p)).
    rewrite (hcast_irr (eq_sym (eq_sym (Nat.add_assoc m p n)))
                       (Nat.add_assoc m p n)).
    apply prop_braid_hex_l.
  - (* TE_braid_hex_right / TE_右编织六边形 *)
    apply heq_intro.
    cbn [interp].
    rewrite interp_eq_rect_cod.
    rewrite !interp_eq_rect_dom.
    cbn [interp].
    rewrite (hcast_irr (eq_sym (eq_sym (Nat.add_assoc m n p)))
                       (Nat.add_assoc m n p)).
    apply prop_braid_hex_r.
  - (* TE_braid_unit_left / TE_编织单元_左 *)
    apply heq_intro.
    rewrite interp_eq_rect_cod.
    cbn [interp].
    apply prop_braid_unit_l.
  - (* TE_braid_unit_right / TE_右编织单元 *)
    apply heq_intro.
    rewrite interp_eq_rect_dom.
    cbn [interp].
    apply prop_braid_unit_r.
Qed.

(** Soundness, in the target's own hom equivalence. / 稳健性，在目标自身的同余等价中。 *)
Theorem interp_sound {m n : nat} {s t : Term S m n} :
  TermEq S s t → interp s ≈ interp t.
Proof using HP OD P S v.
  intros HT.
  exact (heq_elim (interp_sound_heq HT)).
Qed.

End PROPTarget.

Arguments Valuation P S : assert.
Arguments interp P S v {m n} t : assert.
