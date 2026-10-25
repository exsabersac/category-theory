Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
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
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.BaseChange.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * Laws of base change for coloured PROPs / * * 彩色 PROP 的基变律 *)

(*
 nLab: https://ncatlab.org/nlab/show/base+change
 nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
 nLab: https://ncatlab.org/nlab/show/PROP
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

 [Construction/ColouredPROP/BaseChange.v] builds, for every colour
 function [f : Colour → Colour'] and signature morphism [h] over it,
 the strict symmetric monoidal functor

 [BaseChangeF f C'dec S S' h : CFreeCat S ⟶ CFreeCat S']

 through the universal property of the free coloured PROP.  This
 file proves that the construction is (pseudo)functorial in [f], and
 develops its two standard corollaries:

 1.  FUNCTORIALITY.  Along the identity colour function, base change
 is the identity functor ([BaseChangeF_id]); along a composite
 [g ∘ f], it is the composite of the base changes
 ([BaseChangeF_comp]).  Both statements are necessarily
 [hom_cast]-conjugated: the boundary equalities [map_id] and
 [map_map] of the list functor are PROPOSITIONAL, not
 definitional (stdlib's proofs are opaque, and the equations do
 not reduce for variable colour words), so on-the-nose equality
 of the functors is not even well-typed.  The conjugated form is
 the honest statement, and it comes from the UNIQUENESS half of
 the universal property ([cinterp_unique] / [cinterp_unique2])
 rather than from fresh term inductions: each side of the law is
 exhibited as a strict symmetric competitor extending the same
 valuation, and uniqueness pins them together.

 2.  SUBSET RESTRICTION.  A predicate [Q] on colours induces the
 subtype [ColourSub Q := { c | Q c }], and base change along the
 projection [proj1_sig] restricts a free coloured PROP to a
 sub-colour-set ([SubColourFunctor]), with the whole strict
 symmetric monoidal packaging inherited from [BaseChangeF_*].
 Decidability of the subtype is an EXPLICIT hypothesis — it is
 never manufactured from decidability of [Colour] plus proof
 irrelevance of [Q].

 3.  PRESENTED DESCENT.  A signature morphism between the underlying
 signatures of two theories [E], [E'] that carries the axioms of
 [E] to derivable equations of [E'] ([BaseChangeRespects])
 induces a functor between the PRESENTED coloured PROPs
 ([PresentedBaseChange]), by the quotient lifting of
 [Construction/Quotient.v].  The congruence preservation lemma
 [BaseChange_CTermEqW] is a six-case induction whose free-
 equation case is [BaseChangeF]'s own [fmap_respects] — the
 nineteen-case soundness induction is REUSED through the functor,
 never repeated.

 ** Deciders (D2 discipline)

 As everywhere in the coloured spine, colour deciders are explicit
 arguments, one canonical decider per colour type per instance site:
 [Cdec] for the source colours, [C'dec]/[C''dec] for the targets.
 The UIP steps of the functoriality proofs run through [ObjDecEq] on
 the TARGET free category (objects are colour words, decided by
 [list_eq_dec] of the colour decider), via the axiom-free
 [obj_uip]/[id_cast_loop]/[hom_cast_irr] kit of
 [Construction/Quotient.v]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/base+change 
 nLab:  https://ncatlab.org/nlab/show/restriction+of+scalars 
 nLab:  https://ncatlab.org/nlab/show/PROP 
 维基百科:  https://en.wikipedia.org/wiki/PROP_(category_theory) 

 [Construction/ColouredPROP/BaseChange.v] 为每一个颜色函数 [f : Colour → Colour'] 和其上的签名态射 [h] 构建严格对称单体范畴函子 

 [BaseChangeF f C'dec S S' h : CFreeCat S ⟶ CFreeCat S'] 

 通过自由彩色 PROP 的泛性质。这个文件证明了该构造在 [f] 中是（伪）函子性的，并且发展了它的两个标准推论：1. 函子性。沿着恒等色函数，基变换是恒等函子（[BaseChangeF_id]）；沿着复合 [g ∘ f]，它是基变换的复合（[BaseChangeF_comp]）。这两个陈述都必然是 [hom_cast] 共轭的：列表函子的边界等式 [map_id] 和 [map_map] 是命题性的，而不是定义性的（标准库的证明是黑箱的，对于变量色词方程不会化简），所以函子的严格相等甚至类型上都不成立。共轭形式是诚实的陈述，它来源于一般性性质的唯一性部分（[cinterp_unique] / [cinterp_unique2]），而不是来自新的项归纳：定律的两边都被展示为扩展相同赋值的严格对称竞争者，并且唯一性将它们固定在一起。

 2. 子集限制。颜色上的谓词 [Q] 导致子类型 [ColourSub Q := { c | Q c }]，并且沿投影 [proj1_sig] 的基变换将自由着色 PROP 限制到子颜色集合（[SubColourFunctor]），整个严格对称单模包装由 [BaseChangeF_*] 继承。子类型的可判定性是明确的假设——它从不通过 [Colour] 的可判定性加上 [Q] 的证明无关性来生成。3.  呈现下的下降。两个理论 [E] 和 [E'] 的基础签名之间的一个签名态射，将 [E] 的公理转化为 [E']（ZW28WZZ）的可导出方程，通过 [Construction/Quotient.v] 的商提升在呈现的有色 PROP（ZW29WZZ）之间诱导出一个函子。合同保留引理 [BaseChange_CTermEqW] 是一个六情况归纳，其自由方程情况是 [BaseChangeF] 自身的 [fmap_respects]——十九情况的可靠性归纳通过函子重复使用，从不重复。

 ** 决策者（D2 纪律）正如在有色脊的各处一样，颜色决策器是显式参数，每个实例位置每种颜色类型有一个规范的决策器：[Cdec] 用于源颜色，[C'dec] / [C''dec] 用于目标。在函子性证明的 UIP 步骤中，通过目标自由范畴 [ObjDecEq]（对象是颜色词，由颜色决策器 [list_eq_dec] 决定），经过无公理的 [obj_uip] / [id_cast_loop] / [hom_cast_irr] 套件 [Construction/Quotient.v]。
*)

(*
   * ** Transport of generators along boundary equalities

   A signature is a family [S : list Colour → list Colour → Type];
   reindexing a generator along propositional equalities of its
   boundary words is the evident double transport.  Spelled as a
   nested [match] (the [hom_cast] shape of [Construction/Quotient.v])
   so that it computes at [eq_refl]. 

   --------
   * ** 沿边界等式传输生成元

   一个签名是一个族 [S : list Colour → list Colour → Type]；
   沿其边界词的命题等式重新索引生成元就是显而易见的双重传输。拼写为嵌套的 [match]（[Construction/Quotient.v] 的 [hom_cast] 形状），以便它在 [eq_refl] 处计算。
*)

Definition csig_transport {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a b) :
  S a' b' :=
  match e2 in _ = d return S a' d with
  | eq_refl =>
      match e1 in _ = c return S c b with
      | eq_refl => s
      end
  end.

(*
   * At [eq_refl] on both ends, the transport is the identity. 

   --------
   * 在 [eq_refl] 的两端，传输是恒等映射。
*)
Example csig_transport_refl {Colour : Type} {S : CSignature Colour}
  {a b : list Colour} (s : S a b) :
  csig_transport eq_refl eq_refl s = s := eq_refl.

(*
   * Transporting there and back is the identity — [e]-elimination, no
   proof irrelevance needed.  Both round-trip orientations are used:
   [_inv] by the identity law, [_inv_sym] by the composition law. 

   --------
   * 往返的运输就是恒等式 — [e] 消去，无需证明无关性。两种往返方向都使用：[_inv] 通过恒等律，[_inv_sym] 通过复合律。
*)
Lemma csig_transport_inv {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a' b') :
  csig_transport e1 e2 (csig_transport (eq_sym e1) (eq_sym e2) s) = s.
Proof. destruct e1, e2; reflexivity. Qed.

Lemma csig_transport_inv_sym {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a b) :
  csig_transport (eq_sym e1) (eq_sym e2) (csig_transport e1 e2 s) = s.
Proof. destruct e1, e2; reflexivity. Qed.

(*
   * A [hom_cast] of a generator leaf is the generator of the
   transported datum — the bridge between the object-level cast kit
   and the signature-level transport. 

   --------
   * 生成器叶子的 [hom_cast] 是所传输数据的生成器——它是对象级铸件套件与签名级传输之间的桥梁。
*)
Lemma CT_gen_hom_cast {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a b) :
  @hom_cast (CFreeCat S) a b a' b' e1 e2 (CT_gen s)
  = CT_gen (csig_transport e1 e2 s).
Proof. destruct e1, e2; reflexivity. Qed.

(* * ** 1. Base change along the identity colour function / * ** 1. 沿着恒等颜色函数的基底变化 *)

Section BaseChangeIdentity.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).

(*
   * The identity signature morphism over [fun c => c]: each generator
   is transported along [eq_sym (map_id _)] to the boundary words the
   [CSigMap] type demands.  ([map (fun c => c) cs] and [cs] are only
   propositionally equal — the seam this whole section threads.) 

   --------
   * 关于  [fun c => c] 的恒等签名态射：每个生成元沿着  [eq_sym (map_id _)] 传送到 [CSigMap] 类型要求的边界词。（[map (fun c => c) cs] 和 [cs] 只是命题上相等——整个部分的贯穿线。）
*)
Definition CSigMap_id : CSigMap (fun c : Colour => c) S S :=
  fun (cs ds : list Colour) (s : S cs ds) =>
    csig_transport (eq_sym (map_id cs)) (eq_sym (map_id ds)) s.

(*
   * Machine-checked: the identity base change acts on objects by
   [map (fun c => c)] and sends a generator to its transport. 

   --------
   * 机器检查：恒等基变换作用在对象上通过 [map (fun c => c)]，并将生成元发送到其传输。
*)
Example BaseChangeF_identity_fobj (cs : list Colour) :
  fobj[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] cs
  = map (fun c : Colour => c) cs := eq_refl.

Example BaseChangeF_identity_gen {cs ds : list Colour} (s : S cs ds) :
  fmap[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] (CT_gen s)
  = CT_gen (CSigMap_id cs ds s) := eq_refl.

(*
   * The identity functor on [CFreeCat S], as a strict symmetric
   competitor at the identity base-change target: its braid square
   holds because both tensor comparisons are transported identities
   along [eq_refl] and the target's strict-path braiding is the
   [CT_braid] constructor on the nose ([basechange_cstrict_braid]). 

   --------
   * 在 [CFreeCat S] 上的恒等函子，作为恒等基变换目标的严格对称竞争者：它的编织平方成立，因为两个张量比较都是沿 [eq_refl] 传输的恒等式，并且目标的严格路径编织正是 [CT_braid] 构造（[basechange_cstrict_braid]）。
*)
Lemma BaseChangeF_id_square :
  CSymmetricStrict S Cdec (basechange_target (fun c : Colour => c) Cdec S)
    Id[CFreeCat S]
    (@strict_functor_is_monoidal _ _ _ _ Id[CFreeCat S]
       (@Id_StrictMonoidalFunctor (CFreeCat S) (CFreeCat_Monoidal S Cdec))).
Proof.
  intros x y.
  etransitivity; [ apply id_right | symmetry; apply id_left ].
Qed.

(*
   * Generator agreement of the identity competitor: unwinding the
   double [eq_sym] with [eq_sym_involutive], the conjugating cast
   exactly undoes the [CSigMap_id] transport. 

   --------
   * 恒等竞争者的生成元一致性：通过 [eq_sym_involutive] 解开双重 [eq_sym]，结合转换正好抵消了 [CSigMap_id] 的传输。
*)
Lemma BaseChangeF_id_gen (cs ds : list Colour) (s : S cs ds) :
  fmap[Id[CFreeCat S]] (CT_gen s)
    ≈ @hom_cast (CFreeCat S) _ _ _ _
        (eq_sym (eq_sym (map_id cs))) (eq_sym (eq_sym (map_id ds)))
        (basechange_val (fun c : Colour => c) Cdec S S CSigMap_id cs ds s).
Proof.
  rewrite (eq_sym_involutive (map_id cs)), (eq_sym_involutive (map_id ds)).
  unfold basechange_val; cbn beta.
  rewrite CT_gen_hom_cast.
  unfold CSigMap_id; cbn beta.
  rewrite csig_transport_inv.
  reflexivity.
Qed.

(*
   * Functoriality, identity law: the identity base change is the
   identity functor, up to the [hom_cast] conjugation along [map_id].
   By [cinterp_unique] at the identity competitor — no induction on
   terms appears here. 

   --------
   * 函子性，恒等律：恒等基变换是恒等函子，沿着 [map_id] 进行 [hom_cast] 共轭。通过 [cinterp_unique] 在恒等竞赛者处——此处没有对项进行归纳。
*)
Theorem BaseChangeF_id {cs ds : list Colour} (t : CTerm S cs ds) :
  @hom_cast (CFreeCat S)
    (map (fun c : Colour => c) cs) (map (fun c : Colour => c) ds)
    cs ds (map_id cs) (map_id ds)
    (fmap[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] t)
  ≈ t.
Proof.
  assert (HU := @cinterp_unique Colour S Cdec
    (basechange_target (fun c : Colour => c) Cdec S)
    (CFreeCat_ObjDecEq S Cdec)
    (basechange_val (fun c : Colour => c) Cdec S S CSigMap_id)
    Id[CFreeCat S]
    (@Id_StrictMonoidalFunctor (CFreeCat S) (CFreeCat_Monoidal S Cdec))
    BaseChangeF_id_square
    (fun ks : list Colour => eq_sym (map_id ks))
    BaseChangeF_id_gen
    cs ds t).
  symmetry.
  transitivity
    (@hom_cast (CFreeCat S) _ _ _ _
       (eq_sym (eq_sym (map_id cs))) (eq_sym (eq_sym (map_id ds)))
       (fmap[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] t)).
  { exact HU. }
  rewrite (eq_sym_involutive (map_id cs)), (eq_sym_involutive (map_id ds)).
  reflexivity.
Qed.

End BaseChangeIdentity.

(*
 [CSigMap_id] keeps its auto-generated argument status ({Colour} S):
 its type unfolds to a ∀, so the boundary words and the generator
 ride along as trailing arguments (compare [basechange_val] in
 [Construction/ColouredPROP/BaseChange.v]). 

 --------
 [CSigMap_id] 保持其自动生成的参数状态（{Colour} S）：它的类型展开为 ∀，因此边界词和生成器作为尾随参数随之传递（参见 [basechange_val] 在 [Construction/ColouredPROP/BaseChange.v] 中）。
*)

(* * ** 2. Base change along a composite colour function / * ** 2. 沿着复合颜色函数的基底变化 *)

Section BaseChangeComposite.

Context {Colour Colour' Colour'' : Type}.
Context (f : Colour -> Colour').
Context (g : Colour' -> Colour'').
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (C'dec : forall c d : Colour', {c = d} + {c <> d}).
Context (C''dec : forall c d : Colour'', {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (S' : CSignature Colour').
Context (S'' : CSignature Colour'').
Context (hf : CSigMap f S S').
Context (hg : CSigMap g S' S'').

(*
   * The composite signature morphism over [fun c => g (f c)]: apply
   [hf] then [hg], and reindex the boundary words along [map_map]. 

   --------
   * 在复合签名态射 [fun c => g (f c)] 上：先应用 [hf]，然后是 [hg]，并沿 [map_map] 对边界词重新编索引。
*)
Definition CSigMap_compose : CSigMap (fun c : Colour => g (f c)) S S'' :=
  fun (cs ds : list Colour) (s : S cs ds) =>
    csig_transport (map_map f g cs) (map_map f g ds)
      (hg (map f cs) (map f ds) (hf cs ds s)).

(*
   * Local abbreviations for the two legs, their strict structures, and
   their strict tensor comparisons (the [map_app]-shaped object
   equalities pinned by [Example]s in [BaseChange.v]). 

   --------
   * 两条腿的本地缩写，它们的严格结构，以及它们的严格张量比较（由  [Example] 在  [BaseChange.v] 中固定的  [map_app] 形对象等式）。
*)
Notation F1 := (BaseChangeF f C'dec S S' hf).
Notation G1 := (BaseChangeF g C''dec S' S'' hg).
Notation SF1 := (BaseChangeF_Strict f Cdec C'dec S S' hf).
Notation SG1 := (BaseChangeF_Strict g C'dec C''dec S' S'' hg).
Notation apF x y := (@strict_ap_obj _ _ _ _ F1 SF1 x y).
Notation apG x y := (@strict_ap_obj _ _ _ _ G1 SG1 x y).

(*
   * Machine-checked: the composite of the two base changes acts on
   objects by [map g ∘ map f], and the single base change along the
   composite function sends a generator to the composite datum. 

   --------
   * 机器检查：两个基本变换的复合作用在对象上通过 [map g ∘ map f]，而沿复合函数的单个基本变换将生成元发送到复合数据。
*)
Example BaseChangeF_comp_fobj (cs : list Colour) :
  fobj[G1 ◯ F1] cs = map g (map f cs) := eq_refl.

Example BaseChangeF_comp_gen_datum {cs ds : list Colour} (s : S cs ds) :
  fmap[BaseChangeF (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose]
    (CT_gen s)
  = CT_gen (CSigMap_compose cs ds s) := eq_refl.

(*
   * The composite functor is strict monoidal, by the generic
   composition of strict monoidal functors; its strict object
   comparisons are the [eq_trans]/[f_equal] composites of the legs'. 

   --------
   * 复合函子是严格单子函子，通过严格单子函子的通用组合；其严格对象比较是各分支的 [eq_trans] / [f_equal]  复合。
*)
Definition BaseChangeF_comp_Strict :
  @StrictMonoidalFunctor (CFreeCat S) (CFreeCat S'')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S'' C''dec)
    (G1 ◯ F1) :=
  @Compose_StrictMonoidalFunctor (CFreeCat S) (CFreeCat S') (CFreeCat S'')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec)
    (CFreeCat_Monoidal S'' C''dec)
    G1 F1 SG1 SF1.

(*
   * *** The comparison casts of the three functors

   Each strict tensor comparison, spelled as an [id_cast] — the form
   the cast algebra below consumes ([id_cast] is definitionally the
   transported-identity [match] the class fields carry, so each proof
   is the class field itself). 

   --------
   * *** 三个函子（functor）的比较类型转换

   每一个严格张量比较，记作 [id_cast] —— 下面的类型转换代数使用的形式（[id_cast] 在定义上是被传输的恒等 [match]，类字段携带，因此每个证明就是类字段本身）。
*)

Lemma hf_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ F1 (BaseChangeF_Monoidal f Cdec C'dec S S' hf) x y)
    ≈ id_cast (apF x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ F1 SF1 x y). Qed.

Lemma hg_ap_cast (x y : list Colour') :
  to (@ap_iso _ _ _ _ G1 (BaseChangeF_Monoidal g C'dec C''dec S' S'' hg) x y)
    ≈ id_cast (apG x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ G1 SG1 x y). Qed.

Lemma comp_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ (G1 ◯ F1)
        (@strict_functor_is_monoidal _ _ _ _ (G1 ◯ F1)
           BaseChangeF_comp_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ (G1 ◯ F1) BaseChangeF_comp_Strict x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ (G1 ◯ F1) BaseChangeF_comp_Strict x y). Qed.

(*
   * *** The legs' braid images, in cast-conjugated form

   Each leg sends the block braid to the target braid conjugated by
   its own tensor comparison — its [CSymmetricStrict] square of
   [BaseChange.v], with both comparisons rewritten to casts and the
   cast slid across the equation ([comp_cast_shift]).  The target's
   strict-path braiding is the [CT_braid] constructor on the nose
   (the free coherence is [eq_refl]), so the braids are spelled as
   constructors. 

   --------
   * *** 腿的编织图像，以铸造-共轭形式

   每条腿将块状编织发送到由自身张量比较共轭的目标编织——它的 [CSymmetricStrict] 平方
   [BaseChange.v]，两个比较都重写为铸造，铸造通过方程滑动（[comp_cast_shift]）。目标的
   严路径编织是 [CT_braid] 构造器的准确实现（自由相干性是 [eq_refl]），因此这些编织被拼写为构造器。
*)

Lemma hf_braid_conj (x y : list Colour) :
  fmap[F1] (CT_braid x y)
    ≈ id_cast (apF y x) ∘ CT_braid (map f x) (map f y)
        ∘ id_cast (eq_sym (apF x y)).
Proof.
  assert (HB := BaseChangeF_SymmetricStrict f Cdec C'dec S S' hf x y).
  rewrite (hf_ap_cast x y), (hf_ap_cast y x) in HB.
  exact (comp_cast_shift (apF x y) (fmap[F1] (CT_braid x y))
           (id_cast (apF y x) ∘ CT_braid (map f x) (map f y)) HB).
Qed.

Lemma hg_braid_conj (x y : list Colour') :
  fmap[G1] (CT_braid x y)
    ≈ id_cast (apG y x) ∘ CT_braid (map g x) (map g y)
        ∘ id_cast (eq_sym (apG x y)).
Proof.
  assert (HB := BaseChangeF_SymmetricStrict g C'dec C''dec S' S'' hg x y).
  rewrite (hg_ap_cast x y), (hg_ap_cast y x) in HB.
  exact (comp_cast_shift (apG x y) (fmap[G1] (CT_braid x y))
           (id_cast (apG y x) ∘ CT_braid (map g x) (map g y)) HB).
Qed.

(*
   * *** The composite braid square

   The composite functor satisfies the braid-compatibility square
   over ITS composite tensor comparison.  Proof: push [fmap[G1◯F1]]
   through the two conjugated braid images ([hf_braid_conj] under
   [fmap[G1]], then [fmap_id_cast] and [hg_braid_conj]), then fuse
   the resulting cast chain: the three inner casts compose to a loop
   on the tensor object, killed by axiom-free UIP on colour words
   ([id_cast_loop] at [CFreeCat_ObjDecEq S'' C''dec]); the two outer
   casts fuse to exactly the composite comparison. 

   --------
   * *** 复合编织方格

   复合函子满足其复合张量比较下的编织兼容方格。证明：将 [fmap[G1◯F1] ] 推过两个共轭的编织像（在 [fmap[G1] ] 下的 [hf_braid_conj]，然后是 [fmap_id_cast] 和 [hg_braid_conj]），然后融合得到的转换链：三个内部转换组成张量对象上的一个循环，由颜色词的无公理 UIP 消去（在 [CFreeCat_ObjDecEq S'' C''dec] 的 [id_cast_loop]）；两个外部转换恰好融合为复合比较。
*)

Lemma BaseChange_comp_square :
  CSymmetricStrict S Cdec
    (basechange_target (fun c : Colour => g (f c)) C''dec S'')
    (G1 ◯ F1)
    (@strict_functor_is_monoidal _ _ _ _ (G1 ◯ F1) BaseChangeF_comp_Strict).
Proof using C''dec C'dec Cdec Colour Colour' Colour'' S S' S'' f g hf hg.
  intros x y.
  rewrite (comp_ap_cast x y), (comp_ap_cast y x).
  change (fmap[G1 ◯ F1] (CT_braid x y))
    with (fmap[G1] (fmap[F1] (CT_braid x y))).
  rewrite (hf_braid_conj x y).
  rewrite !fmap_comp.
  rewrite (fmap_id_cast G1 (apF y x)).
  rewrite (fmap_id_cast G1 (eq_sym (apF x y))).
  rewrite (hg_braid_conj (map f x) (map f y)).
  rewrite <- !comp_assoc.
  rewrite id_cast_trans.
  rewrite id_cast_trans.
  rewrite (@id_cast_loop (CFreeCat S'') (CFreeCat_ObjDecEq S'' C''dec)).
  rewrite id_right.
  rewrite comp_assoc.
  rewrite id_cast_trans.
  reflexivity.
Qed.

(*
   * Generator agreement of the composite competitor: the conjugating
   cast along [eq_sym (map_map ...)] exactly undoes the
   [CSigMap_compose] transport. 

   --------
   * 复合竞争者的发电机协议：沿着 [eq_sym (map_map ...)] 的结合铸造正好抵消了 [CSigMap_compose] 的传输。
*)
Lemma BaseChangeF_comp_gen (cs ds : list Colour) (s : S cs ds) :
  fmap[G1 ◯ F1] (CT_gen s)
    ≈ @hom_cast (CFreeCat S'') _ _ _ _
        (eq_sym (map_map f g cs)) (eq_sym (map_map f g ds))
        (basechange_val (fun c : Colour => g (f c)) C''dec S S''
           CSigMap_compose cs ds s).
Proof.
  unfold basechange_val; cbn beta.
  rewrite CT_gen_hom_cast.
  unfold CSigMap_compose; cbn beta.
  rewrite csig_transport_inv_sym.
  reflexivity.
Qed.

(*
   * Generator agreement of the one-step competitor, with [eq_refl]
   object family — definitional. 

   --------
   * 单步竞争者的发电机协议，与 [eq_refl] 对象系列 — 定义性。
*)
Lemma BaseChangeF_comp_gen2 (cs ds : list Colour) (s : S cs ds) :
  fmap[BaseChangeF (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose]
    (CT_gen s)
    ≈ @hom_cast (CFreeCat S'') _ _ _ _
        (eq_sym (@eq_refl _ (map (fun c : Colour => g (f c)) cs)))
        (eq_sym (@eq_refl _ (map (fun c : Colour => g (f c)) ds)))
        (basechange_val (fun c : Colour => g (f c)) C''dec S S''
           CSigMap_compose cs ds s).
Proof. reflexivity. Qed.

(*
   * Functoriality, composition law: base change along [g ∘ f] agrees
   with the composite of the base changes, up to the [hom_cast]
   conjugation along [map_map].  Both sides are strict symmetric
   competitors extending the valuation [CT_gen ∘ CSigMap_compose],
   so [cinterp_unique2] pins them together. 

   --------
   * 函子性，组合律：沿  [g ∘ f] 的基变换与基变换的复合一致，直到沿  [map_map] 的  [hom_cast] 共轭。两边都是严格对称的竞争者，扩展了赋值  [CT_gen ∘ CSigMap_compose]，因此  [cinterp_unique2] 将它们固定在一起。
*)
Theorem BaseChangeF_comp {cs ds : list Colour} (t : CTerm S cs ds) :
  @hom_cast (CFreeCat S'')
    (map g (map f cs)) (map g (map f ds))
    (map (fun c : Colour => g (f c)) cs) (map (fun c : Colour => g (f c)) ds)
    (map_map f g cs) (map_map f g ds)
    (fmap[G1 ◯ F1] t)
  ≈ fmap[BaseChangeF (fun c : Colour => g (f c)) C''dec S S''
           CSigMap_compose] t.
Proof using C''dec C'dec Cdec Colour Colour' Colour'' S S' S'' f g hf hg.
  exact (@cinterp_unique2 Colour S Cdec
    (basechange_target (fun c : Colour => g (f c)) C''dec S'')
    (CFreeCat_ObjDecEq S'' C''dec)
    (basechange_val (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose)
    (G1 ◯ F1)
    BaseChangeF_comp_Strict
    BaseChange_comp_square
    (fun ks : list Colour => map_map f g ks)
    BaseChangeF_comp_gen
    (BaseChangeF (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose)
    (BaseChangeF_Strict (fun c : Colour => g (f c)) Cdec C''dec S S''
       CSigMap_compose)
    (BaseChangeF_SymmetricStrict (fun c : Colour => g (f c)) Cdec C''dec
       S S'' CSigMap_compose)
    (fun ks : list Colour => @eq_refl _ (map (fun c : Colour => g (f c)) ks))
    BaseChangeF_comp_gen2
    cs ds t).
Qed.

End BaseChangeComposite.

(*
 [CSigMap_compose] keeps its auto-generated argument status
 ({Colour Colour' Colour''} f g S S' S'' hf hg): its type unfolds to
 a ∀, so the boundary words and the generator ride along as trailing
 arguments. 

 --------
 [CSigMap_compose] 保持其自动生成的论证状态
 ({Colour Colour' Colour''} f g S S' S'' hf hg)：它的类型展开为
 一个 ∀，因此边界词和生成器作为尾随参数随之携带。
*)
Arguments BaseChangeF_comp_Strict {Colour Colour' Colour''} f g Cdec C'dec
  C''dec S S' S'' hf hg : assert.

(*
   * ** 3. Subset restriction: base change along a subtype projection 

   --------
   * ** 3. 子集限制：沿子类型投影进行基变换
*)

(*
   * The subtype of colours satisfying a predicate [Q].  Base change
   along the first projection restricts a free coloured PROP over
   [Colour] to the colours in [Q]. 

   --------
   * 满足谓词 [Q] 的颜色子类型。沿第一个投影的基变换将 [Colour] 上的自由有色 PROP 限制到 [Q] 中的颜色。
*)
Definition ColourSub {Colour : Type} (Q : Colour -> Prop) : Type :=
  { c : Colour | Q c }.

Section SubsetRestriction.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (Q : Colour -> Prop).
Context (Ssub : CSignature (ColourSub Q)).

(*
   * Decidability of the SUBTYPE is an explicit hypothesis: for a
   [Prop]-valued [Q] it does not follow from [Cdec] without proof
   irrelevance of [Q], and this file manufactures no such principle.
   (For proof-irrelevant or decidable [Q] the caller can of course
   construct [CdecSub] and pass it in.) 

   --------
   * 子类型的可判定性是一个明确的假设：对于一个 [Prop] 值的 [Q]，它并不能从 [Cdec] 推出 [Q] 的与证明无关性，而且这个文件并没有制造这样的原理。（对于与证明无关或可判定的 [Q]，调用者当然可以构造 [CdecSub] 并传入。）
*)
Context (CdecSub : forall a b : ColourSub Q, {a = b} + {a <> b}).
Context (hsub : CSigMap (@proj1_sig Colour Q) Ssub S).

(*
   * The restriction functor, and its inherited strict symmetric
   monoidal packaging — each record is the corresponding
   [BaseChangeF_*] of [BaseChange.v] at [f := proj1_sig], typed at
   the two shared [Monoidal] records of the ambient colour types. 

   --------
   * 限制范畴函子及其继承的严格对称单体包装 — 每个记录都是对应于 [BaseChange.v] 在 [f := proj1_sig] 的 [BaseChangeF_*] ，类型为环境颜色类型的两个共享 [Monoidal] 记录。
*)

Definition SubColourFunctor : CFreeCat Ssub ⟶ CFreeCat S :=
  BaseChangeF (@proj1_sig Colour Q) Cdec Ssub S hsub.

Definition SubColourFunctor_Monoidal :
  @MonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Monoidal Ssub CdecSub) (CFreeCat_Monoidal S Cdec)
    SubColourFunctor :=
  BaseChangeF_Monoidal (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_Strict :
  @StrictMonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Monoidal Ssub CdecSub) (CFreeCat_Monoidal S Cdec)
    SubColourFunctor :=
  BaseChangeF_Strict (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_Braided :
  @BraidedMonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Braided Ssub CdecSub) (CFreeCat_Braided S Cdec)
    SubColourFunctor :=
  BaseChangeF_Braided (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Symmetric Ssub CdecSub) (CFreeCat_Symmetric S Cdec)
    SubColourFunctor :=
  BaseChangeF_Symmetric (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_SymmetricStrict :
  CSymmetricStrict Ssub CdecSub
    (basechange_target (@proj1_sig Colour Q) Cdec S)
    SubColourFunctor SubColourFunctor_Monoidal :=
  BaseChangeF_SymmetricStrict (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

(*
   * Machine-checked: the restriction acts on objects by erasing the
   membership proofs, and on generators through [hsub]. 

   --------
   * 机器检查：该限制通过擦除成员资格证明作用于对象，通过 [hsub] 作用于生成器。
*)
Example SubColourFunctor_fobj (cs : list (ColourSub Q)) :
  fobj[SubColourFunctor] cs = map (@proj1_sig Colour Q) cs := eq_refl.

Example SubColourFunctor_gen {cs ds : list (ColourSub Q)}
  (s : Ssub cs ds) :
  fmap[SubColourFunctor] (CT_gen s) = CT_gen (hsub cs ds s) := eq_refl.

(** A restricted wire is the wire of the underlying colour. / 限制电线是基础颜色的电线。 *)
Example SubColourFunctor_wire (c : ColourSub Q) :
  fmap[SubColourFunctor] (CT_id [c]) = CT_id [proj1_sig c] := eq_refl.

End SubsetRestriction.

Arguments SubColourFunctor {Colour} Cdec S Q Ssub hsub : assert.

(* * ** 4. Descent to presented coloured PROPs / * ** 4. 向呈现的有色PROP下降 *)

Section PresentedDescent.

Context {Colour Colour' : Type}.
Context (f : Colour -> Colour').
Context (C'dec : forall c d : Colour', {c = d} + {c <> d}).
Context (E : CSMT Colour).
Context (E' : CSMT Colour').
Context (hE : CSigMap f (csmt_sig E) (csmt_sig E')).

(*
   * The base-change functor between the underlying free categories. 

   --------
   * 基于底层自由范畴之间的基变换函子。
*)
Notation BF := (BaseChangeF f C'dec (csmt_sig E) (csmt_sig E') hE).

(*
   * A signature morphism RESPECTS the theories when it carries every
   axiom of [E] to a derivable equation of [E'].  This is the
   semantic entry fee of the descent — the analogue, one level up, of
   the [ESound] hypothesis of the presented universal property. 

   --------
   * 当一个签名态射将 [E] 的每一个公理都映射到 [E'] 可推导的方程时，它就尊重这些理论。这是下降的语义入场费——相当于比所展示的泛性质更高一级的 [ESound] 假设。
*)
Definition BaseChangeRespects : Type :=
  forall (cs ds : list Colour) (s t : CTerm (csmt_sig E) cs ds),
    csmt_eqs E cs ds s t ->
    CTermEqW E' (fmap[BF] s) (fmap[BF] t).

Context (HR : BaseChangeRespects).

(*
   * [BF] carries the whole theory congruence of [E] into that of
   [E'].  Six cases; the embedded free equations go through [BF]'s
   OWN respectfulness (the nineteen-case soundness induction of the
   universal property, reused through the functor — not repeated);
   the axioms go through [HR]; the composition and tensor congruence
   cases are closed by the corresponding [CTermEqW] constructors,
   since [fmap[BF]] computes to [CT_comp] on composites and to a
   cast-conjugated [CT_tens] on tensors, with the SAME conjugating
   casts on both sides of each equation. 

   --------
   * [BF] 将 [E] 的整个理论合合同于 [E']。六种情况；嵌入的自由方程通过 [BF] 的自身敬意（普遍性质的十九案例有效性归纳，通过函子重用——不重复）；公理通过 [HR]；组合和张量合同情况由相应的 [CTermEqW] 构造器关闭，因为 [fmap[BF] 在复合上计算为 [CT_comp]，在张量上计算为一个类型转换共轭的 [CT_tens]，在每个方程的两边都有相同的共轭类型转换。
*)
Lemma BaseChange_CTermEqW {cs ds : list Colour}
  {s t : CTerm (csmt_sig E) cs ds} :
  CTermEqW E s t -> CTermEqW E' (fmap[BF] s) (fmap[BF] t).
Proof using C'dec E E' HR f hE.
  intros H.
  induction H as
    [ cs0 ds0 s0 t0 Hst
    | cs0 ds0 s0 t0 Hax
    | cs0 ds0 s0 t0 Hst IH
    | cs0 ds0 s0 t0 u0 Hst IH1 Htu IH2
    | cs0 ds0 es0 f0 f0' g0 g0' Hf IHf Hg IHg
    | cs1 ds1 cs2 ds2 f0 f0' g0 g0' Hf IHf Hg IHg ].
  - (* CTEW_termeq: a free equation, through fmap_respects / CTEW_termeq：一个自由方程，通过 fmap_respects *)
    apply CTEW_termeq.
    exact (@fmap_respects _ _ BF cs0 ds0 s0 t0 Hst).
  - (* CTEW_ax: an axiom of E, through the respect hypothesis / CTEW_ax：E 的一个公理，通过尊重假设 *)
    exact (HR cs0 ds0 s0 t0 Hax).
  - (* CTEW_sym *)
    exact (CTEW_sym E' _ _ IH).
  - (* CTEW_trans / CTEW_翻译 *)
    exact (CTEW_trans E' _ _ _ IH1 IH2).
  - (* CTEW_comp: fmap computes to CT_comp on both sides / CTEW_comp：fmap 在两边都计算为 CT_comp *)
    exact (CTEW_comp E' _ _ _ _ IHf IHg).
  - (* CTEW_tens: fmap computes to a cast-conjugated CT_tens; the casts agree on both sides, so two composition congruences around the tensor congruence close the goal / CTEW_tens：fmap 计算得到一个经过共轭转换的 CT_tens；两边的转换是一致的，因此围绕张量合同的两个组合合同可以完成目标 *)
    exact (CTEW_comp E' _ _ _ _
             (CTEW_comp E' _ _ _ _
                (CTermEqW_refl E' _)
                (CTEW_tens E' _ _ _ _ IHf IHg))
             (CTermEqW_refl E' _)).
Qed.

(*
   * The descended functor between the presented coloured PROPs: the
   quotient lifting of the projection-postcomposed base change.  On
   objects it is [map f]; on morphisms it is [fmap[BF]] — only the
   equivalences coarsen. 

   --------
   * 在所呈现的彩色 PROP 之间的下降函子：投影后组合基变换的商提升。在对象上是 [map f]；在态射上是 [fmap[BF] ] — 只有等价关系被粗化。
*)
Definition PresentedBaseChange : CPresentedCat E ⟶ CPresentedCat E' :=
  @QuotientLift (CFreeCat (csmt_sig E))
    (fun cs ds : list Colour => @CTermEqW Colour E cs ds)
    (CTermEqW_Congruence E)
    (CPresentedCat E')
    (CPresentedProj E' ◯ BF)
    (fun (cs ds : list Colour) (s t : CTerm (csmt_sig E) cs ds)
         (H : CTermEqW E s t) => BaseChange_CTermEqW H).

(*
   * Machine-checked: the descended functor acts on objects by [map f],
   on quotiented terms by [fmap[BF]], and the descent square with the
   two projections commutes definitionally. 

   --------
   * 机器校验：下落函子在对象上作用为 [map f]，
   在取商项上作用为 [fmap[BF]，并且带有两个投影的下落平方在定义上是交换的。
*)
Example PresentedBaseChange_fobj (cs : list Colour) :
  fobj[PresentedBaseChange] cs = map f cs := eq_refl.

Example PresentedBaseChange_fmap {cs ds : list Colour}
  (t : CTerm (csmt_sig E) cs ds) :
  fmap[PresentedBaseChange] (cquot E t) = cquot E' (fmap[BF] t) := eq_refl.

Example PresentedBaseChange_factor {cs ds : list Colour}
  (t : CTerm (csmt_sig E) cs ds) :
  fmap[PresentedBaseChange] (fmap[CPresentedProj E] t)
  = fmap[CPresentedProj E'] (fmap[BF] t) := eq_refl.

(*
   * Every axiom of [E] holds in [CPresentedCat E'] after descent — the
   end-to-end form of [BaseChangeRespects]. 

   --------
   * 每一个 [E] 的公理在下降后都在 [CPresentedCat E'] 中成立——这是 [BaseChangeRespects] 的端到端形式。
*)
Example PresentedBaseChange_respects_axioms {cs ds : list Colour}
  (s t : CTerm (csmt_sig E) cs ds) (Hax : csmt_eqs E cs ds s t) :
  fmap[PresentedBaseChange] (cquot E s)
    ≈[CPresentedCat E'] fmap[PresentedBaseChange] (cquot E t) :=
  HR cs ds s t Hax.

End PresentedDescent.

Arguments BaseChangeRespects {Colour Colour'} f C'dec E E' hE : assert.
Arguments PresentedBaseChange {Colour Colour'} f C'dec E E' hE HR : assert.

(*
   * ** Discussion

   The two functoriality laws are as strict as the type theory
   permits: [map_id] and [map_map] are propositional equalities of
   colour words, so the laws hold up to the corresponding [hom_cast]
   conjugations and no more.  (With definitionally-proof-irrelevant
   equality — or with [nat]-indexed one-sorted PROPs, where the donor
   spine keeps every boundary equation in [Nat] — some of these casts
   would collapse; over an arbitrary [Colour : Type] they are
   irreducible.)  Together the laws exhibit free-coloured-PROP
   formation as functorial up to the [hom_cast] comparisons — the
   1-cell-level identity and composition agreements of a would-be
   pseudofunctor from coloured signatures over varying colour sets
   to strict symmetric monoidal categories.  The coherence
   conditions a pseudofunctor additionally demands of its comparison
   cells (compatibility of the [map_id] / [map_map] cast families
   under pasting, and their associativity/unit coherence) are NOT
   formalized here.

   [PresentedBaseChange] extends this to presented coloured PROPs:
   functoriality of the descended construction along identities and
   composites follows from [QuotientLift_unique] together with the
   laws above, at the price of the same casts; the statements are
   omitted here because nothing in the library consumes them —
   the same no-consumer ground on which the free-level laws
   themselves currently stand, since no in-repo file yet imports
   this one. 

   --------
   * ** 讨论两个函子律在类型理论允许的范围内是严格的：[map_id] 和 [map_map] 是颜色词的命题等式，因此这些律仅在相应的 [hom_cast] 共轭下成立，不会更多。（对于定义性不可知等式——或者对于 [nat] 索引的一类单排序 PROP，其中供体脊保持每个边界方程在 [Nat]——这些类型转换中的一些将会坍塌；在任意 [Colour : Type] 上它们是不可约的。）这些律共同展示了自由着色 PROP 的形成在 [hom_cast] 比较下是函子性的——即从不同颜色集合上的着色符号到严格对称单体范畴的拟函子在 1-胞单元级别的恒等与复合一致性。伪函子额外要求其比较单元的相干性条件（在粘贴过程中  [map_id] / [map_map] 类型家族的兼容性，以及它们的结合性/单位相干性）在此并未形式化。

   [PresentedBaseChange] 将其推广到呈现的彩色 PROP：沿恒等和复合的下行构造的函子性可由 [QuotientLift_unique] 以及上述律推出，代价是相同的类型转换；这些陈述在此省略，因为库中没有任何内容使用它们——这与自由层次律目前所处的无使用者基础相同，因为仓库中还没有文件导入该文件。
*)
