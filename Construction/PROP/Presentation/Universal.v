Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Construction.PROP.Presentation.

From Coq Require Import Arith.

Generalizable All Variables.

(* * * The universal property of a presented PROP / * * 一个所呈现的PROP的普遍性质 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/generators+and+relations
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

 [Construction/PROP/Universal.v] packages the interpretation of free
 terms into the strict symmetric monoidal functor [InterpF] and
 proves it unique: the free PROP is initial among PROPs with an
 [S]-valuation.  This file extends that universal property through a
 PRESENTATION: given a symmetric monoidal theory [E : SMT] and a
 valuation [v] of its generators in a PROP [P] that is SOUND for the
 axioms of [E] ([ESound] — axiom-related terms have equivalent
 interpretations), the interpretation factors through the presented
 PROP of [Construction/PROP/Presentation.v], uniquely among strict
 symmetric monoidal functors.

 In one sentence: an [E]-sound valuation extends uniquely through
 the presented PROP.  This is the rule-soundness interface by which
 an equational theory is installed into a semantic target once, and
 every [TermEqW]-derivable equation then holds there for free.

 Contents:

 - [interpW_sound]: soundness of [interp] for the theory congruence
 [TermEqW E] — a six-constructor induction whose [TEW_termeq] case
 is [Interp.v]'s whole nineteen-case [interp_sound_heq], reused;
 as there, [TermEqW] is [Prop]-valued while the hom equivalence of
 the abstract target is [Type]-valued, so the induction lands in
 the [Prop]-reflection [heq] and round-trips through
 [heq_intro]/[heq_elim];

 - [PresentedInterp]: the interpretation functor on [PresentedCat E],
 obtained by the quotient lifting of [Construction/Quotient.v]; it
 factors [InterpF] through [PresentedProj E] DEFINITIONALLY
 ([PresentedInterp_proj] is a Leibniz equality by [eq_refl], and
 [Presented_factor] is its [≈]-level restatement);

 - the strict symmetric monoidal structure on [PresentedInterp]: the
 comparison DATA are the same [prop_unit_zero]/[prop_tensor_plus]
 casts as [InterpF]'s, and every proof field is one of
 [Universal.v]'s named coherence lemmas ([interp_ap_natural],
 [interp_monoidal_unit_left]/[interp_monoidal_unit_right],
 [interp_monoidal_assoc], [interp_braid_ap]) — their statements
 are purely target-side, which is exactly why they were factored
 out there;

 - [Presented_unique]: any strict symmetric competitor
 [G : PresentedCat E ⟶ P] agreeing with [v] on generators agrees
 with [interp] on EVERY morphism of the presented category, up to
 the [hom_cast] conjugation along an object-agreement family
 [Hobj].  Proved by PRECOMPOSITION with the projection: the
 composite [G ◯ PresentedProj E] is strict monoidal by
 [Compose_StrictMonoidalFunctor], its comparisons collapse onto
 [G]'s own because the projection's comparisons are identities
 with [eq_refl] object equalities, so [Universal.v]'s
 [interp_unique] applies to the composite and transfers back
 definitionally — every hom of [PresentedCat E] IS a term;

 - [Presented_unique_from_one]: the object agreement synthesised
 from the single datum [G 1 = ⟦1⟧] by the [PresentedG_obj]
 fixpoint, exactly as [interp_unique_from_one] does on the free
 side ([strict_pure_obj] against [prop_unit_zero] at arity 0,
 [strict_ap_obj] against [prop_tensor_plus] peeling one wire at a
 time).

 As in [Universal.v], "strict symmetric monoidal functor" is one
 [StrictMonoidalFunctor] over the strict-path monoidals plus the
 braid-compatibility square [SymmetricStrictW] over that SAME tensor
 comparison, with the target braiding re-indexed to the strict path
 by [strict_braid]; see the design note there for why the hypothesis
 pack is phrased against this bundle rather than against the two
 independent [StrictMonoidalFunctor]/[BraidedMonoidalFunctor]
 classes of [Functor/Structure/Monoidal/Strict.v] and
 [Functor/Structure/Monoidal/Braided.v]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/PROP
 nLab:  https://ncatlab.org/nlab/show/generators+and+relations
 Wikipedia:  https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia:  https://en.wikipedia.org/wiki/Presentation_of_a_monoid

 [Construction/PROP/Universal.v] 将自由项的解释封装到严格对称单体函子 [InterpF] 中，并证明其唯一性：自由 PROP 在具有 [S] 估值的 PROP 中是初始的。该文件通过一个表达扩展了该泛性质：给定一个对称单体理论 [E : SMT] 以及其生成元在 PROP [P] 中的估值 [v]，该估值对 [E] 的公理是正确的（[ESound] — 公理相关项具有等价解释），则解释唯一地通过 [Construction/PROP/Presentation.v] 的表达 PROP，并且在严格对称单体函子中唯一。一句话概括：[E] 声音估值在所呈现的 PROP 中是唯一扩展的。这是规则-可靠性接口，通过它，一个等式理论被安装到语义目标中一次，然后每一个 [TermEqW] 可导的等式就可以免费在那儿成立。

 内容：

 - [interpW_sound]：[interp] 对理论同余 [TermEqW E] 的可靠性——一个六构造归纳，其 [TEW_termeq] 情况是 [Interp.v] 的整个十九情况 [interp_sound_heq]，被重用；如同那里，[TermEqW] 是 [Prop] 值，同时抽象目标的同伦等价是 [Type] 值，所以归纳落在 [Prop] 反射 [heq]，并通过 [heq_intro] / [heq_elim] 往返。- [PresentedInterp]：在 [PresentedCat E] 上的解释函子，通过 [Construction/Quotient.v] 的商提升获得；它在定义上将 [InterpF] 分解通过 [PresentedProj E]（[PresentedInterp_proj] 是 [eq_refl] 的莱布尼茨等式，[Presented_factor] 是其 [≈] 级别的重述）；

 - [PresentedInterp] 上的严格对称幺半群结构：比较数据（DATA）与 [InterpF] 的 [prop_unit_zero] / [prop_tensor_plus] 强制类型转换相同，并且每个证明字段都是 [Universal.v] 中命名的相干引理（[interp_ap_natural]，[interp_monoidal_unit_left] / [interp_monoidal_unit_right]，[interp_monoidal_assoc]，[interp_braid_ap]）之一——它们的陈述完全是目标端的，这正是它们被分解出去的原因；-  [Presented_unique]：任何严格对称的竞争者  
 [G : PresentedCat E ⟶ P] 在生成元上与 [v] 一致，则在呈现的范畴的每一个态射上也与 [interp] 一致，最多在一个对象一致性族 [Hobj] 作用下的 [hom_cast] 共轭。  
 通过与投影的预组合证明：复合 [G ◯ PresentedProj E] 根据 [Compose_StrictMonoidalFunctor] 是严格单态的，其比较映射归约到 [G] 本身，因为投影的比较映射是 [eq_refl] 对象等式的恒等式，因此 [Universal.v] 的 [interp_unique] 可以应用于复合映射并定义上转回——[PresentedCat E] 的每一个同态都是一个项；-  [Presented_unique_from_one]：由单一数据 [G 1 = https://ncatlab.org/nlab/show/generators+and+relations] 通过 [PresentedG_obj] 不动点合成的对象一致性，正如 [interp_unique_from_one] 在自由端所做的那样（在元数 0 时 [strict_pure_obj] 对 [prop_unit_zero]，逐次剥离一条线时 [strict_ap_obj] 对 [prop_tensor_plus]）。

 如在 [Universal.v] 中，“严格对称单体函子”是一个 [StrictMonoidalFunctor]，作用于严格路径单体上，加上针对相同张量比较的编织兼容方形 [SymmetricStrictW]，其目标编织通过 [strict_braid] 重新索引到严格路径；参见设计说明，了解为何假设包是针对该捆绑而不是针对两个独立的 [StrictMonoidalFunctor] / [BraidedMonoidalFunctor] 类 [Functor/Structure/Monoidal/Strict.v] 和 [Functor/Structure/Monoidal/Braided.v] 来表述。
*)

Section PresentedUniversal.

Context (E : SMT).
Context (P : PROP).
Context {HP : HomEqProp P}.
Context {OD : @ObjDecEq P}.

Notation Σ := (smt_sig E).

Context (v : Valuation P Σ).

Open Scope nat_scope.

Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(*
   * ** 1. Soundness for the theory congruence

   A valuation is [E]-SOUND when the two sides of every axiom of the
   theory have equivalent interpretations.  This is the semantic
   entry fee of the presentation: the free equations hold in any
   PROP ([interp_sound]), and the axioms hold by hypothesis. 

   --------
   * ** 1. 理论一致性的可靠性

   当理论的每条公理的两边具有等价解释时，一个赋值是 [E]-可靠的。这是表示的语义入场费：自由方程在任何 PROP ([interp_sound]) 中都成立，并且公理按假设成立。
*)

Definition ESound : Type :=
  ∀ m n (s t : Term Σ m n),
    smt_eqs E m n s t → interp P Σ v s ≈ interp P Σ v t.

Context (Hv : ESound).

(*
   * Soundness of [interp] for [TermEqW E], in the [Prop]-reflection.
   Six cases: the embedded free equations are [Interp.v]'s
   [interp_sound_heq] wholesale; the axioms are [Hv]; symmetry,
   transitivity and the two composition congruences round-trip
   through [heq_intro]/[heq_elim] as in the donor induction. 

   --------
   * [interp] 对于 [TermEqW E] 的健全性，在 [Prop]-反射中。
   六种情况：嵌入的自由方程是 [Interp.v] 的 [interp_sound_heq] 全部；公理是 [Hv]；对称性、传递性和两个复合合同通过 [heq_intro] / [heq_elim] 循环，如同捐赠者归纳中。
*)
Lemma interpW_sound_heq {m n : nat} {s t : Term Σ m n} :
  TermEqW E s t → heq (interp P Σ v s) (interp P Σ v t).
Proof using E HP Hv OD P v.
  intros HT.
  induction HT as
    [ m n s t Hst
    | m n s t Hax
    | m n s t Hst IH
    | m n s t u Hst IH1 Htu IH2
    | m n p f f' g g' Hf IHf Hg IHg
    | m1 n1 m2 n2 f f' g g' Hf IHf Hg IHg ].
  - (* TEW_termeq: a free equation / TEW_termeq：一个免费的方程 *)
    exact (interp_sound_heq P Σ v Hst).
  - (* TEW_ax: an axiom of the theory / TEW_ax：该理论的公理 *)
    exact (heq_intro (Hv _ _ s t Hax)).
  - (* TEW_sym *)
    apply heq_intro; symmetry; exact (heq_elim IH).
  - (* TEW_trans / TEW_传输 *)
    apply heq_intro.
    rewrite (heq_elim IH1).
    exact (heq_elim IH2).
  - (* TEW_comp *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
  - (* TEW_tens *)
    apply heq_intro; cbn [interp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
Qed.

(** Soundness, in the target's own hom equivalence. / 稳健性，在目标自身的同余等价中。 *)
Theorem interpW_sound {m n : nat} {s t : Term Σ m n} :
  TermEqW E s t → interp P Σ v s ≈ interp P Σ v t.
Proof using E HP Hv OD P v.
  intros HT.
  exact (heq_elim (interpW_sound_heq HT)).
Qed.

(*
   * ** 2. The interpretation functor on the presented category

   [InterpF] identifies [TermEqW]-related morphisms (that is
   [interpW_sound]), so it lifts through the quotient by the
   universal property of [Construction/Quotient.v].  The lift acts
   on objects and morphisms exactly as [InterpF] does. 

   --------
   * ** 2. 在所呈现的范畴上的解释函子

   [InterpF] 识别与 [TermEqW] 相关的态射（也就是 [interpW_sound]），因此它通过 [Construction/Quotient.v] 的普遍性质在商中上升。这个上升作用在对象和态射上完全像 [InterpF] 一样。
*)

Definition PresentedInterp : PresentedCat E ⟶ P :=
  @QuotientLift (FreeCat Σ) (fun m n : nat => @TermEqW E m n)
    (TermEqW_Congruence E) P (InterpF Σ P v)
    (fun (m n : nat) (s t : Term Σ m n) (H : TermEqW E s t) =>
       interpW_sound H).

(*
   * The factorisation through the projection is DEFINITIONAL: both
   sides are the very same interpretation of the very same term. 

   --------
   * 通过投影的分解是定义性的：两边都是对同一术语的完全相同的解释。
*)
Lemma PresentedInterp_proj {m n : nat} (t : Term Σ m n) :
  fmap[PresentedInterp] (fmap[PresentedProj E] t) = fmap[InterpF Σ P v] t.
Proof. reflexivity. Qed.

(*
   * ** 3. The strong and strict monoidal structure

   Same component data as [InterpF]'s in [Universal.v] §3: the tensor
   comparison is the [prop_tensor_plus] cast, packaged as a natural
   isomorphism in the functor category, and every proof field is a
   named target-side lemma of [Universal.v] — the source category
   changed, the target goals did not. 

   --------
   * ** 3. 强且严格的幺半群结构

   与  [InterpF] 中的组件数据相同，如  [Universal.v] §3 所述：张量比较是  [prop_tensor_plus] 的类型转换，在函子范畴中封装为自然同构，并且每个证明字段都是  [Universal.v] 的目标侧命名引理——源类别改变了，目标目标没有改变。
*)

Definition PresentedInterp_ap_dom :
  PresentedCat E ∏ PresentedCat E ⟶ P :=
  @tensor P (MP P) ◯ PresentedInterp ∏⟶ PresentedInterp.

Definition PresentedInterp_ap_cod :
  PresentedCat E ∏ PresentedCat E ⟶ P :=
  PresentedInterp ◯ @tensor (PresentedCat E) (Presented_Monoidal E).

Definition PresentedInterp_ap_to :
  PresentedInterp_ap_dom ⟹ PresentedInterp_ap_cod :=
  @Build_Transform' (PresentedCat E ∏ PresentedCat E) P
    PresentedInterp_ap_dom PresentedInterp_ap_cod
    (fun mn => id_cast (prop_tensor_plus (fst mn) (snd mn)))
    (fun x y f => interp_ap_natural Σ P v (fst f) (snd f)).

Definition PresentedInterp_ap_from :
  PresentedInterp_ap_cod ⟹ PresentedInterp_ap_dom :=
  @Build_Transform' (PresentedCat E ∏ PresentedCat E) P
    PresentedInterp_ap_cod PresentedInterp_ap_dom
    (fun mn => id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn))))
    (fun x y f => interp_ap_natural_from Σ P v (fst f) (snd f)).

(*
   * The two composites are the identity transformation, componentwise
   (in the functor category the identity's component at [mn] is
   [fmap id], which on each side reduces to a tensor of identities);
   proof text as in the donor. 

   --------
   * 这两个复合是逐分量的恒等变换  
   （在函子范畴中，恒等的分量在 [mn] 处是  
   [fmap id]，在每一边都简化为恒等张量）；  
   证明文本与捐赠者中的相同。
*)
Lemma PresentedInterp_ap_to_from (mn : PresentedCat E ∏ PresentedCat E) :
  id_cast (prop_tensor_plus (fst mn) (snd mn))
      ∘ id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
    ≈ interp P Σ v (T_tens (T_id (fst mn)) (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [interp].
  apply tensor_hom_id.
Qed.

Lemma PresentedInterp_ap_from_to (mn : PresentedCat E ∏ PresentedCat E) :
  id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
      ∘ id_cast (prop_tensor_plus (fst mn) (snd mn))
    ≈ (interp P Σ v (T_id (fst mn)) ⨂[MP P] interp P Σ v (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [interp].
  apply bimap_id_id.
Qed.

Program Definition PresentedInterp_ap_iso :
  PresentedInterp_ap_dom
    ≅[[PresentedCat E ∏ PresentedCat E, P]] PresentedInterp_ap_cod := {|
  to := PresentedInterp_ap_to;
  from := PresentedInterp_ap_from;
  iso_to_from := PresentedInterp_ap_to_from;
  iso_from_to := PresentedInterp_ap_from_to
|}.

(*
   * The strong monoidal structure.  All data fields are casts and all
   proof fields are the named lemmas of [Universal.v] §2. 

   --------
   * 强单体结构。所有数据字段都是类型转换，所有证明字段都是 [Universal.v] §2 中的命名引理。
*)
Program Definition PresentedInterp_Monoidal :
  @MonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P)
    PresentedInterp := {|
  pure_iso := id_cast_iso (@prop_unit_zero P);
  ap_functor_iso := PresentedInterp_ap_iso;
  pure_iso_left := fun x : nat => @unit_left P (MP P) ⟦x⟧;
  pure_iso_right := fun x : nat =>
    iso_compose
      (id_cast_iso (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r x))))
      (@unit_right P (MP P) ⟦x⟧);
  ap_iso_assoc := fun x y z : nat =>
    id_cast_iso
      (eq_trans
         (f_equal (fun u : P => (u ⨂[MP P] ⟦z⟧)%object)
                  (prop_tensor_plus x y))
         (eq_trans (prop_tensor_plus (x + y) z)
                   (f_equal (@prop_of_nat P)
                            (eq_sym (Nat.add_assoc x y z)))));
  monoidal_unit_left := interp_monoidal_unit_left Σ P v;
  monoidal_unit_right := interp_monoidal_unit_right Σ P v;
  monoidal_assoc := interp_monoidal_assoc Σ P v
|}.

(*
   * The comparisons ARE the PROP's strictness equalities, verbatim —
   [strict_pure_obj] is [prop_unit_zero] and [strict_ap_obj] is
   [prop_tensor_plus], as the universal property demands.  The two
   reflexivity-grade comparison fields are in-situ Program
   obligations (the [Presented_Strict] discipline of
   [Presentation.v]), which the ambient obligation tactic discharges
   on its own: both comparisons are the transported identities the
   class asks for, definitionally. 

   --------
   * 比较就是道具的严格相等，逐字——
   [strict_pure_obj] 等于 [prop_unit_zero]，[strict_ap_obj] 等于 [prop_tensor_plus]，正如泛性质所要求的。两个自反性等级的比较字段是在原位的程序义务（[Presented_Strict] 的 [Presentation.v] 纪律），环境义务策略会自行处理：这两个比较都是类所要求的传递恒等，定义上如此。
*)
Program Definition PresentedInterp_Strict :
  @StrictMonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P)
    PresentedInterp := {|
  strict_functor_is_monoidal := PresentedInterp_Monoidal;
  strict_pure_obj := @prop_unit_zero P;               (* the PROP field / PROP字段 *)
  strict_ap_obj := fun x y : nat => @prop_tensor_plus P x y      (* ditto *)
|}.

(*
   * ** 4. Symmetry

   The braid-compatibility square of a monoidal functor out of the
   presented category, over its own tensor comparison, with the
   target braiding re-indexed to the strict path by [strict_braid] —
   the presented-source sibling of [Universal.v]'s
   [SymmetricStrict]. 

   --------
   * ** 4. 对称性

   从所给范畴出发的单幺半范畴函子，其编织兼容方形，通过其自身的张量比较，将目标编织按严格路径由 [strict_braid] 重新索引 —— 所给源的 [Universal.v] 的 [SymmetricStrict] 的同源体。
*)

Definition SymmetricStrictW (G : PresentedCat E ⟶ P)
  (MG : @MonoidalFunctor (PresentedCat E) P (Presented_Monoidal E) (MP P) G) :
  Type :=
  ∀ m n : nat,
    fmap[G] (quot E (T_braid m n)) ∘ to (@ap_iso _ _ _ _ G MG m n)
      ≈ to (@ap_iso _ _ _ _ G MG n m) ∘ strict_braid P (G m) (G n).

Lemma PresentedInterp_SymmetricStrict :
  SymmetricStrictW PresentedInterp PresentedInterp_Monoidal.
Proof.
  intros m n.
  exact (interp_braid_ap Σ P v m n).
Qed.

(*
   * ** 5. Factorisation

   The [≈]-level statement of the (definitional) factorisation of
   the interpretation through the projection: [PresentedInterp]
   extends [v]'s interpretation along [PresentedProj E]. 

   --------
   * ** 5. 因式分解

   [≈] 级语句关于通过投影的（定义性）解释的因式分解：[PresentedInterp] 沿 [PresentedProj E] 扩展了 [v] 的解释。
*)

Theorem Presented_factor : ∀ m n (t : Term Σ m n),
  fmap[PresentedInterp] (fmap[PresentedProj E] t) ≈ interp P Σ v t.
Proof.
  intros; reflexivity.
Qed.

(*
   * ** 6. Uniqueness

   Any strict symmetric competitor agreeing with [v] on generators
   agrees with [interp] on every morphism of [PresentedCat E], up to
   the [hom_cast] conjugation along the object family [Hobj].  As on
   the free side, the theorem holds for an ARBITRARY such family —
   axiom-free UIP on [obj P] (the [ObjDecEq] class) makes any two
   proofs of the same object equality interchangeable. 

   --------
   * ** 6. 唯一性

   任何在生成元上与 [v] 一致的严格对称竞争者，
   在 [PresentedCat E] 的每个态射上都与 [interp] 一致，至多经过
   沿对象族 [Hobj] 的 [hom_cast] 共轭。正如在自由侧，该定理适用于任意这样的族——
   对 [obj P]（[ObjDecEq] 类）无公理的 UIP 使得同一对象等式的任意两个证明可以互换。
*)

Section PresentedUniqueness.

Context (G : PresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (PresentedCat E) P
                (Presented_Monoidal E) (MP P) G).
Context (HBW : SymmetricStrictW G SG).
Context (Hobj : ∀ n : nat, G n = ⟦n⟧).
Context (Hgen : ∀ m n (g : Σ m n),
  fmap[G] (quot E (T_gen g))
    ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (v m n g)).

(*
   * The competitor, precomposed with the projection: a functor from
   the FREE category, to which [Universal.v]'s uniqueness applies.
   Its action on objects and morphisms is definitionally [G]'s own,
   because the projection is the identity on both. 

   --------
   * 竞争者，预组合投影：从自由范畴到[Universal.v]唯一性适用的函子。
   其对对象和态射的作用在定义上是[G]自身的作用，
   因为投影在两者上都是恒等的。
*)
Definition PresentedComposite : FreeCat Σ ⟶ P := G ◯ PresentedProj E.

(*
   * The composite is strict monoidal: [Compose_StrictMonoidalFunctor]
   of [SG] after [PresentedProj_Strict].  Because the projection's
   strict object equalities are [eq_refl], the composite's strict
   object data reduce to [SG]'s own ([eq_trans e eq_refl ≡ e]). 

   --------
   * 该复合是严格单模的：[Compose_StrictMonoidalFunctor] 是在 [PresentedProj_Strict] 之后的 [SG]。因为投影的严格对象等式是 [eq_refl]，所以复合的严格对象数据简化为 [SG] 自身的 ([eq_trans e eq_refl ≡ e])。
*)
Definition PresentedComposite_Strict :
  @StrictMonoidalFunctor (FreeCat Σ) P (FreeCat_Monoidal Σ) (MP P)
    PresentedComposite :=
  @Compose_StrictMonoidalFunctor (FreeCat Σ) (PresentedCat E) P
    (FreeCat_Monoidal Σ) (Presented_Monoidal E) (MP P)
    G (PresentedProj E) SG (PresentedProj_Strict E).

(*
   * Machine-checked: the composite's strict object comparisons ARE
   [SG]'s, definitionally.  This is the cast-fusing content of the
   precomposition route. 

   --------
   * 机器检查：复合体的严格对象比较确实是 [SG] 的，从定义上讲。这是预组合路径的投射融合内容。
*)
Example PresentedComposite_ap_obj_is_SG (x y : nat) :
  @strict_ap_obj _ _ _ _ PresentedComposite PresentedComposite_Strict x y
  = @strict_ap_obj _ _ _ _ G SG x y := eq_refl.

Example PresentedComposite_pure_obj_is_SG :
  @strict_pure_obj _ _ _ _ PresentedComposite PresentedComposite_Strict
  = @strict_pure_obj _ _ _ _ G SG := eq_refl.

(*
   * Both tensor comparisons, spelled as the cast along [SG]'s object
   equality (the composite's comparison converts to the same cast,
   by the [Example]s above). 

   --------
   * 两个张量比较，都拼写为沿 [SG] 对象的类型转换相等（复合的比较通过上面的 [Example] 转换为相同的类型转换）。
*)
Lemma PresentedComposite_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ PresentedComposite
        (@strict_functor_is_monoidal _ _ _ _ PresentedComposite
           PresentedComposite_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ PresentedComposite
           PresentedComposite_Strict x y).
Qed.

Lemma Presented_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ G SG x y).
Qed.

(*
   * The composite inherits the braid-compatibility square from [HBW]:
   rewriting all four comparisons to the SAME cast aligns the two
   squares, and the remaining sides agree definitionally. 

   --------
   * 复合继承了来自 [HBW] 的辫兼容性方形：
   将所有四个比较重写为相同的类型可以使两个方形对齐，并且剩余的边在定义上是一致的。
*)
Lemma PresentedComposite_SymmetricStrict :
  SymmetricStrict Σ P PresentedComposite
    (@strict_functor_is_monoidal _ _ _ _ PresentedComposite
       PresentedComposite_Strict).
Proof using E G HBW P SG.
  intros x y.
  rewrite (PresentedComposite_ap_cast x y).
  rewrite (PresentedComposite_ap_cast y x).
  pose proof (HBW x y) as HB.
  rewrite (Presented_ap_cast x y) in HB.
  rewrite (Presented_ap_cast y x) in HB.
  exact HB.
Qed.

(*
   * Main uniqueness.  [interp_unique] pins the composite on every
   term; since the projection is the identity on objects and
   morphisms — every hom of [PresentedCat E] IS a term — the
   conclusion transfers back to [G] definitionally. 

   --------
   * 主要独特性。[interp_unique] 钉住了每个项上的复合；由于投影在对象和态射上是恒等的——[PresentedCat E] 的每个态射都是一个项——结论以定义方式传回到 [G]。
*)
Theorem Presented_unique :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    fmap[G] f ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n))
                         (interp P Σ v f).
Proof using E G HBW Hgen Hobj OD P SG v.
  intros m n f.
  exact (interp_unique Σ P v PresentedComposite PresentedComposite_Strict
           PresentedComposite_SymmetricStrict Hobj Hgen m n f).
Qed.

End PresentedUniqueness.

(*
   * *** Existence, machine-checked against the hypothesis pack

   [PresentedInterp] itself — with its strict structure
   [PresentedInterp_Strict], its braid square
   [PresentedInterp_SymmetricStrict], and the object family
   [Hobj := eq_refl] (its object action is [prop_of_nat] on the
   nose) — satisfies the hypotheses of [Presented_unique]: the
   generator agreement is the definitional action on terms up to
   trivial casts, and instantiating the theorem at [PresentedInterp]
   typechecks.  As in the donor [Construction/PROP/Universal.v], this
   is the named witness that the mediating functor of the existence
   half is itself pinned by the uniqueness half. 

   --------
   * *** 存在性，经机器检查与假设包一致

   [PresentedInterp] 本身 — 具有严格结构
   [PresentedInterp_Strict] 、其编织方块
   [PresentedInterp_SymmetricStrict] 、以及对象族
   [Hobj := eq_refl] （其对象作用是 [prop_of_nat] 在
   鼻子上）— 满足 [Presented_unique] 的假设：生成器一致性是在项上定义的操作，直至平凡类型转换，并且在 [PresentedInterp] 上实例化定理能够类型检查。如同在供体 [Construction/PROP/Universal.v] 中一样，这是存在性半部分的中介函子本身由唯一性半部分固定的命名见证。
*)

Example PresentedInterp_generator_agreement (m n : nat) (g : Σ m n) :
  fmap[PresentedInterp] (quot E (T_gen g))
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (v m n g).
Proof. reflexivity. Qed.

Example PresentedInterp_unique_self (m n : nat)
  (f : m ~{PresentedCat E}~> n) :
  fmap[PresentedInterp] f
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (interp P Σ v f).
Proof.
  exact (Presented_unique PresentedInterp PresentedInterp_Strict
           PresentedInterp_SymmetricStrict (fun k : nat => eq_refl)
           PresentedInterp_generator_agreement m n f).
Qed.

(*
   * *** Uniqueness from a single object datum

   As on the free side, the object family [Hobj] can be synthesised
   from the single equality [G 1 = ⟦1⟧]: zero-arity agreement is
   [strict_pure_obj] against [prop_unit_zero], and successor
   agreement peels one wire off with [strict_ap_obj] against
   [prop_tensor_plus]. 

   --------
   * *** 来自单个对象数据的唯一性

   就像在自由面上一样，对象系列 [Hobj] 可以从单个等式 [G 1 = [G 1 = ⟦1⟧]] 合成：零元同意是 [strict_pure_obj] 与 [prop_unit_zero] 对应，而后继同意使用 [strict_ap_obj] 与 [prop_tensor_plus] 对应剥离一根线路。
*)

Section PresentedUniquenessFromOne.

Context (G : PresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (PresentedCat E) P
                (Presented_Monoidal E) (MP P) G).
Context (HBW : SymmetricStrictW G SG).
Context (H1 : G 1 = ⟦1⟧).

Fixpoint PresentedG_obj (n : nat) : G n = ⟦n⟧ :=
  match n with
  | O => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                  (@prop_unit_zero P)
  | Datatypes.S k =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG 1 k))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MP P] b)%object) H1
                     (PresentedG_obj k))
           (@prop_tensor_plus P 1 k))
  end.

Corollary Presented_unique_from_one
  (Hgen : ∀ m n (g : Σ m n),
     fmap[G] (quot E (T_gen g))
       ≈ hom_cast (eq_sym (PresentedG_obj m)) (eq_sym (PresentedG_obj n))
                  (v m n g)) :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    fmap[G] f ≈ hom_cast (eq_sym (PresentedG_obj m))
                         (eq_sym (PresentedG_obj n))
                         (interp P Σ v f).
Proof using E G H1 HBW OD P SG v.
  exact (Presented_unique G SG HBW PresentedG_obj Hgen).
Qed.

End PresentedUniquenessFromOne.

(*
   * *** Agreement of competitors

   Any two strict symmetric functors out of the presented category
   that agree with [v] on the generators agree with each other on
   every morphism, after re-indexing both to the canonical
   objects. 

   --------
   * *** 竞争者的一致性

   在所展示的范畴中，任意两个严格对称函子，如果它们在生成元上与 [v] 一致，则在重新索引到规范对象后，它们在每一个态射上也相互一致。
*)

Corollary Presented_unique2
  (G1 : PresentedCat E ⟶ P)
  (SG1 : @StrictMonoidalFunctor (PresentedCat E) P (Presented_Monoidal E)
           (MP P) G1)
  (HBW1 : SymmetricStrictW G1 SG1)
  (Hobj1 : ∀ n : nat, G1 n = ⟦n⟧)
  (Hgen1 : ∀ m n (g : Σ m n),
     fmap[G1] (quot E (T_gen g))
       ≈ hom_cast (eq_sym (Hobj1 m)) (eq_sym (Hobj1 n)) (v m n g))
  (G2 : PresentedCat E ⟶ P)
  (SG2 : @StrictMonoidalFunctor (PresentedCat E) P (Presented_Monoidal E)
           (MP P) G2)
  (HBW2 : SymmetricStrictW G2 SG2)
  (Hobj2 : ∀ n : nat, G2 n = ⟦n⟧)
  (Hgen2 : ∀ m n (g : Σ m n),
     fmap[G2] (quot E (T_gen g))
       ≈ hom_cast (eq_sym (Hobj2 m)) (eq_sym (Hobj2 n)) (v m n g)) :
  ∀ m n (f : m ~{PresentedCat E}~> n),
    hom_cast (Hobj1 m) (Hobj1 n) (fmap[G1] f)
      ≈ hom_cast (Hobj2 m) (Hobj2 n) (fmap[G2] f).
Proof using E OD P v.
  intros m n f.
  rewrite (Presented_unique G1 SG1 HBW1 Hobj1 Hgen1 m n f).
  rewrite (Presented_unique G2 SG2 HBW2 Hobj2 Hgen2 m n f).
  now rewrite !hom_cast_roundtrip.
Qed.

(*
   * ** Machine-checked sanity

   Each [Example] pins a definitional behaviour, so any regression in
   the quotient-lifting or shared-record wiring is caught here rather
   than at a distant use site. 

   --------
   * ** 机器检查的合理性

   每个 [Example] 都固定了一种定义行为，因此任何在商提升或共享记录连接中的回归都会在这里被捕捉到，而不是在远处的使用地点。
*)

(** The lifted functor acts as the interpretation on terms. / 提升的函子在项上充当解释。 *)
Example PresentedInterp_fmap_on_terms {m n : nat} (t : Term Σ m n) :
  fmap[PresentedInterp] (quot E t) = interp P Σ v t := eq_refl.

(*
   * The strict object comparisons of [PresentedInterp_Strict] are the
   PROP class fields themselves. 

   --------
   * [PresentedInterp_Strict] 的严格对象比较就是 PROP 类字段本身。
*)
Example PresentedInterp_strict_pure_obj_is_prop_unit_zero :
  @strict_pure_obj _ _ _ _ PresentedInterp PresentedInterp_Strict
  = @prop_unit_zero P := eq_refl.

Example PresentedInterp_strict_ap_obj_is_prop_tensor_plus (x y : nat) :
  @strict_ap_obj _ _ _ _ PresentedInterp PresentedInterp_Strict x y
  = @prop_tensor_plus P x y := eq_refl.

(*
   * Every axiom of the theory holds under the lifted interpretation —
   the end-to-end form of [ESound]. 

   --------
   * 理论的每个公理在提升解释下都成立——[ESound] 的端到端形式。
*)
Example PresentedInterp_respects_axioms {m n : nat} (s t : Term Σ m n)
  (Hax : smt_eqs E m n s t) :
  fmap[PresentedInterp] (quot E s) ≈ fmap[PresentedInterp] (quot E t) :=
  interpW_sound (TEW_ax E s t Hax).

End PresentedUniversal.

Arguments ESound E P v : assert.
Arguments PresentedInterp E P {HP OD} v Hv : assert.
Arguments SymmetricStrictW E P G MG : assert.
