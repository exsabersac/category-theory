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
 wire-datum corollary needs.  The use sites write the qualified
 [@Category.Instance.Fun.Fun] instead — the same discipline as
 [Construction/ColouredPROP/Universal.v]. 

 --------
 [Category.Instance.Fun] 是传递性必需的（它的 [Fun] 类别承载下面的张量比较同构），但故意未导入：它的括号表示法 [C, D] 在语法上与 [ListNotations] 的单元素列表表示法 [c] 不兼容，而后者是线-数据推论所需要的。使用场所改为写限定的 [@Category.Instance.Fun.Fun]——与 [Construction/ColouredPROP/Universal.v] 的做法相同。
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
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.
Require Import Category.Construction.ColouredPROP.Presentation.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * The universal property of a presented coloured PROP / * * 所呈现有色PROP的泛性质 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/generators+and+relations
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Presentation_of_a_monoid

 [Construction/ColouredPROP/Universal.v] packages the interpretation
 of free coloured terms into the strict symmetric monoidal functor
 [CInterpF] and proves it unique: the free coloured PROP is initial
 among coloured PROPs with an [S]-valuation.  This file extends that
 universal property through a PRESENTATION: given a coloured
 symmetric monoidal theory [E : CSMT Colour] and a valuation [v] of
 its generators in a coloured PROP [P] that is SOUND for the axioms
 of [E] ([CESound] — axiom-related terms have equivalent
 interpretations), the interpretation factors through the presented
 coloured PROP of [Construction/ColouredPROP/Presentation.v],
 uniquely among strict symmetric monoidal functors.

 In one sentence: an [E]-sound valuation extends uniquely through
 the presented coloured PROP.  This is the rule-soundness interface
 by which a many-sorted equational theory is installed into a
 semantic target once, and every [CTermEqW]-derivable equation then
 holds there for free.

 This file is the many-sorted mirror of
 [Construction/PROP/Presentation/Universal.v] (the one-sorted
 donor), with [list Colour] replacing [nat], [++] replacing
 [Nat.add], and the boundary equations [app_nil_l] / [app_nil_r] /
 [app_assoc] replacing [Nat.add_0_l] / [Nat.add_0_r] /
 [Nat.add_assoc].  Contents:

 - [cinterpW_sound]: soundness of [cinterp] for the theory
 congruence [CTermEqW E] — a six-constructor induction whose
 [CTEW_termeq] case is [Interp.v]'s whole nineteen-case
 [cinterp_sound_heq], reused; as there, [CTermEqW] is
 [Prop]-valued while the hom equivalence of the abstract target is
 [Type]-valued, so the induction lands in the [Prop]-reflection
 [heq] and round-trips through [heq_intro]/[heq_elim];

 - [CPresentedInterp]: the interpretation functor on
 [CPresentedCat E], obtained by the quotient lifting of
 [Construction/Quotient.v]; it factors [CInterpF] through
 [CPresentedProj E] DEFINITIONALLY ([CPresentedInterp_proj] is a
 Leibniz equality by [eq_refl], and [CPresented_factor] is its
 [≈]-level restatement);

 - the strict symmetric monoidal structure on [CPresentedInterp]:
 the comparison DATA are the same [cprop_unit_nil] /
 [cprop_tensor_app] casts as [CInterpF]'s, and every proof field
 is one of [Universal.v]'s named coherence lemmas
 ([cinterp_ap_natural], [cinterp_monoidal_unit_left] /
 [cinterp_monoidal_unit_right], [cinterp_monoidal_assoc],
 [cinterp_braid_ap]) — their statements are purely target-side,
 which is exactly why they were factored out there;

 - [CPresented_unique]: any strict symmetric competitor
 [G : CPresentedCat E ⟶ P] agreeing with [v] on generators agrees
 with [cinterp] on EVERY morphism of the presented category, up to
 the [hom_cast] conjugation along an object-agreement family
 [Hobj].  Proved by PRECOMPOSITION with the projection: the
 composite [G ◯ CPresentedProj E] is strict monoidal by
 [Compose_StrictMonoidalFunctor], its comparisons collapse onto
 [G]'s own because the projection's comparisons are identities
 with [eq_refl] object equalities, so [Universal.v]'s
 [cinterp_unique] applies to the composite and transfers back
 definitionally — every hom of [CPresentedCat E] IS a term;

 - [CPresented_unique_from_wires]: the object agreement synthesised
 from the single-wire data [∀ c, G [c] = ⟦[c]⟧] by the
 [CPresentedG_obj] fixpoint, exactly as [cinterp_unique_from_wires]
 does on the free side ([strict_pure_obj] against
 [cprop_unit_nil] at the empty word, [strict_ap_obj] against
 [cprop_tensor_app] peeling one typed wire at a time).

 As in [Universal.v], “strict symmetric monoidal functor” is one
 [StrictMonoidalFunctor] over the strict-path monoidals plus the
 braid-compatibility square [CSymmetricStrictW] over that SAME
 tensor comparison, with the target braiding re-indexed to the
 strict path by [cstrict_braid]; see the design note there for why
 the hypothesis pack is phrased against this bundle rather than
 against the two independent functor classes of
 [Functor/Structure/Monoidal/Strict.v] and
 [Functor/Structure/Monoidal/Braided.v]. 

 --------
 nLab：https://ncatlab.org/nlab/show/PROP
 nLab：https://ncatlab.org/nlab/show/generators+and+relations
 维基百科：https://en.wikipedia.org/wiki/PROP_(category_theory)
 维基百科：https://en.wikipedia.org/wiki/Presentation_of_a_monoid

 [Construction/ColouredPROP/Universal.v] 封装了自由着色项的解释
 到严格对称幺范函子 [CInterpF] 并证明其唯一性：自由着色 PROP 是在具有 [S] 估值的着色 PROP 中的初始对象。该文件通过一个表示扩展了该普适性质：给定一个着色的对称幺范理论 [E : CSMT Colour] 和其生成元在一个着色 PROP [P] 中的估值 [v]，且该估值对于 [E] 的公理是 SOUND 的（[CESound] —— 与公理相关的项具有等价的解释），该解释通过 [Construction/ColouredPROP/Presentation.v] 的呈现着色 PROP 因式分解，并在严格对称幺范函子中唯一。一句话总结：一个 [E]-声音赋值通过所呈现的彩色 PROP 独特地扩展。这是规则-合理性接口，通过它，多排序的方程理论被一次性安装到语义目标中，随后每一个 [CTermEqW] 可导出的方程在那里都自动成立。

 该文件是 [Construction/PROP/Presentation/Universal.v]（一排序来源）的多排序镜像，其中 [list Colour] 替换 [nat]，[++] 替换 [Nat.add]，边界方程 [app_nil_l] / [app_nil_r] / [app_assoc] 替换 [Nat.add_0_l] / [Nat.add_0_r] / [Nat.add_assoc]。内容：-  [cinterpW_sound]：[cinterp] 对理论一致性的健全性  
 [CTermEqW E]——一个含六个构造子的归纳，其中  
 [CTEW_termeq] 的情况是重复使用 [Interp.v] 的全部十九个案例  
 [cinterp_sound_heq]；像在那里一样，[CTermEqW] 是 [Prop] 值，而抽象目标的同态等价是  
 [Type] 值，因此归纳落在 [Prop] 反射  
 [heq] 中，并通过 [heq_intro] / [heq_elim] 循环往返；  

 -  [CPresentedInterp]：作用在 [CPresentedCat E] 上的解释函子，由  
 [Construction/Quotient.v] 的商提升得到；它通过定义性将 [CInterpF] 分解到  
 [CPresentedProj E]（[CPresentedInterp_proj] 是 [eq_refl] 证明的赖布尼兹等式，而 [CPresented_factor] 是其 [≈] 层面的重述）；- 在 [CPresentedInterp] 上的严格对称幺半群结构：
 比较数据是同一个 [cprop_unit_nil] / [cprop_tensor_app]，作为 [CInterpF] 的类型，并且每个证明字段都是 [Universal.v] 的一个命名相干性引理（[cinterp_ap_natural]、[cinterp_monoidal_unit_left] / [cinterp_monoidal_unit_right]、[cinterp_monoidal_assoc]、[cinterp_braid_ap]）——它们的陈述完全是目标端的，这正是它们被分离出来的原因；-  [CPresented_unique]：任何严格对称的竞争者  
 [G : CPresentedCat E ⟶ P] 在生成元上与 [v] 一致，也在呈现的范畴的每个态射上与 [cinterp] 一致，直到沿对象一致性族的 [hom_cast] 共轭。  
 通过与投影的前合成证明：复合 [G ◯ CPresentedProj E] 是严格幺半群的，因为 [Compose_StrictMonoidalFunctor]，它的比较会归约到 [G] 自身，因为投影的比较是与 [eq_refl] 对象相等的恒等式，所以 [Universal.v] 的 [cinterp_unique] 适用于复合并且可以定义性地转回——每个 [CPresentedCat E] 的同态都是一个项。- [CPresented_unique_from_wires]：由单线数据 [∀ c, G [c] = ⟦ [c] ⟧ 通过 [CPresentedG_obj] 不动点综合得到的对象一致性，正如 [cinterp_unique_from_wires] 在自由侧（[strict_pure_obj] 对应 [cprop_unit_nil] 在空字上，[strict_ap_obj] 对应 [cprop_tensor_app] 每次剥离一根类型化线路）所做的那样。

 正如在 [Universal.v] 中，“严格对称单体函子”是一个 [StrictMonoidalFunctor]，作用于严格路径单体上，并加上在相同张量比较上的编织兼容性方块 [CSymmetricStrictW]，其中目标编织通过 [cstrict_braid] 重新索引到严格路径；参见那里设计说明，了解为何假设包是针对此捆绑而不是针对 [Functor/Structure/Monoidal/Strict.v] 和 [Functor/Structure/Monoidal/Braided.v] 两个独立的函子类表述的。
*)

Section CPresentedUniversal.

Context {Colour : Type}.
Context (E : CSMT Colour).
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (P : ColouredPROP Colour).
Context {HP : @HomEqProp P}.
Context {OD : @ObjDecEq P}.

Notation Σ := (csmt_sig E).

Context (v : CValuation P Σ).

Notation "⟦ cs ⟧" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧").

(*
   * ** 1. Soundness for the theory congruence

   A valuation is [E]-SOUND when the two sides of every axiom of the
   theory have equivalent interpretations.  This is the semantic
   entry fee of the presentation: the free equations hold in any
   coloured PROP ([cinterp_sound]), and the axioms hold by
   hypothesis. 

   --------
   * ** 1. 理论合取的正确性

   当理论的每条公理的两边具有等价解释时，一个赋值是 [E] -正确的。这是该表示的语义入场券：自由方程在任意着色 PROP ([cinterp_sound]) 中成立，并且假设下公理成立。
*)

Definition CESound : Type :=
  ∀ (cs ds : list Colour) (s t : CTerm Σ cs ds),
    csmt_eqs E cs ds s t → cinterp P Σ v s ≈ cinterp P Σ v t.

Context (HE : CESound).

(*
   * Soundness of [cinterp] for [CTermEqW E], in the [Prop]-reflection.
   Six cases: the embedded free equations are [Interp.v]'s
   [cinterp_sound_heq] wholesale; the axioms are [HE]; symmetry,
   transitivity and the two composition congruences round-trip
   through [heq_intro]/[heq_elim] as in the donor induction. 

   --------
   * [CTermEqW E] 在 [Prop] 反射中的 [cinterp] 的可靠性。  
   六种情况：嵌入的自由方程是 [Interp.v] 的 [cinterp_sound_heq] 整体；公理是 [HE]；对称性、传递性以及两种组合合同通过 [heq_intro] / [heq_elim] 循环，如同在归纳推理中。
*)
Lemma cinterpW_sound_heq {cs ds : list Colour} {s t : CTerm Σ cs ds} :
  CTermEqW E s t → heq (cinterp P Σ v s) (cinterp P Σ v t).
Proof using E HE HP OD P v.
  intros HT.
  induction HT as
    [ cs ds s t Hst
    | cs ds s t Hax
    | cs ds s t Hst IH
    | cs ds s t u Hst IH1 Htu IH2
    | cs ds es f f' g g' Hf IHf Hg IHg
    | cs1 ds1 cs2 ds2 f f' g g' Hf IHf Hg IHg ].
  - (* CTEW_termeq: a free equation / CTEW_termeq：一个免费的方程 *)
    exact (cinterp_sound_heq P Σ v Hst).
  - (* CTEW_ax: an axiom of the theory / CTEW_ax：该理论的公理 *)
    exact (heq_intro (HE _ _ s t Hax)).
  - (* CTEW_sym *)
    apply heq_intro; symmetry; exact (heq_elim IH).
  - (* CTEW_trans / CTEW_翻译 *)
    apply heq_intro.
    rewrite (heq_elim IH1).
    exact (heq_elim IH2).
  - (* CTEW_comp / CTEW_组件 *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
  - (* CTEW_tens / CTEW_十 *)
    apply heq_intro; cbn [cinterp].
    now rewrite (heq_elim IHf), (heq_elim IHg).
Qed.

(** Soundness, in the target's own hom equivalence. / 稳健性，在目标自身的同余等价中。 *)
Theorem cinterpW_sound {cs ds : list Colour} {s t : CTerm Σ cs ds} :
  CTermEqW E s t → cinterp P Σ v s ≈ cinterp P Σ v t.
Proof using E HE HP OD P v.
  intros HT.
  exact (heq_elim (cinterpW_sound_heq HT)).
Qed.

(*
   * ** 2. The interpretation functor on the presented category

   [CInterpF] identifies [CTermEqW]-related morphisms (that is
   [cinterpW_sound]), so it lifts through the quotient by the
   universal property of [Construction/Quotient.v].  The lift acts
   on objects and morphisms exactly as [CInterpF] does. 

   --------
   * ** 2. 在所给范畴上的解释函子

   [CInterpF] 识别 [CTermEqW] 相关的态射（即 [cinterpW_sound]），因此它通过 [Construction/Quotient.v] 的泛性质在商上提升。该提升在对象和态射上的作用与 [CInterpF] 完全相同。
*)

Definition CPresentedInterp : CPresentedCat E ⟶ P :=
  @QuotientLift (CFreeCat Σ)
    (fun cs ds : list Colour => @CTermEqW Colour E cs ds)
    (CTermEqW_Congruence E) P (CInterpF Σ P v)
    (fun (cs ds : list Colour) (s t : CTerm Σ cs ds)
         (H : CTermEqW E s t) => cinterpW_sound H).

(*
   * The factorisation through the projection is DEFINITIONAL: both
   sides are the very same interpretation of the very same term. 

   --------
   * 通过投影的分解是定义性的：两边都是对同一术语的完全相同的解释。
*)
Lemma CPresentedInterp_proj {cs ds : list Colour} (t : CTerm Σ cs ds) :
  fmap[CPresentedInterp] (fmap[CPresentedProj E] t)
  = fmap[CInterpF Σ P v] t.
Proof. reflexivity. Qed.

(*
   * ** 3. The strong and strict monoidal structure

   Same component data as [CInterpF]'s in [Universal.v] §3: the
   tensor comparison is the [cprop_tensor_app] cast, packaged as a
   natural isomorphism in the functor category, and every proof field
   is a named target-side lemma of [Universal.v] — the source
   category changed, the target goals did not. 

   --------
   * ** 3. 强且严格的幺半群结构

   与  [CInterpF] 中  [Universal.v] §3 的组件数据相同：张量比较是  [cprop_tensor_app] 类型转换，作为函子范畴中的自然同构封装，每个证明字段都是  [Universal.v] 的命名目标端引理——源范畴发生了变化，目标命题没有变化。
*)

Definition CPresentedInterp_ap_dom :
  CPresentedCat E ∏ CPresentedCat E ⟶ P :=
  @tensor P (MPc P) ◯ CPresentedInterp ∏⟶ CPresentedInterp.

Definition CPresentedInterp_ap_cod :
  CPresentedCat E ∏ CPresentedCat E ⟶ P :=
  CPresentedInterp ◯ @tensor (CPresentedCat E) (CPresented_Monoidal E Cdec).

Definition CPresentedInterp_ap_to :
  CPresentedInterp_ap_dom ⟹ CPresentedInterp_ap_cod :=
  @Build_Transform' (CPresentedCat E ∏ CPresentedCat E) P
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod
    (fun mn => id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    (fun x y f => cinterp_ap_natural Σ P v (fst f) (snd f)).

Definition CPresentedInterp_ap_from :
  CPresentedInterp_ap_cod ⟹ CPresentedInterp_ap_dom :=
  @Build_Transform' (CPresentedCat E ∏ CPresentedCat E) P
    CPresentedInterp_ap_cod CPresentedInterp_ap_dom
    (fun mn =>
       id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn))))
    (fun x y f => cinterp_ap_natural_from Σ P v (fst f) (snd f)).

(*
   * The two composites are the identity transformation, componentwise
   (in the functor category the identity's component at [mn] is
   [fmap id], which on each side reduces to a tensor of identities);
   proof text as in the free-source donor. 

   --------
   * 这两个复合是按分量的恒等变换
   （在函子范畴中，恒等的分量在  [mn]  上是
   [fmap id] ，在每一边都约化为恒等张量）；
   证明文本如自由源提供者中所示。
*)
Lemma CPresentedInterp_ap_to_from
  (mn : CPresentedCat E ∏ CPresentedCat E) :
  id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
      ∘ id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
    ≈ cinterp P Σ v (CT_tens (CT_id (fst mn)) (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [cinterp].
  apply ctensor_hom_id.
Qed.

Lemma CPresentedInterp_ap_from_to
  (mn : CPresentedCat E ∏ CPresentedCat E) :
  id_cast (eq_sym (@cprop_tensor_app Colour P (fst mn) (snd mn)))
      ∘ id_cast (@cprop_tensor_app Colour P (fst mn) (snd mn))
    ≈ (cinterp P Σ v (CT_id (fst mn))
         ⨂[MPc P] cinterp P Σ v (CT_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [cinterp].
  apply bimap_id_id.
Qed.

(*
 The functor-category isomorphism is an explicit [Build_Isomorphism]
 application, pinning the ambient category to the functor category
 [Fun (CPresentedCat E ∏ CPresentedCat E) P] (a record literal would
 leave it to inference; see the import note at the top for why the
 category is written in qualified form rather than bracket
 notation). 

 --------
 函子范畴同构是一个明确的 [Build_Isomorphism] 应用，将环境范畴固定到函子范畴 [Fun (CPresentedCat E ∏ CPresentedCat E) P]（使用记录字面量会留给推断处理；见顶部的导入说明了解为何该范畴以限定形式而非括号符号表示）。
*)
Definition CPresentedInterp_ap_iso :
  @Isomorphism
    (@Category.Instance.Fun.Fun (CPresentedCat E ∏ CPresentedCat E) P)
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod :=
  @Build_Isomorphism
    (@Category.Instance.Fun.Fun (CPresentedCat E ∏ CPresentedCat E) P)
    CPresentedInterp_ap_dom CPresentedInterp_ap_cod
    CPresentedInterp_ap_to CPresentedInterp_ap_from
    CPresentedInterp_ap_to_from CPresentedInterp_ap_from_to.

(*
   * The strong monoidal structure.  All data fields are casts and all
   proof fields are the named lemmas of [Universal.v] §2. 

   --------
   * 强单体结构。所有数据字段都是类型转换，所有证明字段都是 [Universal.v] §2 中的命名引理。
*)
Definition CPresentedInterp_Monoidal :
  @MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp :=
  @Build_MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp
    (id_cast_iso (@cprop_unit_nil Colour P))
    CPresentedInterp_ap_iso
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
    (fun x : list Colour => cinterp_monoidal_unit_left Σ P v x)
    (fun x : list Colour => cinterp_monoidal_unit_right Σ P v x)
    (fun x y z : list Colour => cinterp_monoidal_assoc Σ P v x y z).

(*
   * The comparisons ARE the coloured PROP's strictness equalities,
   verbatim — [strict_pure_obj] is [cprop_unit_nil] and
   [strict_ap_obj] is [cprop_tensor_app], as the universal property
   demands.  The two reflexivity-grade comparison fields are in-situ
   Program obligations (the [CPresented_Strict] discipline of
   [Presentation.v]): a separately-declared comparison lemma carries
   its own universe instance of the polymorphic [CPresentedCat], and
   the record-field unifier stops at the instance mismatch inside the
   transported-identity [match] before it would reduce both sides;
   proving the field in situ keeps the whole comparison at the
   record's single instance. 

   --------
   * 这些比较是彩色道具严格相等性的对比，逐字——[strict_pure_obj] 等于 [cprop_unit_nil]，[strict_ap_obj] 等于 [cprop_tensor_app]，正如通用性质所要求的。两个反身级比较字段是在原地的程序义务（[CPresented_Strict] 的 [Presentation.v] 纪律）：一个单独声明的比较引理携带它自己的多态 [CPresentedCat] 宇宙实例，而记录字段统一器会在被传输的同一性 [match] 内部的实例不匹配处停止，然后才会简化双方；在原地证明该字段保持整个比较在记录的单一实例上。
*)
Program Definition CPresentedInterp_Strict :
  @StrictMonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
    (MPc P) CPresentedInterp := {|
  strict_functor_is_monoidal := CPresentedInterp_Monoidal;
  strict_pure_obj := @cprop_unit_nil Colour P;         (* the class field / 类字段 *)
  strict_ap_obj := fun x y : list Colour =>
    @cprop_tensor_app Colour P x y                     (* ditto *)
|}.

(*
   * ** 4. Symmetry

   The braid-compatibility square of a monoidal functor out of the
   presented category, over its own tensor comparison, with the
   target braiding re-indexed to the strict path by [cstrict_braid] —
   the presented-source sibling of [Universal.v]'s
   [CSymmetricStrict]. 

   --------
   * ** 4. 对称性

   从所给范畴出发的单幺半范畴函子，其编织兼容方形，通过其自身的张量比较，将目标编织按严格路径由 [cstrict_braid] 重新索引 —— 所给源的 [Universal.v] 的 [CSymmetricStrict] 的同源体。
*)

Definition CSymmetricStrictW (G : CPresentedCat E ⟶ P)
  (MG : @MonoidalFunctor (CPresentedCat E) P (CPresented_Monoidal E Cdec)
          (MPc P) G) : Type :=
  ∀ cs ds : list Colour,
    fmap[G] (cquot E (CT_braid cs ds)) ∘ to (@ap_iso _ _ _ _ G MG cs ds)
      ≈ to (@ap_iso _ _ _ _ G MG ds cs) ∘ cstrict_braid P (G cs) (G ds).

Lemma CPresentedInterp_SymmetricStrict :
  CSymmetricStrictW CPresentedInterp CPresentedInterp_Monoidal.
Proof.
  intros cs ds.
  exact (cinterp_braid_ap Σ P v cs ds).
Qed.

(*
   * ** 5. Factorisation

   The [≈]-level statement of the (definitional) factorisation of
   the interpretation through the projection: [CPresentedInterp]
   extends [v]'s interpretation along [CPresentedProj E]. 

   --------
   * ** 5. 因式分解

   [≈] 级语句关于通过投影的（定义性）解释的因式分解：[CPresentedInterp] 沿 [CPresentedProj E] 扩展了 [v] 的解释。
*)

Theorem CPresented_factor : ∀ cs ds (t : CTerm Σ cs ds),
  fmap[CPresentedInterp] (fmap[CPresentedProj E] t) ≈ cinterp P Σ v t.
Proof.
  intros; reflexivity.
Qed.

(*
   * ** 6. Uniqueness

   Any strict symmetric competitor agreeing with [v] on generators
   agrees with [cinterp] on every morphism of [CPresentedCat E], up
   to the [hom_cast] conjugation along the object family [Hobj].  As
   on the free side, the theorem holds for an ARBITRARY such family —
   axiom-free UIP on [obj P] (the [ObjDecEq] class) makes any two
   proofs of the same object equality interchangeable. 

   --------
   * ** 6. 唯一性

   任何在生成元上与 [v] 一致的严格对称竞争者，
   在 [CPresentedCat E] 的每个态射上都与 [cinterp] 一致，
   至沿着对象族 [Hobj] 的 [hom_cast] 共轭。正如在自由侧，
   该定理对于任意这样的族成立——在 [obj P] 上的无公理 UIP（
   [ObjDecEq] 类）使得同一对象等式的任意两个证明可以互换。
*)

Section CPresentedUniqueness.

Context (G : CPresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (CPresentedCat E) P
                (CPresented_Monoidal E Cdec) (MPc P) G).
Context (HBW : CSymmetricStrictW G SG).
Context (Hobj : ∀ cs : list Colour, G cs = ⟦cs⟧).
Context (Hgen : ∀ cs ds (g : Σ cs ds),
  fmap[G] (cquot E (CT_gen g))
    ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds)) (v cs ds g)).

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
Definition CPresentedComposite : CFreeCat Σ ⟶ P := G ◯ CPresentedProj E.

(*
   * The composite is strict monoidal: [Compose_StrictMonoidalFunctor]
   of [SG] after [CPresentedProj_Strict].  Because the projection's
   strict object equalities are [eq_refl], the composite's strict
   object data reduce to [SG]'s own ([eq_trans e eq_refl ≡ e]). 

   --------
   * 该复合是严格单模的：[Compose_StrictMonoidalFunctor] 是在 [CPresentedProj_Strict] 之后的 [SG]。因为投影的严格对象等式是 [eq_refl]，所以复合的严格对象数据简化为 [SG] 自身的 ([eq_trans e eq_refl ≡ e])。
*)
Definition CPresentedComposite_Strict :
  @StrictMonoidalFunctor (CFreeCat Σ) P (CFreeCat_Monoidal Σ Cdec)
    (MPc P) CPresentedComposite :=
  @Compose_StrictMonoidalFunctor (CFreeCat Σ) (CPresentedCat E) P
    (CFreeCat_Monoidal Σ Cdec) (CPresented_Monoidal E Cdec) (MPc P)
    G (CPresentedProj E) SG (CPresentedProj_Strict E Cdec).

(*
   * Machine-checked: the composite's strict object comparisons ARE
   [SG]'s, definitionally.  This is the cast-fusing content of the
   precomposition route. 

   --------
   * 机器检查：复合体的严格对象比较确实是 [SG] 的，从定义上讲。这是预组合路径的投射融合内容。
*)
Example CPresentedComposite_ap_obj_is_SG (x y : list Colour) :
  @strict_ap_obj _ _ _ _ CPresentedComposite CPresentedComposite_Strict x y
  = @strict_ap_obj _ _ _ _ G SG x y := eq_refl.

Example CPresentedComposite_pure_obj_is_SG :
  @strict_pure_obj _ _ _ _ CPresentedComposite CPresentedComposite_Strict
  = @strict_pure_obj _ _ _ _ G SG := eq_refl.

(*
   * Both tensor comparisons, spelled as the cast along [SG]'s object
   equality (the composite's comparison converts to the same cast,
   by the [Example]s above). 

   --------
   * 两个张量比较，都拼写为沿 [SG] 对象的类型转换相等（复合的比较通过上面的 [Example] 转换为相同的类型转换）。
*)
Lemma CPresentedComposite_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ CPresentedComposite
        (@strict_functor_is_monoidal _ _ _ _ CPresentedComposite
           CPresentedComposite_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof.
  exact (@strict_ap_iso_id _ _ _ _ CPresentedComposite
           CPresentedComposite_Strict x y).
Qed.

Lemma CPresented_ap_cast (x y : list Colour) :
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
Lemma CPresentedComposite_SymmetricStrict :
  CSymmetricStrict Σ Cdec P CPresentedComposite
    (@strict_functor_is_monoidal _ _ _ _ CPresentedComposite
       CPresentedComposite_Strict).
Proof using Cdec E G HBW P SG.
  intros x y.
  rewrite (CPresentedComposite_ap_cast x y).
  rewrite (CPresentedComposite_ap_cast y x).
  pose proof (HBW x y) as HB.
  rewrite (CPresented_ap_cast x y) in HB.
  rewrite (CPresented_ap_cast y x) in HB.
  exact HB.
Qed.

(*
   * Main uniqueness.  [cinterp_unique] pins the composite on every
   term; since the projection is the identity on objects and
   morphisms — every hom of [CPresentedCat E] IS a term — the
   conclusion transfers back to [G] definitionally. 

   --------
   * 主要独特性。[cinterp_unique] 钉住了每个项上的复合；由于投影在对象和态射上是恒等的——[CPresentedCat E] 的每个态射都是一个项——结论以定义方式传回到 [G]。
*)
Theorem CPresented_unique :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    fmap[G] f ≈ hom_cast (eq_sym (Hobj cs)) (eq_sym (Hobj ds))
                         (cinterp P Σ v f).
Proof using Cdec E G HBW Hgen Hobj OD P SG v.
  intros cs ds f.
  exact (cinterp_unique Σ Cdec P v CPresentedComposite
           CPresentedComposite_Strict CPresentedComposite_SymmetricStrict
           Hobj Hgen cs ds f).
Qed.

End CPresentedUniqueness.

(*
   * *** Existence, machine-checked against the hypothesis pack

   [CPresentedInterp] itself — with its strict structure
   [CPresentedInterp_Strict], its braid square
   [CPresentedInterp_SymmetricStrict], and the object family
   [Hobj := eq_refl] (its object action is [cprop_of_list] on the
   nose) — satisfies the hypotheses of [CPresented_unique]: the
   generator agreement is the definitional action on terms up to
   trivial casts, and instantiating the theorem at
   [CPresentedInterp] typechecks.  As in the donor
   [Construction/ColouredPROP/Universal.v], this is the named
   witness that the mediating functor of the existence half is
   itself pinned by the uniqueness half. 

   --------
   * *** 存在性，经过机器检查以符合假设包

   [CPresentedInterp] 本身——具有严格的结构
   [CPresentedInterp_Strict]、其辫子平方
   [CPresentedInterp_SymmetricStrict] 和对象族
   [Hobj := eq_refl]（其对象作用是在
   鼻子上的 [cprop_of_list]）——满足 [CPresented_unique] 的假设：生成器一致性是在项上除了平凡类型转换外的定义性作用，并且在 [CPresentedInterp] 处实例化定理能够类型检查。如同在供体
   [Construction/ColouredPROP/Universal.v] 中，这是命名的见证，存在性部分的中介函子本身由唯一性部分固定。
*)

Example CPresentedInterp_generator_agreement (cs ds : list Colour)
  (g : Σ cs ds) :
  fmap[CPresentedInterp] (cquot E (CT_gen g))
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦cs⟧)) (eq_sym (@eq_refl _ ⟦ds⟧))
               (v cs ds g).
Proof. reflexivity. Qed.

Example CPresentedInterp_unique_self (cs ds : list Colour)
  (f : cs ~{CPresentedCat E}~> ds) :
  fmap[CPresentedInterp] f
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦cs⟧)) (eq_sym (@eq_refl _ ⟦ds⟧))
               (cinterp P Σ v f).
Proof using Cdec E HE HP OD P v.
  exact (CPresented_unique CPresentedInterp CPresentedInterp_Strict
           CPresentedInterp_SymmetricStrict (fun ks : list Colour => eq_refl)
           CPresentedInterp_generator_agreement cs ds f).
Qed.

(*
   * *** Uniqueness from single-wire object data

   As on the free side, the object family [Hobj] can be synthesised
   from the single-wire data [∀ c, G [c] = ⟦[c]⟧]: empty-word
   agreement is [strict_pure_obj] against [cprop_unit_nil], and cons
   agreement peels one typed wire off with [strict_ap_obj] against
   [cprop_tensor_app], using the definitional fact
   [[c] ⨂ cs' = [c] ++ cs' = c :: cs'] on the presented side. 

   --------
   * *** 来自单线对象数据的唯一性

   在自由侧，对象族 [Hobj] 可以从单线数据 [∀ c, G [c] = ⟦ [c] ⟧ 合成：空词
   一致性为 [strict_pure_obj] 对 [cprop_unit_nil]，而 cons 一致性通过 [strict_ap_obj] 对 [cprop_tensor_app] 将一个类型化线剥离，
   使用定义事实 [[c] ⨂ cs' = [c] ++ cs' = c :: cs'] 在展示侧。
*)

Section CPresentedUniquenessFromWires.

Context (G : CPresentedCat E ⟶ P).
Context (SG : @StrictMonoidalFunctor (CPresentedCat E) P
                (CPresented_Monoidal E Cdec) (MPc P) G).
Context (HBW : CSymmetricStrictW G SG).
Context (H1 : ∀ c : Colour, G [c] = ⟦[c]⟧).

Fixpoint CPresentedG_obj (cs : list Colour) : G cs = ⟦cs⟧ :=
  match cs with
  | [] => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                   (@cprop_unit_nil Colour P)
  | c :: cs' =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG [c] cs'))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MPc P] b)%object)
                     (H1 c) (CPresentedG_obj cs'))
           (@cprop_tensor_app Colour P [c] cs'))
  end.

Corollary CPresented_unique_from_wires
  (Hgen : ∀ cs ds (g : Σ cs ds),
     fmap[G] (cquot E (CT_gen g))
       ≈ hom_cast (eq_sym (CPresentedG_obj cs))
                  (eq_sym (CPresentedG_obj ds)) (v cs ds g)) :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    fmap[G] f ≈ hom_cast (eq_sym (CPresentedG_obj cs))
                         (eq_sym (CPresentedG_obj ds))
                         (cinterp P Σ v f).
Proof using Cdec E G H1 HBW OD P SG v.
  exact (CPresented_unique G SG HBW CPresentedG_obj Hgen).
Qed.

End CPresentedUniquenessFromWires.

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

Corollary CPresented_unique2
  (G1 : CPresentedCat E ⟶ P)
  (SG1 : @StrictMonoidalFunctor (CPresentedCat E) P
           (CPresented_Monoidal E Cdec) (MPc P) G1)
  (HBW1 : CSymmetricStrictW G1 SG1)
  (Hobj1 : ∀ cs : list Colour, G1 cs = ⟦cs⟧)
  (Hgen1 : ∀ cs ds (g : Σ cs ds),
     fmap[G1] (cquot E (CT_gen g))
       ≈ hom_cast (eq_sym (Hobj1 cs)) (eq_sym (Hobj1 ds)) (v cs ds g))
  (G2 : CPresentedCat E ⟶ P)
  (SG2 : @StrictMonoidalFunctor (CPresentedCat E) P
           (CPresented_Monoidal E Cdec) (MPc P) G2)
  (HBW2 : CSymmetricStrictW G2 SG2)
  (Hobj2 : ∀ cs : list Colour, G2 cs = ⟦cs⟧)
  (Hgen2 : ∀ cs ds (g : Σ cs ds),
     fmap[G2] (cquot E (CT_gen g))
       ≈ hom_cast (eq_sym (Hobj2 cs)) (eq_sym (Hobj2 ds)) (v cs ds g)) :
  ∀ cs ds (f : cs ~{CPresentedCat E}~> ds),
    hom_cast (Hobj1 cs) (Hobj1 ds) (fmap[G1] f)
      ≈ hom_cast (Hobj2 cs) (Hobj2 ds) (fmap[G2] f).
Proof using Cdec E OD P v.
  intros cs ds f.
  rewrite (CPresented_unique G1 SG1 HBW1 Hobj1 Hgen1 cs ds f).
  rewrite (CPresented_unique G2 SG2 HBW2 Hobj2 Hgen2 cs ds f).
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
Example CPresentedInterp_fmap_on_terms {cs ds : list Colour}
  (t : CTerm Σ cs ds) :
  fmap[CPresentedInterp] (cquot E t) = cinterp P Σ v t := eq_refl.

(*
   * The strict object comparisons of [CPresentedInterp_Strict] are the
   coloured-PROP class fields themselves. 

   --------
   * [CPresentedInterp_Strict] 的严格对象比较是彩色-PROP 类字段本身。
*)
Example CPresentedInterp_strict_pure_obj_is_cprop_unit_nil :
  @strict_pure_obj _ _ _ _ CPresentedInterp CPresentedInterp_Strict
  = @cprop_unit_nil Colour P := eq_refl.

Example CPresentedInterp_strict_ap_obj_is_cprop_tensor_app
  (x y : list Colour) :
  @strict_ap_obj _ _ _ _ CPresentedInterp CPresentedInterp_Strict x y
  = @cprop_tensor_app Colour P x y := eq_refl.

(*
   * Every axiom of the theory holds under the lifted interpretation —
   the end-to-end form of [CESound]. 

   --------
   * 理论的每一个公理在提升的解释下都成立 —— [CESound] 的端到端形式。
*)
Example CPresentedInterp_respects_axioms {cs ds : list Colour}
  (s t : CTerm Σ cs ds) (Hax : csmt_eqs E cs ds s t) :
  fmap[CPresentedInterp] (cquot E s) ≈ fmap[CPresentedInterp] (cquot E t) :=
  cinterpW_sound (CTEW_ax E s t Hax).

End CPresentedUniversal.

Arguments CESound {Colour} E P v : assert.
Arguments CPresentedInterp {Colour} E P {HP OD} v HE : assert.
Arguments CSymmetricStrictW {Colour} E Cdec P G MG : assert.
