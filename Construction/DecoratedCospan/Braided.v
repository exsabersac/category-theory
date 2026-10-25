Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.Monoidal.

Generalizable All Variables.

(*
   * * Braided and Symmetric Monoidal structure on [DecoratedCospanCat] 

   --------
   * * 在 [DecoratedCospanCat] 上的编织和对称幺半群结构
*)

(*
 nLab: https://ncatlab.org/nlab/show/braided+monoidal+category
 nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category
 Wikipedia: https://en.wikipedia.org/wiki/Symmetric_monoidal_category

 The braiding on [DC] is the decorated lift [dec_mor_as_cospan paws] of the
 C-coproduct swap [paws], carrying the canonical [id_decoration] on the apex.
 It satisfies naturality and the two hexagon identities ([hexagon_identity],
 [hexagon_identity_sym]) of a braided monoidal category, and is involutive
 ([braid ∘ braid ≈ id]) for the symmetric structure; the concept definitions
 live in Structure/Monoidal/Braided.v and Structure/Monoidal/Symmetric.v. 

 --------
 nLab:  https://ncatlab.org/nlab/show/braided+monoidal+category 
 nLab:  https://ncatlab.org/nlab/show/symmetric+monoidal+category 
 维基百科:  https://en.wikipedia.org/wiki/Braided_monoidal_category 
 维基百科:  https://en.wikipedia.org/wiki/Symmetric_monoidal_category 

 在 [DC] 上的编织是 C-余积交换 [paws] 的装饰升 [dec_mor_as_cospan paws] ，在顶点携带规范的 [id_decoration] 。
 它满足自然性和编织单体范畴的两个六边形恒等式（[hexagon_identity]、[hexagon_identity_sym]），并且对于对称结构是自反的（[braid ∘ braid ≈ id]）；概念定义存在于 Structure/Monoidal/Braided.v 和 Structure/Monoidal/Symmetric.v。
*)

(*
    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,
    Theorem 3.5 (the symmetric-monoidal / hypergraph structure; in the
    arXiv numbering 3.1 is the Definition, 3.2 the Proposition, 3.4 a
    Remark, and 3.5 the Theorem).  This module assembles the [BraidedMonoidal] and
    [SymmetricMonoidal] instances on [DecoratedCospanCat] by layering
    decoration coherences on top of [Cospan_BraidedMonoidal] /
    [Cospan_SymmetricMonoidal] from [Construction/Cospan/Symmetric.v].

    ** Architecture

    [DecCospan_Braided_Coherent]      (braid naturality + hexagon)
    [DecCospan_Symmetric_Coherent]    (braid involution)

    Each coherence field states a [dec_cospan_equiv] between the
    decorated-cospan LHS and RHS of the matching Braided/Symmetric
    obligation, with the braiding built as [dec_mor_as_cospan paws]
    (the [paws] swap from [C]'s [Cocartesian] structure lifted to a
    decorated cospan via the canonical [id_decoration]).

    The cospan-level part is already proved in
    [Cospan_BraidedMonoidal] / [Cospan_SymmetricMonoidal]; the
    decoration-level part is the genuine content of the field, and
    typically requires [F] to be a SYMMETRIC lax monoidal functor
    (i.e. [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D]).  Concrete
    decoration instances supply explicit proofs from their chosen [F]. 

    --------
    参考文献：Brendan Fong，“Decorated Cospans”，arXiv:1502.00872，定理 3.5（对称单体/超图结构；在 arXiv 编号中，3.1 是定义，3.2 是命题，3.4 是备注，3.5 是定理）。本模块通过在 [Cospan_BraidedMonoidal] / [Cospan_SymmetricMonoidal] 从 [Construction/Cospan/Symmetric.v] 之上叠加装饰一致性，将 [BraidedMonoidal] 和 [SymmetricMonoidal] 实例组装到 [DecoratedCospanCat] 上。  

    ** 架构

    [DecCospan_Braided_Coherent]       （编织自然性 + 六边形）
    [DecCospan_Symmetric_Coherent]     （编织自反性）

    每个一致性字段陈述了 [dec_cospan_equiv]  在匹配的编织/对称约束的装饰 cospan 左侧和右侧之间，其中编织作为 [dec_mor_as_cospan paws] 构建（[C] 的 [Cocartesian] 结构中的 [paws] 交换，通过规范 [id_decoration] 提升到装饰 cospan）。cospan 级部分已经在 [Cospan_BraidedMonoidal] / [Cospan_SymmetricMonoidal] 中证明；装饰级部分是该领域的真正内容，通常需要 [F] 是一个对称 lax 幺半群函子（即 [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D]）。具体的装饰实例提供了来自它们所选 [F] 的明确证明。
*)

Section DecoratedCospanBraided.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCMC : @DecCospan_Monoidal_Coherent C HP H_Coc H_Ini MC D MD F LM
                                               id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).
Notation Dtensor f g := (dec_cospan_tensor LM cospan_merge f g).
Notation Dcompose g f := (dec_cospan_compose HP LM cospan_merge g f).
Notation Did X := (dec_cospan_id id_decoration X).
Notation Dlift f := (dec_mor_as_cospan id_decoration f).

(*
   * ** Coherence class for the Braided structure on [DecoratedCospanCat]

   The braiding on [DC] is [dec_mor_as_cospan paws]: the decorated lift
   of the C-coproduct swap, with the canonical [id_decoration] on the
   apex.  The Braided-class obligations are:

   - [braid_natural]   : the naturality square for [braid] is a
   decorated-cospan equivalence;
   - [hexagon_identity], [hexagon_identity_sym] : the hexagon
   coherence relating [braid] with
   [tensor_assoc], in both forms.

   Each field below pairs the LHS and RHS of the corresponding
   obligation directly. 

   --------
   * ** [DecoratedCospanCat] 上编织结构的相干性类

   [DC] 上的编织是 [dec_mor_as_cospan paws]：C-余积交换的装饰提升，并在顶点上带有标准的 [id_decoration]。Braided 类的义务如下：

   - [braid_natural] ： [braid] 的自然性方形是一个装饰共尾对等式；
   - [hexagon_identity], [hexagon_identity_sym] ：六边形相干性将 [braid] 与 [tensor_assoc] 联系起来，包含两种形式。

   以下每个字段直接配对相应义务的左侧和右侧。
*)

Class DecCospan_Braided_Coherent : Type := {

  (*
   * Naturality of [braid] : as a decorated-cospan equation.
   Goal shape (matching [@braid_natural]):
   [bimap h f ∘ braid_{x,z} ≈ braid_{y,w} ∘ bimap f h]
   where the bimap is [dec_cospan_tensor] and braid is
   [Dlift paws]. 

   --------
   * [braid]的自然性：作为一个装饰余积方程。
   目标形状（匹配[@braid_natural]）：
   [bimap h f ∘ braid_{x,z} ≈ braid_{y,w} ∘ bimap f h]
   其中双映射是[dec_cospan_tensor]，络线是[Dlift paws]。
*)
  dec_braid_natural_eq :
    forall {x y z w : C}
           (f : DecoratedCospanArrow x y)
           (h : DecoratedCospanArrow z w),
      dec_cospan_equiv
        (Dcompose (Dtensor h f) (Dlift (@paws C H_Coc x z)))
        (Dcompose (Dlift (@paws C H_Coc y w)) (Dtensor f h));

  (*
   * Hexagon identity (to form).  LHS and RHS are both
   RIGHT-associated.  The corresponding [Monoidal] obligation is
   left-associated; the proof reassociates via
   [dec_cospan_compose_assoc] before applying this field. 

   --------
   * 六边形恒等式（用于形成）。左右两边都是右结合的。相应的 [Monoidal] 义务是左结合的；证明在应用此字段之前通过 [dec_cospan_compose_assoc] 重新结合。
*)
  dec_hexagon_identity_eq :
    forall {x y z : C},
      dec_cospan_equiv
        (Dcompose
           (Dlift (to (@coprod_assoc C H_Coc y z x)))
           (Dcompose
              (Dlift (@paws C H_Coc x (y + z)%object))
              (Dlift (to (@coprod_assoc C H_Coc x y z)))))
        (Dcompose
           (Dtensor (Did y) (Dlift (@paws C H_Coc x z)))
           (Dcompose
              (Dlift (to (@coprod_assoc C H_Coc y x z)))
              (Dtensor (Dlift (@paws C H_Coc x y)) (Did z))));

  (** Hexagon identity (from form), RIGHT-associated. / 六边形恒等式（来自形式），右结合。 *)
  dec_hexagon_identity_sym_eq :
    forall {x y z : C},
      dec_cospan_equiv
        (Dcompose
           (Dlift (from (@coprod_assoc C H_Coc z x y)))
           (Dcompose
              (Dlift (@paws C H_Coc (x + y)%object z))
              (Dlift (from (@coprod_assoc C H_Coc x y z)))))
        (Dcompose
           (Dtensor (Dlift (@paws C H_Coc x z)) (Did y))
           (Dcompose
              (Dlift (from (@coprod_assoc C H_Coc x z y)))
              (Dtensor (Did x) (Dlift (@paws C H_Coc y z)))))
}.

Context `{DCBrC : DecCospan_Braided_Coherent}.

Set Default Proof Using "All".

(*
   * ** [DecoratedCospan_BraidedMonoidal] : the BraidedMonoidal instance 

   --------
   * ** [DecoratedCospan_BraidedMonoidal] ：BraidedMonoidal 实例
*)

Program Definition DecoratedCospan_BraidedMonoidal
  : @BraidedMonoidal DC := {|
  braided_is_monoidal := DecoratedCospan_Monoidal HP LM id_decoration cospan_merge;
  braid := fun X Y => Dlift (@paws C H_Coc X Y)
|}.
Next Obligation.
  (*
 braid_natural: arity-2 naturality.
 The Coq-level shape (after Bifunctor unfolds to [dec_cospan_tensor]):
 Dcompose (Dcompose (Dtensor h f) (Dlift paws)) ?
 We use the same pattern as in [Cospan_BraidedMonoidal] —
 re-associate the outer compose, fuse via tensor_compose_compat
 and tensor_respects, then apply the coherence field. 

 --------
 braid_natural：二元自然性。
 Coq级别的形状（在 Bifunctor 展开为 [dec_cospan_tensor] 后）：
 Dcompose (Dcompose (Dtensor h f) (Dlift paws)) ?
 我们使用与 [Cospan_BraidedMonoidal] 中相同的模式——
 重新关联外层的 compose，通过 tensor_compose_compat 和 tensor_respects 融合，然后应用一致性字段。
*)
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl.
    - apply dec_cospan_equiv_sym.
      apply (dec_cospan_tensor_compose_compat HP LM id_decoration cospan_merge
                h (Did _) (Did _) g). }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl.
    - apply (dec_cospan_tensor_respects HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_right HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_left HP LM id_decoration cospan_merge). }
  apply dec_cospan_equiv_sym.
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_sym.
      apply (dec_cospan_tensor_compose_compat HP LM id_decoration cospan_merge
               (Did _) g h (Did _)).
    - apply dec_cospan_equiv_refl. }
  eapply dec_cospan_equiv_trans.
  { apply (dec_cospan_compose_respects_aux HP LM id_decoration cospan_merge).
    - apply (dec_cospan_tensor_respects HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_left HP LM id_decoration cospan_merge).
      + apply (dec_cospan_id_right HP LM id_decoration cospan_merge).
    - apply dec_cospan_equiv_refl. }
  apply dec_cospan_equiv_sym.
  apply dec_braid_natural_eq.
Qed.
Next Obligation.
  (*
 Hexagon LHS and RHS are both left-associated in the Monoidal goal;
 the [dec_hexagon_identity_eq] coherence is right-associated.
 Reassociate both sides via [dec_cospan_compose_assoc_sym]. 

 --------
 六边形的左边和右边在单体目标中都是左结合的；[dec_hexagon_identity_eq] 一致性是右结合的。通过 [dec_cospan_compose_assoc_sym] 对双方重新结合。
*)
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply dec_hexagon_identity_eq. }
  apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
Qed.
Next Obligation.
  eapply dec_cospan_equiv_trans.
  { apply dec_cospan_equiv_sym.
    apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge). }
  eapply dec_cospan_equiv_trans.
  { apply dec_hexagon_identity_sym_eq. }
  apply (dec_cospan_compose_assoc HP LM id_decoration cospan_merge).
Qed.

(*
   * ** Coherence class for the Symmetric structure on [DecoratedCospanCat]

   A single field: [braid ∘ braid ≈ id] on the decorated side.
   Cospan-level: [cospan_braid_invol_C] (from [Cospan_SymmetricMonoidal]). 

   --------
   * ** 对称结构在 [DecoratedCospanCat] 上的连贯性类

   单一场：在装饰侧的 [braid ∘ braid ≈ id]。
   共跨水平：[cospan_braid_invol_C]（来自 [Cospan_SymmetricMonoidal]）。
*)

Class DecCospan_Symmetric_Coherent : Type := {
  dec_braid_invol_eq :
    forall {x y : C},
      dec_cospan_equiv
        (Dcompose (Dlift (@paws C H_Coc x y))
                  (Dlift (@paws C H_Coc y x)))
        (Did (y + x)%object)
}.

Context `{DCSC : DecCospan_Symmetric_Coherent}.

(*
   * ** [DecoratedCospan_SymmetricMonoidal] : the SymmetricMonoidal instance 

   --------
   * ** [DecoratedCospan_SymmetricMonoidal] ：对称单体实例
*)

Program Definition DecoratedCospan_SymmetricMonoidal
  : @SymmetricMonoidal DC := {|
  symmetric_is_braided := DecoratedCospan_BraidedMonoidal
|}.
Next Obligation.
  apply dec_braid_invol_eq.
Qed.

End DecoratedCospanBraided.

(*
   * ** Discussion: when [F] must be symmetric

   The [DecCospan_Braided_Coherent] field [dec_braid_natural_eq]
   requires the decoration on the LHS — built by tensoring decorations
   via [lax_ap] then composing with the cospan-side [braid] — to agree
   with the decoration on the RHS.  In Fong's [F = Set] case (where
   decorations are global elements of [F N]) this is automatic; in the
   general monoidal-codomain case it requires [F] to be a SYMMETRIC
   lax monoidal functor, i.e. [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D].

   [DecCospan_Symmetric_Coherent]'s single field
   [dec_braid_invol_eq] follows on the cospan side from
   [paws_invol] (proved generically in [Cospan_SymmetricMonoidal]);
   its decoration side is the [id_decoration]-coherence on the
   identity cospan, i.e., the composite of two identity-style
   decorations through [paws ∘ paws ≈ id] collapses back to
   [id_decoration].

   Both coherence classes are populated trivially when [F = Δ I_D]
   (the constant lax-monoidal functor), in which case all decorations
   are [id : I_D ~> I_D] and every coherence reduces to refl. 

   --------
   * ** 讨论：何时 [F] 必须是对称的

   [DecCospan_Braided_Coherent] 字段 [dec_braid_natural_eq] 
   要求左侧的装饰——通过 [lax_ap] 张量装饰然后与余箭侧 [braid] 组合而成——与右侧的装饰一致。在 Fong 的 [F = Set] 情况下（装饰是 [F N] 的全局元素）这是自动的；在一般的单体余域情况下，则需要 [F] 是一个对称松单体函子，即 [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D] 。

   [DecCospan_Symmetric_Coherent] 的单一字段 
   [dec_braid_invol_eq] 从余箭侧的 [paws_invol] 推出（在 [Cospan_SymmetricMonoidal] 中一般性证明）；其装饰侧是 [id_decoration] 在单位余箭上的相容性，即通过 [paws ∘ paws ≈ id] 的两个单位类装饰的复合会折叠回 [id_decoration]。当 [F = Δ I_D]（常数松单范式函子）时，两个相干类都被平凡地填充，在这种情况下，所有修饰都是 [id : I_D ~> I_D]，并且每个相干性都化简为 refl。
*)
