Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.

Generalizable All Variables.

(*
nLab: https://ncatlab.org/nlab/show/adjoint+functor
   nLab: https://ncatlab.org/nlab/show/equivalence+of+categories

   Adjunctions transport along equivalences of categories.  Given a
   hom-setoid adjunction F ⊣ U between C and D (Theory/Adjunction.v: the
   left adjoint is F : D ⟶ C, the right adjoint U : C ⟶ D) together with
   equivalences of categories G : C ⟶ C' and K : D ⟶ D'
   (Theory/Equivalence.v), the two conjugated functors

       G ◯ (F ◯ K⁻¹) : D' ⟶ C'      and      (K ◯ U) ◯ G⁻¹ : C' ⟶ D'

   — where G⁻¹ and K⁻¹ are the chosen quasi-inverses — are again adjoint.
   [Transported_Adjunction] below is that adjunction, assembled as the
   three-fold composite (Adjunction/Compose.v) of

       K⁻¹ ⊣ K,   then   F ⊣ U,   then   G ⊣ G⁻¹.

   The two outer constituents are the underlying adjunctions of the
   adjoint equivalences of Theory/Equivalence/Adjoint.v: on the codomain
   side, [equiv_adjunction EC] refines the equivalence carried by G
   directly; on the domain side, the equivalence carried by K is first
   reversed with [EquivalenceOfCategories_sym] (Theory/Equivalence.v) so
   that the quasi-inverse K⁻¹ becomes the left adjoint — this is the same
   pair of constructions that [Equivalence_to_AdjointEquivalence] and
   [AdjointEquivalence_swap] package with their unit/counit isomorphism
   witnesses.

   Alongside the composite adjunction we record its two transposes
   definitionally ([Transported_Adjunction_to]/[_from]: the three-fold
   pasting of the constituent transposes), the standard whiskering
   formulas for its unit and counit in terms of the units and counits of
   the three constituents ([Transported_Adjunction_unit]/[_counit]), and
   the identification of the outer constituents' counits and F-imaged
   units with counit-cell components of the respective equivalences
   ([transported_adj_cod_counit], [transported_adj_dom_counit],
   [transported_adj_cod_fmap_unit], [transported_adj_dom_fmap_unit] —
   all instances of [equiv_adjunction_counit_at] and
   [equiv_adjunction_fmap_unit] from Theory/Equivalence/Adjoint.v).

   Transporting on one side only is the special case in which the other
   equivalence is the identity equivalence [EquivalenceOfCategories_Id]
   (Theory/Equivalence.v), whose quasi-inverse is Id.

   Following Theory/Equivalence.v, nothing in this file is registered for
   instance resolution: the equivalences and the adjunction are data,
   always passed explicitly at use sites.

--------
nLab：https://ncatlab.org/nlab/show/adjoint+functor
nLab：https://ncatlab.org/nlab/show/equivalence+of+categories

伴随可以沿着范畴的等价进行传递。给定一个 C 和 D 之间的同态集伴随 F ⊣ U（Theory/Adjunction.v：左伴随是 F : D ⟶ C，右伴随是 U : C ⟶ D）以及范畴的等价 G : C ⟶ C' 和 K : D ⟶ D'（Theory/Equivalence.v），这两个共轭的函子

G ◯ (F ◯ K⁻¹) : D' ⟶ C'      和      (K ◯ U) ◯ G⁻¹ : C' ⟶ D'

——其中 G⁻¹ 和 K⁻¹ 是选定的准逆——再次是伴随的。下面的 [Transported_Adjunction] 是该伴随，通过三重复合（Adjunction/Compose.v）组装而成的

K⁻¹ ⊣ K，然后 F ⊣ U，然后 G ⊣ G⁻¹。

两个外部成分是 Theory/Equivalence/Adjoint.v 中伴随等价的基本附加结构：在陪域一侧，[equiv_adjunction EC] 直接细化了 G 所携带的等价；在定义域一侧，K 所携带的等价首先通过 [EquivalenceOfCategories_sym]（Theory/Equivalence.v）被反转，使得准逆 K⁻¹ 成为左伴随——这与 [Equivalence_to_AdjointEquivalence] 和 [AdjointEquivalence_swap] 使用它们的单位/余单位同构证明打包的构造成对相同。

除了复合伴随外，我们还记录了它的两个转置在定义上的表示 ([Transported_Adjunction_to]/[_from]：构成转置的三重粘贴)，以及关于单位和余单位的标准胡须公式，这些公式以三个组成部分的单位和余单位表示 ([Transported_Adjunction_unit]/[_counit])，并将外部组成部分的余单位和 F 映射的单位与各自等价的余单位单元分量进行识别 ([transported_adj_cod_counit], [transported_adj_dom_counit], [transported_adj_cod_fmap_unit], [transported_adj_dom_fmap_unit] — 全部来自 Theory/Equivalence/Adjoint.v 中的 [equiv_adjunction_counit_at] 和 [equiv_adjunction_fmap_unit] 实例)。

仅在一侧运输是另一种等价关系为恒等等价 [EquivalenceOfCategories_Id]（Theory/Equivalence.v）的特殊情况，其准逆为 Id。

根据 Theory/Equivalence.v，本文件中没有任何内容被注册用于实例解析：等价和伴随是数据，总是在使用时显式传递。
*)

Section TransportedAdjunction.

Context {C : Category}.
Context {D : Category}.
Context {C' : Category}.
Context {D' : Category}.

(*
The adjunction being transported, in the variable convention of
   Theory/Adjunction.v: F is the left adjoint.

--------
在 Theory/Adjunction.v 的变量约定中，被传递的伴随：F 是左伴随。
*)
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* The equivalence on the codomain side of F ... / F 的值域侧的等价性 ... *)
Context {G : C ⟶ C'}.
Context (EC : @EquivalenceOfCategories C C' G).

(* ... and the equivalence on its domain side. / ... 以及其定义域上的等价关系。 *)
Context {K : D ⟶ D'}.
Context (ED : @EquivalenceOfCategories D D' K).

(*
Section-local shorthands for the two chosen quasi-inverses; the printed
   statements expand them back to [quasi_inverse].

--------
所选两个准逆的段局部简写；打印的语句将它们展开回 [quasi_inverse]。
*)
Local Notation Ginv := (@quasi_inverse C C' G EC).
Local Notation Kinv := (@quasi_inverse D D' K ED).

(*
The domain-side constituent K⁻¹ ⊣ K: the adjoint-equivalence adjunction
   of the reversed equivalence, whose carrying functor is Kinv and whose
   quasi-inverse is K itself.

--------
域侧构件 K⁻¹ ⊣ K：逆等价的伴随等价伴随，其中承载函子是 Kinv，其准逆是 K 本身。
*)
Definition transported_adj_dom : Kinv ⊣ K :=
  equiv_adjunction (@EquivalenceOfCategories_sym D D' K ED).

(*
The codomain-side constituent G ⊣ G⁻¹: the adjoint-equivalence
   adjunction of EC itself.

--------
余域端分量 G ⊣ G⁻¹：EC 自身的伴随等价伴随。
*)
Definition transported_adj_cod : G ⊣ Ginv :=
  equiv_adjunction EC.

(*
The transported adjoints: conjugate each of F and U by the two
   equivalences.

--------
传输的伴随：通过这两个等价对 F 和 U 的每一个进行共轭。
*)
Definition transported_left_adjoint : D' ⟶ C' := G ◯ (F ◯ Kinv).

Definition transported_right_adjoint : C' ⟶ D' := (K ◯ U) ◯ Ginv.

(*
The transported adjunction: paste K⁻¹ ⊣ K, F ⊣ U and G ⊣ G⁻¹ by two
   applications of [Adjunction_Compose].

--------
传输的伴随：通过两次应用 [Adjunction_Compose] 粘贴 K⁻¹ ⊣ K、F ⊣ U 和 G ⊣ G⁻¹。
*)
Definition Transported_Adjunction :
  transported_left_adjoint ⊣ transported_right_adjoint :=
  Adjunction_Compose (Adjunction_Compose transported_adj_dom A)
    transported_adj_cod.

(*
The forward transpose of the composite is the pasting of the three
   constituent forward transposes, definitionally: transpose through the
   codomain equivalence, then through the original adjunction, then
   through the domain equivalence.

--------
复合的前向转置是三个组成前向转置的粘贴，从定义上讲：先通过陪域等价进行转置，然后通过原始伴随进行转置，再通过定义域等价进行转置。
*)
Corollary Transported_Adjunction_to {d : D'} {c : C'}
  (f : G (F (Kinv d)) ~{C'}~> c) :
  to (@adj _ _ _ _ Transported_Adjunction d c) f
    ≈ to (@adj _ _ _ _ transported_adj_dom d (U (Ginv c)))
        (to (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (to (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c) f)).
Proof. reflexivity. Qed.

(* ... and dually for the inverse transpose, in the opposite order. / ……并且对于逆转置也是如此，但顺序相反。 *)
Corollary Transported_Adjunction_from {d : D'} {c : C'}
  (g : d ~{D'}~> K (U (Ginv c))) :
  from (@adj _ _ _ _ Transported_Adjunction d c) g
    ≈ from (@adj _ _ _ _ transported_adj_cod (F (Kinv d)) c)
        (from (@adj _ _ _ _ A (Kinv d) (Ginv c))
           (from (@adj _ _ _ _ transported_adj_dom d (U (Ginv c))) g)).
Proof. reflexivity. Qed.

(*
The unit of the composite: the domain-side unit, followed by the
   K-image of the unit of A, followed by the (K ◯ U)-image of the
   codomain-side unit — [Adjunction_Compose_unit] applied twice.

--------
复合体的单位：先是域侧单位，然后是 A 的单位的 K 映射，再然后是陪域侧单位的 (K ◯ U) 映射——[Adjunction_Compose_unit] 应用两次。
*)
Corollary Transported_Adjunction_unit {d : D'} :
  @unit _ _ _ _ Transported_Adjunction d
    ≈ fmap[K ◯ U] (@unit _ _ _ _ transported_adj_cod (F (Kinv d)))
        ∘ (fmap[K] (@unit _ _ _ _ A (Kinv d))
             ∘ @unit _ _ _ _ transported_adj_dom d).
Proof.
  transitivity
    (fmap[K ◯ U] (@unit _ _ _ _ transported_adj_cod (F (Kinv d)))
       ∘ @unit _ _ _ _ (Adjunction_Compose transported_adj_dom A) d).
  - apply (Adjunction_Compose_unit
             (Adjunction_Compose transported_adj_dom A) transported_adj_cod).
  - apply compose_respects; [reflexivity|].
    apply (Adjunction_Compose_unit transported_adj_dom A).
Qed.

(*
The counit of the composite, dually: the G-image of (the F-image of the
   domain-side counit, followed by the counit of A), followed by the
   codomain-side counit — [Adjunction_Compose_counit] applied twice.

--------
复合的余单位，对偶地：先取（定义域侧余单位的 F-像，再跟随 A 的余单位）的 G-像，然后跟随陪域侧的余单位——[Adjunction_Compose_counit] 应用两次。
*)
Corollary Transported_Adjunction_counit {c : C'} :
  @counit _ _ _ _ Transported_Adjunction c
    ≈ @counit _ _ _ _ transported_adj_cod c
        ∘ fmap[G] (@counit _ _ _ _ A (Ginv c)
                     ∘ fmap[F] (@counit _ _ _ _ transported_adj_dom
                                  (U (Ginv c)))).
Proof.
  transitivity
    (@counit _ _ _ _ transported_adj_cod c
       ∘ fmap[G] (@counit _ _ _ _ (Adjunction_Compose transported_adj_dom A)
                    (Ginv c))).
  - apply (Adjunction_Compose_counit
             (Adjunction_Compose transported_adj_dom A) transported_adj_cod).
  - apply compose_respects; [reflexivity|].
    now rewrite (Adjunction_Compose_counit transported_adj_dom A).
Qed.

(*
The counit of the codomain-side constituent is the counit-cell
   component of EC.

--------
余单位在余域端组成部分是 EC 的余单位单元分量。
*)
Corollary transported_adj_cod_counit (c : C') :
  @counit _ _ _ _ transported_adj_cod c
    ≈ to (@equivalence_counit_at C C' G EC c).
Proof. exact (equiv_adjunction_counit_at EC c). Qed.

(*
The counit of the domain-side constituent is the counit-cell component
   of the reversed equivalence (whose counit cell is the symmetrized unit
   cell of ED).

--------
域侧组成部分的余单元是反等价的余单元-元件（其余单元元件是 ED 的对称化单位元件）。
*)
Corollary transported_adj_dom_counit (d : D) :
  @counit _ _ _ _ transported_adj_dom d
    ≈ to (@equivalence_counit_at D' D Kinv
            (@EquivalenceOfCategories_sym D D' K ED) d).
Proof.
  exact (equiv_adjunction_counit_at (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

(*
The G-image of the codomain-side unit is an inverse counit-cell
   component of EC ...

--------
余域侧单位的 G-像是 EC 的一个逆余单位单元组件...
*)
Corollary transported_adj_cod_fmap_unit (x : C) :
  fmap[G] (@unit _ _ _ _ transported_adj_cod x)
    ≈ from (@equivalence_counit_at C C' G EC (G x)).
Proof. exact (equiv_adjunction_fmap_unit EC x). Qed.

(*
... and the K⁻¹-image of the domain-side unit is an inverse counit-cell
   component of the reversed equivalence.

--------
... 并且该域侧单位的 K⁻¹-像是反转等价的逆余单位单元分量。
*)
Corollary transported_adj_dom_fmap_unit (d : D') :
  fmap[Kinv] (@unit _ _ _ _ transported_adj_dom d)
    ≈ from (@equivalence_counit_at D' D Kinv
              (@EquivalenceOfCategories_sym D D' K ED) (Kinv d)).
Proof.
  exact (equiv_adjunction_fmap_unit (@EquivalenceOfCategories_sym D D' K ED) d).
Qed.

End TransportedAdjunction.
