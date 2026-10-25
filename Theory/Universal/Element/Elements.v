Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Elements.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * A universal element is an initial object of the category of elements / * 一个泛元素是元素范畴的初始对象 *)

(*
nLab: https://ncatlab.org/nlab/show/category+of+elements
   Text: Riehl, "Category Theory in Context", Dover 2016, §2.4,
         Proposition 2.4.8

   Riehl's Proposition 2.4.8 is the sharpest form of the universal-element
   idea: a universal element of H : D ⟶ Sets is precisely an INITIAL OBJECT
   of the category of elements of H.  Both notions are already in the tree --
   [AUniversalElement] (Theory/Universal/Element.v) and [Elements]
   (Construction/Elements.v) -- and this file is the two-line-per-direction
   bridge between them.

   It is kept SEPARATE from Theory/Universal/Element.v for the reason
   Theory/Universal/Arrow/Dual/Examples.v is kept separate from its parent:
   the statement costs a dependency on [Structure/Initial.v] and on
   [Construction/Elements.v]'s category (as opposed to its [SetsOne], which
   the parent already uses), and a consumer wanting only the subsumption
   theorem should not inherit them.

   A DOCUMENTATION ERRATUM, found here and REPAIRED IN THE SAME COMMIT at the
   file that carried it.  Instance/Coq/Nat.v used to say its concrete argument
   presents "the category of elements ... concretely as [FAlg NatF] rather
   than built as a general construction, WHICH THE TREE DOES NOT CARRY".  The
   tree does carry it.  The sentence was true when written (30c01af0,
   5 August 2026) and went stale four days later, when
   [Construction/Elements.v] landed (f2177328, 9 August 2026).  Nat.v now
   carries the correction and its own pointer here; no line citation is given
   for it, since the two files move independently.  What remains true is the narrower
   claim -- Nat.v does not USE the general construction, and the comparison
   [Elements Endos_Forget ≃ FAlg NatF] is not in the tree either.  This file
   supplies the general theorem the comment was reaching for; it does not
   supply that comparison, so Nat.v's [repr_initial] is not re-derived here
   and is not made redundant.

--------
nLab: https://ncatlab.org/nlab/show/category+of+elements
   文本：Riehl，《语境中的范畴论》，Dover 2016，第2.4节，命题2.4.8

Riehl 的命题 2.4.8 是普遍元素概念的最尖锐形式：H : D ⟶ Sets 的一个普遍元素正是 H 的元素范畴的一个初始对象。这两个概念已经存在于树中 —— [AUniversalElement] (Theory/Universal/Element.v) 和 [Elements] (Construction/Elements.v) —— 而这个文件就是它们之间每个方向两行的桥梁。

它被单独保存在 Theory/Universal/Element.v 之外，其原因与 Theory/Universal/Arrow/Dual/Examples.v 与其父级分开保存的原因相同：该语句会导致对 [Structure/Initial.v] 以及 [Construction/Elements.v] 的范畴的依赖（与 [SetsOne] 相反，父级已经使用了 [SetsOne]），而仅希望使用下属定理的使用者不应继承它们。

文档勘误，在此处发现，并在同一提交中修复于携带它的文件中。Instance/Coq/Nat.v 以前说它的具体参数以“[FAlg NatF]”的方式具体呈现“元素的范畴……”而不是构建为一般构造，‘树没有携带’。树确实携带它。该句在编写时成立（30c01af0, 2026年8月5日），但在四天后 [Construction/Elements.v] 出现时（f2177328, 2026年8月9日）过时了。Nat.v 现在包含了修正及其在此处的指针；未给出行号引用，因为两个文件独立移动。仍然成立的是更狭义的说法——Nat.v 并不使用一般构造，而且比较 [Elements Endos_Forget ≃ FAlg NatF] 也不在树中。此文件提供了注释所指向的一般定理；它并未提供该比较，因此 Nat.v 中的 [repr_initial] 并未在此处重新推导，也未被使得冗余。
*)

(*
WHAT IS DELIVERED

   [Elements_Initial], [AUniversalElement_of_Elements_Initial] and
   [UniversalElement_of_Elements_Initial], with the object and element kept
   by [eq_refl] in both directions, and the mediating morphism identified
   with the factorization of [aue_universal] ([Elements_zero_is_med]).

   WHAT IS NOT DELIVERED

   No isomorphism of setoids between [AUniversalElement H r] and the
   initial-object structures: [Initial] carries a chosen [one] field, so two
   [Initial (Elements H)] values at the same object need not be equal and
   there is no in-tree setoid on them to state such an iso against.  The
   round trips below are therefore recorded on the DATA (object, element),
   which is what the two directions actually preserve.

--------
交付的内容

[Elements_Initial]、[AUniversalElement_of_Elements_Initial] 和 [UniversalElement_of_Elements_Initial]，[eq_refl] 在双向中保持对象和元素，并且中介态射与 [aue_universal]（[Elements_zero_is_med]）的分解相对应。

未交付的内容

在 [AUniversalElement H r] 与初始对象结构之间没有集合等价异构：[Initial] 承载一个选定的 [one] 字段，因此同一对象上的两个 [Initial (Elements H)] 值不必相等，并且在它们上没有树内集合等价可以声明这样的异构。因此，下面的往返记录在 DATA（对象，元素）上，这就是两个方向实际保持的内容。
*)

Section ElementsInitial.

Context {D : Category}.
Context (H : D ⟶ Sets).

(*
Forward.  The object (r, e) is initial: the unique arrow to (d, x) is the
   unique k with (H k) e ≈ x, and the [Elements] hom-setoid compares only
   the underlying D-morphism, so uniqueness there IS [uniqueness].

--------
前进。对象 (r, e) 是初始的：到 (d, x) 的唯一箭头是唯一的 k，使得 (H k) e ≈ x，并且 [Elements] 同态集合只比较底层的 D-态射，因此在此处的唯一性确实是 [uniqueness]。
*)
(*
Built with [unshelve refine] rather than [Program] so that the names in
   the uniqueness obligation are this file's and not the elaborator's.

--------
使用 [unshelve refine] 而不是 [Program] 构建，以便唯一性义务中的名称属于此文件，而不是定义者的。
*)
Definition Elements_Initial {r : D} (U : AUniversalElement H r)
  : @Initial (Elements H).
Proof.
  unshelve eapply (@Build_Terminal ((Elements H)^op)).
  - exact ((r; @aue_elem D H r U) : Elements H).
  - intros [d elt].
    exists (unique_obj (aue_universal d elt)).
    exact (unique_property (aue_universal d elt)).
  - intros [d elt] [f Hf] [g Hg]; simpl in *.
    transitivity (unique_obj (aue_universal d elt)).
    + symmetry; exact (uniqueness (aue_universal d elt) f Hf).
    + exact (uniqueness (aue_universal d elt) g Hg).
Defined.

(* The mediating arrow IS the factorization, by conversion. / 中介箭头是通过转换实现的分解。 *)
Lemma Elements_zero_is_med {r : D} (U : AUniversalElement H r) (d : D) (x : H d) :
  `1 (@zero (Elements H) (Elements_Initial U) ((d; x) : Elements H))
    = unique_obj (aue_universal d x).
Proof. reflexivity. Qed.

(*
Backward.  The initial object's two projections are the universal object
   and the universal element; its [zero] is the factorization and
   [zero_unique] its uniqueness.  The only step with content is that the
   carried condition [`2 (zero ...)] is exactly the required equation.

--------
向后。初始对象的两个射影是通用对象和通用元素；它的 [zero] 是分解，[zero_unique] 是其唯一性。唯一有内容的步骤是所携带的条件 [`2 (zero ...)] 恰好是所需的方程。
*)
Definition AUniversalElement_of_Elements_Initial (I : @Initial (Elements H))
  : AUniversalElement H (`1 (@initial_obj (Elements H) I)).
Proof.
  unshelve econstructor.
  - exact (`2 (@initial_obj (Elements H) I)).
  - intros d x.
    unshelve eexists (`1 (@zero (Elements H) I ((d; x) : Elements H))).
    + exact (`2 (@zero (Elements H) I ((d; x) : Elements H))).
    + intros v Hv.
      exact (@zero_unique (Elements H) I ((d; x) : Elements H)
               (@zero (Elements H) I ((d; x) : Elements H)) (v; Hv)).
Defined.

Definition UniversalElement_of_Elements_Initial (I : @Initial (Elements H))
  : UniversalElement H :=
  UniversalElement_of_AUniversalElement
    (AUniversalElement_of_Elements_Initial I).

(* Both directions keep the data on the nose. / 两个方向都保持数据准确无误。 *)
Corollary Elements_Initial_obj {r : D} (U : AUniversalElement H r) :
  `1 (@initial_obj (Elements H) (Elements_Initial U)) = r.
Proof. reflexivity. Qed.

Corollary Elements_Initial_elem {r : D} (U : AUniversalElement H r) :
  `2 (@initial_obj (Elements H) (Elements_Initial U)) = @aue_elem D H r U.
Proof. reflexivity. Qed.

Corollary aue_of_Elements_Initial_elem (I : @Initial (Elements H)) :
  @aue_elem D H _ (AUniversalElement_of_Elements_Initial I)
    = `2 (@initial_obj (Elements H) I).
Proof. reflexivity. Qed.

(* ... and the element-side round trip closes by [eq_refl]. / ... 并且元素端的往返由 [eq_refl] 关闭。 *)
Corollary Elements_Initial_round {r : D} (U : AUniversalElement H r) :
  @aue_elem D H _
    (AUniversalElement_of_Elements_Initial (Elements_Initial U))
    = @aue_elem D H r U.
Proof. reflexivity. Qed.

End ElementsInitial.
