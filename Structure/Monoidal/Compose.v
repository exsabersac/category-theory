Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Fun.

Generalizable All Variables.

#[local] Obligation Tactic := intros; simplify; simpl in *; intros; normal.

(*
 nLab: https://ncatlab.org/nlab/show/endofunctor
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 The endofunctor category [C, C] is monoidal, with functor composition ◯ as
 the tensor product and the identity functor Id as the unit object:

 F ⨂ G := F ◯ G            (tensor on objects, [tensor.fobj]),
 I     := Id               (unit object).

 On morphisms the tensor is the horizontal (Godement) composite of natural
 transformations: for N = (fst N, snd N) with fst N : fst F ⟹ fst G and
 snd N : snd F ⟹ snd G, the component at x is

 (fst N) (snd G x) ∘ fmap[fst F] (snd N x)   ([tensor.fmap]),

 the standard interchange formula α(G' x) ∘ F(β x).

 This reflects the fact that categories are themselves “monoidoids”, or
 monoidal with respect to identity and composition; it is also the structure
 behind “a monad is a monoid in the category of endofunctors”.

 In the literature this monoidal structure is strict: the associator and the
 two unitors are identity natural transformations, since F ◯ (G ◯ H) and
 (F ◯ G) ◯ H, and Id ◯ F and F ◯ Id, are equal on the nose. Here it is
 nonetheless presented as a general (non-strict) Monoidal instance whose
 unitors and associator are component-wise identity isomorphisms, which is
 why the associator/unitor and coherence obligations still appear below. 

 --------
 nLab: https://ncatlab.org/nlab/show/endofunctor
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 自函子范畴 [C, C] 是单幺半的，其中函子合成 ◯ 作为张量积，单位函子 Id 作为单位对象：

 F ⨂ G := F ◯ G         （对象上的张量，[tensor.fobj]），
 I     := Id              （单位对象）。

 在态射上，张量是自然变换的水平（Godement）复合：对于 N = (fst N, snd N) 且 fst N : fst F ⟹ fst G，snd N : snd F ⟹ snd G，x 上的分量为

 (fst N) (snd G x) ∘ fmap [fst F]  (snd N x)   （[tensor.fmap]），

 这是标准的交换公式 α(G' x) ∘ F(β x)。

 这反映了范畴本身是“单幺半态”，或关于单位和合成是单幺半的；它也是“一个单子是在自函子范畴中的一个幺半”的结构基础。在文献中，这种幺半群结构是严格的：结合子和两个单位子是恒等自然变换，因为 F ◯ (G ◯ H) 和 (F ◯ G) ◯ H，以及 Id ◯ F 和 F ◯ Id，在定义上是相等的。然而这里仍然将其表示为一般的（非严格的）幺半群实例，其单位子和结合子在各个分量上是恒等同构，这就是为什么下面仍然会出现结合子/单位子和一致性义务的原因。
*)

Program Definition Compose_Monoidal {C : Category} :
  @Monoidal ([C, C]) := {|
  tensor :=
    {| fobj := fun p => fst p ◯ snd p
     ; fmap := fun F G N =>
         {| transform := fun x =>
              fst N (snd G x) ∘ fmap[fst F] (snd N x) |}
     |};
  I := Id
|}.
Next Obligation.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (naturality[snd N]).
  rewrite fmap_comp.
  comp_left.
  apply naturality.
Qed.
Next Obligation.
  rewrite naturality.
  rewrite <- !comp_assoc.
  comp_left.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  apply naturality_sym.
Qed.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. rewrite !fmap_id; cat. Qed.
Next Obligation.
  rewrite <- !comp_assoc.
  apply compose_respects.
  - reflexivity.
  - rewrite <- !naturality.
    rewrite fmap_comp.
    rewrite comp_assoc.
    reflexivity.
Qed.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation.
  isomorphism; simpl.
  - transform; simpl; cat.
  - transform; simpl; cat.
  - simpl; cat.
  - simpl; cat.
Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation.
  rewrite !fmap_id.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  rewrite !fmap_id.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  normal; reflexivity.
Qed.
Next Obligation.
  normal; rewrite !fmap_id; reflexivity.
Qed.
