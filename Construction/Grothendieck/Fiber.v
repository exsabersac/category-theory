Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.

Generalizable All Variables.

(*
   * * Fibre categories, and the fibres of the Grothendieck construction 

   --------
   * * 纤维类别，以及格罗滕迪克构造的纤维
*)

(*
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
 nLab:      https://ncatlab.org/nlab/show/displayed+category
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
 Wikipedia: https://en.wikipedia.org/wiki/Fibred_category

 The fibre of a displayed category [D] over a base object [x] is the
 category [Fiber D x] whose objects are the objects displayed over [x]
 and whose morphisms are the displayed morphisms lying over [id[x]].
 The identity is the displayed identity.  The displayed composite of
 two morphisms over [id] lies over [id ∘ id], so composition recentres
 it over [id] by transporting along the base unit law [id_left id]; by
 proof irrelevance of [dtransport] ([dtransport_id] and its
 consequences in Theory/Displayed.v) the choice of base law is
 immaterial, and each category law of the fibre closes with one lemma
 of the derived transport pack.

 The second half of the file is the committed half of the Grothendieck
 round trip: for an indexed category [A : IndexedCat B]
 (Construction/Indexed.v) and [x : B], the fibre at [x] of the
 Grothendieck construction of [A] (Construction/Grothendieck.v) is
 equivalent to the fibre [A] indexes at [x]:

 Fiber (Grothendieck_Displayed A) x  ≃  idx_fib A x

 The equivalence is near-isomorphic.  On objects both functors are the
 identity: an object of the Grothendieck fibre at [x] is literally an
 object of [idx_fib A x].  Only the homs differ: a Grothendieck-fibre
 morphism from [a] to [b] is a fibre morphism [idx_map A id a ~> b]
 (reindex along [id], then compare in the fibre), while a plain fibre
 morphism goes [a ~> b]; the two functors mediate by composing with
 the unit isomorphism [idx_id A a : idx_map A id a ≅ a] on the
 appropriate side.  Both natural-isomorphism cells of the equivalence
 carry identity components, and their conjugation coherence reduces to
 the unit coherence fields [idx_unit_left]/[idx_unit_right] of
 [IndexedCat] together with naturality of [idx_id]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+fibration 
 nLab:       https://ncatlab.org/nlab/show/displayed+category 
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+construction 
 Wikipedia:  https://en.wikipedia.org/wiki/Fibred_category 

 在基对象  [x] 上显示的范畴  [D] 的纤维是范畴  [Fiber D x] ，其对象是在  [x] 上显示的对象，态射是在  [id[x] 上的显示态射。恒等态射是显示的恒等态射。在  [id] 上的两个态射的显示合成位于  [id ∘ id] 上，因此通过沿基单位律  [id_left id] 的传递，将其组合重新定位到  [id] 上；根据  [dtransport] 的证明无关性（[dtransport_id] 及其在 Theory/Displayed.v 中的结论），基律的选择无关紧要，并且纤维的每个范畴律通过派生传递包中的一个引理闭合。文件的后半部分是 Grothendieck 循环往返的已提交部分：对于一个索引范畴 [A : IndexedCat B]（Construction/Indexed.v）和 [x : B]，ZWZ17WZZ 的纤维在 [A] 的 Grothendieck 构造（Construction/Grothendieck.v）中等价于索引在 [x] 的纤维 [A]：

 Fiber (Grothendieck_Displayed A) x  ≃  idx_fib A x等价性是近同构的。在对象上，两个函子都是恒等的：Grothendieck纤维在  [x] 上的一个对象字面上就是  [idx_fib A x] 的一个对象。只有 Hom 不同：从 [a] 到 [b] 的 Grothendieck-纤维态射是一个纤维态射 [idx_map A id a ~> b]（沿 [id] 重新索引，然后在纤维中比较），而普通纤维态射是 [a ~> b]；两个函子通过在适当的一边与单位同构 [idx_id A a : idx_map A id a ≅ a] 组合来调解。等价性的两个自然同构单元的分量都是恒等的，它们的共轭相干性化简为 [IndexedCat] 的单位相干场 [idx_unit_left] / [idx_unit_right] 以及 [idx_id] 的自然性。
*)

#[local] Obligation Tactic := idtac.

(*
 Conjugating by the identity isomorphism does nothing: the generic
 stripping step for equivalence cells whose isomorphism family is
 [iso_id] pointwise. 

 --------
 通过恒等同构进行共轭不会有任何作用：对于同构族在每一点上都是 [iso_id] 的等价单元，其通用的剥离步骤。
*)
Lemma conjugate_iso_id {C : Category} {a b : C} (f : a ~> b) :
  from (@iso_id C b) ∘ f ∘ to (@iso_id C a) ≈ f.
Proof.
  simpl.
  now rewrite id_left, id_right.
Qed.

(* * ** The fibre category of a displayed category / * ** 显示范畴的纤维范畴 *)

Section FiberCategory.

Context {C : Category}.
Context (D : Displayed C).
Context (x : C).

(*
 Associativity of the recentred composition, stated over arbitrary
 proofs of the base unit law: both sides fuse into a single transport
 of the displayed associator, and parallel transports agree by proof
 irrelevance. 

 --------
 重新定位组合的结合性，在基单位律的任意证明上陈述：两边融合为显示的结合子的单一迁移，并且通过证明不可变性，平行迁移一致。
*)
Lemma Fiber_comp_assoc {da db dc dd : dobj x}
  (e1 e2 e3 e4 : @id C x ∘ @id C x ≈ @id C x)
  (ff : dhom dc dd id) (gg : dhom db dc id) (hh : dhom da db id) :
  dtransport e1 (dcomp ff (dtransport e2 (dcomp gg hh)))
    ≈ dtransport e3 (dcomp (dtransport e4 (dcomp ff gg)) hh).
Proof.
  rewrite (dtransport_comp_r e2
             (compose_respects id id (Equivalence_Reflexive id) _ _ e2)
             ff (dcomp gg hh)).
  rewrite (dtransport_comp_l e4
             (compose_respects _ _ e4 id id (Equivalence_Reflexive id))
             (dcomp ff gg) hh).
  rewrite !dtransport_trans.
  rewrite dcomp_assoc.
  rewrite dtransport_trans.
  apply dtransport_proof_irrel.
Qed.

(*
 The fibre of [D] over [x]: objects displayed over [x], morphisms
 displayed over [id[x]], composition recentred over [id] along the
 base unit law. 

 --------
 [D] 在 [x] 上的纤维：在 [x] 上展示的对象，在 [id[x] 上展示的态射，沿着基单位律在 [id] 上重新中心化的合成。
*)
Program Definition Fiber : Category := {|
  obj := dobj x;
  hom := fun dx dy => dhom dx dy id;
  homset := fun dx dy => dhomset dx dy id;
  id := fun dx => did dx;
  compose := fun dx dy dz ff gg => dtransport (id_left id) (dcomp ff gg)
|}.
Next Obligation.
  (* composition respects ≈ in both arguments / 组合在两个参数中都尊重 ≈ *)
  intros dx dy dz ff ff' Hf gg gg' Hg.
  now rewrite Hf, Hg.
Qed.
Next Obligation.
  (* left identity, over the base unit law / 左单位元，对基本单位律 *)
  intros dx dy ff.
  apply dtransport_did_left.
Qed.
Next Obligation.
  (* right identity, over the base unit law / 正确单位元，在基本单位律之上 *)
  intros dx dy ff.
  apply dtransport_did_right.
Qed.
Next Obligation.
  (* associativity / 结合性 *)
  intros da db dc dd ff gg hh.
  apply Fiber_comp_assoc.
Qed.
Next Obligation.
  (* associativity, dual orientation / 结合性，双重方向 *)
  intros da db dc dd ff gg hh.
  symmetry; apply Fiber_comp_assoc.
Qed.

End FiberCategory.

(*
   * ** The fibres of the Grothendieck construction

   For [A : IndexedCat B] and [x : B], the fibre of the displayed
   presentation of ∫ A over [x] recovers [idx_fib A x] up to an
   equivalence of categories that is the identity on objects. 

   --------
   * ** Grothendieck 构造的纤维

   对于  [A : IndexedCat B] 和  [x : B] ，在  [x] 上显示的 ∫ A 表示的纤维
   可以恢复  [idx_fib A x] ，直到一个在对象上为恒等的范畴等价。
*)

Section GrothendieckFiber.

Context {B : Category}.
Context (A : IndexedCat B).
Context (x : B).

(*
 The from-side of the unit coherence [idx_unit_left] at [f := id]: the
 inverses of the mediator and compositor isos fuse into the inverse of
 the unit iso at the reindexed object. 

 --------
 单位相干 [idx_unit_left] 在 [f := id] 上的 from-side：中介器和组合器同构的逆融合为重新索引对象上的单位同构的逆。
*)
Lemma Grothendieck_fiber_unit_left_inv (a : idx_fib A x) :
  from (idx_comp A id id a) ∘ from (idx_resp A (id_left (@id B x)) a)
    ≈ from (idx_id A (idx_map A (@id B x) a)).
Proof.
  exact (snd (to_equiv_implies_iso_equiv
    (iso_compose (idx_resp A (id_left (@id B x)) a) (idx_comp A id id a))
    (idx_id A (idx_map A (@id B x) a))
    (idx_unit_left A id a))).
Qed.

(*
 The from-side of [idx_unit_right] at [f := id], fused against the
 compositor/mediator tail of the Grothendieck fibre's composition: the
 whole composite cancels. 

 --------
 [idx_unit_right] 的 from-side 在 [f := id] ，与 Grothendieck 纤维组合的合成器/中介尾部融合：整个组合被抵消。
*)
Lemma Grothendieck_fiber_unit_right_inv (a : idx_fib A x) :
  fmap[idx_map A (@id B x)] (to (idx_id A a))
      ∘ from (idx_comp A id id a)
      ∘ from (idx_resp A (id_left (@id B x)) a)
    ≈ id.
Proof.
  rewrite <- (idx_unit_right A id a).
  rewrite <- (comp_assoc (to (idx_resp A (id_right (@id B x)) a))).
  (*
 the rewrites below are pinned: the base identity [id ∘ id] also occurs
 inside the (dependent) implicit arguments of [idx_resp], where the
 generalized rewrite may not abstract 

 --------
 下面的重写被置顶：基础标识 [id ∘ id] 也出现在 [idx_resp] 的（依赖）隐式参数中，其中泛化重写可能无法抽象
*)
  rewrite (iso_to_from (idx_comp A (@id B x) (@id B x) a)).
  rewrite (id_right (to (idx_resp A (id_right (@id B x)) a))).
  rewrite (idx_resp_from_irrel A (id_left (@id B x)) (id_right (@id B x)) a).
  apply iso_to_from.
Qed.

(*
 From the Grothendieck fibre to the indexed fibre: the identity on
 objects; on homs, recentre the source along the unit iso.  Both
 functors here are assembled with an explicit [Build_Functor]: a
 Grothendieck-fibre hom IS a fibre hom [idx_map A id a ~> b] up to
 definitional unfolding, and the type ascriptions below make that
 reading explicit for the elaborator (Program-mode elaboration would
 instead mediate the object mismatch with equality coercions, which
 are not available: [idx_map A id a] is only isomorphic to [a]). 

 --------
 从格罗滕迪克纤维到索引纤维：对象上的恒等；在态射上，将源沿单元同构重新中心化。这里的两个函子都是通过一个显式的 [Build_Functor] 组合而成：一个格罗滕迪克纤维态射在定义性展开下是一个纤维态射 [idx_map A id a ~> b]，下方的类型标注使这种解读对阐释器显式（程序模式下的阐释会通过等式强制来调解对象不匹配，但其不可用：[idx_map A id a] 仅与 [a] 同构）。
*)
Definition Fiber_Grothendieck_To :
  Fiber (Grothendieck_Displayed A) x ⟶ idx_fib A x.
Proof.
  unshelve refine
    (Build_Functor (Fiber (Grothendieck_Displayed A) x) (idx_fib A x)
       (fun a => a)
       (fun a b ff =>
          (ff : idx_map A (@id B x) a ~{ idx_fib A x }~> b)
            ∘ from (idx_id A a))
       _ _ _).
  - (* fmap respects ≈ / fmap 遵守 ≈ *)
    intros a b ff gg Hfg; simpl in *.
    now rewrite Hfg.
  - (* identities: the two sides of the unit iso cancel / 身份：单位的两个方面 iso 取消 *)
    intros a; simpl.
    apply iso_to_from.
  - (* composition: the compositor/mediator tail is the inverted left unit law, and the unit iso is natural / 组成：组合器/中介尾是倒置的左单元律，且单元同构是自然的 *)
    intros a b c ff gg; simpl.
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    rewrite (comp_assoc (from (idx_comp A id id a))).
    rewrite Grothendieck_fiber_unit_left_inv.
    rewrite !comp_assoc.
    now rewrite (idx_id_natural_from A gg).
Defined.

(*
 From the indexed fibre to the Grothendieck fibre: the identity on
 objects; on homs, precompose with the unit iso. 

 --------
 从索引纤维到Grothendieck纤维：在对象上保持恒等；在同态上，与单位同构预组合。
*)
Definition Fiber_Grothendieck_From :
  idx_fib A x ⟶ Fiber (Grothendieck_Displayed A) x.
Proof.
  unshelve refine
    (Build_Functor (idx_fib A x) (Fiber (Grothendieck_Displayed A) x)
       (fun a => a)
       (fun a b k => (k ∘ to (idx_id A a)
                      : a ~{ Fiber (Grothendieck_Displayed A) x }~> b))
       _ _ _).
  - (* fmap respects ≈ / fmap 遵守 ≈ *)
    intros a b k l Hkl; simpl in *.
    now rewrite Hkl.
  - (* identities / 身份 *)
    intros a; simpl.
    apply id_left.
  - (* composition: the inverted right unit law cancels the tail, then the unit iso is natural / 组成：倒置的右单位律消除尾部，然后单位同构是自然的 *)
    intros a b c k l; simpl.
    symmetry.
    rewrite fmap_comp.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap[idx_map A (@id B x)] (to (idx_id A a)))).
    rewrite Grothendieck_fiber_unit_right_inv.
    rewrite id_right.
    now rewrite <- (idx_id_natural A l).
Defined.

(*
 The counit cell: To ◯ From ≈ Id on the indexed fibre, with identity
 components. 

 --------
 余单位单元格：在索引纤维上，从 To ◯ 到 ≈ Id，具有恒等分量。
*)
Definition Grothendieck_fiber_counit :
  Fiber_Grothendieck_To ◯ Fiber_Grothendieck_From ≈ Id[idx_fib A x].
Proof.
  exists (fun a => iso_id).
  intros a b k; cbv beta.
  rewrite conjugate_iso_id; simpl.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  apply id_right.
Defined.

(*
 The unit cell: Id on the Grothendieck fibre ≈ From ◯ To, with
 identity components. 

 --------
 单元格：在格罗滕迪克纤维上的恒等元 ≈ 从 ◯ 到，带有恒等分量。
*)
Definition Grothendieck_fiber_unit :
  Id[Fiber (Grothendieck_Displayed A) x]
    ≈ Fiber_Grothendieck_From ◯ Fiber_Grothendieck_To.
Proof.
  exists (fun a => iso_id).
  intros a b ff; cbv beta.
  rewrite conjugate_iso_id; simpl.
  rewrite <- comp_assoc.
  rewrite iso_from_to.
  now rewrite id_right.
Defined.

(*
 The committed half of the round trip, packaged: the fibre of the
 Grothendieck construction of [A] at [x] is equivalent to the fibre
 [A] indexes at [x]. 

 --------
 往返行程的已提交部分，打包：在 [x] 处 [A] 的 Grothendieck 构造的纤维等同于在 [x] 处索引的 [A] 纤维。
*)
Definition fiber_grothendieck_equiv :
  EquivalenceOfCategories Fiber_Grothendieck_To :=
  @Build_EquivalenceOfCategories
    (Fiber (Grothendieck_Displayed A) x) (idx_fib A x)
    Fiber_Grothendieck_To Fiber_Grothendieck_From
    Grothendieck_fiber_counit Grothendieck_fiber_unit.

End GrothendieckFiber.
