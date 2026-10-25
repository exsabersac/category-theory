Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Pullback.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
The subobject presheaf Sub : C^op ⟶ Sets.

   nLab: https://ncatlab.org/nlab/show/subobject

   In a category with chosen pullbacks, a morphism f : y ~> x induces a
   reindexing map SubObj x → SubObj y: pull the mono u ↪ x back along f; the
   projection opposite u is again monic (monic_pullback_stable), so it is a
   subobject of y.  Reindexing respects the SubObj setoid (equivalent monos
   pull back to equivalent monos), is the identity on subobjects when f is
   the identity, and turns composition into composition of reindexings — the
   last by the pasting law for pullbacks (pullback_paste).  Assembled, this
   is a contravariant functor from C to the category of setoids.

--------
子对象预层 Presheaf Sub : C^op ⟶ Sets。

nLab: https://ncatlab.org/nlab/show/subobject

在具有选定拉回的范畴中，一个态射 f : y ~> x 诱导一个重索引映射 SubObj x → SubObj y：沿 f 拉回单射 u ↪ x；相反的投影 u 仍然是单射（monic_pullback_stable），因此它是 y 的一个子对象。重索引尊重 SubObj 等价类集合（等价单射拉回为等价单射）、当 f 为恒等映射时是子对象上的恒等映射，并且将复合转化为重索引的复合——最后这一点由拉回的粘合法则（pullback_paste）保证。组合起来，这就是从 C 到等价类集合范畴的一个逆变函子。
*)

Section SubFunctor.

Context {C : Category}.
Context `{@HasPullbacks C}.

(*
Reindex a subobject of x along f : y ~> x, via the chosen pullback.  The
   reindexed mono is the projection opposite sub_mono u, monic because monos
   are stable under pullback.

--------
通过所选择的拉回沿 f : y ~> x 对 x 的子对象进行重索引。重索引的单态是与 sub_mono u 相对的投影，单态是单态因为单态在拉回下是稳定的。
*)
Definition sub_reindex {x y : C} (f : y ~> x) (u : SubObj x) : SubObj y := {|
  sub_dom  := Pull f (sub_mono u) (pullback f (sub_mono u));
  sub_mono := pullback_fst f (sub_mono u) (pullback f (sub_mono u));
  sub_is_monic := monic_pullback_stable f (sub_mono u) (sub_is_monic u)
                    (pullback f (sub_mono u))
|}.

(*
The workhorse: if a given subobject v of y sits atop ANY pullback square
   of sub_mono u along f, then v is the reindexing of u along f, up to the
   SubObj setoid.  The isomorphism of apexes and its triangle with the two
   first projections come from pullback_transport.

--------
主力：如果给定的子对象 v 位于任意子单态射 u 沿 f 的拉回图的顶点上，那么 v 就是 u 沿 f 的重索引，在 SubObj 集合上同构。顶点的同构以及它与两个第一投影的三角形来自拉回传输。
*)
Lemma sub_reindex_transport {x y : C} (f : y ~> x) (u : SubObj x)
      (v : SubObj y) (p2 : sub_dom v ~> sub_dom u)
      (HP : IsPullback f (sub_mono u) (sub_dom v) (sub_mono v) p2) :
  sub_reindex f u ≈ v.
Proof.
  pose proof (pullback_transport (pullback f (sub_mono u))
                                 (is_pullback_pullback HP)) as T.
  exists (transport_iso T).
  exact (transport_fst T).
Qed.

(*
Reindexing respects the SubObj setoid: if u ≈ v via a domain isomorphism
   i, then the chosen pullback of v along f, corrected by i, is itself a
   pullback square for sub_mono u along f; sub_reindex_transport concludes.

--------
重新索引遵循 SubObj 等价关系：如果 u ≈ v 通过一个域同构 i，那么沿 f 选择的 v 的拉回，并通过 i 校正，本身就是沿 f 的 sub_mono u 的拉回方形；sub_reindex_transport 得出结论。
*)
#[export] Instance sub_reindex_respects {x y : C} (f : y ~> x) :
  Proper (equiv ==> equiv) (@sub_reindex x y f).
Proof.
  intros u v [i Hi].
  apply (sub_reindex_transport
           f u (sub_reindex f v)
           (from i ∘ pullback_snd f (sub_mono v) (pullback f (sub_mono v)))).
  constructor; simpl.
  - (* the corrected square commutes / 修正后的平方可交换 *)
    rewrite (pullback_commutes f (sub_mono v) (pullback f (sub_mono v))).
    rewrite <- Hi.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to i)).
    rewrite iso_to_from; cat.
  - intros Q q1 q2 Hq.
    (* transport the cone across i and mediate into the chosen pullback / 将圆锥体横跨 i 并介入到选定的拉回中 *)
    assert (Hq' : f ∘ q1 ≈ sub_mono v ∘ (to i ∘ q2)).
    { rewrite Hq, <- Hi.
      now rewrite comp_assoc. }
    pose proof (ump_pullbacks f (sub_mono v) (pullback f (sub_mono v))
                              Q q1 (to i ∘ q2) Hq') as W.
    destruct (unique_property W) as [W1 W2].
    unshelve refine {| unique_obj := unique_obj W |}.
    + split.
      * exact W1.
      * rewrite <- comp_assoc.
        rewrite W2.
        rewrite comp_assoc.
        rewrite iso_from_to; cat.
    + intros w [Hw1 Hw2].
      apply (uniqueness W); split.
      * exact Hw1.
      * rewrite <- Hw2.
        rewrite !comp_assoc.
        rewrite iso_to_from; cat.
Qed.

(*
A pullback square is stable under replacing the left leg of its cospan by
   an ≈-equal morphism; both fields transport by rewriting.

--------
当把余锥的左边换成一个≈-等价的态射时，拉回方块是稳定的；两个范畴都通过重写进行传输。
*)
Lemma is_pullback_respects_left {x y z : C} {f f' : x ~> z} {g : y ~> z}
      {P : C} {p1 : P ~> x} {p2 : P ~> y} (Hf : f ≈ f') :
  IsPullback f g P p1 p2 → IsPullback f' g P p1 p2.
Proof.
  intros [Hc Hu].
  constructor.
  - now rewrite <- Hf.
  - intros Q q1 q2 Hq.
    apply Hu.
    now rewrite Hf.
Qed.

(*
Reindexing along ≈-equal morphisms yields equivalent subobjects: the
   chosen pullback along f is also a pullback square along f'.

--------
沿≈-等态射重新索引会生成等价的子对象：沿 f 选择的拉回也沿 f' 是一个拉回方格。
*)
Lemma sub_reindex_respects_mor {x y : C} (f f' : y ~> x) (Hf : f ≈ f')
      (u : SubObj x) :
  sub_reindex f u ≈ sub_reindex f' u.
Proof.
  symmetry.
  apply (sub_reindex_transport
           f' u (sub_reindex f u)
           (pullback_snd f (sub_mono u) (pullback f (sub_mono u)))).
  apply (is_pullback_respects_left Hf).
  apply pullback_is_pullback.
Qed.

(*
The square with id on top and bottom and m on both sides is a pullback:
   the mediator for a cone (q1, q2) is q2 itself.

--------
顶部和底部有 id、两侧有 m 的方形是一个回拉：
   锥体 (q1, q2) 的中介是 q2 本身。
*)
Lemma is_pullback_along_id {x y : C} (m : y ~> x) :
  IsPullback id m y m id.
Proof.
  constructor.
  - cat.
  - intros Q q1 q2 Hq.
    rewrite id_left in Hq.
    unshelve refine {| unique_obj := q2 |}.
    + split.
      * now rewrite <- Hq.
      * cat.
    + intros w [Hw1 Hw2].
      now rewrite <- Hw2; cat.
Qed.

(* Reindexing along the identity is the identity on subobjects. / 沿恒等进行重新索引在子对象上是恒等。 *)
Lemma sub_reindex_id {x : C} (u : SubObj x) : sub_reindex id u ≈ u.
Proof.
  apply (sub_reindex_transport id u u id).
  apply is_pullback_along_id.
Qed.

(*
Reindexing along a composite g ∘ f is reindexing along g and then along
   f: pasting the two chosen squares exhibits the double pullback as one
   pullback square for the composite.

--------
沿复合 g ∘ f 的重新索引是先沿 g 再沿 f：粘贴两个选定的正方形显示双拉回可以作为复合的一个拉回正方形。
*)
Lemma sub_reindex_comp {x y z : C} (g : y ~> x) (f : z ~> y)
      (u : SubObj x) :
  sub_reindex (g ∘ f) u ≈ sub_reindex f (sub_reindex g u).
Proof.
  apply (sub_reindex_transport
           (g ∘ f) u (sub_reindex f (sub_reindex g u))
           (pullback_snd g (sub_mono u) (pullback g (sub_mono u))
              ∘ pullback_snd f (sub_mono (sub_reindex g u))
                  (pullback f (sub_mono (sub_reindex g u))))).
  apply (pullback_paste
           (pullback_is_pullback g (sub_mono u) (pullback g (sub_mono u)))
           (pullback_is_pullback f (sub_mono (sub_reindex g u))
              (pullback f (sub_mono (sub_reindex g u))))).
Qed.

(*
The subobject presheaf: contravariant on C, valued in setoids.  A
   C^op-arrow f : x ~> y is a C-arrow y ~> x, and acts by pullback
   reindexing; the functor laws are the three lemmas above, read at the
   pointwise hom-setoid of Sets.  Naming note: [Sub] is the work
   order's name and coexists with Construction/Subcategory.v's
   category [Sub]; the two live in different modules, so qualify the
   reference in any file importing both.  The generic transport lemma
   [is_pullback_respects_left] above (and its companion
   [is_pullback_respects_snd] in Structure/SubobjectClassifier.v) are
   candidates for promotion into Theory/Morphisms/Stability.v beside
   [IsPullback].

--------
子对象预层：在 C 上是逆变的，取值于集合同构。一个 C^op 箭头 f : x ~> y 是一个 C 箭头 y ~> x，并通过拉回重索引操作；函子定律是上面三条引理，在集合点态的同态集中读取。命名说明：[Sub] 是工作顺序的名称，与 Construction/Subcategory.v 中的范畴 [Sub] 共存；它们位于不同模块，因此在导入两个模块的任何文件中引用时要加以限定。上文的泛型传输引理 [is_pullback_respects_left]（及其在 Structure/SubobjectClassifier.v 中的配套 [is_pullback_respects_snd]）是候选，可以连同 [IsPullback] 一起提升到 Theory/Morphisms/Stability.v 中。
*)
Local Obligation Tactic := simpl; intros.

Program Definition Sub : C^op ⟶ Sets := {|
  fobj := fun x : C => {| carrier   := SubObj x
                        ; is_setoid := @SubObj_Setoid C x |};
  fmap := fun x y (f : x ~{C^op}~> y) =>
            {| morphism := sub_reindex (unop f)
             ; proper_morphism := sub_reindex_respects (unop f) |}
|}.
Next Obligation.
  repeat intro.
  apply sub_reindex_respects_mor.
  exact X.
Qed.
Next Obligation.
  apply sub_reindex_id.
Qed.
Next Obligation.
  apply sub_reindex_comp.
Qed.

End SubFunctor.
