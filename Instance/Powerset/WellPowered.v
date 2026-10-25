Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Powerset.

Generalizable All Variables.

(* * * The intersection theorem at the powerset lattice of a setoid / * * 集合等价类幂集上的交集定理 *)

(*
 nLab:      https://ncatlab.org/nlab/show/well-powered+category
 nLab:      https://ncatlab.org/nlab/show/power+set
 Wikipedia: https://en.wikipedia.org/wiki/Power_set

 Mac Lane, "Categories for the Working Mathematician", 2nd ed., §V.8,
 book p. 130: a well-powered complete category has the intersection of
 any collection of subobjects of an object.  Structure/WellPowered.v
 proves that as [wellpowered_complete_has_intersections] and its
 [Prop]-class form [wellpowered_complete_has_intersections_prop].  This
 file instantiates it, unconditionally, at a complete category whose
 subobject lattices are NOT degenerate: Instance/Powerset.v's [Subsets X],
 the subsets of a setoid [X] under inclusion.  It is a satellite so that
 Structure/ does not import Instance/Powerset.v.

 WHAT IS DELIVERED.

 - [Subsets_Complete_free X : Complete (Subsets@{o u} X)], at a FREE
 hom level [u].  It is Instance/Powerset.v's [Subsets_Complete] with
 the literal [Set] of that file's hom slot left open: the same term,
 [snd (proset_Complete_iff_all_meets (subset_le_preorder X))
 Subsets_HasAllMeets].  That file's comment on [Subsets_Complete]
 records that the [Set] there became a choice once
 Instance/Discrete.v was annotated, and that the restatement was not
 attempted; this is the restatement, measured below.
 - [Subsets_WellPowered X : WellPowered (Subsets@{o u} X)] for
 [o <= u], by Structure/WellPowered.v's [trivial_small]: the objects
 of [Subsets@{o u} X] sit at [o], at or below the homs.
 - [Subsets_has_intersections] and [Subsets_intersection_all]: the
 consequence at [Subsets X], for every ≈-closed [Prop]-class of
 subobjects and for the class of all subobjects.
 - [Subsets_intersection_all_not_top]: the intersection of ALL
 subobjects of the full subset [subset_top] is not the top subobject
 as soon as [X] has a point, because the subobject named by the empty
 subset ([subsets_sub_bot]) is a member of the class and is not the
 top.  So the theorem is exercised at a lattice with at least two
 distinct subobjects, where Structure/WellPowered.v's
 [Indiscrete_types_has_intersections] has only one.

 UNIVERSES, measured with [Set Printing Universes. About ...], stdlib
 bounds omitted:

 Subsets_Complete_free@{o u ...} :
 ∀ X : SetoidObject@{o o}, Complete@{u0 u1 u o}
 ( * Set < o, u <= u0, u1 <= u0, and bounds on internal universes * )
 Subsets_WellPowered@{o u t} :
 ∀ X, WellPowered@{o u u u t} (Subsets@{o u} X)
 ( * Set < o, u < t, o <= u * )

 [Subsets_Complete_free] bounds the hom level [u] only by [Complete]'s
 first slot [u0] and by universes internal to the proof, never by [o],
 so completeness holds at every [u]; the well-poweredness witness, and
 with it the consequence, needs [o <= u].  [Set < o] comes from
 [Prop]-valued subsets.

 WHAT THIS DOES NOT SHOW.  Well-poweredness is the trivial kind here:
 the objects sit at or below the homs, so [trivial_small] indexes the
 subobjects by themselves.  Of the instances of the consequence in
 tree, none has BOTH objects strictly above homs AND a non-degenerate
 subobject lattice unconditionally: Structure/WellPowered.v's
 [Indiscrete_types_has_intersections] has objects above homs and one
 subobject per object, this file has the reverse, and Instance/Sets/
 WellPowered.v's [Sets_wellpowered_intersection] has both but takes
 [Untruncate].

 MEASUREMENTS.  Six constants ([.glob] heads), no [Program] obligation;
 five transparent definitions and one [Qed] refutation
 ([Subsets_intersection_all_not_top]); each reports "Closed under the
 global context" by its fully qualified name.  Closure 132 files
 excluding itself, counted over .Makefile.coq.d; Instance/Powerset.v's
 is 87, and the difference is Structure/WellPowered.v's development. 

 --------
 nLab:       https://ncatlab.org/nlab/show/well-powered+category 
 nLab:       https://ncatlab.org/nlab/show/power+set 
 Wikipedia:  https://en.wikipedia.org/wiki/Power_set 

 Mac Lane, 《为工作数学家而设的范畴论》(Categories for the Working Mathematician), 第二版, §V.8,
 书本第130页: 一个良幂完备范畴具有任意对象子对象集合的交。Structure/WellPowered.v
 将其证明为 [wellpowered_complete_has_intersections]，并且它的 [Prop] 类形成 [wellpowered_complete_has_intersections_prop] 。
 这个文件在一个完备范畴上无条件地实例化它，该范畴的子对象格不是退化的：Instance/Powerset.v 的 [Subsets X] ，
 在包含关系下的集合族 [X] 。它是一个卫星，因此 Structure/ 不会导入 Instance/Powerset.v。

 交付的内容是什么。-  [Subsets_Complete_free X : Complete (Subsets@{o u} X)]，在一个自由的  
 hom 层级 [u]。这是 Instance/Powerset.v 的 [Subsets_Complete]，  
 其文件的 hom 槽的字面 [Set] 保留为空：同一个项，  
 [snd (proset_Complete_iff_all_meets (subset_le_preorder X))  
 Subsets_HasAllMeets]。该文件对 [Subsets_Complete] 的注释记录了  
 一旦 Instance/Discrete.v 被标注，[Set] 变成了一个选择，  
 并且该重述未被尝试；这是下面测量的重述。-  [Subsets_WellPowered X : WellPowered (Subsets@{o u} X)] 针对 [o <= u]，由 Structure/WellPowered.v 的 [trivial_small] ：  
 [Subsets@{o u} X] 的对象位于 [o]，在 hom 或其以下。-  [Subsets_has_intersections] 和 [Subsets_intersection_all] ：其结果位于 [Subsets X]，对于每个 ≈-闭的 [Prop] 子对象类，以及所有子对象的类。- [Subsets_intersection_all_not_top]：当[X]有一个点时，完整子集[subset_top]的所有子对象的交集就不再是顶部子对象，因为由空子集（[subsets_sub_bot]）命名的子对象是该类的成员，且不是顶部对象。因此，该定理在至少有两个不同子对象的格中被应用，而Structure/WellPowered.v中的[Indiscrete_types_has_intersections]只有一个子对象。

 UNIVERSES，用[Set Printing Universes. About ...]测量，stdlib边界省略：

 Subsets_Complete_free@{o u ...}：
 ∀ X : SetoidObject@{o o}, Complete@{u0 u1 u o}
 ( * 集合 < o, u <= u0, u1 <= u0, 以及内部宇宙的边界 * )

 Subsets_WellPowered@{o u t}：
 ∀ X, WellPowered@{o u u u t} (Subsets@{o u} X)
 ( * 集合 < o, u < t, o <= u * )[Subsets_Complete_free]  仅通过  [Complete] 的第一个槽 [u0] 以及证明内部的整体，约束同级别 [u]，而从不通过 [o]，所以在每个 [u] 上完全性成立；良幂性证据，以及随之而来的结论，需要 [o <= u]。[Set < o] 来自 [Prop] 值的子集。这没有显示的内容。这里的充分性是平凡的：对象位于 Hom 以下或相等，所以 [trivial_small] 按自身索引子对象。在树中后果的实例中，没有一个同时严格位于 Hom 之上并且具有非退化子对象格的：Structure/WellPowered.v 的 [Indiscrete_types_has_intersections] 对象位于 Hom 之上并且每个对象只有一个子对象，这个文件情况相反，而 Instance/Sets/WellPowered.v 的 [Sets_wellpowered_intersection] 两者都有，但使用 [Untruncate]。测量。六个常数（[.glob] 头），无 [Program] 义务；五个透明定义和一个 [Qed] 反驳（[Subsets_intersection_all_not_top]）；每个都通过其完全限定名报告“在全局上下文下封闭”。封闭 132 个文件，不包括自身，统计在 .Makefile.coq.d 上；Instance/Powerset.v 的为 87，其差值为 Structure/WellPowered.v 的开发。
*)

Definition Subsets_Complete_free@{o u +} (X : SetoidObject@{o o}) :
  @Complete (Subsets@{o u} X) :=
  snd (proset_Complete_iff_all_meets (subset_le_preorder@{o} X))
    Subsets_HasAllMeets.

Definition Subsets_WellPowered@{o u t | o <= u, u < t +}
  (X : SetoidObject@{o o}) : WellPowered@{o u u u t} (Subsets@{o u} X) :=
  trivial_small _.

(* The consequence at [Subsets X], for a [Prop]-class of subobjects. / 在 [Subsets X] 上的结果，对于 [Prop] 类的子对象。 *)
Definition Subsets_has_intersections@{o u +} (X : SetoidObject@{o o})
  (S : Subsets@{o u} X) (P : SubObj S → Prop)
  (HP : ∀ m m' : SubObj S, m ≈ m' → P m → P m') :
  { w : SubObj S &
    IsIntersection (fun k : { m : SubObj S & P m } => `1 k) w } :=
  wellpowered_complete_has_intersections_prop
    (Subsets_WellPowered X) (Subsets_Complete_free X) S P HP.

(* The class of all subobjects. / 所有子对象的类。 *)
Definition Subsets_intersection_all@{o u +} (X : SetoidObject@{o o})
  (S : Subsets@{o u} X) :
  { w : SubObj S & IsIntersection (fun m : SubObj S => m) w } :=
  wellpowered_complete_intersection_all
    (Subsets_WellPowered X) (Subsets_Complete_free X) S.

(*
 The empty subset, as a subobject of the full one.  Every arrow of
 [Subsets X] is monic, the category being thin. 

 --------
 空子集，作为整体的子对象。[Subsets X] 的每条箭头都是单射，因为该范畴是稀薄范畴。
*)
Definition subsets_sub_bot@{o u +} (X : SetoidObject@{o o}) :
  @SubObj (Subsets@{o u} X) subset_top :=
  {| sub_dom := (subset_bot : obj[Subsets@{o u} X]);
     sub_mono := (subset_bot_least subset_top
                    : subset_bot ~{Subsets@{o u} X}~> subset_top);
     sub_is_monic := @Build_Monic (Subsets@{o u} X) _ _
                       (subset_bot_least subset_top) (fun _ _ _ _ => I) |}.

(* Non-degeneracy: at a pointed [X], the intersection of all subobjects of the full subset lies below [subsets_sub_bot], so it is not the top. / 非退化性：在一个尖点 [X] 处，完整子集的所有子对象的交集位于 [subsets_sub_bot] 之下，因此它不是顶点。 *)
Lemma Subsets_intersection_all_not_top@{o u +} (X : SetoidObject@{o o})
  (x : carrier X) :
  `1 (Subsets_intersection_all X (subset_top : obj[Subsets@{o u} X]))
    ≈ sub_top → False.
Proof.
  intros [iso _].
  destruct (inter_le _ _
              (`2 (Subsets_intersection_all X
                     (subset_top : obj[Subsets@{o u} X])))
              (subsets_sub_bot X)) as [k _].
  destruct (k x (from iso x (fun i => match i with end))) as [i _].
  destruct i.
Qed.
