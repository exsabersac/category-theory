Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Theory.Universal.Arrow.

(* * * A universal arrow is a universal property / * * 一个通用箭头是一个通用性质 *)

(*
 nLab: https://ncatlab.org/nlab/show/universal+morphism
 nLab: https://ncatlab.org/nlab/show/representable+functor
 Wikipedia: https://en.wikipedia.org/wiki/Universal_property

 A universal arrow from an object c : C to a functor U : D ⟶ C is a pair
 (a, u : c ~> U a) such that every h : c ~> U d factors as h ≈ fmap[U] g ∘ u
 through a unique g : a ~> d (see Theory/Universal/Arrow.v, where the same
 data is packaged as [AUniversalArrow] and, equivalently, as an initial
 object of the comma category =(c) ↓ U).  Equivalently — this is the
 “universal property ⟺ representability” equivalence — the object a together
 with the assignment g ↦ fmap[U] g ∘ u exhibits a natural isomorphism of
 copresheaves

 Hom_D(a, ─) ≅ Hom_C(c, U ─)    (natural in the target)

 so that a represents the functor d ↦ Hom_C(c, U d).  This is exactly the
 representable-functor characterisation given on both reference pages.

 [UniversalArrowIsUniversalProperty] instantiates the generic packaging
 [IsUniversalProperty] from [Structure.UniversalProperty] for the predicate
 P := fun a => AUniversalArrow c U a, with the representing functor taken to
 be (Curried_Hom C c) ◯ U : D ⟶ Sets, i.e. d ↦ Hom_C(c, U d).  Its per-object
 obligations build, in both directions, the natural isomorphism between the
 setoid of universal arrows AUniversalArrow c U a and the setoid of natural
 isomorphisms [Hom a,─] ≅ ((Curried_Hom C c) ◯ U); the universal element is
 recovered through the Yoneda computation [preyoneda].  [fmap_respects'] is a
 local, [cat]-resolvable restatement of [fmap_respects] used by the
 automation discharging those obligations. 

 --------
 nLab:  https://ncatlab.org/nlab/show/universal+morphism 
 nLab:  https://ncatlab.org/nlab/show/representable+functor 
 Wikipedia:  https://en.wikipedia.org/wiki/Universal_property 

 从对象 c : C 到函子 U : D ⟶ C 的一个通用箭头是一个对 (a, u : c ~> U a)，满足每个 h : c ~> U d 都可以分解为 h ≈ fmap [U] g ∘ u，通过一个唯一的 g : a ~> d（参见 Theory/Universal/Arrow.v，其中相同的数据被打包为 [AUniversalArrow]，并且等价地，被视为逗号范畴 =(c) ↓ U 的初始对象）。等价地——这就是“通用性质 ⟺ 可表示性”的等价——对象 a 以及赋值 g ↦ fmap [U] g ∘ u 展示了余预层的自然同构

 Hom_D(a, ─) ≅ Hom_C(c, U ─)    （在目标上是自然的）

 因此 a 表示函子 d ↦ Hom_C(c, U d)。这正是两个参考页面上给出的可表示函子特征。[UniversalArrowIsUniversalProperty] 实例化了通用包装 [IsUniversalProperty]，从 [Structure.UniversalProperty] 为谓词 P := fun a => AUniversalArrow c U a，采用的表示函子为 (Curried_Hom C c) ◯ U : D ⟶ Sets，即 d ↦ Hom_C(c, U d)。它的每个对象的义务在两个方向上构建了通用箭头 AUniversalArrow c U a 的集合等价类与自然同构集合等价类 [Hom a,─] ≅ ((Curried_Hom C c) ◯ U) 之间的自然同构；通用元素通过 Yoneda 计算 [preyoneda] 被恢复。[fmap_respects'] 是 [fmap_respects] 的局部、[cat] 可解析的重述，用于自动化履行这些义务。
*)

Section UniversalArrowUniversalProperty.
  Context (C D: Category).
  Context (U : D ⟶ C).
  Context (c : C).

  Hint Resolve fmap : cat.

  Proposition fmap_respects' (x y : D) (f g : x ~> y) :
    f ≈ g -> fmap[U] f ≈ fmap[U] g.
  Proof using Type.
    apply fmap_respects.
  Qed.

  Hint Resolve fmap_respects' : cat.
  Hint Rewrite @fmap_comp : categories.
  Hint Resolve uniqueness : cat.

  Proposition UniversalArrowIsUniversalProperty :
    IsUniversalProperty D (fun a : D => AUniversalArrow c U a) _.
  Proof.
    exists ((Curried_Hom C c) ◯ U).
    intro a.
    repeat(unshelve econstructor; try intro).
    - simpl in *. destruct X. auto with cat.
    - abstract(auto with cat).
    - abstract(auto with cat).
    - abstract(auto with cat).
    - simpl in *. destruct X. now apply universal_arrow_universal.
    - abstract(simpl; intros; apply uniqueness;
      rewrite (unique_property universal_arrow_universal); easy).
    - abstract(simpl; intros; symmetry; apply uniqueness;
      autorewrite with categories;
               now rewrite (unique_property universal_arrow_universal)).
    - abstract(simpl; intros; destruct X; simpl; apply uniqueness;
      autorewrite with categories; apply compose_respects; [ reflexivity |];
               apply (unique_property (universal_arrow_universal _ _))).
    - abstract(simpl; intros; rewrite (unique_property universal_arrow_universal);
               auto with cat).
    - abstract(auto with cat).
    - abstract(auto with cat).
    - abstract(simpl; intros; apply uniqueness;
      simpl in X;
               now rewrite X, (unique_property (universal_arrow_universal ))).
    - exact (((to X) a) id).
    - now apply (from X d).
    - abstract(simpl; set (M := @preyoneda D^op _ d _ (to X));
      simpl in M; rewrite <- M; clear M;
      assert (K := (@iso_to_from _ _ _ X)); simpl in K; rewrite K;
               now autorewrite with categories).
    - (* This obligation is discharged directly by the tactic sequence below. It relies on setoid rewriting that handles universe polymorphism well enough to close the goal, available on every supported version (Coq >= 8.19, Rocq 9.0 and 9.1). The development stays axiom-free: [Print Assumptions UniversalArrowIsUniversalProperty] reports “Closed under the global context” on Rocq 9.1. / 这一义务直接通过下面的策略序列来完成。它依赖于集合重写（setoid rewriting），能够很好地处理宇宙多态性，从而完成目标，在所有支持的版本（Coq >= 8.19, Rocq 9.0 和 9.1）中都可用。开发保持无公理状态：[Print Assumptions UniversalArrowIsUniversalProperty] 在 Rocq 9.1 上报告“在全局上下文中关闭”。 *)
      simpl; assert (M := @preyoneda D^op _ d _ (to X));
      simpl in M; intro A; rewrite <- M in A; clear M;
      apply (proper_morphism (from X d)) in A;
      set (B := (iso_from_to X)); simpl in B; now rewrite B , id_left in A.
    - abstract(simpl; intros; destruct X as [e ?]; simpl in e; apply e).
    - abstract(simpl; intro; assert (M := @preyoneda D^op _ x0 _ (to x));
               simpl in M; now rewrite <- M).
    - abstract (auto with cat).
    - abstract(auto with cat).
  Defined.

End UniversalArrowUniversalProperty.


