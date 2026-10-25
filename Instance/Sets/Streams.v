Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Construction.FCoalg.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

(* * * Streams as the final coalgebra of [StreamF] over [Sets] / * * 流作为 [StreamF] 上 [Sets] 的最终余代数 *)

(*
 nLab:      https://ncatlab.org/nlab/show/coalgebra+of+an+endofunctor
 nLab:      https://ncatlab.org/nlab/show/bisimulation
 nLab:      https://ncatlab.org/nlab/show/terminal+coalgebra
 Wikipedia: https://en.wikipedia.org/wiki/Coinduction
 Wikipedia: https://en.wikipedia.org/wiki/Bisimulation

 For a fixed setoid [A] the "head/tail" endofunctor on [Sets] is
 [StreamF X := A × X] (the product setoid).  Its coalgebras [(X, c)] with
 [c : X ~> A × X] are precisely deterministic [A]-labelled transition
 systems: each state [x] emits a head [fst (c x)] and steps to [snd (c x)].
 The greatest fixed point of [StreamF] is the type of infinite streams over
 [A], carrying the coalgebra [γ s = (shead s, stail s)].  This file realises
 that greatest fixed point as the final object of [FCoalg (StreamF)].

 Two subtleties are specific to a constructive, axiom-free setting:

 - Streams are a [CoInductive] and equality of coinductives is intensionally
 too fine (it is not provable without extra axioms), so the "correct" home
 for streams is the setoid whose relation is bisimilarity [bisim] — the
 largest relation matching heads (under [A]'s [≈]) and relating tails.  We
 prove [bisim] is an equivalence by guarded corecursion and package the
 result as [Stream_SO : SetoidObject].

 - Because [equiv] lives in [crelation] ([Type]-valued, proof-relevant),
 [bisim] is itself [Type]-valued so it may serve as the hom/carrier setoid
 relation directly.

 The universal property is the anamorphism [ana]: every coalgebra [(X, c)]
 has a unique (up to bisimilarity) coalgebra map into [(Stream, γ)].
 Existence is the corecursive [ana_fn]; uniqueness is [ana_unique_gen], again
 by guarded corecursion, generalised over an intermediate state so that the
 corecursive call stays guarded (a plain bisimilarity chain would place the
 call under a transitivity, breaking the guard).  Since
 [FCoalg F = (FAlg (F^op))^op] and [Initial C = Terminal (C^op)] hold
 definitionally, the final coalgebra is assembled directly as a
 [@Terminal (FCoalg StreamF)]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/coalgebra+of+an+endofunctor 
 nLab:       https://ncatlab.org/nlab/show/bisimulation 
 nLab:       https://ncatlab.org/nlab/show/terminal+coalgebra 
 维基百科:  https://en.wikipedia.org/wiki/Coinduction 
 维基百科:  https://en.wikipedia.org/wiki/Bisimulation 

 对于一个固定集值 [A]，作用在 [Sets] 上的“头/尾”自函子是
 [StreamF X := A × X]（乘积集值）。其余代数 [(X, c)] 与
 [c : X ~> A × X] 精确地对应于确定性的 [A] 标记转移
 系统：每个状态 [x] 发出一个头 [fst (c x)] 并转到 [snd (c x)]。
 [StreamF] 的最大不动点是 [A] 上无限流的类型，携带代数 [γ s = (shead s, stail s)]。
 该文件将该最大不动点实现为 [FCoalg (StreamF)] 的终对象。

 两个细微差别特有于构造性、无公理的环境：- 流是一个 [CoInductive]，而共归类型的等式在强度上过于精细（没有额外公理无法证明），因此流的“正确”归属是其关系为双模的集合等价类 [bisim]——这是匹配头元素（在 [A] 的 [≈] 下）并关联尾元素的最大关系。我们通过受控核心归纳证明 [bisim] 是等价关系，并将结果封装为 [Stream_SO : SetoidObject]。

 - 因为 [equiv] 存在于 [crelation]（[Type] 值，证明相关），[bisim] 自身是 [Type] 值，因此它可以直接作为同态/载体集合等价类关系。普适性是反态射 [ana]：每一个余代数 [(X, c)] 都有一个唯一的（在双态相似下）余代数映射到 [(Stream, γ)]。存在性是余递归 [ana_fn]；唯一性是 [ana_unique_gen]，同样通过守护余递归推广到一个中间状态，以保证余递归调用保持被守护（普通的双态相似链会把调用置于传递性之下，从而破坏守护）。由于 [FCoalg F = (FAlg (F^op))^op] 和 [Initial C = Terminal (C^op)] 在定义上成立，最终余代数可以直接作为 [@Terminal (FCoalg StreamF)] 组装。
*)

Section Streams.

Context (A : SetoidObject).

(* Infinite streams over the carrier of [A]: a head element and a tail stream, produced coinductively. / 在 [A] 的承载体上无限流：一个头元素和一个尾流，通过共归归纳产生。 *)
CoInductive Stream : Type := SCons { shead : carrier A ; stail : Stream }.

(*
 Bisimilarity: the largest relation equating heads under [A]'s [≈] and
 relating tails.  It is [Type]-valued so it can be the carrier setoid's
 relation. 

 --------
 双模相似性：在 [A] 的 [≈] 下将头部等同并关联尾部的最大关系。它是 [Type] 值的，因此可以成为承载集合的关系。
*)
CoInductive bisim : Stream → Stream → Type :=
  Bisim : ∀ s t, shead s ≈ shead t → bisim (stail s) (stail t) → bisim s t.

(* Head and tail projections of a bisimilarity witness (an [in]-annotated match, so the indices need not be variables). / 双模等价见证的头尾投影（一个 [in] 标注的匹配，因此索引不必是变量）。 *)
Definition bisim_head {s t : Stream} (H : bisim s t) : shead s ≈ shead t :=
  match H in bisim s0 t0 return shead s0 ≈ shead t0 with
  | Bisim _ _ h _ => h
  end.

Definition bisim_tail {s t : Stream} (H : bisim s t) :
  bisim (stail s) (stail t) :=
  match H in bisim s0 t0 return bisim (stail s0) (stail t0) with
  | Bisim _ _ _ tl => tl
  end.

(* Reflexivity, symmetry and transitivity of bisimilarity by guarded corecursion: in each case the corecursive call sits directly under the [Bisim] constructor. / 通过受控核心递归的双向相似性的自反性、对称性和传递性：在每种情况下，核心递归调用直接位于 [Bisim] 构造函数下面。 *)
Lemma bisim_refl : ∀ s, bisim s s.
Proof.
  cofix CIH.
  intro s.
  constructor.
  - reflexivity.
  - apply CIH.
Qed.

Lemma bisim_sym : ∀ s t, bisim s t → bisim t s.
Proof.
  cofix CIH.
  intros s t H.
  constructor.
  - symmetry.
    exact (bisim_head H).
  - apply CIH.
    exact (bisim_tail H).
Qed.

Lemma bisim_trans : ∀ s t u, bisim s t → bisim t u → bisim s u.
Proof.
  cofix CIH.
  intros s t u Hst Htu.
  constructor.
  - transitivity (shead t).
    + exact (bisim_head Hst).
    + exact (bisim_head Htu).
  - apply (CIH (stail s) (stail t) (stail u)).
    + exact (bisim_tail Hst).
    + exact (bisim_tail Htu).
Qed.

Definition bisim_equivalence : Equivalence bisim :=
  Build_Equivalence bisim bisim_refl bisim_sym bisim_trans.

(* The stream setoid: streams under bisimilarity. / 流集合：在双模拟下的流。 *)
#[export] Instance Stream_Setoid : Setoid Stream :=
  {| equiv := bisim ; setoid_equiv := bisim_equivalence |}.

Definition Stream_SO : SetoidObject :=
  {| carrier := Stream ; is_setoid := Stream_Setoid |}.

(*
 The head/tail endofunctor [StreamF X = A × X].  Objects use the product
 setoid of [Sets]; on morphisms it keeps the head and applies [f] to the
 tail component. 

 --------
 头/尾端函子 [StreamF X = A × X]。对象使用 [Sets] 的乘积集合；在态射上，它保持头部并将 [f] 应用于尾部组件。
*)

#[local] Obligation Tactic := idtac.

Program Definition StreamF_fmap {X Y : SetoidObject} (f : X ~{Sets}~> Y) :
  @product_obj Sets Sets_Cartesian A X ~{Sets}~>
  @product_obj Sets Sets_Cartesian A Y :=
  {| morphism := fun p => (fst p, f (snd p)) |}.
Next Obligation.
  intros X Y f a b Hab.
  destruct Hab as [H1 H2].
  split.
  - exact H1.
  - now rewrite H2.
Qed.

Program Definition StreamF : Sets ⟶ Sets := {|
  fobj := fun X => @product_obj Sets Sets_Cartesian A X ;
  fmap := fun X Y f => StreamF_fmap f
|}.
Next Obligation.
  intros X Y f g Hfg p.
  split.
  - reflexivity.
  - exact (Hfg (snd p)).
Qed.
Next Obligation.
  intros X p.
  split.
  - reflexivity.
  - reflexivity.
Qed.
Next Obligation.
  intros X Y Z f g p.
  split.
  - reflexivity.
  - reflexivity.
Qed.

(* The stream coalgebra [γ s = (shead s, stail s)]. / 流煤代数 [γ s = (shead s, stail s)] 。 *)
Program Definition gamma : Stream_SO ~{Sets}~> StreamF Stream_SO :=
  {| morphism := fun s => (shead s, stail s) |}.
Next Obligation.
  intros a b Hab.
  split.
  - exact (bisim_head Hab).
  - exact (bisim_tail Hab).
Qed.

(*
 Packaged as an object of [FCoalg StreamF] (an [StreamF^op]-algebra in
 [Sets^op] read covariantly). 

 --------
 作为 [FCoalg StreamF] 的一个对象打包（在 [Sets^op] 中按协变方式读取的 [StreamF^op]-代数）。
*)
Definition Stream_coalg : FCoalg StreamF := (Stream_SO; gamma).

(* The anamorphism: unfold a coalgebra [(X, c)] into a stream by corecursion. / 拟态：通过余归纳将一个余代数 [(X, c)] 展开成一个流。 *)
CoFixpoint ana_fn (X : SetoidObject) (c : X ~{Sets}~> StreamF X)
  (x : carrier X) : Stream :=
  SCons (fst (c x)) (ana_fn X c (snd (c x))).

(*
 The anamorphism respects [≈]: [≈]-related states unfold to bisimilar
 streams. 

 --------
 自形态遵循 [≈] : [≈] 相关的状态展开为双模相似的流。
*)
Lemma ana_proper (X : SetoidObject) (c : X ~{Sets}~> StreamF X) :
  ∀ x y, x ≈ y → bisim (ana_fn X c x) (ana_fn X c y).
Proof.
  cofix CIH.
  intros x y Hxy.
  assert (Hc : c x ≈ c y) by (apply proper_morphism; exact Hxy).
  destruct Hc as [H1 H2].
  constructor.
  - exact H1.
  - exact (CIH (snd (c x)) (snd (c y)) H2).
Qed.

Definition ana (X : SetoidObject) (c : X ~{Sets}~> StreamF X) :
  X ~{Sets}~> Stream_SO :=
  {| morphism := ana_fn X c ; proper_morphism := ana_proper X c |}.

(*
 Uniqueness, generalised over an intermediate state [s] bisimilar to [h x]
 so that the corecursive call sits under [Bisim] with a non-corecursive
 proof of its premise.  Here [h] is any coalgebra map satisfying the
 head/tail transition equations [Hh1]/[Hh2]. 

 --------
 唯一性，通过一个与  [h x]  双模态的中间状态  [s]  广义化，因此核心递归调用位于  [Bisim]  下，并且其前提有一个非核心递归的证明。这里  [h]  是任何满足头/尾转换方程  [Hh1] / [Hh2] 的余代数映射。
*)
Lemma ana_unique_gen (X : SetoidObject) (c : X ~{Sets}~> StreamF X)
  (h : carrier X → Stream)
  (Hh1 : ∀ x, shead (h x) ≈ fst (c x))
  (Hh2 : ∀ x, bisim (stail (h x)) (h (snd (c x)))) :
  ∀ s x, bisim s (h x) → bisim s (ana_fn X c x).
Proof.
  cofix CIH.
  intros s x Hs.
  pose proof (bisim_head Hs) as Hhead.
  pose proof (bisim_tail Hs) as Htail.
  constructor.
  - transitivity (shead (h x)).
    + exact Hhead.
    + exact (Hh1 x).
  - exact (CIH (stail s) (snd (c x))
             (bisim_trans (stail s) (stail (h x)) (h (snd (c x)))
                Htail (Hh2 x))).
Qed.

(*
 [Stream_coalg] is the final object of [FCoalg StreamF]: for every coalgebra
 there is exactly one coalgebra map into the streams (up to bisimilarity). 

 --------
 [Stream_coalg] 是 [FCoalg StreamF] 的终对象：对于每个余代数，恰好存在一个余代数映射到流中（至双模拟相似性）。
*)
Definition Stream_final : @Terminal (FCoalg StreamF).
Proof.
  unshelve refine {| terminal_obj := Stream_coalg |}.
  - (* the unique coalgebra map is the anamorphism / 唯一的余代数映射是自态射 *)
    intro y.
    refine {| falg_hom := (ana (`1 y) (`2 y) : Stream_SO ~{(Sets^op)}~> `1 y) |}.
    (* the coalgebra-hom square, componentwise by the corecursive equation / 通过余递归方程，按组成部分来处理余代数同态平方 *)
    intro x.
    split.
    + reflexivity.
    + apply bisim_refl.
  - (* uniqueness: any two coalgebra maps are pointwise bisimilar / 唯一性：任意两个余代数映射在每一点上都是双模相似的 *)
    intros y f g.
    destruct f as [hf Hf].
    destruct g as [hg Hg].
    intro x.
    (* extract the head/tail transition equations of each map / 提取每个映射的头/尾转换方程 *)
    assert (Hf1 : ∀ z, shead (hf z) ≈ fst ((`2 y) z))
      by (intro z; exact (fst (Hf z))).
    assert (Hf2 : ∀ z, bisim (stail (hf z)) (hf (snd ((`2 y) z))))
      by (intro z; exact (snd (Hf z))).
    assert (Hg1 : ∀ z, shead (hg z) ≈ fst ((`2 y) z))
      by (intro z; exact (fst (Hg z))).
    assert (Hg2 : ∀ z, bisim (stail (hg z)) (hg (snd ((`2 y) z))))
      by (intro z; exact (snd (Hg z))).
    apply (bisim_trans (hf x) (ana_fn (`1 y) (`2 y) x) (hg x)).
    + apply (ana_unique_gen (`1 y) (`2 y) hf Hf1 Hf2 (hf x) x).
      apply bisim_refl.
    + apply bisim_sym.
      apply (ana_unique_gen (`1 y) (`2 y) hg Hg1 Hg2 (hg x) x).
      apply bisim_refl.
Defined.

End Streams.
