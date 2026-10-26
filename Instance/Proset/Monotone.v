Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Two.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Functors between prosets are monotone maps

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §I.3
   (printed p. 15), Exercise 3(a) [maclane:I.3:ex3]: a functor between
   two preorders regarded as categories is exactly a monotone map.
   Riehl, “Category Theory in Context”, §1.3 Exercise 1.3.ii
   [riehl:1.3:exii]: the same question, and the sharpening that the
   correspondence should carry NO decidability hypothesis.
   Fong and Spivak, “Seven Sketches in Compositionality”, §3.3.2
   Example 3.42 [7sketches:3.3.2:example3.42] (the identification,
   worked at the naturals), §1.2.3 Examples 60 and 61
   [7sketches:1.2.3:example60, example61] (the 17/24 witness, and the
   tree-of-life rank map).

   THE ORDINARY CORRESPONDENCE, decidability-free.  Two fragments
   predate this file.  Construction/Enriched/Two.v's
   [EnrichedFunctor_Two_monotone] is 2-ENRICHED, and its reverse leg
   genuinely case-splits on the [TwoPreorder] decidability field
   [tpre_dec] — a hypothesis Riehl's exercise does not impose.
   Instance/Pos.v's [MonotoneAsFunctor] is ordinary and
   decidability-free but is the FORWARD leg only, for posets bundled
   as [PosetObject]s.  What this file adds is the full correspondence
   over arbitrary prosets — both legs and both round trips, with no
   decision procedure anywhere: the forward leg reads monotonicity
   off [fmap], the backward leg USES the thinness of the target — in
   a thin category the functor laws are automatic, every hom-setoid
   being a subsingleton, which is the observation (Seven Sketches
   §3.3.2's, and Pos.v's, made once in the general setting) that
   [Functor_of_monotone] operationalizes as a smart constructor.

   ROUND TRIPS.  Monotone → functor → monotone returns the same map on
   the nose ([monotone_of_Functor_of_monotone]); functor → monotone →
   functor returns the same functor up to the thin-category
   identification, i.e. up to [Functor_Setoid]'s natural isomorphism,
   with identity-arrow components ([Functor_of_monotone_of_Functor]).

   WITNESSES.
   - [seventeen_twentyfour] (Example 60): the monotone map from the
   two-element order (bool under false ≤ true) to (ℕ, ≤) sending
   bottom to 17 and top to 24 — the first concrete [MonotoneFun]
   inhabitant, its functor [Seventeen_TwentyFour_Proset] obtained
   through the smart constructor.  Alongside it,
   [Seventeen_TwentyFour] reads the same map out of the library's
   walking arrow as a functor [_2 ⟶ LessThanEqualTo_Category],
   hand-built: [_2] is presented with strict-equality homs rather
   than as a [Proset], so it sits outside the correspondence's
   domain.
   - [nondecreasing] (Example 3.42's payload): endofunctors of
   (ℕ, ≤) are exactly the non-decreasing sequences, a named
   instantiation of the correspondence.
   - [taxonomy_rank] (Example 61): a PRESENTED tree preorder — five
   classification terms with four generating edges, closed under
   reflexivity-transitivity by [clos_refl_trans] — mapped to the
   three-element chain of ranks, with monotonicity proved by
   INDUCTION ON THE GENERATING RELATION (one case per edge, plus the
   closure rules) rather than by enumerating the closure. 

   --------
   * * 前序集之间的函子是单调映射

   Mac Lane，《为工作数学家准备的范畴论》，第2版，第I.3节
   （印刷版第15页），练习3(a)  [maclane:I.3:ex3]：两个被视为范畴的前序集之间的函子正好是一个单调映射。
   Riehl，《上下文中的范畴论》，第1.3节，练习1.3.ii
   [riehl:1.3:exii]：同样的问题，以及加强版，即对应关系不应携带任何可判定性假设。
   Fong 和 Spivak，《组合性的七个示意》，第3.3.2节
   例3.42  [7sketches:3.3.2:example3.42]（在自然数上处理的识别），第1.2.3节 例60和61
   [7sketches:1.2.3:example60, example61]（17/24 证据，以及生命树等级映射）。普通对应，无可判定性。两个片段出现在这个文件之前。Construction/Enriched/Two.v 的 [EnrichedFunctor_Two_monotone] 是 2-ENRICHED，其反向部分确实对 [TwoPreorder] 的可判定性字段 [tpre_dec] 进行了情形拆分——这是 Riehl 的练习没有强加的假设。Instance/Pos.v 的 [MonotoneAsFunctor] 是普通且无可判定性的，但只是正向部分，对于以 [PosetObject] 打包的偏序集合。这个文件增加的是关于任意序对（prosets）的完整对应——包括正向和反向的两个行程，没有任何决策程序：正向行程从 [fmap] 中读取单调性，反向行程使用目标的稀疏性——在稀疏类别中函子律是自动成立的，每个 Hom-集合（hom-setoid）都是单子集（subsingleton），这是观察到的（Seven Sketches §3.3.2 及 Pos.v 在一般设置中的一次性观察）并且 [Functor_of_monotone] 将其运作化为一个智能构造器。

   循环往返（ROUND TRIPS）。单调 → 函子 → 单调会精确返回相同的映射（[monotone_of_Functor_of_monotone]）；函子 → 单调 → 函子会在稀疏类别识别下返回相同函子，即在 [Functor_Setoid] 的自然同构下，具有恒等箭头组成部分（[Functor_of_monotone_of_Functor]）。见证者。- [seventeen_twentyfour]（示例 60）：从两个元素的序（布尔值在 false ≤ true 下）到（ℕ, ≤）的单调映射，将底元素映射为 17，顶元素映射为 24——第一个具体的 [MonotoneFun] 成员，其函子 [Seventeen_TwentyFour_Proset] 通过智能构造器获得。与此一起，[Seventeen_TwentyFour] 从库的 walking arrow 中以函子 [_2 ⟶ LessThanEqualTo_Category] 读取相同的映射，手工构建：[_2] 以严格相等的同态呈现，而不是作为 [Proset]，因此它位于对应关系域之外。- [nondecreasing]（示例 3.42 的有效负载）：(ℕ, ≤) 的自函子正是非递减序列，是该对应关系的一个命名实例。- [taxonomy_rank]（示例 61）：一个呈现的树的前序——五个分类项和四条生成边，在 [clos_refl_trans] 的自反-传递闭包下——映射到秩的三元素链，其单调性通过对生成关系的归纳（每条边一个情况，加上闭包规则）而不是通过枚举闭包来证明。
*)

(* * ** Monotone maps, and the correspondence / * ** 单调映射及对应关系 *)

Section Monotone.

Context {A : Type} {R : relation A} (P : PreOrder R).
Context {B : Type} {S : relation B} (Q : PreOrder S).

(* A monotone map between the underlying preorders: no decidability, no packaging — just the order-preserving function. / 基础预序之间的单调映射：没有可判定性，没有封装——只是保持顺序的函数。 *)
Record MonotoneFun := {
  mono_map :> A → B;
  mono_pres : ∀ x y, R x y → S (mono_map x) (mono_map y)
}.

(*
 The thin-category smart constructor: BECAUSE the target is a proset —
 every hom-setoid a subsingleton with the all-True equivalence — the
 functor laws cost nothing.  This is Seven Sketches §3.3.2's “the
 functor laws are automatic in a thin category”, operationalized.
 The file sets [Obligation Tactic := idtac] (Pos.v's idiom), so the
 three laws are discharged explicitly: each is an equation between
 parallel morphisms in a thin target, hence [I]. 

 --------
 薄范畴的智能构造器：因为目标是一个预序集合——每个同态集合都是带有全真等价关系的亚单元——函子律不费力。这是《七个草图》第3.3.2节的“在薄范畴中，函子律是自动的”的操作实现。文件设置了 [Obligation Tactic := idtac]（Pos.v 的惯用法），所以这三条律被明确解除：每一条都是薄目标中平行态射之间的等式，因此 [I]。
*)
Program Definition Functor_of_monotone (f : MonotoneFun) :
  Proset P ⟶ Proset Q := {|
  fobj := mono_map f;
  fmap := fun x y (h : R x y) => mono_pres f x y h
|}.
Next Obligation. intros f x y g h Hgh; exact I. Qed.
Next Obligation. intros f x; exact I. Qed.
Next Obligation. intros f x y z g h; exact I. Qed.

(*
 The forward leg: a functor restricts to a monotone map on objects,
 monotonicity being the action on (unique) arrows. 

 --------
 前向函数：函子在对象上限制为单调映射，单调性体现在（唯一）箭头上的作用。
*)
Definition monotone_of_Functor (F : Proset P ⟶ Proset Q) : MonotoneFun := {|
  mono_map := fobj[F];
  mono_pres := fun x y h => fmap[F] h
|}.

(* Round trip on the monotone side: the same map, on the nose. / 单调一边的往返：同一张地图，正中目标。 *)
Lemma monotone_of_Functor_of_monotone (f : MonotoneFun) :
  mono_map (monotone_of_Functor (Functor_of_monotone f)) = mono_map f.
Proof. reflexivity. Qed.

(*
 Round trip on the functor side: the same functor up to the thin
 identification — a [Functor_Setoid] natural isomorphism whose
 components are identity arrows. 

 --------
 函子一侧的往返：相同的函子，直到薄身份——一个 [Functor_Setoid] 自然同构，其分量是恒等箭头。
*)
Lemma Functor_of_monotone_of_Functor (F : Proset P ⟶ Proset Q) :
  Functor_of_monotone (monotone_of_Functor F) ≈ F.
Proof.
  exists (fun x => iso_id).
  intros x y h; simpl.
  constructor.
Qed.

End Monotone.

(* * ** Example 60: the 17/24 monotone map / * ** 示例 60：17/24 单调映射 *)

(* The two-element order as a preorder on [bool]: false ≤ true. / 在 [bool] 上作为前序的二元素顺序：false ≤ true。 *)
Definition bool_le (a b : bool) : Prop := a = true → b = true.

#[export] Instance bool_le_preorder : PreOrder bool_le.
Proof.
  constructor.
  - intros a H; exact H.
  - intros a b c Hab Hbc H; exact (Hbc (Hab H)).
Qed.

(* The monotone map itself — the notion's first concrete inhabitant. / 单调映射本身——这一概念的第一个具体体现者。 *)
Program Definition seventeen_twentyfour :
  @MonotoneFun bool bool_le nat Nat.le := {|
  mono_map := fun b : bool => if b then 24%nat else 17%nat
|}.
Next Obligation.
  intros x y H; destruct x, y.
  - exact (le_n 24).
  - discriminate (H eq_refl).
  - repeat constructor.
  - exact (le_n 17).
Qed.

(* ...and its functor, through the smart constructor. / ...以及它的函子，通过智能构造器。 *)
Definition Seventeen_TwentyFour_Proset :
  Proset bool_le_preorder ⟶ LessThanEqualTo_Category :=
  Functor_of_monotone bool_le_preorder Nat.le_preorder
    seventeen_twentyfour.

Example Seventeen_TwentyFour_Proset_bot :
  Seventeen_TwentyFour_Proset false = 17%nat := eq_refl.
Example Seventeen_TwentyFour_Proset_top :
  Seventeen_TwentyFour_Proset true = 24%nat := eq_refl.

(*
 The same map read out of the library's walking arrow [_2] —
 hand-built, since [_2] is not presented as a [Proset] (its homs are
 an inductive type compared by strict equality), so it sits outside
 the correspondence's domain. 

 --------
 从图书馆的行走箭头 [_2] 读取的同一张地图——手工构建的，因为 [_2] 并未呈现为 [Proset]（其 hom 是通过严格相等比较的归纳类型），所以它位于对应域之外。
*)
Program Definition Seventeen_TwentyFour : _2 ⟶ LessThanEqualTo_Category := {|
  fobj := fun x => match x with TwoX => 17%nat | TwoY => 24%nat end;
  fmap := fun x y f => _
|}.
Next Obligation.
  intros x y f; destruct x, y.
  - exact (le_n 17).
  - repeat constructor.
  - inversion f.
  - exact (le_n 24).
Defined.
(*
 [_2]'s homset is strict equality, so the [Proper] law is inferred
 during elaboration; only the two remaining laws obligate, each an
 equation between parallel morphisms in a thin target. 

 --------
 [_2] 的同态集合是严格相等的，所以 [Proper] 定律在推导过程中被推断出来；只有剩下的两个定律是强制的，每个定律都是在薄目标中平行态射之间的一个方程。
*)
Next Obligation. intros x; exact I. Qed.
Next Obligation. intros x y z f g; exact I. Qed.

Example Seventeen_TwentyFour_bot : Seventeen_TwentyFour TwoX = 17%nat
  := eq_refl.
Example Seventeen_TwentyFour_top : Seventeen_TwentyFour TwoY = 24%nat
  := eq_refl.

(* * ** Example 3.42's payload: endofunctors of (ℕ, ≤) are the non-decreasing sequences / * ** 示例 3.42 的内容：(ℕ, ≤) 的端函子是非递减序列 *)

Definition nondecreasing (f : nat → nat) : Type :=
  ∀ m n : nat, (m <= n)%nat → (f m <= f n)%nat.

(*
 The pair is built with the family and both component types
 explicit: [x ~> y] in [LessThanEqualTo_Category] IS [x <= y] and
 its objects ARE [nat], but Coq 8.19/8.20's unifier declines to
 unfold the [hom] and [obj] projections inside the evar problems
 that infer a sigma pair's parts, while ascriptions route the same
 identifications through ordinary conversion, which every supported
 version performs. 

 --------
 该对是用族和两种组件类型构建的
 显式：[x ~> y] 在 [LessThanEqualTo_Category] 中 IS [x <= y] 并且
 其对象为 [nat]，但 Coq 8.19/8.20 的统一器拒绝展开 evar 问题中推断 sigma 对部分的 [hom] 和 [obj] 投影，而归属通过普通转换路由相同的标识，每个支持的版本都执行该操作。
*)
Definition nondecreasing_of_endo
  (F : LessThanEqualTo_Category ⟶ LessThanEqualTo_Category) :
  { f : nat → nat & nondecreasing f } :=
  existT nondecreasing (fobj[F] : nat → nat)
    (fun m n (h : (m <= n)%nat) =>
       (fmap[F] h : (fobj[F] m <= fobj[F] n)%nat)).

Definition endo_of_nondecreasing
  (f : { f : nat → nat & nondecreasing f }) :
  LessThanEqualTo_Category ⟶ LessThanEqualTo_Category :=
  Functor_of_monotone Nat.le_preorder Nat.le_preorder
    {| mono_map := `1 f ; mono_pres := `2 f |}.

Example nondecreasing_round (f : { f : nat → nat & nondecreasing f }) :
  `1 (nondecreasing_of_endo (endo_of_nondecreasing f)) = `1 f := eq_refl.

(* * ** Example 61: the tree of life, by generators / * ** 示例 61：生命之树，由生成器生成 *)

(*
 Five classification terms: a tiny fragment of the tree of life.
 The GENERATING edges point from the more specific to the more
 general term; the preorder is their reflexive-transitive closure. 

 --------
 五个分类术语：生命树的一小片段。
 生成边从更具体的术语指向更一般的术语；前序是它们的自反传递闭包。
*)
Inductive Taxon : Set := Life | Animal | Plant | Mammal | Bird.

Inductive taxon_edge : Taxon → Taxon → Prop :=
  | edge_animal : taxon_edge Animal Life
  | edge_plant  : taxon_edge Plant Life
  | edge_mammal : taxon_edge Mammal Animal
  | edge_bird   : taxon_edge Bird Animal.

Definition taxon_le : relation Taxon := clos_refl_trans _ taxon_edge.

#[export] Instance taxon_le_preorder : PreOrder taxon_le.
Proof.
  constructor.
  - intro x; apply rt_refl.
  - intros x y z Hxy Hyz; exact (rt_trans _ _ _ _ _ Hxy Hyz).
Qed.

(*
 The three-element chain of ranks: species-level < kingdom-level <
 root, encoded as 0 < 1 < 2 under ≤. 

 --------
 等级的三元素链：物种级 < 界级 < 根，编码为 0 < 1 < 2 在 ≤ 下。
*)
Definition rank (t : Taxon) : nat :=
  match t with
  | Life => 2
  | Animal | Plant => 1
  | Mammal | Bird => 0
  end.

(*
 Monotonicity from the GENERATING relation: one case per edge — each
 generator raises the rank — and the two closure rules; the closure is
 never enumerated. 

 --------
 来自生成关系的单调性：每条边一个情况——每个生成元都会提升秩——以及两个闭包规则；闭包从不被枚举。
*)
Lemma rank_monotone : ∀ s t, taxon_le s t → (rank s <= rank t)%nat.
Proof.
  intros s t H.
  induction H as [x y Hxy | x | x y z Hxy IH1 Hyz IH2].
  - destruct Hxy; simpl; repeat constructor.
  - reflexivity.
  - exact (Nat.le_trans _ _ _ IH1 IH2).
Qed.

Definition Taxonomy : Category := Proset taxon_le_preorder.

Definition taxonomy_rank : Taxonomy ⟶ LessThanEqualTo_Category :=
  Functor_of_monotone taxon_le_preorder Nat.le_preorder
    {| mono_map := rank ; mono_pres := rank_monotone |}.

Example taxonomy_rank_mammal : taxonomy_rank Mammal = 0%nat := eq_refl.
Example taxonomy_rank_life : taxonomy_rank Life = 2%nat := eq_refl.
