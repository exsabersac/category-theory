Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Theory.Lambek.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Adamek.Corollaries.

Generalizable All Variables.

(* * * The natural numbers as the initial algebra of [NatF] over COQ / * * 自然数作为 COQ 上 [NatF] 的初始代数 *)

(*
 nLab:      https://ncatlab.org/nlab/show/natural+numbers+object
 Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

 The polynomial endofunctor [NatF X := option X = 1 + X] on COQ
 (Theory/Adamek/Corollaries.v) has the type [nat] as its initial algebra.
 The structure map [nat_alg : 1 + nat ~> nat] is [O]/[S] ([None ↦ O],
 [Some k ↦ S k]), and initiality is exactly primitive recursion: for every
 [NatF]-algebra [β : 1 + Y ~> Y] there is a unique algebra map
 [nat ~> Y], namely the fold determined by [β].  Uniqueness is the induction
 that any algebra map into [(Y, β)] agrees with the fold.

 This exhibits [nat] as the least fixed point [μ NatF]; by Lambek's lemma
 (Theory/Lambek.v) the structure map is then an isomorphism
 [1 + nat ≅ nat], recorded below as [nat_lambek].  As in Instance/Coq/Lists.v
 the development stays within pointwise equality on COQ hom-sets and ordinary
 [nat] induction, so it carries no axioms (in particular no functional
 extensionality).

 Three readings of the same theorem are carried explicitly, because the
 sources state it in three different vocabularies:

 - Mac Lane's and Riehl's TRIPLES ⟨X, x₀, f⟩.  A [NatF]-algebra
 [α : 1 + X ~> X] is precisely a point together with an endomap, and the
 commuting square of an algebra map is precisely the pair of clauses
 [h x₀ ≈ x₀'] and [h ∘ f ≈ f' ∘ h].  [alg_of_triple]/[alg_pt]/[alg_step]
 and [alg_hom_clauses]/[clauses_alg_hom] are that dictionary, stated as
 lemmas rather than left as a remark, and [nat_recursion] restates
 initiality in the resulting clause form: a unique [h] with [h O = y₀]
 and [h (S n) = f (h n)].

 - Awodey's characterisation UP TO ISOMORPHISM.  [nat_initial_unique] shows
 that any initial algebra of [NatF] is isomorphic to [(nat, [O, S])] by an
 isomorphism *of algebras* — an isomorphism in [FAlg NatF], not merely a
 bijection of carriers, which [nat_initial_carrier_unique] then reads off.

 - Riehl's REPRESENTABILITY.  [Endos := FAlg Id[Coq]] is the category of
 sets with an endomorphism, [Endos_Forget] its forgetful functor to
 [Sets], and [nat_succ_represents] the natural isomorphism exhibiting
 [(nat, S)] as a representing object with universal element [O]
 ([nat_universal_element]).  [repr_initial] is the universal-element
 criterion for this functor: a representation of [Endos_Forget] makes the
 algebra built from the representing object and its universal element
 initial in [FAlg NatF].  [nat_initial_via_universal_element] is
 a second, independent construction of the same initial object through
 that criterion (its mediator is [nat_iter], not [nat_fold]; the two
 records are distinct terms), and [nat_initial_agree] checks by
 [reflexivity] that the two constructions name the same algebra. 

 --------
 nLab：https://ncatlab.org/nlab/show/natural+numbers+object
 Wikipedia：https://en.wikipedia.org/wiki/Initial_algebra

 COQ 上的多项式自函子 [NatF X := option X = 1 + X] （Theory/Adamek/Corollaries.v）具有类型 [nat] 作为其初代代数。结构映射 [nat_alg : 1 + nat ~> nat] 为 [O] / [S]（[None ↦ O], [Some k ↦ S k]），而初等性恰好是原始递归：对于每个 [NatF]-代数 [β : 1 + Y ~> Y]，都存在唯一的代数映射 [nat ~> Y]，即由 [β] 决定的 fold。唯一性是指任何指向 [(Y, β)] 的代数映射都与 fold 一致的归纳。这展示了 [nat] 作为最小不动点 [μ NatF]；根据 Lambek 引理（Theory/Lambek.v），结构映射则是一个同构 [1 + nat ≅ nat]，下文记录为 [nat_lambek]。与 Instance/Coq/Lists.v 相同，发展保持在 COQ 同态集上的逐点相等性和普通的 [nat] 归纳内，因此不涉及公理（特别是没有函数外延性）。

 同一条定理的三种表述被明确列出，因为来源用三种不同的术语来说明它：- Mac Lane 和 Riehl 的三元组 ⟨X, x₀, f⟩。一个 [NatF] -代数 [α : 1 + X ~> X] 精确地是一个点及其自映射，而代数映射的交换方正精确地对应于 [h x₀ ≈ x₀'] 和 [h ∘ f ≈ f' ∘ h] 这对条款。[alg_of_triple] / [alg_pt] / [alg_step] 和 [alg_hom_clauses] / [clauses_alg_hom] 是那个字典，以引理的形式陈述，而不是作为备注保留，[nat_recursion] 以结果条款形式重述初始性：存在唯一的 [h] ，满足 [h O = y₀] 和 [h (S n) = f (h n)]。

 - Awodey 的同构意义上的特征化。[nat_initial_unique] 显示 [NatF] 的任何初始代数都同构于 [(nat, [O, S]，通过一个*代数同构*——在 [FAlg NatF] 中的同构，而不仅仅是载体的双射，[nat_initial_carrier_unique] 因此可以直接解读出来。- Riehl的可表示性。[Endos := FAlg Id[Coq] 是带有一个自同态的集合范畴，[Endos_Forget] 是其到 [Sets] 的忘记函子，[nat_succ_represents] 是自然同构，它展示了 [(nat, S)] 作为具有普遍元素 [O] ([nat_universal_element]) 的表示对象。[repr_initial] 是该函子的普遍元素判据：对 [Endos_Forget] 的表示使得由表示对象及其普遍元素构建的代数在 [FAlg NatF] 中成为初始对象。[nat_initial_via_universal_element] 是通过该判据对相同初始对象的第二个、独立的构造（其中介是 [nat_iter]，而不是 [nat_fold]；这两个记录是不同的项），而 [nat_initial_agree] 通过 [reflexivity] 检查这两个构造是否命名同一个代数。
*)

(*
 Where the statement comes from, and what it is used for

 nLab:      https://ncatlab.org/nlab/show/natural+numbers+object
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §I.5, Exercise 8, p. 21
 Book:      Awodey, “Category Theory” (1st ed., Carnegie Mellon
 pre-print, September 2005), §10.5 and Exercise 10.6.1(c)
 Book:      Riehl, “Category Theory in Context” (2nd ed. numbering,
 per issue #252),
 Example 2.1.1 and Example 2.4.11
 Paper:     Lawvere, “An elementary theory of the category of sets”,
 PNAS 52, 1964
 Paper:     Lambek, “A Fixpoint Theorem for Complete Categories”,
 Mathematische Zeitschrift 103, 1968

 Mac Lane poses the result as an exercise in the chapter on monics, epis
 and zeros: in the category whose objects are triples ⟨X, e, t⟩ — a set,
 a point of it, and an endomap — and whose arrows are the maps commuting
 with both, the triple ⟨ℕ, 0, successor⟩ is initial (CWM §I.5, Ex 8).
 The same universal property is the natural numbers object, a notion
 Lawvere introduced in the setting of an elementary theory of the
 category of sets: arithmetic is fixed by a mapping property and not by
 any particular set-theoretic implementation (Lawvere 1964; nLab,
 “natural numbers object”).  Awodey draws the consequence that the
 classical recursion theorem IS this initiality (§10.5), and asks in
 Exercise 10.6.1(c) for the same statement in its uniqueness form, that
 the property determines ℕ up to isomorphism.

 Riehl states the identical property twice from two different angles,
 which is why this file carries two proofs of it.  Example 2.1.1
 presents ⟨X, f, x₀⟩ as a discrete dynamical system and ⟨ℕ, succ, 0⟩ as
 the initial one; Example 2.4.11 re-derives the same fact from
 representability, observing that the category of such systems is the
 category of elements of the forgetful functor from sets-with-an-
 endomorphism to sets, that this functor is represented by (ℕ, succ)
 with universal element 0, and that a universal element is initial in
 the category of elements.  In this library that category of elements
 needs no separate construction: an object of [FAlg NatF] is a carrier
 with a point and an endomap, which is exactly a pair of an object of
 [Endos] and an element of its image under [Endos_Forget], and an
 arrow of [FAlg NatF] is exactly an arrow of [Endos] carrying one point
 to the other.  [repr_initial] therefore states the criterion directly
 over [FAlg NatF]; the deviation from Riehl is one of packaging, not of
 content.  The tree carries no [el(F)] for a [Sets]-valued functor to
 instantiate instead, though the header of Construction/Grothendieck.v
 notes that restricting the Grothendieck fibres to discrete categories
 would recover it.

 The computational reading is the reason the initiality matters here.
 Lambek (1968) observed that the structure map of an initial algebra is
 invertible, so [nat] is a fixed point of [1 + (-)]; the unique algebra
 map out of it is the fold, which Theory/Recursion.v names [cata] and
 whose defining square is the recursion equation.  Instance/Coq/Lists.v
 proves the structurally identical statement one parameter up, with
 [list A] initial for [ListF A X := 1 + A × X]; [NatF] is the [A := unit]
 reading of that functor up to [unit × X ≅ X].  Theory/Adamek.v
 constructs initial algebras in general as ω-colimits, but its
 [AdamekData] leg-agreement hypothesis has no concrete in-tree witness
 (see the header of Theory/Adamek/Corollaries.v), so — as with the list
 algebra — the initial [NatF]-algebra is established here directly
 rather than through that route. 

 --------
 该陈述的来源及其用途

 nLab:       https://ncatlab.org/nlab/show/natural+numbers+object
 书籍:      Mac Lane，《为在职数学家而作的范畴论》，第二版，
 Springer GTM 5, 1998, §I.5, 练习题 8, 第 21 页
 书籍:      Awodey，《范畴论》（第一版，卡内基梅隆预印本，2005 年 9 月），
 §10.5 和 练习题 10.6.1(c)
 书籍:      Riehl，《语境中的范畴论》（第二版编号，
 见第 252 期），
 示例 2.1.1 和 示例 2.4.11
 论文:     Lawvere，《集合范畴的初等理论》，
 PNAS 52, 1964
 论文:     Lambek，《完备范畴的不动点定理》，
 Mathematische Zeitschrift 103, 1968Mac Lane 在关于单射、满射和零的章节中以练习的形式提出这个结果：在对象为三元组 ⟨X, e, t⟩ —— 一个集合、其上的一个元素以及一个自映射 —— 且箭头为同时与两者交换的映射的范畴中，三元组 ⟨ℕ, 0, successor⟩ 是初始的（CWM §I.5, 练习 8）。相同的泛性质就是自然数对象，这是 Lawvere 在集合的范畴的初等理论背景下引入的概念：算术是由映射性质决定的，而不是由任何特定的集合论实现决定的（Lawvere 1964；nLab，“natural numbers object”）。Awodey 推出了一个结论，即经典的递归定理就是这种初始性（§10.5），并在练习 10.6.1(c) 中要求用唯一性形式来说明同样的命题，即该性质将 ℕ 确定到同构类。Riehl 从两个不同的角度两次陈述了相同的性质，这就是为什么这个文件包含两个关于它的证明。例 2.1.1 将 ⟨X, f, x₀⟩ 表示为一个离散动力系统，并将 ⟨ℕ, succ, 0⟩ 表示为初始系统；例 2.4.11 从可表示性重新推导了相同的事实，观察到此类系统的范畴是从带自同态的集合到集合的忘记函子的元素范畴，这个函子由 (ℕ, succ) 与普遍元素 0 表示，并且普遍元素在元素范畴中是初始的。在这个范畴中，这一类元素不需要单独构造：一个 [FAlg NatF] 的对象是一个带有一点和一个末自映的载体，这正好是一个 [Endos] 的对象和其在 [Endos_Forget] 下像中的一个元素的对偶，而 [FAlg NatF] 的箭正好是 [Endos] 的一个箭，将一个点映射到另一个点。因此 [repr_initial] 直接在 [FAlg NatF] 上陈述了判据；与 Riehl 的差异在于包装形式，而非内容。该树没有 [el(F)] 供 [Sets] 值函子实例化，尽管 Construction/Grothendieck.v 的头文件提到将 Grothendieck 纤维限制在离散范畴中可以恢复它。计算性阅读是这里初始性重要的原因。Lambek（1968）观察到初始代数的结构映射是可逆的，因此 [nat] 是 [1 + (-)] 的一个不动点；从它出发的唯一代数映射是折叠，Theory/Recursion.v 将其命名为 [cata]，其定义的方形即递归方程。Instance/Coq/Lists.v 证明了在高一层参数下结构上相同的命题，其中 [list A] 对于 [ListF A X := 1 + A × X] 是初始的；[NatF] 是该函子在 [unit × X ≅ X] 下的 [A := unit] 阅读。Theory/Adamek.v 一般将初始代数构造为 ω-余极限，但其 [AdamekData] 腿部一致性假设在具体树中没有证据（参见 Theory/Adamek/Corollaries.v 的标题），因此——与列表代数类似——初始 [NatF] 代数在这里是直接建立的，而不是通过那条路径。
*)

(*
 Keep obligation handling explicit and predictable, as in
 Instance/Coq/Lists.v: this file builds functor, natural-transformation and
 F-algebra-hom records whose remaining fields are commuting squares, and we
 want every one surfaced as its own obligation rather than silently
 discharged. 

 --------
 保持义务处理的明确性和可预测性，如在 Instance/Coq/Lists.v 中：该文件构建了函子、自然变换和 F-代数同态的记录，其剩余字段是交换方格，我们希望每一个都作为其自身的义务呈现，而不是被默默地完成。
*)
#[local] Obligation Tactic := idtac.

(* * ** Mac Lane's triples: algebras of [NatF] are points with an endomap / * ** 麦克莱恩的三元组： [NatF] 的代数是带有自映射的点 *)

(* The point of an algebra: the image of the [None] summand. / 代数的要点：[None] 直和项的像。 *)
Definition alg_pt {X : Type} (α : FAlgebra NatF X) : X := α None.

(* The endomap of an algebra: the restriction to the [Some] summand. / 一个代数的端映射：限制到 [Some] 子项。 *)
Definition alg_step {X : Type} (α : FAlgebra NatF X) : X ~{Coq}~> X :=
  fun x => α (Some x).

(* Conversely, a point and an endomap assemble into an algebra. / 相反，一个点和一个自映射组合成一个代数。 *)
Definition alg_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X)
  : FAlgebra NatF X :=
  fun o => match o with
           | None   => x0
           | Some x => f x
           end.

(*
 The two directions are mutually inverse: the triple read off an assembled
 algebra is the original triple, and the algebra assembled from the triple
 read off an algebra is the original algebra. 

 --------
 这两个方向是相互逆的：从组装好的代数中读出的三元组是原始三元组，而从从代数中读出的三元组组装出的代数是原始代数。
*)

Lemma alg_pt_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X) :
  alg_pt (alg_of_triple x0 f) = x0.
Proof. reflexivity. Qed.

Lemma alg_step_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X) :
  alg_step (alg_of_triple x0 f) ≈ f.
Proof. intro x; reflexivity. Qed.

Lemma alg_of_triple_eta {X : Type} (α : FAlgebra NatF X) :
  alg_of_triple (alg_pt α) (alg_step α) ≈ α.
Proof. intro o; destruct o as [x|]; reflexivity. Qed.

(*
 At the level of arrows, the commuting square of an algebra map is exactly
 Riehl's pair of clauses: the map carries point to point and intertwines the
 two endomaps. 

 --------
 在箭头层面上，代数映射的可交换方形正是里尔的两个条款：该映射将点对应到点，并交错两个自映射。
*)

Lemma alg_hom_clauses {X Y : Type}
      (α : FAlgebra NatF X) (β : FAlgebra NatF Y) (h : X ~{Coq}~> Y) :
  h ∘ α ≈ β ∘ fmap[NatF] h ->
  (h (alg_pt α) = alg_pt β) * (∀ x, h (alg_step α x) = alg_step β (h x)).
Proof.
  intro Hh; split.
  - exact (Hh None).
  - intro x; exact (Hh (Some x)).
Qed.

Lemma clauses_alg_hom {X Y : Type}
      (α : FAlgebra NatF X) (β : FAlgebra NatF Y) (h : X ~{Coq}~> Y) :
  h (alg_pt α) = alg_pt β ->
  (∀ x, h (alg_step α x) = alg_step β (h x)) ->
  h ∘ α ≈ β ∘ fmap[NatF] h.
Proof.
  intros H0 HS o; destruct o as [x|].
  - exact (HS x).
  - exact H0.
Qed.

(* * ** The algebra (nat, [O, S]) and its initiality / * ** 代数 (nat, [O, S]) 及其初始性 *)

(* The structure map of the natural-numbers algebra: [None] is [O] and [Some k] is [S k]. This is Mac Lane's triple ⟨ℕ, 0, successor⟩. / 自然数代数的结构映射：[None]是[O]，[Some k]是[S k]。这是Mac Lane的三重组⟨ℕ, 0, 后继⟩。 *)
Definition nat_alg : FAlgebra NatF nat := alg_of_triple O S.

(* The catamorphism (fold) determined by an algebra [β : 1 + Y ~> Y]. This is primitive recursion, and it is the carrier of the unique algebra map out of [(nat, nat_alg)]. / 由代数 [β : 1 + Y ~> Y] 决定的双态射（折叠）。这是原始递归，它是唯一从 [(nat, nat_alg)] 出来的代数映射的承载体。 *)
Fixpoint nat_fold {Y : Type} (beta : FAlgebra NatF Y) (n : nat) : Y :=
  match n with
  | O   => alg_pt beta
  | S k => alg_step beta (nat_fold beta k)
  end.

(*
 Any [NatF]-algebra map [h : (nat, nat_alg) ~> (Y, β)] coincides with the
 fold determined by [β].  This is the uniqueness half of initiality, proven
 by induction on [n] using the commuting-square hypothesis [Hh] at the two
 relevant argument shapes. 

 --------
 任何 [NatF] -代数映射 [h : (nat, nat_alg) ~> (Y, β)] 都与 [β] 所确定的折叠一致。这是初始性的唯一性部分，通过对 [n] 使用归纳法，并利用在两个相关参数形状下的交换方假设 [Hh] 证明的。
*)
Lemma hom_is_nat_fold {Y : Type} (beta : FAlgebra NatF Y)
      (h : nat ~{Coq}~> Y)
      (Hh : h ∘ nat_alg ≈ beta ∘ fmap[NatF] h)
      (n : nat) : h n = nat_fold beta n.
Proof.
  induction n as [|k IH].
  - exact (Hh None).
  - simpl.
    rewrite <- IH.
    exact (Hh (Some k)).
Qed.

(*
 The unique algebra map from [(nat, nat_alg)] to an arbitrary algebra [y],
 packaging the fold together with its commuting square. 

 --------
 从  [(nat, nat_alg)]  到任意代数  [y] 的唯一代数映射，将折叠及其交换方整合在一起。
*)
Program Definition nat_alg_hom (y : FAlg NatF)
  : (nat; nat_alg) ~{FAlg NatF}~> y :=
  {| falg_hom := nat_fold (`2 y) |}.
Next Obligation.
  (* fold ∘ nat_alg ≈ β ∘ fmap fold, checked shape by shape / fold ∘ nat_alg ≈ β ∘ fmap fold，逐形状检查 *)
  intros y o; destruct o as [k|]; reflexivity.
Qed.

(*
 [nat] together with [nat_alg] is the initial [NatF]-algebra: it is the
 terminal object of the opposite of the algebra category. 

 --------
 [nat] 连同 [nat_alg] 是初始的 [NatF] 代数：它是代数范畴的对偶范畴中的终对象。
*)
Program Definition nat_initial : @Initial (FAlg NatF) := {|
  terminal_obj := (nat; nat_alg);
  one := fun y => nat_alg_hom y
|}.
Next Obligation.
  (* uniqueness: any two algebra maps out of [(nat, nat_alg)] agree, since each coincides with the fold determined by the target algebra / 唯一性：从 [(nat, nat_alg)] 出发的任意两个代数映射都一致，因为每个映射都与目标代数确定的折叠相符 *)
  intros x f g.
  destruct f as [hf Hf], g as [hg Hg].
  intro n; simpl.
  rewrite (hom_is_nat_fold (`2 x) hf Hf n).
  rewrite (hom_is_nat_fold (`2 x) hg Hg n).
  reflexivity.
Qed.

(*
 Initiality spelled out in Riehl's clause form (Example 2.1.1): for a set
 [Y] with a point [y0] and an endomap [f] there is exactly one
 [h : nat ~> Y] with [h O = y0] and [h ∘ S ≈ f ∘ h].  This is the same
 content as [nat_initial] with the algebra packaging unwound, and it is the
 shape in which the recursion theorem is usually met. 

 --------
 在 Riehl 的子句形式中明确表达的初始性（示例 2.1.1）：对于一个集合 [Y]，具有一个点 [y0] 和一个自映射 [f]，存在且仅存在一个 [h : nat ~> Y]，使得 [h O = y0] 和 [h ∘ S ≈ f ∘ h] 成立。这与去掉代数封装的 [nat_initial] 的内容相同，并且这是递归定理通常出现的形式。
*)
Corollary nat_recursion {Y : Type} (y0 : Y) (f : Y ~{Coq}~> Y) :
  ∃! h : nat ~{Coq}~> Y, (h O = y0) * (∀ n, h (S n) = f (h n)).
Proof.
  exists (nat_fold (alg_of_triple y0 f)).
  - split; [ reflexivity | intro n; reflexivity ].
  - intros v [Hz Hs] n.
    symmetry.
    exact (hom_is_nat_fold (alg_of_triple y0 f) v
             (clauses_alg_hom nat_alg (alg_of_triple y0 f) v Hz Hs) n).
Qed.

(** ** Lambek's lemma at [nat] / ** Lambek 引理在 [nat] *)

(*
 The initial structure map is invertible, so [nat] is a fixed point of
 [1 + (-)]: the isomorphism [option nat ≅ nat] whose forward direction is
 [nat_alg] itself. 

 --------
 初始结构映射是可逆的，因此 [nat] 是 [1 + (-)] 的不动点：同构 [option nat ≅ nat]，其正向是 [nat_alg] 本身。
*)
Corollary nat_lambek : NatF nat ≅ nat.
Proof. exact (lambek NatF nat_initial). Qed.

(* The same isomorphism in the orientation [nat ≅ 1 + nat]. / 在方向 [nat ≅ 1 + nat] 中的相同同构。 *)
Corollary nat_lambek_sym : nat ≅ NatF nat.
Proof. exact (iso_sym nat_lambek). Qed.

(* * ** Awodey Ex 10.6.1(c): the characterisation up to isomorphism / * ** Awodey 练习 10.6.1(c)：同构下的刻画 *)

(*
 Any initial algebra of [NatF] is isomorphic to [(nat, nat_alg)] BY AN
 ISOMORPHISM OF ALGEBRAS — the isomorphism lives in [FAlg NatF], so both its
 directions are algebra maps.  The argument is the generic one for initial
 objects, spelled out inline because Structure/Initial.v carries no
 uniqueness-up-to-isomorphism lemma to appeal to — only [initial_obj],
 [zero], [zero_unique] and [zero_comp]: the two mediators compose to
 endomorphisms of initial objects, which [zero_unique] forces to be
 identities. 

 --------
 [NatF] 的任何初始代数都是 [(nat, nat_alg)] 的代数同构——这个同构存在于 [FAlg NatF] 中，因此它的两个方向都是代数映射。该论证是初始对象的一般性论证，这里逐步展开，因为 Structure/Initial.v 中没有唯一性至同构的引理可供引用——只有 [initial_obj]、[zero]、[zero_unique] 和 [zero_comp]：两个中介对象复合为初始对象的自同态，而 [zero_unique] 强制其为恒等映射。
*)
Theorem nat_initial_unique (I : @Initial (FAlg NatF)) :
  @initial_obj (FAlg NatF) I ≅[FAlg NatF] (nat; nat_alg).
Proof.
  unshelve refine {| to   := @zero (FAlg NatF) I (nat; nat_alg)
                   ; from := @zero (FAlg NatF) nat_initial
                               (@initial_obj (FAlg NatF) I) |}.
  - exact (@zero_unique (FAlg NatF) nat_initial (nat; nat_alg) _ id).
  - exact (@zero_unique (FAlg NatF) I (@initial_obj (FAlg NatF) I) _ id).
Qed.

(*
 Reading off the carriers: the underlying type of any initial [NatF]-algebra
 is isomorphic to [nat] in COQ, by the carrier of the algebra isomorphism
 above (so the bijection does commute with the structure maps). 

 --------
 从载体读取：任何初始 [NatF] -代数的基础类型在 COQ 中同构于 [nat]，通过上述代数同构的载体（因此双射确实与结构映射交换）。
*)
Corollary nat_initial_carrier_unique (I : @Initial (FAlg NatF)) :
  `1 (@initial_obj (FAlg NatF) I) ≅[Coq] nat.
Proof.
  pose proof (nat_initial_unique I) as iso.
  unshelve refine {| to   := falg_hom[to iso]
                   ; from := falg_hom[from iso] |}.
  - exact (iso_to_from iso).
  - exact (iso_from_to iso).
Qed.

(* * ** Riehl Example 2.4.11: the representability reading / * ** Riehl 示例 2.4.11：可表示性读法 *)

(*
 [Endos] is Riehl's category of sets with an endomorphism and maps commuting
 with them: an [Id]-algebra is an object with a map [X ~> X], and an
 [Id]-algebra map is a commuting square, with no point involved. 

 --------
 [Endos] 是 Riehl 的带有自同态的集合范畴及与之交换的映射：一个 [Id]-代数是一个带有映射 [X ~> X] 的对象，而 [Id]-代数映射是一个交换方形，不涉及任何点。
*)
Definition Endos : Category := FAlg (Id[Coq]).

(*
 The forgetful functor to [Sets].  A COQ object is a bare type, so it is
 made a setoid by Leibniz equality ([eq_Setoid] of Lib/Setoid.v); this is
 the one place where the [Coq]-vs-[Sets] variance noted in the issue is
 paid for, and it costs nothing because [Coq]'s hom-setoid is already
 pointwise [eq]. 

 --------
 到 [Sets] 的忘记函子。COQ 对象是一个裸类型，因此它通过莱布尼茨等式（Lib/Setoid.v 的 [eq_Setoid]）被构造成一个集合；这是问题中提到的 [Coq] 和 [Sets] 变体唯一需要处理的地方，而且不花费任何代价，因为 [Coq] 的同态集合已经是逐点的 [eq]。
*)
Program Definition Endos_Forget : Endos ⟶ Sets := {|
  fobj := fun x => {| carrier := ``x ; is_setoid := eq_Setoid ``x |};
  fmap := fun x y f => {| morphism := falg_hom[f] |}
|}.
Next Obligation. intros x y f a b Hab; now rewrite Hab. Qed.
Next Obligation. intros x y f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros x a; reflexivity. Qed.
Next Obligation. intros x y z f g a; reflexivity. Qed.

(* The candidate representing object: the naturals with successor, no point. / 代表对象的候选项：带有后继的自然数，无零点。 *)
Definition nat_succ : FAlgebra Id[Coq] nat := S.

Definition NatSucc : Endos := (nat; nat_succ).

#[local] Notation HomNS := (@Curried_Hom Endos NatSucc).

(* Iteration: the [n]-fold application of the endomap to the point. / 迭代：对该点进行 [n] 次端映射的应用。 *)
Fixpoint nat_iter {X : Type} (x0 : X) (f : X ~{Coq}~> X) (n : nat) : X :=
  match n with
  | O   => x0
  | S k => f (nat_iter x0 f k)
  end.

(*
 Iteration is natural in the object of [Endos]: an endomorphism-preserving
 map carries the iterate of a point to the iterate of its image. 

 --------
 在 [Endos] 的对象中，迭代是自然的：一个保持自同态的映射将一个点的迭代映射到其像的迭代。
*)
Lemma nat_iter_natural {y z : Endos} (g : y ~{Endos}~> z) (y0 : ``y) (n : nat) :
  falg_hom[g] (nat_iter y0 (`2 y) n) = nat_iter (falg_hom[g] y0) (`2 z) n.
Proof.
  induction n as [|k IH]; simpl.
  - reflexivity.
  - transitivity ((`2 z) (falg_hom[g] (nat_iter y0 (`2 y) k))).
    + exact (@falg_commutes _ _ _ _ _ _ g (nat_iter y0 (`2 y) k)).
    + f_equal; exact IH.
Qed.

(* Every endomorphism-preserving map out of [(nat, S)] is the iterate of its own value at zero. This is the injectivity half of the representation. / 从 [(nat, S)] 出发的每个保持自同态的映射都是它在零处取值的迭代。这是表示的单射性部分。 *)
Lemma nat_iter_eval {y : Endos} (h : NatSucc ~{Endos}~> y) (n : nat) :
  nat_iter (falg_hom[h] O) (`2 y) n = falg_hom[h] n.
Proof.
  induction n as [|k IH]; simpl.
  - reflexivity.
  - transitivity ((`2 y) (falg_hom[h] k)).
    + f_equal; exact IH.
    + symmetry; exact (@falg_commutes _ _ _ _ _ _ h k).
Qed.

(* Φ: evaluate an endomorphism-preserving map at zero. / Φ：在零点处评估一个保持自同态的映射。 *)
Program Definition nat_eval_at_zero (y : Endos)
  : HomNS y ~{Sets}~> Endos_Forget y :=
  {| morphism := fun h => falg_hom[h] O |}.
Next Obligation. intros y h k Hhk; exact (Hhk O). Qed.

(*
 Ψ: send a point to the iterate along the endomap, which is automatically an
 endomorphism-preserving map because [nat_iter x0 f (S n)] is [f] applied to
 [nat_iter x0 f n] by definition. 

 --------
 Ψ：将一个点沿着endomap迭代发送，这自动是一个保持endomorphism的映射，因为[nat_iter x0 f (S n)]按照定义是[nat_iter x0 f n]应用于[f]。
*)
Program Definition nat_iterate (y : Endos)
  : Endos_Forget y ~{Sets}~> HomNS y :=
  {| morphism := fun y0 => {| falg_hom := nat_iter y0 (`2 y) |} |}.
Next Obligation. intros y y0 n; reflexivity. Qed.

Program Definition nat_eval_transform : HomNS ⟹ Endos_Forget :=
  Build_Transform' nat_eval_at_zero _.
Next Obligation. intros y z g h; reflexivity. Qed.

Program Definition nat_iterate_transform : Endos_Forget ⟹ HomNS :=
  Build_Transform' nat_iterate _.
Next Obligation. intros y z g y0 n; exact (nat_iter_natural g y0 n). Qed.

(*
 The representation: [Hom((nat, S), ─) ≅ Endos_Forget] in [[Endos, Sets]].
 Evaluation at zero and iteration are mutually inverse, naturally in the
 object of [Endos]. 

 --------
 表示：[Hom((nat, S), ─) ≅ Endos_Forget] 在 [[Endos, Sets] 中]。在零点的评估和迭代在 [Endos] 的对象中自然是互为逆运算的。
*)
Program Definition nat_succ_represents
  : HomNS ≅[[Endos, Sets]] Endos_Forget :=
  {| to := nat_eval_transform; from := nat_iterate_transform |}.
Next Obligation. intros y y0; reflexivity. Qed.
Next Obligation. intros y h n; exact (nat_iter_eval h n). Qed.

#[export] Program Instance nat_succ_Representable
  : Representable Endos_Forget := {|
  repr_obj := NatSucc;
  represented := nat_succ_represents
|}.

(*
 The universal element of the representation, in the sense of the Yoneda
 lemma: the image of the identity under the representing isomorphism.  It is
 zero, on the nose. 

 --------
 表示的普遍元素，从Yoneda引理的意义上说：在表示同构下恒等映射的像。它严格为零。
*)
Lemma nat_universal_element :
  transform (to nat_succ_represents) NatSucc (id{Endos}) = O.
Proof. reflexivity. Qed.

(* * ** The universal-element criterion / * ** 通用元素标准 *)

(*
 Riehl's Proposition 2.4.8, stated for this functor: a representation of
 [Endos_Forget] makes the algebra built from the representing object and the
 universal element initial in [FAlg NatF].  Objects of [FAlg NatF] ARE pairs
 of an object of [Endos] and an element of its image under [Endos_Forget],
 and arrows of [FAlg NatF] ARE the arrows of [Endos] carrying one such
 element to the other (that is [alg_hom_clauses]/[clauses_alg_hom] above), so
 this is exactly the statement that a universal element is initial in the
 category of elements — with the category of elements presented concretely as
 [FAlg NatF] rather than built as a general construction.

 ERRATUM (#303).  The clause that used to close that sentence, “which the
 tree does not carry”, was true when written (commit 30c01af0, 2026-08-05)
 and went stale four days later: [Construction/Elements.v] landed the general
 category of elements on 2026-08-09 (f2177328), and
 Theory/Universal/Element/Elements.v now states Riehl 2.4.8 — a universal
 element is an initial object of it — over that general construction.  What
 is still NOT built is the comparison [Elements Endos_Forget ≃ FAlg NatF], so
 [repr_initial] below is neither re-derived nor made redundant by it; the two
 remain independent statements. 

 --------
 Riehl 的命题 2.4.8，对于该函子表述如下：[Endos_Forget] 的一个表示使得由表示对象和通用元素构建的代数在 [FAlg NatF] 中是初始的。[FAlg NatF] 的对象是 [Endos] 的一个对象和其在 [Endos_Forget] 下的像中的一个元素的配对，[FAlg NatF] 的箭头是 [Endos] 的箭头，将一个这样的元素映射到另一个（即上文的 [alg_hom_clauses] / [clauses_alg_hom]），因此这正是通用元素在元素范畴中是初始对象的陈述——元素范畴具体表示为 [FAlg NatF]，而不是作为一般构造建立。勘误 (#303)。 之前用来结束那句话的从句“树没有携带的”在写作时是正确的（提交 30c01af0，2026-08-05），但四天后就已经过时：[Construction/Elements.v] 在 2026-08-09 进行了元素的一般分类（f2177328），而 Theory/Universal/Element/Elements.v 现在在该一般构造上说明了 Riehl 2.4.8 —— 一个普遍元素是其初始对象。 仍未构建的是比较 [Elements Endos_Forget ≃ FAlg NatF]，因此下文的 [repr_initial] 既没有被重新推导，也没有因它而变得多余；这两个仍然是独立的陈述。
*)

Section UniversalElement.

Context (Repr : Representable Endos_Forget).

(*
 The representing object and the representing natural isomorphism.  These
 are spelled as abbreviations rather than as further section variables so
 that the [Sets] universe instance is the one fixed by [Endos_Forget]. 

 --------
 表示对象和表示自然同构。它们被拼写为缩写，而不是作为进一步的章节变量，这样 [Sets] 宇宙实例就是由 [Endos_Forget] 固定的那个。
*)
Notation RObj := (@repr_obj _ _ Repr).
Notation RIso := (@represented _ _ Repr).

(* The universal element: the image of the identity. / 普遍元素：身份的形象。 *)
Definition repr_element : ``RObj := transform (to RIso) RObj (id{Endos}).

(* The algebra of the representing object pointed at its universal element. / 指向其普遍元素的表示对象的代数。 *)
Definition repr_alg : FAlg NatF :=
  (``RObj ; alg_of_triple repr_element (`2 RObj)).

(*
 The Yoneda computation: the representing isomorphism sends an arrow to the
 image of the universal element under it.  This is naturality evaluated at
 the identity, followed by the right unit law inside the setoid map. 

 --------
 Yoneda 计算：表示同构将一个箭头发送到其下普遍元素的像。这是在恒等下评估的自然性，然后是集合等价映射内部的右单位律。
*)
Lemma repr_eval {y : Endos} (h : RObj ~{Endos}~> y) :
  falg_hom[h] repr_element = transform (to RIso) y h.
Proof.
  transitivity (transform (to RIso) y (h ∘ id{Endos})).
  - exact (naturality (to RIso) RObj y h (id{Endos})).
  - apply (@proper_morphism _ _ _ _ (transform (to RIso) y)).
    apply id_right.
Qed.

(* Each [NatF]-algebra gives an object of [Endos] by forgetting the point. / 每个 [NatF]-代数通过忘记点给出一个 [Endos] 的对象。 *)
Definition endo_of (y : FAlg NatF) : Endos :=
  (``y ; (alg_step (`2 y) : FAlgebra Id[Coq] ``y)).

(* The mediating arrow: the inverse of the representation applied to the point of the target algebra. / 调解箭头：应用于目标代数点的表示的逆。 *)
Definition repr_med (y : FAlg NatF) : RObj ~{Endos}~> endo_of y :=
  transform (from RIso) (endo_of y) (alg_pt (`2 y)).

(* It carries the universal element to the point of the target. / 它将普遍元素带到目标点。 *)
Lemma repr_med_pt (y : FAlg NatF) :
  falg_hom[repr_med y] repr_element = alg_pt (`2 y).
Proof.
  transitivity (transform (to RIso) (endo_of y) (repr_med y)).
  - exact (repr_eval (repr_med y)).
  - exact (iso_to_from RIso (endo_of y) (alg_pt (`2 y))).
Qed.

(* Hence it is an algebra map out of [repr_alg], by the triple dictionary: the point clause is [repr_med_pt] and the step clause is its [Endos] square. / 因此，它是一个从 [repr_alg] 出发的代数映射，通过三重字典：点从句是 [repr_med_pt]，步从句是它的 [Endos] 平方。 *)
Program Definition repr_alg_hom (y : FAlg NatF)
  : repr_alg ~{FAlg NatF}~> y :=
  {| falg_hom := falg_hom[repr_med y] |}.
Next Obligation.
  intro y.
  apply clauses_alg_hom.
  - exact (repr_med_pt y).
  - exact (@falg_commutes _ _ _ _ _ _ (repr_med y)).
Qed.

(* Conversely every algebra map out of [repr_alg] is an [Endos] arrow, by the step clause of the same dictionary. / 相反，根据同一词典的步骤条款，每个从 [repr_alg] 出发的代数映射都是一个 [Endos] 箭头。 *)
Program Definition endo_of_alg_hom {y : FAlg NatF}
        (f : repr_alg ~{FAlg NatF}~> y) : RObj ~{Endos}~> endo_of y :=
  {| falg_hom := falg_hom[f] |}.
Next Obligation.
  intros y f.
  exact (snd (alg_hom_clauses _ _ _ (@falg_commutes _ _ _ _ _ _ f))).
Qed.

(*
 An arrow out of the representing object is determined by its image under
 the representation, since that is an isomorphism at every object. 

 --------
 表示对象的箭头由其在表示下的像决定，因为那是在每个对象上的同构。
*)
Lemma repr_hom_determined {y : Endos} (k l : RObj ~{Endos}~> y)
      (H : transform (to RIso) y k = transform (to RIso) y l) : k ≈ l.
Proof.
  transitivity (transform (from RIso) y (transform (to RIso) y k)).
  - symmetry; exact (iso_from_to RIso y k).
  - transitivity (transform (from RIso) y (transform (to RIso) y l)).
    + apply (@proper_morphism _ _ _ _ (transform (from RIso) y)); exact H.
    + exact (iso_from_to RIso y l).
Qed.

(*
 Every algebra map out of [repr_alg] sends the universal element to the
 point of the target: that is the point clause of its commuting square,
 transported along [repr_eval]. 

 --------
 从 [repr_alg] 出发的每个代数映射都会将通用元发送到目标的点：也就是其交换方形的点子句，通过 [repr_eval] 进行传送。
*)
Lemma repr_alg_hom_pt {y : FAlg NatF} (f : repr_alg ~{FAlg NatF}~> y) :
  transform (to RIso) (endo_of y) (endo_of_alg_hom f) = alg_pt (`2 y).
Proof.
  transitivity (falg_hom[endo_of_alg_hom f] repr_element).
  - symmetry; exact (repr_eval (endo_of_alg_hom f)).
  - exact (fst (alg_hom_clauses _ _ _ (@falg_commutes _ _ _ _ _ _ f))).
Qed.

(* ... so any two of them agree. / ...所以他们中任意两个都同意。 *)
Lemma repr_alg_hom_unique {y : FAlg NatF}
      (f g : repr_alg ~{FAlg NatF}~> y) : f ≈ g.
Proof.
  refine (repr_hom_determined (endo_of_alg_hom f) (endo_of_alg_hom g) _).
  transitivity (alg_pt (`2 y)).
  - exact (repr_alg_hom_pt f).
  - symmetry; exact (repr_alg_hom_pt g).
Qed.

(* The criterion itself. / 标准本身。 *)
Program Definition repr_initial : @Initial (FAlg NatF) := {|
  terminal_obj := repr_alg;
  one := fun y => repr_alg_hom y
|}.
Next Obligation. intros y f g; exact (repr_alg_hom_unique f g). Qed.

End UniversalElement.

(*
 [nat_initial] as an instance of the criterion rather than as a standalone
 proof: feeding the representation [nat_succ_represents] to [repr_initial]
 produces an initial [NatF]-algebra, and it is literally the same algebra —
 the universal element is [O] and the endomap is [S], so the structure map is
 [nat_alg] by conversion. 

 --------
 [nat_initial] 作为该准则的一个实例，而不是作为一个独立的证明：将表示 [nat_succ_represents] 输入到 [repr_initial] 会生成一个初始的 [NatF] 代数，而且它字面上是相同的代数——通用元素是 [O]，端映射是 [S]，因此结构映射是 [nat_alg] 通过转换得到。
*)
Definition nat_initial_via_universal_element : @Initial (FAlg NatF) :=
  repr_initial nat_succ_Representable.

Lemma nat_initial_agree :
  @initial_obj (FAlg NatF) nat_initial_via_universal_element
    = @initial_obj (FAlg NatF) nat_initial.
Proof. reflexivity. Qed.
