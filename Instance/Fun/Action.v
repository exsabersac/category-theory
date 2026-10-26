(* * * Monoid and group actions as functor categories / * * 单位半群和群作用作为函子范畴 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §II.4, printed pp. 41–42 (PDF 51–52) —
 maclane:II.4:construction2, maclane:II.4:ex5
 nLab:      https://ncatlab.org/nlab/show/action
 nLab:      https://ncatlab.org/nlab/show/G-set

 Mac Lane's construction 2: a functor from a delooped monoid into
 Sets is exactly an action of M on a set, and a natural
 transformation between two such functors is exactly a single
 EQUIVARIANT map — its one component, at the one object.  This file
 packages the correspondence at category strength: the category
 [MSet M] of M-actions with equivariant maps, and the equivalence
 [MSet_Fun_equiv : [Deloop M, Sets] ≅[Cat] MSet M].  Exercise 5
 specializes to a group acting on finite sets: every finite-set
 value of a functor on a delooped GROUP is acted on by
 permutations, since group elements are invertible arrows and
 functors preserve isomorphisms — the permutation-representation
 reading.

 - [Equivariant]: a setoid morphism between the carriers
 commuting with the actions, with the componentwise setoid
 - [MSet M]: the category of M-actions and equivariant maps
 - [MSet_to]/[MSet_from]: the two comparison functors, riding
 Construction/Deloop/Functors.v's [action_of_functor] and
 [functor_of_action] (cited, not rebuilt)
 - [MSet_Fun_equiv]: the equivalence [Deloop M, Sets] ≅ [MSet M]
 in Cat, and [MSet_hom_iso], the hom-setoid isomorphism
 stating literally that a natural transformation IS one
 equivariant map
 - [perm_of_group_element]/[FinPermRep]/
 [perm_rep_acts_by_bijections]: Exercise 5 — for a group G,
 each g acts on the finite-set value of any
 F : Deloop G ⟶ FinSet as an isomorphism of FinSet (a
 permutation), and representations correspond to functors
 along the spine, invertibility being automatic rather than
 part of the data

 Design:

 1. THE OBJECT-LEVEL DICTIONARY IS ALREADY IN THE TREE, AND IS NOT
 REBUILT.  Construction/Deloop/Functors.v has [MSetoidAction],
 [action_of_functor], [functor_of_action], the object-level
 round trips ([action_round] is pointwise reflexivity;
 [action_functor_round] is the [Functor_Setoid] witness), the
 spine correspondence [functor_of_hom_monoid]/
 [hom_monoid_of_functor] with its round trips, and
 [action_automorphism] with its definitional readings — all
 consumed below, none re-proved.  What this file adds is the
 MORPHISM level — equivariant maps as a category — and the
 equivalence at [Cat] strength.  The one thing rebuilt is the
 functor-side round-trip ISOMORPHISM, with a transparent
 component family ([MSet_round_iso]): the in-tree lemma is
 opaque (Qed) and the equivalence needs to compute with the
 components — the same transparent-witness discipline as
 Construction/Arrow/Functor.v's [fs_refl].

 2. NATURALITY AT THE ONE OBJECT IS EQUIVARIANCE.  A transformation
 η between functors on [Deloop M] has one component, and its
 naturality square at g : ttt ~> ttt says precisely that this
 component commutes with the two actions.  [MSet_to]'s morphism
 action reads this off; [MSet_from] materializes an equivariant
 map as the constant transformation family, naturality being
 equivariance again.

 3. EXERCISE 5 RIDES INVERTIBILITY, AND ITS SCOPE IS THIS.
 [perm_of_group_element] is Construction/Deloop/Functors.v's
 [action_automorphism] read at the FinSet target — a functor
 carries the group inverse to the inverse permutation — and
 [FinPermRep] identifies representations with functors at the
 OBJECT level along the spine (mirroring [MatrixRep]), with
 invertibility a theorem rather than data
 ([perm_rep_acts_by_bijections]).  A FinSet hom is a function
 on positions (Instance/FinSet.v), so an isomorphism is
 literally a permutation; Instance/FinSet/Classifier.v holds
 the injectivity/surjectivity characterizations, cited not
 imported.  What is NOT built: a separate CATEGORY of
 permutation representations with an equivalence
 [Deloop G, FinSet] ≃ PermRep (the morphism-level story at
 FinSet would repeat the [MSet] development at a second
 target), and no finiteness hypothesis on the GROUP is
 rendered — [GrpObject] carries none, so every statement here
 holds for all groups, strictly more than the exercise's
 “finite group” asks.

 4. THE GROUP-WITH-OPERATORS ASIDE.  Mac Lane's remark that
 functors [Deloop M ⟶ Grp] are groups with operator monoid M
 (and similarly for other targets) is the same dictionary at a
 different target; there is no in-tree category of groups at
 the needed generality to instantiate it, so it remains this
 prose note, per the issue's own scoping. 

 --------
 书籍：      Mac Lane，《为数学工作者准备的范畴学》，第2版，
 §II.4，第41–42页（PDF第51–52页）——
 maclane:II.4:construction2, maclane:II.4:ex5
 nLab：      https://ncatlab.org/nlab/show/action 
 nLab：      https://ncatlab.org/nlab/show/G-setMac Lane 的构造 2：从一个去环单子到集合的函子恰好是 M 在一个集合上的作用，而两个这样的函子之间的自然变换恰好是一个单一的等变映射——它在唯一对象上的唯一分量。这个文件将对应关系以范畴强度打包：带有等变映射的 M-作用范畴 [MSet M]，以及等价 [MSet_Fun_equiv : [Deloop M, Sets] ≅ [Cat] MSet M。练习 5 专门针对群作用在有限集合上：函子在去环群上的每个有限集合值都会被置换作用，因为群元素是可逆箭头，函子保持同构——即置换表示法的理解。- [Equivariant]：载体之间的集合同态，满足与作用的交换性，并且是分量级的集合同态
 - [MSet M]：M-作用及等变映射的范畴
 - [MSet_to] / [MSet_from]：两个比较函子，基于 Construction/Deloop/Functors.v 的 [action_of_functor] 和 [functor_of_action]（引用自其他地方，未重建）
 - [MSet_Fun_equiv]：在 Cat 中的等价  [Deloop M, Sets] ≅ [MSet M]，以及 [MSet_hom_iso]，态射集同构，字面意思说明自然变换就是一个等变映射
 - [perm_of_group_element] / [FinPermRep] / [perm_rep_acts_by_bijections]：练习 5——对于一个群 G，每个 g 都作为 FinSet 上任意 F : Deloop G ⟶ FinSet 的有限集合值的等变同构（一个置换）作用，并且表示对应于沿着脊柱的函子，逆元自动成立而不是数据的一部分设计：1. 对象级别字典已经在树中，且未重新构建。Construction/Deloop/Functors.v 包含 [MSetoidAction]、[action_of_functor]、[functor_of_action]，对象级别的来回操作（[action_round] 是点态自反；[action_functor_round] 是 [Functor_Setoid] 的证明），脊对应 [functor_of_hom_monoid] / [hom_monoid_of_functor] 及其来回操作，以及 [action_automorphism] 及其定义性读法——所有这些都在下文使用，未重新证明。该文件新增的是 MORPHISM 级别——作为范畴的等变映射——以及 [Cat] 强度下的等价性。唯一重建的是函子端的往返同构（ISOMORPHISM），具有透明的分量族（[MSet_round_iso]）：树内引理是不透明的（Qed），等价性需要与这些分量计算——与 Construction/Arrow/Functor.v 的 [fs_refl] 中使用的透明证据纪律相同。

 2. 在单一对象上的自然性即为等变性。[Deloop M] 上函子之间的变换 η 有一个分量，其在 g : ttt ~> ttt 处的自然性方形恰好说明该分量与两个作用交换。[MSet_to] 的态射作用读出了这一点；[MSet_from] 将等变映射具体化为常量变换族，自然性再次即为等变性。3. 练习 5 涉及可逆性，其范围如下。[perm_of_group_element] 是 Construction/Deloop/Functors.v 的内容，[action_automorphism] 在 FinSet 目标上读取 —— 一个函子将群的逆映射到逆排列 —— 并且 [FinPermRep] 将表示在沿主干的对象级别与函子进行识别（镜像 [MatrixRep]），其可逆性是一个定理而非数据（[perm_rep_acts_by_bijections]）。FinSet 的同态是位置上的一个函数（Instance/FinSet.v），因此同构实际上就是一个排列；Instance/FinSet/Classifier.v 保存了单射/满射的表征，引用而非导入。未建立的内容：一个独立的排列表示类别及其等价关系 [Deloop G, FinSet] ≃ PermRep（在 FinSet 上的态射层面故事将在第二个目标上重复 [MSet] 的发展），并且对群没有有限性假设——[GrpObject] 没有携带任何假设，因此这里的每个陈述都适用于所有群，严格来说比练习中要求的“有限群”更多。

 4. 关于带算子的群。Mac Lane 的备注指出函子 [Deloop M ⟶ Grp] 是带有算子幺半群 M 的群（对于其他目标亦然），这只是一个在不同目标上的同一词典；在所需的一般性下，并不存在一个可实例化它的群的树内类别，因此它仍然是这段文字说明，根据问题自身的范围。
*)

(** ** Equivariant maps / ** 等变映射 *)

(*
 A morphism of M-actions: a setoid morphism between the carriers
 commuting with the actions. 

 --------
 M-作用的态射：在承载体之间的等价集态射，与作用相交换。
*)
Record Equivariant {M : MonObject} (A B : MSetoidAction M) := {
  equiv_map :> act_setoid A ~{Sets}~> act_setoid B;
  equivar : ∀ (g : carrier M) x,
    equiv_map (act A g x) ≈ act B g (equiv_map x)
}.

Arguments equiv_map {M A B} _.
Arguments equivar {M A B} _ _ _.

(** ** The category of M-actions / ** M 行为的类别 *)

Program Definition MSet (M : MonObject) : Category := {|
  obj := MSetoidAction M;
  hom := fun A B => Equivariant A B;
  homset := fun A B =>
    {| equiv := fun f g => ∀ x, equiv_map f x ≈ equiv_map g x |};
  id := fun A =>
    {| equiv_map := {| morphism := fun x => x |} |};
  compose := fun A B C f g =>
    {| equiv_map := {| morphism := fun x => equiv_map f (equiv_map g x) |} |}
|}.
Next Obligation.
  intros M A B; constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; apply Hfg.
  - intros f g h H1 H2 x; transitivity (equiv_map g x); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; reflexivity.
Qed.
Next Obligation.
  intros M A B C f g x y Hxy.
  apply (proper_morphism (equiv_map f)).
  apply (proper_morphism (equiv_map g)).
  exact Hxy.
Qed.
Next Obligation.
  intros M A B C f g gr x; simpl.
  rewrite (equivar g gr x).
  apply (equivar f).
Qed.
Next Obligation.
  intros M A B C f f' Hf g g' Hg x; simpl.
  rewrite (Hg x).
  exact (Hf (equiv_map g' x)).
Qed.
Next Obligation.
  intros M A B f x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B f x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B C D f g h x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A B C D f g h x; simpl; reflexivity.
Qed.

(** ** The comparison functors / ** 比较函数对象 *)

(*
 Reading an action and its equivariant maps off a functor: the
 morphism action takes a transformation to its single component,
 whose naturality at g IS equivariance. 

 --------
 从函子中读取一个作用及其等变映射：态射作用将一个变换映射到它的单个分量，其在 g 处的自然性就是等变性。
*)
Program Definition MSet_to (M : MonObject) :
  [Deloop M, Sets] ⟶ MSet M := {|
  fobj := fun F => action_of_functor F;
  fmap := fun F G η =>
    {| equiv_map := transform[η] ttt |}
|}.
Next Obligation.
  intros M F G η g x; simpl.
  symmetry.
  exact (naturality[η] ttt ttt g x).
Qed.
Next Obligation.
  intros M F G η θ Hηθ x; exact (Hηθ ttt x).
Qed.
Next Obligation.
  intros M F x; simpl; exact (@fmap_id _ _ F ttt x).
Qed.
Next Obligation.
  intros M F G H η θ x; simpl; reflexivity.
Qed.

(*
 Materializing an equivariant map as the constant transformation
 family; naturality is equivariance. 

 --------
 将一个等变映射实现为常数变换族；自然性就是等变性。
*)
Program Definition MSet_from (M : MonObject) :
  MSet M ⟶ [Deloop M, Sets] := {|
  fobj := fun A => functor_of_action A;
  fmap := fun A B h =>
    {| transform := fun _ => equiv_map h |}
|}.
Next Obligation.
  intros M A B h [] [] g x; simpl.
  symmetry.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M A B h [] [] g x; simpl.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M A B h h' Hh [] x; exact (Hh x).
Qed.
Next Obligation.
  intros M A [] x; simpl.
  now rewrite (act_unit A x).
Qed.
Next Obligation.
  intros M A B C f g [] x; simpl; reflexivity.
Qed.

(** ** The equivalence / ** 等价 *)

(*
 The functor-side round trip, with a transparent component family
 (the in-tree [action_functor_round] is opaque). 

 --------
 函子端的往返，具有透明的组件系列（树内的 [action_functor_round] 是不透明的）。
*)
Program Definition MSet_round_iso {M : MonObject} (F : Deloop M ⟶ Sets) :
  @Isomorphism ([Deloop M, Sets])
    (functor_of_action (action_of_functor F)) F := {|
  to   := {| transform := fun x =>
    match x return (functor_of_action (action_of_functor F) x ~{Sets}~> F x)
    with ttt => {| morphism := fun p => p |} end |};
  from := {| transform := fun x =>
    match x return (F x ~{Sets}~> functor_of_action (action_of_functor F) x)
    with ttt => {| morphism := fun p => p |} end |}
|}.
Next Obligation.
  intros M F [] x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] [] g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F [] x; simpl; symmetry; exact (@fmap_id _ _ F ttt x).
Qed.
Next Obligation.
  intros M F [] x; simpl; symmetry; exact (@fmap_id _ _ F ttt x).
Qed.

(*
 The action-side round trip: the two actions coincide pointwise
 ([action_round] is reflexivity), so the identity map is
 equivariant in both directions. 

 --------
 动作侧的往返：两个动作在每一点上重合（[action_round] 是自反性），因此恒等映射在两个方向上都是等变的。
*)
Program Definition MSet_action_round_iso {M : MonObject}
        (A : MSetoidAction M) :
  @Isomorphism (MSet M) (action_of_functor (functor_of_action A)) A := {|
  to   := {| equiv_map := {| morphism := fun x => x |} |};
  from := {| equiv_map := {| morphism := fun x => x |} |}
|}.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x y Hxy; exact Hxy.
Qed.
Next Obligation.
  intros M A g x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M A x; simpl; reflexivity.
Qed.

(*
 Mac Lane's construction 2 at category strength: the functor
 category over a delooped monoid IS the category of M-actions, an
 isomorphism in Cat and hence (by Cat's convention) an equivalence
 of categories. 

 --------
 Mac Lane 在范畴强度下的构造 2：在去环 monoid 上的函子范畴就是 M-作用的范畴，是 Cat 中的一个同构，因此（按照 Cat 的惯例）是范畴的等价。
*)
Program Definition MSet_Fun_equiv (M : MonObject) :
  [Deloop M, Sets] ≅[Cat] MSet M := {|
  to   := MSet_to M;
  from := MSet_from M
|}.
Next Obligation.
  (*
 MSet_to ∘ MSet_from ≈ Id: the action round trip is pointwise
 reflexivity 

 --------
 MSet_to ∘ MSet_from ≈ Id：操作往返是逐点自反的
*)
  intros M.
  exists (fun A => MSet_action_round_iso A).
  intros A B h x; simpl; reflexivity.
Qed.
Next Obligation.
  (* MSet_from ∘ MSet_to ≈ Id: the transparent functor-side round trip / MSet_from ∘ MSet_to ≈ Id：透明函子端的往返 *)
  intros M.
  exists (fun F => MSet_round_iso F).
  intros F G η [] x; simpl.
  reflexivity.
Qed.

(* * ** The transformation setoid IS the equivariant-map setoid / * ** 转换宿主是等变映射宿主 *)

(*
 Issue item 2's “unwind”, stated literally as a hom-setoid
 isomorphism in Sets, following the same-directory precedents
 [One_hom_iso] and [Discrete_hom_iso]: a natural transformation
 between functors on the delooping is exactly one equivariant
 map. 

 --------
 发布条目 2 的“展开”，在集合中字面上表示为同类集同构，遵循相同目录的先例 [One_hom_iso] 和 [Discrete_hom_iso]：去循环上的函子之间的自然变换恰好是一个等变映射。
*)
Program Definition MSet_hom_iso {M : MonObject}
        (F G : Deloop M ⟶ Sets) :
  ({| carrier := F ⟹ G;
      is_setoid := @Transform_Setoid (Deloop M) Sets F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := Equivariant (action_of_functor F) (action_of_functor G);
     is_setoid :=
       {| equiv := fun f g => ∀ x, equiv_map f x ≈ equiv_map g x |} |} := {|
  to   := {| morphism := fun η => {| equiv_map := transform[η] ttt |} |};
  from := {| morphism := fun h =>
    {| transform := fun o =>
         match o return (fobj[F] o ~{Sets}~> fobj[G] o) with
         | ttt => equiv_map h
         end |} |}
|}.
Next Obligation.
  intros M F G; constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; apply Hfg.
  - intros f g h H1 H2 x;
    transitivity (equiv_map g x); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros M F G η g x; simpl.
  symmetry.
  exact (naturality[η] ttt ttt g x).
Qed.
Next Obligation.
  intros M F G η θ Hηθ x; exact (Hηθ ttt x).
Qed.
Next Obligation.
  intros M F G h [] [] g x; simpl.
  symmetry.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M F G h [] [] g x; simpl.
  exact (equivar h g x).
Qed.
Next Obligation.
  intros M F G h h' Hh [] x; exact (Hh x).
Qed.
Next Obligation.
  intros M F G h x; simpl; reflexivity.
Qed.
Next Obligation.
  intros M F G η [] x; simpl; reflexivity.
Qed.

(* * ** Exercise 5: groups act on finite sets by permutations / * ** 练习 5：群通过置换作用于有限集合 *)

(*
 Each group element acts on the finite-set value as an isomorphism
 of FinSet — a permutation.  The isomorphism is Construction/
 Deloop/Functors.v's [action_automorphism] read at the FinSet
 target (the donor is general in the target category and carries
 the definitional readings [action_automorphism_to]/[_from]);
 nothing is re-proved here. 

 --------
 每个群元素作用于有限集的值上，作为 FinSet 的一个同构——一个排列。该同构是 Construction/Deloop/Functors.v 中的 [action_automorphism]，在 FinSet 目标上读取（源对象在目标范畴中是一般的，并携带定义性的读取 [action_automorphism_to] / [_from]）；这里没有重新证明任何内容。
*)
Definition perm_of_group_element {G : GrpObject}
        (F : Deloop G ⟶ FinSet) (g : carrier G) :
  @Isomorphism FinSet (F ttt) (F ttt) :=
  action_automorphism F g.

(*
 The identification with permutation representations, at the object
 level and along the spine correspondence: a permutation
 representation is a dimension with a homomorphism into the
 endomorphism monoid of that object of FinSet — mirroring
 [MatrixRep] — and the passage to and from functors is the spine,
 with the round trips already in the tree.  Invertibility is NOT
 part of the data: over a group it is automatic
 ([perm_rep_acts_by_bijections]). 

 --------
 在对象层面上以及沿着脊柱对应的置换表示的识别：置换表示是一个带有同态映射到该 FinSet 对象的自同态半群的维度——反映 [MatrixRep] ——而到函子和从函子的转换就是脊柱，来回已经在树中。可逆性不是数据的一部分：在群上它是自动的（[perm_rep_acts_by_bijections]）。
*)
Definition FinPermRep (M : MonObject) : Type :=
  { n : nat & MonHom M (hom_monoid FinSet n) }.

Definition functor_of_perm_rep {M : MonObject} (ρ : FinPermRep M) :
  Deloop M ⟶ FinSet :=
  functor_of_hom_monoid (C := FinSet) (`1 ρ) (`2 ρ).

Definition perm_rep_of_functor {M : MonObject} (F : Deloop M ⟶ FinSet) :
  FinPermRep M :=
  existT (fun n : nat => MonHom M (hom_monoid FinSet n))
    (F ttt : nat) (hom_monoid_of_functor (C := FinSet) F).

(*
 Over a group, every representation acts by bijections: each element
 goes to an isomorphism of FinSet. 

 --------
 在一个群上，每个表示都通过双射作用：每个元素都映射到 FinSet 的一个同构。
*)
Definition perm_rep_acts_by_bijections {G : GrpObject}
        (ρ : FinPermRep G) (g : carrier G) :
  @Isomorphism FinSet (`1 ρ) (`1 ρ) :=
  perm_of_group_element (functor_of_perm_rep ρ) g.
