Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* * * Limits in a preorder are greatest lower bounds / * * 预序中的极限是最大下界 *)

(*
 nLab: https://ncatlab.org/nlab/show/preorder
 nLab: https://ncatlab.org/nlab/show/thin+category
 nLab: https://ncatlab.org/nlab/show/join
 Wikipedia: https://en.wikipedia.org/wiki/Infimum_and_supremum

 Regard a preorder [(A, R)] as the thin category [Proset P] of
 Instance/Proset.v, in which [x ~> y] is the relation [R x y] itself.
 Under that dictionary the categorical universal constructions become
 the order-theoretic ones:

 - a product   x × y   is a greatest lower bound (a meet) of x and y;
 - a terminal object   1   is a greatest element (a top);
 - a limit of a diagram is a greatest lower bound of the family of
 its objects, whatever the shape of the diagram;

 and dually coproducts are least upper bounds (joins), the initial
 object is a least element, and colimits are least upper bounds.

 CITATIONS ARE LOCATIONS ONLY.  The passages below are cited for where
 the statement is found, not paraphrased from a consulted copy; none of
 these sources was read while preparing this file, and no sentence here
 is offered as their wording. Mac Lane, “Categories for the Working
 Mathematician”, 2nd ed., V.2; Awodey, “Category Theory”, 2nd ed., 2.6
 and the example in 3.2; Riehl, “Category Theory in Context”, 1.2, 3.1
 and 3.6; Fong and Spivak, “An Invitation to Applied Category Theory
 (Seven Sketches in Compositionality)”, 3.5.1 and 6.2.

 WHAT CARRIES CONTENT, AND WHAT DEGENERATES.  [Proset P] is thin: its
 hom-setoid equivalence is the constant relation [True], by the
 construction in Instance/Proset.v ([proset_equiv_is_True] below states
 this literally and proves it by [eq_refl]). Consequently every
 requirement that is an EQUATION between parallel morphisms holds by
 [Logic.I] and constrains nothing:

 - the [Proper] obligation [fork_respects] of Structure/Cartesian.v;
 - both halves of [ump_products] there;
 - the [cone_coherence] field of Structure/Cone.v, for every shape of
 diagram — this is why the identification below holds at an
 arbitrary index category and not merely at a discrete one;
 - the commutation clause and the [uniqueness] clause of the [∃!]
 in [ump_limits] / [ump_limit] of Structure/Limit.v;
 - [one_unique] of Structure/Terminal.v.

 What carries the mathematics is exactly the DATA:

 - the apex object [m] ([product_obj], [terminal_obj], the cone
 vertex) — the candidate bound;
 - the leg family ([exl], [exr], [vertex_map], [iprod_proj]) — the
 lower-bound clause of [IsGLB];
 - the mediating arrow ([fork], the [unique_obj] of the [∃!]) — the
 greatest clause of [IsGLB].

 So “limit = greatest lower bound” is an identification of data, with
 the proof obligations on both sides degenerate. Following the same
 discipline, this file does not leave that observation unguarded:
 [nat_glb_not_4] refutes an [IsGLB] claim over a concrete preorder, and
 [discrete_two_no_initial] and [discrete_two_no_cartesian] exhibit a
 preorder that has neither a least element nor binary meets. The
 predicates are therefore not uniformly inhabited, and the theorems
 above are not statements about an empty distinction.

 COORDINATION WITH ADJACENT WORK.  Two neighbouring developments touch
 the same vocabulary, and this file is written to stay clear of both.
 (i) A Galois-connection development for a preorder (issue #380)
 introduces a [Thin] predicate with [proset_thin] and companion lemmas
 in a separate Instance/Proset/ module. This file deliberately
 introduces no such predicate and does not require that module:
 wherever thinness is needed it is used concretely, as the fact that
 the hom-setoid of [Proset P] is the constant-[True] setoid.
 (ii) Order-theoretic vocabulary proper — meet- and join-semilattices,
 lattices, Heyting and Boolean algebras — is claimed by a separate
 Structure/Lattice.v effort (issues #340, #389, #1003). This file
 therefore defines no [Meet], [Join], [Lattice] or [BooleanAlgebra]
 class and creates no such module: [IsGLB] and [IsLUB] below are
 family-level PREDICATES over a bare [PreOrder], not an algebraic
 structure, and the four constructors [Proset_Cartesian],
 [Proset_Cocartesian], [Proset_Terminal] and [Proset_Initial] are
 exactly the interface such a class would later consume. 

 --------
 nLab:  https://ncatlab.org/nlab/show/preorder 
 nLab:  https://ncatlab.org/nlab/show/thin+category 
 nLab:  https://ncatlab.org/nlab/show/join 
 Wikipedia:  https://en.wikipedia.org/wiki/Infimum_and_supremum 

 将一个预序  [(A, R)]  视为 Instance/Proset.v 的薄范畴  [Proset P]，其中  [x ~> y]  是关系  [R x y] 本身。
 在该对应下，范畴的通用构造变为序理论中的构造：

 - 一个积   x × y   是 x 和 y 的最大下界（交）；
 - 一个终对象   1   是最大元素（顶）；
 - 一个图的极限是其对象族的最大下界，无论图的形状如何；

 对偶地，余积是最小上界（并），初对象是最小元素，余极限是最小上界。引用仅表示位置。以下段落所引用的是声明所在的位置，而不是从所查阅的副本中释义；在准备此文件时没有阅读这些来源，也没有以其中的措辞提供任何句子。Mac Lane，《面向工作数学家的范畴论》，第二版，第2卷；Awodey，《范畴论》，第二版，2.6和3.2中的示例；Riehl，《语境中的范畴论》，1.2, 3.1和3.6；Fong和Spivak，《应用范畴论邀请（组合性的七个草图）》，3.5.1和6.2。什么承载内容，什么退化。[Proset P] 是薄的：其同类集合等价关系是常量关系 [True]，根据 Instance/Proset.v 中的构造（下面的 [proset_equiv_is_True] 字面上陈述了这一点，并通过 [eq_refl] 证明）。因此，每一个在平行态射之间的等式的要求都由 [Logic.I] 成立，并且不约束任何东西：- Structure/Cartesian.v 的 [Proper] 义务；
 -  [ump_products] 的两部分；
 - Structure/Cone.v 的 [cone_coherence] 域，对于每种图形 — 这就是为什么以下在任意指标范畴下成立，而不仅仅是在离散范畴下；
 - Structure/Limit.v 中  [ump_limits] / [ump_limit] 的交换条款和 [∃!] 的 [uniqueness] 条款；
 - Structure/Terminal.v 的 [one_unique]。

 支撑数学的恰恰是这些数据：- 顶点对象 [m]（[product_obj]，[terminal_obj]，锥顶）——候选界限；
 - 腿族（[exl]，[exr]，[vertex_map]，[iprod_proj]）——[IsGLB] 的下界子句；
 - 中介箭头（[fork]，[∃!] 的 [unique_obj]）——[IsGLB] 的最大子句。因此“极限 = 最大下界”是一种数据的识别，其双方的证明义务都退化了。遵循相同的原则，这个文件没有忽视这一观察：[nat_glb_not_4] 反驳了关于具体预序的 [IsGLB] 的主张，而 [discrete_two_no_initial] 和 [discrete_two_no_cartesian] 展示了一个既没有最小元素也没有二元上确界的预序。因此，这些谓词不是统一可居的，上述定理也不是关于空区分的陈述。与相邻工作的协调。两个相邻的开发项目使用相同的词汇，本文件编写的目的是避免与两者冲突。(i) 用于前序的 Galois 连接开发（问题 #380）引入了一个 [Thin] 谓词及其伴随引理 [proset_thin]，在一个单独的 Instance/Proset/ 模块中。本文件故意不引入此类谓词，也不依赖该模块：在需要薄性时，它被具体使用，作为 [Proset P] 的同态集是常数 [True] 集的事实。(ii) 适当的序理论词汇——会合半格和并半格、格、Heyting 代数和布尔代数——由一个单独的 Structure/Lattice.v 项目负责（问题 #340，#389，#1003）。因此，本文件未定义任何 [Meet]、[Join]、[Lattice] 或 [BooleanAlgebra] 类，也未创建任何此类模块：[IsGLB] 和 [IsLUB] 下面是对裸 [PreOrder] 的家族级谓词，而不是代数结构，并且四个构造函数 [Proset_Cartesian]、[Proset_Cocartesian]、[Proset_Terminal] 和 [Proset_Initial] 正是这样的类以后会使用的接口。
*)

(** ** Bounds over a preorder / ** 预序上的界 *)

(*
 [R] is kept explicit in the bound predicates: it does not occur in the
 types of [d] or [m], so an implicit binder would be unresolvable at
 the use sites. Families are indexed by an arbitrary [Type]; the
 library carries no subset machinery, so “every subset has an
 infimum” is modelled throughout as “every [Type]-indexed family has
 a greatest lower bound”. 

 --------
 [R] 在绑定谓词中保持显式：它不会出现在 [d] 或 [m] 的类型中，因此在使用位置上隐式绑定无法解析。族由任意 [Type] 索引；库中不包含子集机制，因此“每个子集都有下确界”在整个过程中被建模为“每个 [Type] 索引的族都有最大下界”。
*)

(* [m] is a lower bound of the family [d]. / [m] 是 [d] 系列的下界。 *)
Definition IsLowerBound {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type :=
  ∀ i : Ix, R m (d i).

(*
 [m] is a greatest lower bound (an infimum, a meet) of [d]: a lower
 bound that every other lower bound precedes. 

 --------
 [m] 是 [d] 的最大下界（下确界，交）：每个其他下界都在其之前的下界。
*)
Definition IsGLB {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type :=
  IsLowerBound R d m * (∀ n : A, IsLowerBound R d n → R n m).

(*
 The reversed preorder. Upper bounds and least upper bounds are the
 lower bounds and greatest lower bounds of it — definitionally, so
 that every dual statement below is the original one read at
 [op_rel R] and no dual proof is written twice. 

 --------
 反向前序。上界和最小上界就是它的下界和最大下界——从定义上讲，因此下面的每一个对偶陈述都是在 [op_rel R] 上读取的原始陈述，并且没有对偶证明被重复书写。
*)
Definition op_rel {A : Type} (R : relation A) : relation A :=
  fun x y => R y x.

Definition op_PreOrder {A : Type} {R : relation A} (P : PreOrder R) :
  PreOrder (op_rel R) :=
  {| PreOrder_Reflexive := fun x => @PreOrder_Reflexive A R P x;
     PreOrder_Transitive :=
       fun x y z Hxy Hyz => @PreOrder_Transitive A R P z y x Hyz Hxy |}.

Definition IsUpperBound {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type := IsLowerBound (op_rel R) d m.

Definition IsLUB {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m : A) : Type := IsGLB (op_rel R) d m.

(*
 Uniqueness of an infimum, and of a supremum. Without antisymmetry the
 sharpest available conclusion is mutual precedence, which is exactly
 isomorphism of the two apexes in [Proset P]; over a poset
 (Instance/Poset.v, where [Poset P] is [Proset P] with an
 antisymmetry constraint) it upgrades to equality by antisymmetry.

 The supremum statement is obtained by reading the infimum statement
 at the reversed preorder, since [IsLUB R] is by definition
 [IsGLB (op_rel R)]: [lub_unique] below is literally [glb_unique]
 applied to [op_rel R], with no second argument. That is the
 duality-respecting formulation, in which the dual proof establishes
 the dual result rather than a fresh proof being written. 

 --------
 下确界和上确界的唯一性。如果没有反对称性，可得出的最强结论是相互优先，这正是 [Proset P] 中两个顶点的同构；在一个偏序集合 (Instance/Poset.v，其中 [Poset P] 是带有反对称性约束的 [Proset P]) 上，通过反对称性可以升级为相等。

 上确界的陈述可以通过在逆序前序下读取下确界的陈述来获得，因为 [IsLUB R] 按定义是 [IsGLB (op_rel R)]：下面的 [lub_unique] 字面上就是 [glb_unique] 应用于 [op_rel R]，没有第二个参数。这就是尊重对偶性的表述，其中对偶的证明确立了对偶的结果，而不是写一个新的证明。
*)
Definition glb_unique {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m m' : A) (G : IsGLB R d m) (G' : IsGLB R d m') :
  R m m' * R m' m :=
  (snd G' m (fst G), snd G m' (fst G')).

Definition lub_unique {A : Type} (R : relation A) {Ix : Type}
  (d : Ix → A) (m m' : A) (G : IsLUB R d m) (G' : IsLUB R d m') :
  R m' m * R m m' :=
  glb_unique (op_rel R) d m m' G G'.

(* The binary family, used to read a two-element meet as a product. / 二元族，用于将两个元素的会合读取为乘积。 *)
Definition pair_family {A : Type} (x y : A) : bool → A :=
  fun b => if b then x else y.

(*
 The empty family, used to read a greatest element as the nullary
 meet. A greatest element is exactly a greatest lower bound of it,
 matching the fact that the terminal object is the limit of the empty
 diagram; the least/supremum form is the same statement at the
 reversed preorder, with no second proof. 

 --------
 空族，用于将最大元素读作零元会（nullary meet）。最大元素恰好是它的最大下界，这与终对象是空图的极限的事实相符合；最小/上确界的形式是在逆序预序上的相同陈述，无需第二个证明。
*)
Definition empty_family {A : Type} : False → A := fun e => match e with end.

Lemma greatest_iff_empty_glb {A : Type} (R : relation A) (top : A) :
  (∀ x, R x top) ↔ IsGLB R (@empty_family A) top.
Proof.
  split.
  - intro Htop; split; [ intros [] | intros n _; exact (Htop n) ].
  - intros [_ Hg] x; exact (Hg x (fun e => match e with end)).
Qed.

Definition least_iff_empty_lub {A : Type} (R : relation A) (bot : A) :
  (∀ x, R bot x) ↔ IsLUB R (@empty_family A) bot :=
  greatest_iff_empty_glb (op_rel R) bot.

(*
 Completeness of the order, in the form the bicompleteness statement
 consumes below. 

 --------
 订单的完整性，以下以双完备性声明的形式体现。
*)
Definition HasAllMeets {A : Type} (R : relation A) : Type :=
  ∀ (Ix : Type) (d : Ix → A), { m : A & IsGLB R d m }.

Definition HasAllJoins {A : Type} (R : relation A) : Type :=
  HasAllMeets (op_rel R).

Section Proset_Limits.

Context {A : Type} {R : relation A} (P : PreOrder R).

(** ** Thinness, stated concretely / ** 瘦，具体说明 *)

(*
 Every equivalence of parallel morphisms in [Proset P] is the
 proposition [True], by construction of the hom-setoid in
 Instance/Proset.v. This is the one fact about thinness this file
 uses, and it holds by [eq_refl]. No [Thin] predicate is introduced;
 see the coordination note in the header. 

 --------
 在  [Proset P]  中，每个平行态射的等价都是命题  [True] ，这是通过在 Instance/Proset.v 中构造同态集而得出的。这是该文件使用的关于稀薄性（thinness）的唯一事实，并且它由  [eq_refl]  保证。没有引入  [Thin]  谓词；请参见标题中的协调说明。
*)
Lemma proset_equiv_is_True (x y : A) (f g : x ~{Proset P}~> y) :
  (f ≈ g) = True.
Proof. reflexivity. Qed.

(** ** Binary products are meets / ** 二元产品是相交 *)

(*
 Structure ⇒ order: the chosen product object of a cartesian structure
 on [Proset P] is a greatest lower bound of its two factors. The two
 projections ARE the lower-bound clause and [fork] IS the greatest
 clause; each bullet below is a projection of the class, not a
 proof step. 

 --------
 结构 ⇒ 顺序：笛卡尔结构 [Proset P] 上选定的产品对象是其两个因子的最大下界。这两个投影分别是下界子句，而 [fork] 是最大子句；下面的每一个要点都是该类的投影，而不是证明步骤。
*)
Lemma cartesian_product_IsGLB (CP : @Cartesian (Proset P)) (x y : A) :
  IsGLB R (pair_family x y) (@product_obj (Proset P) CP x y).
Proof.
  split.
  - intros [|].
    + exact (@exl (Proset P) CP x y).
    + exact (@exr (Proset P) CP x y).
  - intros n Hn.
    exact (@fork (Proset P) CP n x y (Hn true) (Hn false)).
Qed.

(*
 Order ⇒ structure: a choice of binary meets equips [Proset P] with a
 cartesian structure. Both law fields are equations between parallel
 morphisms of a thin category, so the global obligation tactic
 discharges them and the whole mathematical content is the data
 supplied here. 

 --------
 顺序 ⇒ 结构：一个二元运算的选择为 [Proset P] 配备了一个笛卡尔结构。两个律场都是薄范畴中平行态射之间的方程，因此全局约束策略可以解决它们，整个数学内容就是这里提供的数据。
*)
Program Definition Proset_Cartesian
  (glb : A → A → A)
  (glb_l : ∀ x y, R (glb x y) x)
  (glb_r : ∀ x y, R (glb x y) y)
  (glb_greatest : ∀ n x y, R n x → R n y → R n (glb x y)) :
  @Cartesian (Proset P) := {|
  product_obj := glb;
  fork := fun x y z f g => glb_greatest x y z f g;
  exl := fun x y => glb_l x y;
  exr := fun x y => glb_r x y
|}.

(*
 Dually, a choice of binary joins equips [Proset P] with a cocartesian
 structure. Recall from Structure/Cocartesian.v that [Cocartesian C]
 is notation for [@Cartesian (C^op)] — there is no separate class — so
 the fields below are read in the opposite category and the
 “projections” run [x ~> lub x y]. 

 --------
 同样，二元并的选择为 [Proset P] 配备了一个余笛卡尔结构。回忆 Structure/Cocartesian.v 中的内容，[Cocartesian C] 是 [@Cartesian (C^op)] 的符号表示——没有单独的类——因此下面的字段在对立范畴中读取，“投影”运行 [x ~> lub x y]。
*)
Program Definition Proset_Cocartesian
  (lub : A → A → A)
  (lub_l : ∀ x y, R x (lub x y))
  (lub_r : ∀ x y, R y (lub x y))
  (lub_least : ∀ n x y, R x n → R y n → R (lub x y) n) :
  @Cocartesian (Proset P) := {|
  product_obj := lub;
  fork := fun x y z f g => lub_least x y z f g;
  exl := fun x y => lub_l x y;
  exr := fun x y => lub_r x y
|}.

(* The dual of [cartesian_product_IsGLB]: a chosen coproduct is a join. / [cartesian_product_IsGLB] 的对偶：一个选定的余积是一个并。 *)
Lemma cocartesian_coproduct_IsLUB (CP : @Cocartesian (Proset P)) (x y : A) :
  IsLUB R (pair_family x y) (@product_obj ((Proset P)^op) CP x y).
Proof.
  split.
  - intros [|].
    + exact (@exl ((Proset P)^op) CP x y).
    + exact (@exr ((Proset P)^op) CP x y).
  - intros n Hn.
    exact (@fork ((Proset P)^op) CP n x y (Hn true) (Hn false)).
Qed.

(* * ** Terminal is greatest, initial is least / * ** 终端最大，起始最小 *)

Program Definition Proset_Terminal (top : A) (Htop : ∀ x, R x top) :
  @Terminal (Proset P) := {| terminal_obj := top; one := Htop |}.

Definition terminal_is_greatest (T : @Terminal (Proset P)) :
  ∀ x, R x (@terminal_obj (Proset P) T) := fun x => @one (Proset P) T x.

(* [Initial C] is notation for [@Terminal (C^op)] (Structure/Initial.v), so the record is built with the field names [terminal_obj] and [one], whose op-reading gives [R bot x]. / [Initial C] 是 [@Terminal (C^op)]（Structure/Initial.v）的表示法，因此该记录是用字段名 [terminal_obj] 和 [one] 构建的，其操作读取结果为 [R bot x]。 *)
Program Definition Proset_Initial (bot : A) (Hbot : ∀ x, R bot x) :
  @Initial (Proset P) := {| terminal_obj := bot; one := Hbot |}.

Definition initial_is_least (Iobj : @Initial (Proset P)) :
  ∀ x, R (@terminal_obj ((Proset P)^op) Iobj) x :=
  fun x => @one ((Proset P)^op) Iobj x.

(* The nullary case of the identification is [greatest_iff_empty_glb] above, stated over the bare preorder. / 上述识别的零元情况是 [greatest_iff_empty_glb]，在裸前序上陈述。 *)

(** ** Cones over a thin category / ** 薄范畴上的圆锥 *)

(*
 A cone over ANY diagram valued in [Proset P] is nothing but a lower
 bound of the diagram's objects: the leg family is the lower-bound
 clause, and the coherence condition [fmap[F] f ∘ ψ x ≈ ψ y] is an
 equation in a thin category, hence [Logic.I]. This is the single
 observation that makes the identification below independent of the
 shape [J]. 

 --------
 在  [Proset P] 中取值的任意图的锥，只不过是该图对象的下界：leg 家族就是下界子句，而相干条件  [fmap[F]  f ∘ ψ x ≈ ψ y] 是薄范畴中的一个等式，因此  [Logic.I] 。这是唯一的观察，使得下面的识别与形状  [J] 无关。
*)
Definition proset_cone {J : Category} (F : J ⟶ Proset P) (n : A)
  (Hn : IsLowerBound R (fobj[F]) n) : Cone F.
Proof.
  unshelve econstructor.
  - exact n.                             (* apex: the candidate bound / 顶点：被绑的候选人 *)
  - unshelve econstructor.
    + exact Hn.                          (* legs: the lower-bound clause / 腿：下界从句 *)
    + intros x y f; exact Logic.I.       (* coherence: degenerate, thin / 一致性：退化，稀薄 *)
Defined.

(*
 The same statement in the opposite category, used for the colimit
 half. Note that [(Proset P)^op] is NOT [Proset (op_PreOrder P)] by
 definitional unfolding — the two categories have distinct
 Program-generated law fields — so the dual construction is carried
 out directly rather than by re-instantiating [Proset] at the
 reversed relation. Its hom-setoid is nonetheless the same
 constant-[True] setoid, so the coherence condition degenerates in
 exactly the same way. 

 --------
 在相反的范畴中使用相同的陈述，用于余极限的一半。注意，[(Proset P)^op] 并不是 [Proset (op_PreOrder P)]，根据定义展开——这两个范畴有不同的程序生成的法则字段——所以对偶构造是直接执行的，而不是通过在反转关系中重新实例化 [Proset] 来实现的。尽管如此，它的 Hom-setoid 仍然是相同的常量 [True] 集合，所以相干性条件以完全相同的方式退化。
*)
Definition proset_op_cone {J : Category} (G : J ⟶ (Proset P)^op) (n : A)
  (Hn : ∀ j : J, R (G j) n) : Cone G.
Proof.
  unshelve econstructor.
  - exact n.
  - unshelve econstructor.
    + exact Hn.
    + intros x y f; exact Logic.I.
Defined.

(* * ** The identification, at an arbitrary diagram shape / * ** 在任意图形上的识别 *)

(*
 An object is a limit of [F] exactly when it is a greatest lower bound
 of the family of objects of [F]. Both directions are the data
 transposition described in the header: legs against lower-bound
 clause, mediating arrow against greatest clause. 

 --------
 一个对象是 [F] 的极限，当且仅当它是 [F] 对象族的最大下界。两个方向都是标题中描述的数据换位：支腿对应下界子句，中介箭头对应最大子句。
*)

Definition Proset_IsALimit {J : Category} (F : J ⟶ Proset P) (m : A)
  (H : IsGLB R (fobj[F]) m) : IsALimit F m.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + exact (fst H).
    + intros x y f; exact Logic.I.
  - intro N.
    unshelve econstructor.
    + exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
    + intro x; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

Definition isalimit_IsGLB {J : Category} (F : J ⟶ Proset P) (c : A)
  (H : IsALimit F c) : IsGLB R (fobj[F]) c.
Proof.
  split.
  - exact (fun j => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) j).
  - intros n Hn.
    exact (unique_obj (@ump_limit _ _ _ _ H (proset_cone F n Hn))).
Defined.

Theorem proset_limit_iff_glb {J : Category} (F : J ⟶ Proset P) (c : A) :
  IsALimit F c ↔ IsGLB R (fobj[F]) c.
Proof.
  split.
  - exact (isalimit_IsGLB F c).
  - exact (Proset_IsALimit F c).
Defined.

(* The unpinned form, for callers holding the [Limit] class. / 未固定的表格，适用于持有 [Limit] 类的呼叫者。 *)
Program Definition Proset_Limit_general {J : Category} (F : J ⟶ Proset P)
  (m : A) (H : IsGLB R (fobj[F]) m) : Limit F := {|
  limit_cone := proset_cone F m (fst H)
|}.
Next Obligation.
  unshelve econstructor.
  - exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
  - intro x; exact Logic.I.
  - intros v Hv; exact Logic.I.
Defined.

Definition limit_general_IsGLB {J : Category} (F : J ⟶ Proset P)
  (L : Limit F) : IsGLB R (fobj[F]) (vertex_obj[L]) :=
  isalimit_IsGLB F _ (limit_is_alimit L).

(*
 Dually: an object is a colimit of [F] exactly when it is a least
 upper bound of the family of objects of [F]. [IsAColimit F c] is
 [IsALimit (F^op) c] (Structure/Limit/Preservation.v), whose legs run
 [F j ~> c] in [Proset P], that is [R (F j) c]. 

 --------
 对偶地：当且仅当一个对象是  [F]  对象族的最小上界时，它是  [F] 的余极限。  [IsAColimit F c] 是  [IsALimit (F^op) c] （Structure/Limit/Preservation.v），其箭头在  [Proset P] 中运行，即  [R (F j) c]。
*)

Definition Proset_IsAColimit {J : Category} (F : J ⟶ Proset P) (m : A)
  (H : IsLUB R (fobj[F]) m) : IsAColimit F m.
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + exact (fst H).
    + intros x y f; exact Logic.I.
  - intro N.
    unshelve econstructor.
    + exact (snd H _ (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
    + intro x; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

Definition isacolimit_IsLUB {J : Category} (F : J ⟶ Proset P) (c : A)
  (H : IsAColimit F c) : IsLUB R (fobj[F]) c.
Proof.
  split.
  - exact (fun j => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) j).
  - intros n Hn.
    exact (unique_obj (@ump_limit _ _ _ _ H (proset_op_cone (F^op) n Hn))).
Defined.

Theorem proset_colimit_iff_lub {J : Category} (F : J ⟶ Proset P) (c : A) :
  IsAColimit F c ↔ IsLUB R (fobj[F]) c.
Proof.
  split.
  - exact (isacolimit_IsLUB F c).
  - exact (Proset_IsAColimit F c).
Defined.

(* * ** The discrete case: indexed products are indexed meets / * ** 离散情况：索引乘积是索引交集 *)

(*
 A family [d : Ix → A] is a functor out of the discrete category on
 [Ix] via [DiscreteCat_Functor], and Structure/Limit/Product.v reads a
 limit of that diagram as an indexed product. This is the special case
 [J := DiscreteCat Ix] of the theorems above, kept as a separate
 interface because that is the form indexed consumers want; nothing
 new is proved. 

 --------
 一个族  [d : Ix → A]  是从离散范畴 [Ix]  通过  [DiscreteCat_Functor]  出去的函子，而 Structure/Limit/Product.v 将该图的极限读作一个索引积。这是上述定理的特殊情况 [J := DiscreteCat Ix] ，作为一个独立的接口保留，因为这是索引使用者希望的形式；没有证明新的内容。
*)

Program Definition Proset_Limit {Ix : Type} (d : Ix → A) (m : A)
  (H : IsGLB R d m) :
  Limit (DiscreteCat_Functor (C:=Proset P) d) :=
  Proset_Limit_general (DiscreteCat_Functor (C:=Proset P) d) m H.

Definition limit_IsGLB {Ix : Type} (d : Ix → A)
  (L : Limit (DiscreteCat_Functor (C:=Proset P) d)) :
  IsGLB R d (iprod (C:=Proset P) d L).
Proof.
  split.
  - intro i; exact (iprod_proj (C:=Proset P) d L i).
  - intros n Hn.
    exact (unique_obj (iprod_ump (C:=Proset P) d L n Hn)).
Defined.

(* The elementary indexed-product reading, for callers that prefer the [IsIndexedProduct] record of Structure/Limit/Product.v to the [Limit] class. / 对于那些更喜欢 Structure/Limit/Product.v 的 [IsIndexedProduct] 记录而不是 [Limit] 类的调用者，基本索引产品读取。 *)
Definition Proset_IsIndexedProduct {Ix : Type} (d : Ix → A) (m : A)
  (H : IsGLB R d m) :
  IsIndexedProduct (C:=Proset P) d m (fst H).
Proof.
  constructor; intros c pi.
  unshelve econstructor.
  - exact (snd H c pi).
  - intro a; exact Logic.I.
  - intros v Hv; exact Logic.I.
Defined.

(** ** Bicompleteness / ** 双完备性 *)

(*
 The complete-lattice form of the identification: the thin category of
 a preorder is complete exactly when the preorder has all
 [Type]-indexed infima. [Complete] here is the library's own
 unrestricted predicate (Structure/Complete.v), quantifying over every
 diagram category with no smallness side condition, so this is
 completeness at the library's universe discipline rather than
 small-completeness.

 Both halves are stated: [proset_Complete_iff_all_meets] for infima and
 [proset_Cocomplete_iff_all_joins] for suprema, the latter over
 [Cocomplete (Proset P)] itself rather than [Complete] at the reversed
 preorder (the two readings are not definitionally equal).  That the two
 HYPOTHESES are not independent — all infima already yield all suprema, a
 supremum being the infimum of the family of upper bounds — is the
 standard complete-lattice redundancy; it is treated separately (issue
 #684) and is not re-proved here. 

 --------
 识别的完全格形式：预序的薄范畴仅当预序具有所有 [Type] 索引的下确界时才是完全的。这里的 [Complete] 是库自身的无限制谓词（Structure/Complete.v），量化于每一个没有小性条件的图范畴，因此这是库的宇宙学科下的完全性，而不是小完全性。两半部分都已说明：下确界为 [proset_Complete_iff_all_meets]，上确界为 [proset_Cocomplete_iff_all_joins]，后者是针对 [Cocomplete (Proset P)] 本身而非在逆序预顺序下的 [Complete]（这两种读法在定义上并不相等）。这两个假设并非独立——所有下确界已经能得出所有上确界，因为上确界是上界族的下确界——这是标准的完全格冗余；该问题已单独处理（问题 #684），此处不再重新证明。
*)
Theorem proset_Complete_iff_all_meets :
  @Complete (Proset P) ↔ HasAllMeets R.
Proof.
  split.
  - intros HC Ix d.
    exists (vertex_obj[HC (DiscreteCat Ix)
                          (@DiscreteCat_Functor Ix (Proset P) d)]).
    exact (limit_general_IsGLB
             (@DiscreteCat_Functor Ix (Proset P) d)
             (HC (DiscreteCat Ix) (@DiscreteCat_Functor Ix (Proset P) d))).
  - intros HM D F.
    exact (Proset_Limit_general F
             (projT1 (HM (obj[D]) (fun j : D => F j)))
             (projT2 (HM (obj[D]) (fun j : D => F j)))).
Defined.

(** ** Pushouts from joins / ** 来自连接的推出 *)

(*
 Since a colimit of any diagram is the join of its objects, pushouts
 exist in [Proset P] as soon as binary joins do: the apex of the
 pushout of a span is the join of its two feet, and the span itself
 contributes nothing, its commutation condition being an equation in a
 thin category. 

 --------
 由于任何图的余极限都是其对象的并，推动出（pushouts）在 [Proset P] 中一旦存在二元并就存在：一个跨度（span）的推动顶点是其两个底点的并，而跨度本身不贡献任何东西，其交换条件在一个薄范畴中就是一个方程。
*)
Program Definition Proset_HasPushouts
  (lub : A → A → A)
  (lub_l : ∀ x y, R x (lub x y))
  (lub_r : ∀ x y, R y (lub x y))
  (lub_least : ∀ n x y, R x n → R y n → R (lub x y) n) :
  HasPushouts (Proset P) := {| pushout := fun x y z f g => _ |}.
Next Obligation.
  unshelve econstructor.
  - exact (lub y z).
  - exact (lub_l y z).
  - exact (lub_r y z).
  - exact Logic.I.
  - intros q i1 i2 Hc.
    unshelve econstructor.
    + exact (lub_least q y z i1 i2).
    + split; exact Logic.I.
    + intros v Hv; exact Logic.I.
Defined.

(* Conversely, any pushout apex in [Proset P] is a join of the two feet of the span. / 相反，[Proset P] 中的任何推顶点都是该跨度两个端点的连接。 *)
Lemma proset_pushout_IsLUB {x y z : A}
  (f : x ~{Proset P}~> y) (g : x ~{Proset P}~> z)
  (Q : IsPushout (C:=Proset P) f g) :
  IsLUB R (pair_family y z) (pushout_apex Q).
Proof.
  split.
  - intros [|].
    + exact (pushout_in1 Q).
    + exact (pushout_in2 Q).
  - intros n Hn.
    exact (unique_obj (pushout_ump Q n (Hn true) (Hn false) Logic.I)).
Qed.

(*
 The join half, PROVED rather than left to duality-by-remark: an earlier
 revision stated only the meet side under a “bicompleteness” heading; the
 verifier of that revision assembled this biconditional from the file's
 own pieces, and it is landed here so the heading is earned.  Note the
 conclusion is [Cocomplete (Proset P)] itself, not
 [Complete (Proset (op_PreOrder P))] -- the two are NOT definitionally
 equal (checked by a rejected [eq_refl] probe). 

 --------
 连接部分，是被证明的，而不是留给通过备注的二元性：早期的修订在“二完全性”标题下仅说明了会聚侧；该修订的验证者从文件本身的部分组装了这个双条件，并将其放在这里，因此标题是有根据的。注意，结论是 [Cocomplete (Proset P)] 本身，而不是 [Complete (Proset (op_PreOrder P))]——两者在定义上并不相等（通过被拒绝的 [eq_refl] 探针检验）。
*)
Theorem proset_Cocomplete_iff_all_joins : @Cocomplete (Proset P) ↔ HasAllJoins R.
Proof.
  split.
  - intros HC Ix d.
    exists (vertex_obj[HC (DiscreteCat Ix)
                        (@DiscreteCat_Functor Ix (Proset P) d)]).
    exact (isacolimit_IsLUB (@DiscreteCat_Functor Ix (Proset P) d) _
             (limit_is_alimit (HC (DiscreteCat Ix)
                                 (@DiscreteCat_Functor Ix (Proset P) d)))).
  - intros HJ D F.
    unshelve econstructor.
    + exact (proset_op_cone (F^op)
               (projT1 (HJ (obj[D]) (fun j : D => F j)))
               (fst (projT2 (HJ (obj[D]) (fun j : D => F j))))).
    + intro N.
      unshelve econstructor.
      * exact (snd (projT2 (HJ (obj[D]) (fun j : D => F j))) _
                 (fun j => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) j)).
      * intro x; exact Logic.I.
      * intros v Hv; exact Logic.I.
Defined.

(*
 Hence the pushout of any span coincides with the coproduct of its two
 feet: both are joins of the same pair, and two joins of one family
 precede each other. In [Proset P] mutual precedence is exactly
 isomorphism of the two objects. 

 --------
 因此，任何跨度的推出与其两个底的余积一致：两者都是同一对的上确界，而一个族的两个上确界彼此互为前置。在 [Proset P] 中，相互前置正好是两个对象的同构。
*)
Definition pushout_is_coproduct_of_feet (CP : @Cocartesian (Proset P))
  {x y z : A} (f : x ~{Proset P}~> y) (g : x ~{Proset P}~> z)
  (Q : IsPushout (C:=Proset P) f g) :
  R (@product_obj ((Proset P)^op) CP y z) (pushout_apex Q)
  * R (pushout_apex Q) (@product_obj ((Proset P)^op) CP y z) :=
  lub_unique R (pair_family y z) (pushout_apex Q)
    (@product_obj ((Proset P)^op) CP y z)
    (proset_pushout_IsLUB f g Q)
    (cocartesian_coproduct_IsLUB CP y z).

End Proset_Limits.

(*
 The dual indexed statement is this development applied to the
 reversed preorder: [IsLUB R d m] is by definition [IsGLB (op_rel R)
 d m], so a least upper bound of the original preorder is a limiting
 cone in [Proset (op_PreOrder P)]. 

 --------
 双重索引语句是这个发展应用于逆序前序：[IsLUB R d m] 根据定义是 [IsGLB (op_rel R) d m]，因此原始前序的最小上界是在 [Proset (op_PreOrder P)] 中的一个极限圆锥。
*)
Definition Proset_LUB_Limit {A : Type} {R : relation A} (P : PreOrder R)
  {Ix : Type} (d : Ix → A) (m : A) (H : IsLUB R d m) :
  Limit (DiscreteCat_Functor (C:=Proset (op_PreOrder P)) d) :=
  Proset_Limit (op_PreOrder P) d m H.

(*
 Named for what it concludes: [Complete] at the REVERSED preorder.  The
 genuine cocompleteness corollary follows from the biconditional above. 

 --------
 以其结论命名：在反向前序中的 [Complete]。真正的余完备性推论来自上述的双条件。
*)
Definition Proset_op_Complete_of_all_joins {A : Type} {R : relation A}
  (P : PreOrder R) (H : HasAllJoins R) :
  @Complete (Proset (op_PreOrder P)) :=
  snd (proset_Complete_iff_all_meets (op_PreOrder P)) H.

Definition Proset_Cocomplete_of_all_joins {A : Type} {R : relation A}
  (P : PreOrder R) (H : HasAllJoins R) :
  @Cocomplete (Proset P) :=
  snd (proset_Cocomplete_iff_all_joins P) H.

(* * ** Equivalence-invariance of completeness / * ** 完备性的等价不变性 *)

(*
 Theory/Equivalence/Limit.v transports an individual limit along an
 equivalence ([equivalence_creates_limits]) but does not record that
 the completeness PREDICATE is invariant. The two lemmas below supply
 that, by running the transport at the quasi-inverse, which is itself
 an equivalence (Theory/Equivalence.v, [EquivalenceOfCategories_sym]).

 PLACEMENT.  These are general statements about categories, not about
 prosets, and Theory/Equivalence/Limit.v would be their natural home;
 they are kept here because that file does not currently depend on
 Structure/Complete.v and adding the dependency to a shared Theory/
 module is a change with a wider blast radius than this issue needs.
 Moving them later is a pure relocation.

 The intended order-theoretic corollary — a preorder is bicomplete
 exactly when its skeletal poset is — is NOT stated, because the
 library has no skeleton construction for a preorder (the quotient by
 mutual precedence, together with the equivalence between a preorder
 and that quotient). Once such a construction exists the corollary is
 an immediate instance of the two lemmas below; until then it is
 deliberately left unclaimed. 

 --------
 Theory/Equivalence/Limit.v 沿着一个等价 ([equivalence_creates_limits]) 传递单个极限，但并未记录完备谓词 (completeness PREDICATE) 是不变的。下面的两个引理提供了这一点，通过在准逆 (quasi-inverse) 上运行传递，而该准逆本身就是一个等价 (Theory/Equivalence.v, [EquivalenceOfCategories_sym])。

 位置说明。这些是关于范畴的通用陈述，而不是关于前序集合 (prosets) 的，Theory/Equivalence/Limit.v 本应是它们的自然归属；它们之所以保留在这里，是因为该文件目前不依赖 Structure/Complete.v，而向共享的 Theory/ 模块添加依赖会带来比此问题所需更广泛的影响。以后移动它们纯粹是位置调整。预期的序理论推论——一个预序是双完全的，当且仅当它的骨架偏序是双完全的——没有被陈述，因为库中没有预序的骨架构造（通过相互优先关系的商，以及预序与该商之间的等价）。一旦存在这样的构造，该推论就是下面两个引理的直接例子；在那之前，它故意未被声明。
*)

Section Complete_Invariance.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

Definition Complete_equivalence_invariant (HC : @Complete C) : @Complete D :=
  fun J H =>
    @equivalence_creates_limits D C (@quasi_inverse C D F E)
      (@EquivalenceOfCategories_sym C D F E) J H
      (HC J (@quasi_inverse C D F E ◯ H)).

Definition Cocomplete_equivalence_invariant (HC : @Cocomplete C) :
  @Cocomplete D :=
  fun J H =>
    @equivalence_creates_colimits D C (@quasi_inverse C D F E)
      (@EquivalenceOfCategories_sym C D F E) J H
      (HC J (@quasi_inverse C D F E ◯ H)).

End Complete_Invariance.

(* * ** The two existing thin witnesses, read through the identification / * ** 现有的两份简略证据，通过鉴定进行审阅 *)

(*
 [Instance/Props.v]'s [Props] and [Instance/Two.v]'s [_2] are thin, but
 neither is [Proset P] for any [P]: each is its own [Program
 Definition], and [_2] carries the strict-equality hom-setoid
 [Morphism_equality] rather than the constant-[True] one. The general
 theorems above therefore do not apply to them directly.

 CORRECTION (#463): for [Props] the reason is narrower than “its own
 [Program Definition]” suggests. At Instance/Props/Modal.v's
 [impl_PreOrder] (the relation [Basics.impl] as a stdlib [PreOrder])
 the [obj], [hom], [id] and [compose] fields of [Props] and
 [Proset impl_PreOrder] agree by [eq_refl] and [homset] does not; the
 equation of the two records is refused by conversion, and that
 refusal is the opacity of the two [Program Definition]s' obligations:
 with both restated verbatim under [Set Transparent Obligations] the
 whole records are equal by [eq_refl]. Test/ProbeClosure463.v pins
 this as its refusal N25 with the control [P463Flip.p463_props_T]. For
 a variable [P : PreOrder Basics.impl] the refusal is structural,
 already at [id], and it stays with the obligations transparent (N26
 and N27 there, the objects and homs agreeing by the control
 [P463Flip.p463_props_var_T]). So [Props] is not [Proset P] for any
 [P] as the tree stands, which is all the paragraph above needs.

 What does apply, to EVERY category, is the identification read at the
 hom-inhabitation preorder [hom_le]: the chosen product of a cartesian
 structure is a greatest lower bound of its factors for the relation
 “there exists a morphism”. Recording the two existing binary
 witnesses through that bridge is the honest sense in which they are
 instances of the general statement rather than freestanding facts —
 instances of the CHARACTERIZATION, not of the [Proset]
 construction. 

 --------
 [Instance/Props.v] 的 [Props] 和 [Instance/Two.v] 的 [_2] 很薄，但对于任何 [P]，它们都不是 [Proset P]：每个都是它自己的 [程序定义]，并且 [_2] 承载严格相等的同态集 [Morphism_equality]，而不是常量 [True] 的同态集。因此，上述一般定理不能直接应用于它们。更正 (#463)：对于 [Props]，原因比“其自身 [Program Definition] 所暗示的”要窄。在 Instance/Props/Modal.v 的 [impl_PreOrder]（关系 [Basics.impl] 作为 stdlib [PreOrder]）中，[Props] 和 [Proset impl_PreOrder] 的 [obj]、[hom]、[id] 和 [compose] 字段通过 [eq_refl] 一致，而 [homset] 不一致；两个记录的等式被转换拒绝，而这种拒绝就是两个 [Program Definition] 义务的不透明性：在 [Set Transparent Obligations] 下逐字重述后，整个记录通过 [eq_refl] 相等。Test/ProbeClosure463.v 将其作为拒绝 N25 固定，控制为 [P463Flip.p463_props_T]。对于变量 [P : PreOrder Basics.impl]，拒绝是结构性的，在 [id] 已经如此，并且它随着义务保持透明（N26 和 N27 在那里，对象和 Homs 通过 [P463Flip.p463_props_var_T] 一致）。所以对于任何 [P] 来说，[Props] 并不是 [Proset P]，就现有的树而言，上面段落所需的只是这些内容。

 适用于每一类的是，在同居前序 [hom_le] 下的识别：笛卡尔结构中选择的乘积，对于“存在一个态射”这个关系来说，是其因子的最大下界。通过那座桥记录两个现有的二元见证，这才是它们作为一般陈述实例的真实意义，而不是独立事实——它们是表征的实例，而不是 [Proset] 构造的实例。
*)

(*
 Theory/Category.v already records that a category has an underlying
 preorder of objects, as the exported instance [hom_preorder :
 PreOrder (@hom C)]. That one cannot be reused here: [IsGLB] is stated
 over a [relation], which is [Prop]-valued, whereas [@hom C] is
 [Type]-valued. [hom_le] is therefore its propositional truncation,
 and [hom_le_preorder] below is the corresponding [PreOrder] — named
 apart from [hom_preorder] deliberately, so that this file shadows no
 existing instance. 

 --------
 Theory/Category.v 已经记录了一个范畴具有一个对象的基础预序，作为导出的实例 [hom_preorder : PreOrder (@hom C)]。这里不能重复使用那个：[IsGLB] 是在 [relation] 上陈述的，而 [relation] 是 [Prop] 值的，而 [@hom C] 是 [Type] 值的。因此 [hom_le] 是它的命题截断，下面的 [hom_le_preorder] 是相应的 [PreOrder] — 除了 [hom_preorder] 特意命名，以便这个文件不覆盖现有实例。
*)
Definition hom_le (C : Category) (x y : C) : Prop := inhabited (x ~{C}~> y).

Program Definition hom_le_preorder (C : Category) : PreOrder (hom_le C) :=
  Build_PreOrder _ _ _.
Next Obligation. intro x; exact (inhabits id). Qed.
Next Obligation. intros x y z [f] [g]; exact (inhabits (g ∘ f)). Qed.

Definition cartesian_is_glb (C : Category) (CP : @Cartesian C) (x y : C) :
  IsGLB (hom_le C) (pair_family x y) (@product_obj C CP x y).
Proof.
  split.
  - intros [|].
    + exact (inhabits (@exl C CP x y)).
    + exact (inhabits (@exr C CP x y)).
  - intros n Hn.
    destruct (Hn true) as [f]; destruct (Hn false) as [g].
    exact (inhabits (@fork C CP n x y f g)).
Defined.

Definition cocartesian_is_lub (C : Category) (CP : @Cocartesian C) (x y : C) :
  IsLUB (hom_le C) (pair_family x y) (@product_obj (C^op) CP x y) :=
  cartesian_is_glb (C^op) CP x y.

(*
 The two existing binary witnesses, recorded through that bridge:
 conjunction is the meet of two propositions, disjunction their join,
 and [Instance/Two/Monoidal.v]'s [two_meet] is the meet of the
 two-element order. 

 --------
 通过那座桥记录的两个现有二进制见证：
 合取是两个命题的交，析取是它们的并，
 而 [Instance/Two/Monoidal.v] 的 [two_meet] 是两个元素序的交。
*)
Definition props_product_is_glb (p q : Prop) :=
  cartesian_is_glb Props Props_Cartesian p q.

Definition props_coproduct_is_lub (p q : Prop) :=
  cocartesian_is_lub Props Props_Cocartesian p q.

Definition two_product_is_glb (x y : TwoObj) :=
  cartesian_is_glb _2 Two_Cartesian x y.

(* * ** A concrete witness: the natural numbers under [<=] / * ** 一个具体的见证：在 [<=] 下的自然数 *)

(*
 [Instance/Proset.v]'s [LessThanEqualTo_Category] is the thin category
 of [(nat, <=)]. The name is also defined in Instance/Poset.v, over
 [Poset] rather than [Proset]; it is written qualified here so the
 intended one is unambiguous. 

 --------
 [Instance/Proset.v] 的 [LessThanEqualTo_Category] 是 [(nat, <=)] 的薄范畴。这个名称也在 Instance/Poset.v 中定义，作用于 [Poset] 而不是 [Proset]；这里加了限定，以便意图明确。
*)
Definition Nat_Proset : Category :=
  Category.Instance.Proset.LessThanEqualTo_Category.

(*
 [Nat.min] is the binary meet for [<=], so it produces a genuine
 cartesian structure on that thin category. 

 --------
 [Nat.min] 是 [<=] 的二元交集，所以它在那个稀疏范畴上产生了一个真正的笛卡尔结构。
*)
Definition Nat_Cartesian : @Cartesian Nat_Proset :=
  Proset_Cartesian Nat.le_preorder Nat.min
    Nat.le_min_l Nat.le_min_r
    (fun n x y Hx Hy => Nat.min_glb x y n Hx Hy).

Definition nat_meet (x y : nat) : nat :=
  @product_obj Nat_Proset Nat_Cartesian x y.

(*
 The identification computes: the categorical product of 3 and 5 in
 this thin category is the number 3, by reduction alone. (Object
 positions parse in [object_scope], where a bare numeral has no
 interpretation, hence the [%nat] annotation.) 

 --------
 该标识计算：在这个稀疏范畴中，3 和 5 的范畴积仅通过约简就是数字 3。（对象位置在 [object_scope] 中解析，其中裸数字没有解释，因此有 [%nat] 注释。）
*)
Example nat_product_3_5 : nat_meet 3 5 = 3%nat := eq_refl.

Definition nat_product_IsGLB (x y : nat) :
  IsGLB le (pair_family x y) (@product_obj Nat_Proset Nat_Cartesian x y) :=
  cartesian_product_IsGLB Nat.le_preorder Nat_Cartesian x y.

(*
 Non-vacuity, in the sense described in the header: [IsGLB] is a
 refutable predicate, so the theorems above are not statements about a
 uniformly inhabited type. 4 is not a lower bound of {3, 5}. 

 --------
 非空性，以标题中描述的意义：[IsGLB] 是一个可反驳的谓词，所以上述定理不是关于一个统一存在类型的陈述。4 不是 {3, 5} 的下界。
*)
Lemma nat_glb_not_4 : IsGLB le (pair_family 3%nat 5%nat) 4%nat → False.
Proof.
  intros [Hlb _].
  pose proof (Hlb true) as H4.
  apply Nat.nle_succ_diag_l with (n:=3%nat).
  exact H4.
Qed.

(*
 Zero is least, hence initial. The natural numbers have no greatest
 element, so this thin category has an initial object but no terminal
 one — a reminder that the identification transports the ORDER facts,
 it does not manufacture them.  The negative half is PROVED below
 ([Nat_no_Terminal]), not asserted. 

 --------
 零是最小的，因此是初始的。自然数没有最大的元素，所以这个稀薄的范畴有一个初始对象，但没有终对象——这提醒我们，标识传递的是顺序事实，而不是制造它们。负半部分在下面被证明（[Nat_no_Terminal]），而不是被断言。
*)
Definition Nat_Initial : @Initial Nat_Proset :=
  Proset_Initial Nat.le_preorder 0%nat Nat.le_0_l.

(* Registered as an instance, which is what the Seven Sketches §6.2.1 checkbox asks for; usable by typeclass search as well as by name. / 已注册为一个实例，这正是《七个素描》第 §6.2.1 节复选框所要求的；可通过类型类搜索以及按名称使用。 *)
#[export] Existing Instance Nat_Initial.

(*
 A terminal object of this thin category would be an upper bound of
 every natural, in particular of its own successor. 

 --------
 这个稀疏范畴的终对象将是每一个自然数的上界，特别是它自身的后继的上界。
*)
Theorem Nat_no_Terminal : @Terminal Nat_Proset → False.
Proof.
  intros T.
  pose proof (@one Nat_Proset T (S (@terminal_obj Nat_Proset T))) as H.
  simpl in H.
  exact (Nat.nle_succ_diag_l _ H).
Qed.

Definition nat_indexed_limit (x y : nat) :
  Limit (DiscreteCat_Functor (C:=Nat_Proset) (pair_family x y)) :=
  Proset_Limit Nat.le_preorder (pair_family x y) (Nat.min x y)
    (nat_product_IsGLB x y).

(* * ** A preorder with no least element, and no binary meets / * ** 一个没有最小元素的前序集，并且没有二元下确界 *)

(*
 The two-element discrete order: [bool] under equality. It is a
 preorder, so the constructions above apply to it, and it has neither
 a bottom nor binary meets. Both facts are stated in the refutation
 form, which is what makes the corresponding positive statements
 informative.

 Two other in-tree candidates were available and are deliberately not
 used: Instance/Two/Discrete.v's [Two_Discrete] is a hand-built
 category rather than a [Proset], so it would not witness a statement
 about preorders without a bridge; and packaging
 Construction/Enriched/Two.v's [two_bot] as an initial object of [_2]
 belongs to a separate effort on joins in the two-element order
 (issue #756), which owns those names. 

 --------
 两元素离散序：在等式下为 [bool]。它是一个预序，因此上面提到的构造适用于它，并且它既没有下界也没有二元交。两个事实都以反驳的形式陈述，这正是使对应的正面陈述具有信息量的原因。

 还有两个其他的树内候选对象可用，但故意未使用：Instance/Two/Discrete.v 的 [Two_Discrete] 是一个手工构建的范畴，而不是 [Proset]，因此在没有桥接的情况下不能证明关于预序的陈述；而将 Construction/Enriched/Two.v 的 [two_bot] 打包作为 [_2] 的初始对象属于对两元素序中联合的单独研究（问题 #756），这些名称归该研究所有。
*)
Definition bool_eq_preorder : PreOrder (@eq bool) :=
  Build_PreOrder (@eq bool) (@eq_Reflexive bool) (@eq_Transitive bool).

Lemma discrete_two_no_initial :
  @Initial (Proset bool_eq_preorder) → False.
Proof.
  intro Iobj.
  pose proof (initial_is_least bool_eq_preorder Iobj true) as Ht.
  pose proof (initial_is_least bool_eq_preorder Iobj false) as Hf.
  rewrite Ht in Hf; discriminate.
Qed.

Lemma discrete_two_no_cartesian :
  @Cartesian (Proset bool_eq_preorder) → False.
Proof.
  intro CP.
  assert (Hl : @product_obj (Proset bool_eq_preorder) CP true false = true)
    by exact (@exl (Proset bool_eq_preorder) CP true false).
  assert (Hr : @product_obj (Proset bool_eq_preorder) CP true false = false)
    by exact (@exr (Proset bool_eq_preorder) CP true false).
  rewrite Hl in Hr; discriminate.
Qed.
