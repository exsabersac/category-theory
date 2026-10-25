(** * Graded abelian groups / * 分级阿贝尔群 *)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.Discrete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd
 ed., §II.4 Exercise 3, printed p. 41 (PDF 51) —
 maclane:II.4:ex3
 nLab:      https://ncatlab.org/nlab/show/graded+object
 Wikipedia: https://en.wikipedia.org/wiki/Graded_(mathematics)

 A graded abelian group is a family of abelian groups, one in each
 degree, and a map of graded abelian groups is a family of
 homomorphisms, one in each degree.  Nothing ties the degrees
 together — no operation carries degree n to degree m — so both the
 objects and the arrows are bare ℕ-indexed families, and every law is
 checked one degree at a time.  Said categorically: the degrees form
 a DISCRETE shape, and the category of graded abelian groups is the
 functor category out of it, Mac Lane's Aᴶ at J discrete and A := Ab.
 That is [Graded_Fun_equiv].

 - [GradedAb]: the direct definition the exercise asks for —
 objects [nat → AbObject], homs the degreewise families of
 [AbHom]s, hom-setoid, identity and composition all componentwise
 - [graded_obj_definitional] … [graded_compose_definitional]: the
 record against [PiCat (fun _ : nat => Ab)] — objects, homs, the
 hom-setoid's RELATION, identity and composition all agree by
 [eq_refl] (the [homset] field itself does not, nor does
 [compose_respects] — see Design note 2)
 - [PiCat_GradedAb_iso]: the two spellings compared in [Cat], by
 functors that are the identity on objects and on arrows
 - [Graded_Fun_equiv]: [([DiscreteCat nat, Ab]) ≅[Cat] GradedAb]
 - [GradedAb_shift]: the degree shift [F ↦ F ∘ S] as an endofunctor,
 with [graded_degree_one] reading a degree-one map as an ordinary
 (degree-preserving) map into the shift
 - witnesses: [Zgroup] and the constant family [ConstZ], the
 degree-dependent endomorphism [graded_deg_mul] (multiplication
 by n in degree n), and [conc0], a group concentrated in degree
 zero, with the shift computing on both

 Design:

 1. THE DISCRETE-SHAPE COLLAPSE IS CONSUMED, NOT REPROVED.  Instance/
 Fun/Discrete.v already proves [Fun_Discrete_PiCat :
 [DiscreteCat A, B] ≅[Cat] PiCat (fun _ : A => B)] for ANY index
 type A — that a transformation over a discrete domain is a bare
 family ([Discrete_Transform], naturality free), and that
 rebuilding a functor from its object function is the identity up
 to identity components ([DiscreteCat_Functor_iso]).  This file
 instantiates it at A := nat, B := Ab and adds only the comparison
 between the indexed product and the hand-written [GradedAb].  No
 transformation over [DiscreteCat nat] is built below; the only
 naturality-shaped goals here are the two coherence conditions of
 the identity-component isomorphisms in [Cat].

 2. WHAT IS DEFINITIONAL, EXACTLY.  [GradedAb] and
 [PiCat (fun _ : nat => Ab)] agree by [eq_refl] on objects
 ([nat → AbObject] against the choice functions
 [∀ _ : nat, obj[Ab]]), on homs, on the hom-setoid's RELATION,
 and on identity and composition — the five Examples below, each
 true by construction, since [GradedAb]'s data were written in
 PiCat's shape; what was MEASURED rather than arranged is the
 divergence: [eq_refl] at the type
 [GradedAb = PiCat (fun _ : nat => Ab)] is rejected, and so are
 the [homset] field itself (only its [equiv] projection agrees),
 [compose_respects], the four category laws and the hom-setoid's
 [Equivalence] witness — separately elaborated proof terms all.
 So the comparison is a genuine pair of functors rather than an
 [eq_refl] — but they are the identity on data, each functor
 obligation closing either by [reflexivity] or by handing back
 the hypothesis, and the natural isomorphisms witnessing both
 round trips have identity components.  Strength note: [≅[Cat]]
 in this tree IS equivalence of categories (Cat's hom-setoid is
 [Functor_Setoid]); the [PiCat] leg of the comparison is in fact
 STRICTER than that — identity on data in both directions —
 while the [Fun_Discrete_PiCat] leg is an equivalence proper
 (its round trip rebuilds a functor from its object function,
 and only one direction is [eq_refl] on objects).

 3. WHY DEGREE-PRESERVING MAPS.  The arrows here are the degree-zero
 maps, which is what makes the category a functor category over a
 discrete shape: a map that raised degrees would have to know how
 to move along ℕ, and a discrete shape supplies no such arrow.
 Maps of higher degree are recovered through [GradedAb_shift]
 rather than lost: a family [∀ n, F n ~> G (S n)] IS a
 [GradedAb]-arrow [F ~> shift G], definitionally
 ([graded_degree_one]).

 4. INDEX-GENERIC MACHINERY, ℕ-SPECIFIC STATEMENT.  Both DONORS are
 generic in the index type; THIS FILE's own definitions are not —
 [GradedAb], both comparison functors and the iso all hardcode
 [nat], as the exercise asks.  A ℤ-graded or multigraded variant
 would reuse the same two donors unchanged but would RESTATE this
 file's definitions at the other index (with their obligations);
 what it would not need to redo is the discrete-shape collapse or
 the indexed-product category, which is where the actual content
 lives.

 5. NAME COLLISION, DISAMBIGUATED.  Monad/Graded.v is about GRADED
 MONADS — a monad indexed by a monoid of effect grades, with
 multiplication [T i ◯ T j ⟹ T (i ⊗ j)].  That is an unrelated
 concept: it grades an endofunctor by a monoid and its grades
 interact, whereas the objects here are families over a discrete
 index whose degrees never interact.  The two share only the
 English word. 

 --------
 书籍： 麦克·莱恩，《工作数学家的范畴论》，第二版，第 II.4 节习题 3，第 41 页（PDF 第 51 页）—— maclane:II.4:ex3
 nLab: https://ncatlab.org/nlab/show/graded+object
 维基百科: https://en.wikipedia.org/wiki/Graded_(mathematics)

 一个分次阿贝尔群是一族阿贝尔群，每一个度数对应一个阿贝尔群，而分次阿贝尔群的映射是一族同态映射，每个度数对应一个同态映射。没有任何东西将不同度数联系在一起——没有操作会将度数 n 转移到度数 m——所以无论是对象还是箭头都只是 ℕ 索引的空壳族，并且每条规律都是逐度检查的。换成范畴论的说法：度数组成一个离散形状，而分次阿贝尔群的范畴是从该离散形状出发的函子范畴，即麦克莱恩的 Aᴶ 在 J 为离散，A := Ab。即 [Graded_Fun_equiv]。- [GradedAb]：练习要求的直接定义——对象 [nat → AbObject]，[AbHom] 的分级族的同态，逐组件的同态集、身份和组合
 - [graded_obj_definitional] … [graded_compose_definitional]：针对 [PiCat (fun _ : nat => Ab)] 的记录——对象、同态、同态集的关系、身份和组合通过 [eq_refl] 一致（[homset] 字段本身不一致，[compose_respects] 也不一致——见设计说明2）
 - [PiCat_GradedAb_iso]：在 [Cat] 中比较的两种拼写，通过在对象和箭头上是恒等的函子
 - [Graded_Fun_equiv]：[([DiscreteCat nat, Ab] ) ≅ [Cat] 分级阿贝尔群]
 - [GradedAb_shift]：度移 [F ↦ F ∘ S] 作为一个自函子，[graded_degree_one] 将度为一的映射读取为进入该移位的普通（度保持）映射
 - 证明人：[Zgroup] 和 con恒等族 [ConstZ]，度依赖的自同态 [graded_deg_mul]（在度 n 上乘以 n），以及 [conc0]，一个集中在度零的群，同时计算移位设计：

 1. 离散形态的塌缩是被消耗的，而不是被否定的。Instance/Fun/Discrete.v 已经证明了 [Fun_Discrete_PiCat : [DiscreteCat A, B] ≅ [Cat] PiCat (fun _ : A => B)] 对于任何索引类型 A —— 即离散域上的变换是一个简单的族 ([Discrete_Transform]，自然性自由)，并且从对象函数重建函子是恒等函数（恒等分量下为 [DiscreteCat_Functor_iso]）。这个文件将其在 A := nat, B := Ab 下实例化，并且仅增加了索引积与手写的 [GradedAb] 之间的比较。下面没有构建任何 [DiscreteCat nat] 上的变换；这里唯一与自然性相关的目标是 [Cat] 中恒等分量同构的两个相干性条件。2. 什么是定义性的，确切地说。[GradedAb] 和 [PiCat (fun _ : nat => Ab)] 通过 [eq_refl] 在对象上达成一致（[nat → AbObject] 针对选择函数 [∀ _ : nat, obj[Ab] ），在同态、同态集的关系上，以及在同一性和组合上——下面的五个例子，由于 [GradedAb] 的数据是以 PiCat 的形式编写的，因此都是按构造而真实；被测量而非安排的是分歧：[eq_refl] 在类型 [GradedAb = PiCat (fun _ : nat => Ab)] 上被拒绝，[homset] 字段本身也被拒绝（只有它的 [equiv] 投影一致），[compose_respects]、四条范畴定律以及同态集的 [Equivalence] 证据——都是单独详细阐述的证明项。因此，这个比较是真正的一对函子，而不是一个 [eq_refl] —— 但是它们在数据上是恒等的，每个函子义务要么通过 [reflexivity] 来关闭，要么通过返回假设来关闭，并且见证两次往返的自然同构具有恒等分量。强度说明：在这棵树中 [≅[Cat] 是范畴的等价（Cat 的 hom-集是 [Functor_Setoid]）；比较的 [PiCat] 分支实际上比这更严格 —— 双向数据恒等 —— 而 [Fun_Discrete_PiCat] 分支则是一个正规的等价（其往返可以从对象函数重建一个函子，并且只有一个方向在对象上是 [eq_refl]）。3. 为什么选择保持次数的映射。这些箭头是零次数映射，这正是使得该范畴成为离散形状上的函子范畴的原因：一个提升次数的映射必须知道如何沿ℕ移动，而离散形状并不提供这样的箭头。更高次数的映射是通过[GradedAb_shift]恢复的，而不是丢失的：一个家族[∀ n, F n ~> G (S n)]根据定义是一个[GradedAb]-箭头[F ~> shift G]（[graded_degree_one]）。4. 索引-通用机械，ℕ-特定声明。两个捐助者在索引类型上都是通用的；本文件自己的定义不是——[GradedAb]，比较函子和同构都硬编码了[nat]，如练习要求的那样。一个ℤ-分级或多分级的变体会在不改变的情况下重用相同的两个捐助者，但会在其他索引上重新声明本文件的定义（及其义务）；它不需要重新做的是离散形状的塌缩或索引积范畴，这些才是实际内容所在的地方。5. 名称冲突，已消歧。Monad/Graded.v 关于分级单子（GRADED MONADS）——一种由效应等级的幺半群索引的单子，其乘法为 [T i ◯ T j ⟹ T (i ⊗ j)]。这是一个无关的概念：它通过一个幺半群对一个自函子进行分级，并且其等级会相互作用，而这里的对象是离散索引上的族，其度数从不相互作用。两者仅共享英文单词。
*)

(* * ** The category of graded abelian groups / * ** 分级阿贝尔群的类别 *)

(*
 Objects are ℕ-indexed families of abelian groups; an arrow is a
 homomorphism in each degree; everything is checked degreewise. 

 --------
 对象是以ℕ为索引的阿贝尔群族；箭头是在每一阶的同态；所有内容都按阶检查。
*)
Program Definition GradedAb : Category := {|
  obj     := nat → AbObject;
  hom     := fun F G => ∀ n : nat, F n ~{Ab}~> G n;
  homset  := fun F G =>
    {| equiv := fun f g => ∀ n : nat, f n ≈ g n |};
  id      := fun F n => @id Ab (F n);
  compose := fun F G H f g n => f n ∘ g n
|}.
Next Obligation.
  intros F G; constructor.
  - intros f n; reflexivity.
  - intros f g Hfg n; symmetry; exact (Hfg n).
  - intros f g h H1 H2 n.
    transitivity (g n); [ exact (H1 n) | exact (H2 n) ].
Qed.
Next Obligation.
  (*
 [Ab]'s hom-setoid unfolds to [CMonHom_Setoid], so the ambient
 category of the [Proper] instance has to be named. 

 --------
 [Ab] 的同态集展开为 [CMonHom_Setoid]，因此 [Proper] 实例的所属范畴必须被命名。
*)
  intros F G H f f' Hf g g' Hg n.
  exact (@compose_respects Ab (F n) (G n) (H n) _ _ (Hf n) _ _ (Hg n)).
Qed.
Next Obligation.
  intros F G f n; exact (id_left (f n)).
Qed.
Next Obligation.
  intros F G f n; exact (id_right (f n)).
Qed.
Next Obligation.
  intros F G H K f g h n; exact (comp_assoc (f n) (g n) (h n)).
Qed.
Next Obligation.
  intros F G H K f g h n; exact (comp_assoc_sym (f n) (g n) (h n)).
Qed.

(* * ** The measurement against the indexed product / * ** 针对指数产品的测量 *)

(*
 The five data fields of [GradedAb] and of the indexed product over
 the constant family agree on the nose.  These are equalities of
 TYPES and of the data carried by the two records — the library's
 convertibility exception to the "never [=] on morphisms" rule — and
 they are what makes the comparison functors below the identity. 

 --------
 [GradedAb] 的五个数据字段和在常数族上索引的积完全一致。这些是类型以及两个记录所携带的数据的等式——库对“在态射上绝不 [=]”规则的可转换性例外——它们正是使下面的比较函子成为恒等函子的原因。
*)

Example graded_obj_definitional :
  obj[GradedAb] = obj[PiCat (fun _ : nat => Ab)] := eq_refl.

Example graded_hom_definitional (F G : obj[GradedAb]) :
  (F ~{GradedAb}~> G) = (F ~{PiCat (fun _ : nat => Ab)}~> G) := eq_refl.

Example graded_equiv_definitional (F G : obj[GradedAb]) :
  @equiv _ (@homset GradedAb F G)
    = @equiv _ (@homset (PiCat (fun _ : nat => Ab)) F G) := eq_refl.

Example graded_id_definitional (F : obj[GradedAb]) :
  @id GradedAb F = @id (PiCat (fun _ : nat => Ab)) F := eq_refl.

Example graded_compose_definitional (F G H : obj[GradedAb]) :
  @compose GradedAb F G H
    = @compose (PiCat (fun _ : nat => Ab)) F G H := eq_refl.

(* * ** The two spellings compared in Cat / * **《Cat》中比较的两种拼写 *)

(*
 Both directions are the identity on objects and on arrows.  Since
 the data fields coincide, the two functor laws are [reflexivity] and
 respectfulness is the hypothesis handed back degreewise. 

 --------
 两个方向在对象和箭头上都是恒等的。由于数据字段一致，这两个函子律是 [reflexivity]，并且保持性是逐度回传的假设。
*)
Program Definition GradedAb_PiCat :
  GradedAb ⟶ PiCat (fun _ : nat => Ab) := {|
  fobj := fun F => F;
  fmap := fun F G f => f
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg n).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

Program Definition PiCat_GradedAb :
  PiCat (fun _ : nat => Ab) ⟶ GradedAb := {|
  fobj := fun F => F;
  fmap := fun F G f => f
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg n).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

(*
 Oriented towards [GradedAb], so that it composes on the left of the
 donor isomorphism below. 

 --------
 面向[GradedAb]，使其在下方的供体同构体的左侧组合。
*)
Program Definition PiCat_GradedAb_iso :
  PiCat (fun _ : nat => Ab) ≅[Cat] GradedAb := {|
  to   := PiCat_GradedAb;
  from := GradedAb_PiCat
|}.
Next Obligation.
  exists (fun F => iso_id).
  intros F G f n; simpl; cat.
Qed.
Next Obligation.
  exists (fun F => iso_id).
  intros F G f n; simpl; cat.
Qed.

(** ** Mac Lane §II.4 Exercise 3 / ** 马克·莱恩 §II.4 练习 3 *)

(*
 Graded abelian groups are the diagrams of shape "the discrete
 category on the degrees" in Ab.  The whole content of the discrete
 shape — naturality is free, a functor is its object function — is
 Instance/Fun/Discrete.v's [Fun_Discrete_PiCat], consumed here at
 A := nat and B := Ab; this file contributes the second leg. 

 --------
 分级阿贝尔群是形状为“度的离散范畴”的 Ab 中的图。离散形状的全部内容——自然性是自由的，一个函子就是它的对象函数——是在 Instance/Fun/Discrete.v 的 [Fun_Discrete_PiCat]，这里在 A := nat 和 B := Ab 被使用；该文件贡献了第二条腿。
*)
Definition Graded_Fun_equiv :
  ([DiscreteCat nat, Ab]) ≅[Cat] GradedAb :=
  iso_compose PiCat_GradedAb_iso Fun_Discrete_PiCat.

(** ** The degree shift / ** 度数变化 *)

(*
 Reindexing along the successor: an endofunctor, since the arrows are
 degreewise and reindexing them needs no more than reindexing the
 objects. 

 --------
 沿着继任者重新索引：一个端函子，因为箭头是按度数的，重新索引它们不需要超过重新索引对象。
*)
Program Definition GradedAb_shift : GradedAb ⟶ GradedAb := {|
  fobj := fun F n => F (S n);
  fmap := fun F G f n => f (S n)
|}.
Next Obligation.
  intros F G f g Hfg n; exact (Hfg (S n)).
Qed.
Next Obligation.
  intros F n; reflexivity.
Qed.
Next Obligation.
  intros F G H f g n; reflexivity.
Qed.

(*
 Maps of degree one are not outside the category: they are ordinary
 arrows into the shift, definitionally. 

 --------
 一次映射不在范畴之外：从定义上讲，它们是进入移位的普通箭头。
*)
Example graded_degree_one (F G : obj[GradedAb]) :
  (∀ n : nat, F n ~{Ab}~> G (S n))
    = (F ~{GradedAb}~> fobj[GradedAb_shift] G) := eq_refl.

(** ** Witnesses / ** 证人 *)

(*
 ℤ as an abelian group, through the ring layer: Instance/Rng.v's
 [ring_ab] applied to Theory/Algebra/Rig.v's axiom-free [Int_Ring],
 the same donor Instance/Ab/Monoidal.v uses for its unit object. 

 --------
 ℤ 作为阿贝尔群，通过环层：Instance/Rng.v 的 [ring_ab] 应用于 Theory/Algebra/Rig.v 的无公理 [Int_Ring]，相同的供体 Instance/Ab/Monoidal.v 用于它的单位对象。
*)
Definition Zgroup : AbObject := ring_ab Int_Ring.

(*
 Multiplication by a fixed integer, as an endomorphism of ℤ.  The
 [Proper] obligation of the underlying setoid morphism needs no
 proof: ℤ's setoid equivalence is Leibniz equality ([Z_eqT]), so
 elaboration discharges it. 

 --------
 作为 ℤ 的一个自同态，通过固定整数的乘法。底层集合等价的态射（setoid morphism）的义务不需要证明：ℤ 的集合等价是莱布尼兹相等（Leibniz equality），因此展开可以解决它。
*)
Program Definition Zmul_hom (k : Z) : Zgroup ~{Ab}~> Zgroup := {|
  cmon_map := {| morphism := fun m => Z.mul k m |}
|}.
Next Obligation.
  intros k; simpl; exact (Z.mul_0_r k).
Qed.
Next Obligation.
  intros k a b; simpl; exact (Z.mul_add_distr_l k a b).
Qed.

(* The constant graded group ℤ in every degree. / 每个度中的常数分级群 ℤ。 *)
Definition ConstZ : obj[GradedAb] := fun _ => Zgroup.

(*
 A genuinely graded endomorphism: multiplication by n in degree n.
 Its components differ from degree to degree — PROVED below
 ([graded_deg_mul_not_constant]), not asserted: no single
 homomorphism h has [graded_deg_mul] as its constant family. 

 --------
 一个真正分级的端同态：在度 n 中乘以 n。它的分量随度数而异——如下证明（[graded_deg_mul_not_constant]），而不是断言：没有单一的同态 h 有 [graded_deg_mul] 作为其常数族。
*)
Definition graded_deg_mul : ConstZ ~{GradedAb}~> ConstZ :=
  fun n => Zmul_hom (Z.of_nat n).

Lemma graded_deg_mul_not_constant
      (h : Zgroup ~{Ab}~> Zgroup) :
  (∀ n : nat, graded_deg_mul n ≈ h) → False.
Proof.
  intro Hc.
  pose proof (Hc 0%nat 5%Z) as H0.
  pose proof (Hc 1%nat 5%Z) as H1.
  simpl in H0, H1.
  rewrite <- H0 in H1.
  discriminate H1.
Qed.

Example graded_deg_mul_at_3 :
  cmon_map (graded_deg_mul 3%nat) 5%Z = 15%Z := eq_refl.

Example graded_deg_mul_at_0 :
  cmon_map (graded_deg_mul 0%nat) 5%Z = 0%Z := eq_refl.

(* Shifting relabels the degrees: the component in degree 2 of the shifted map is the component in degree 3 of the original. / 平移会重新标记度数：平移映射的度数为2的分量是原始映射中度数为3的分量。 *)
Example shift_deg_mul_at_2 :
  cmon_map (fmap[GradedAb_shift] graded_deg_mul 2%nat) 5%Z = 15%Z := eq_refl.

(*
 A group concentrated in degree zero — the standard example of a
 graded object that is not constant. 

 --------
 一个集中在零度的群——一个关于分次对象的标准例子，它不是常数。
*)
Definition conc0 : obj[GradedAb] :=
  fun n => match n with
           | O   => Zgroup
           | S _ => Ab_trivial
           end.

Example conc0_at_0 : conc0 0%nat = Zgroup := eq_refl.

(* Shifting a group concentrated in degree zero leaves nothing behind: every degree of the shift is the trivial group. / 将一个集中在零次的群进行移位不会留下任何东西：移位的每个次数都是平凡群。 *)
Example shift_conc0_at_0 :
  fobj[GradedAb_shift] conc0 0%nat = Ab_trivial := eq_refl.

Example shift_conc0_at_3 :
  fobj[GradedAb_shift] conc0 3%nat = Ab_trivial := eq_refl.

(* Iterating the shift is reindexing twice, on the nose. / 迭代移位就是精确地重新索引两次。 *)
Example shift_twice (F : obj[GradedAb]) (n : nat) :
  fobj[GradedAb_shift] (fobj[GradedAb_shift] F) n = F (S (S n)) := eq_refl.
