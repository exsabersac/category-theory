(* * * The tensor product of abelian groups / * * 阿贝尔群的张量积 *)

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §I.8, printed pp. 28–29 (PDF pp. 38–39) — maclane:I.8:def5
 Book:      Mac Lane, ibid., §VII.1, printed pp. 163–164 (PDF pp.
 171–172) — maclane:VII.1:remark1 (the monoidal reading,
 delivered in Instance/Ab/Monoidal.v over this file)
 nLab:      https://ncatlab.org/nlab/show/tensor+product+of+abelian+groups
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_product

 Because composition in an Ab-category is bilinear, it factors through
 the tensor product of abelian groups: G ⊗ H is the recipient of the
 universal bilinear map out of G × H, turning bilinear maps into plain
 group homomorphisms.  This file builds it for Instance/Ab.v's
 [AbObject]s, setoid-first and axiom-free:

 - [tsum]/[ts_eq]: formal sums over the two carriers, quotiented by
 exactly the commutative-group laws and the two bilinearity
 equations — an inductive setoid quotient in the style of
 Instance/Sets/Coend.v
 - [AbTensor G H : AbObject]: the tensor product itself
 - [Bilinear]: the bilinear-map interface, with [tensor_gen] the
 universal one
 - [tensor_ump]: the factorization of a bilinear map through a
 homomorphism out of the tensor, computing definitionally on
 formal sums
 - [tensor_hom_ext]: two homomorphisms out of the tensor agreeing on
 generators agree — the uniqueness half of the UMP, and the
 workhorse every later coherence proof reduces to
 - [AbTensor_Functor : Ab ∏ Ab ⟶ Ab]: bifunctoriality, its laws all
 instances of [tensor_hom_ext]

 Design:

 1. THE QUOTIENT IS AN INDUCTIVE RELATION, REFLEXIVITY DERIVED.  As in
 Instance/Sets/Coend.v (and Construction/Quotient.v's [CongClosure]),
 the carrier is a plain inductive of formal sums and the setoid
 equality [ts_eq] is an inductive relation closing under the group
 laws, the two bilinearity rules, congruence for the two term
 formers, saturation under the point setoids ([te_gen]), and
 symmetry/transitivity.  Reflexivity is a lemma ([ts_refl], by
 induction on the term), keeping the relation's induction principle
 one case shorter everywhere it is consumed.

 2. NO FREE-ALGEBRA DETOUR.  The tree has no free abelian group to
 quotient (verified across Construction/ and Instance/); building
 formal sums directly keeps the development self-contained and the
 mediator's respectfulness a single induction over [ts_eq], each
 rule discharged by the corresponding law of the target — which is
 precisely Mac Lane's “bilinear maps out of G × H are homomorphisms
 out of G ⊗ H”.  This trades away the issue sketch's “free-abelian-
 group-on-a-setoid machinery, kept reusable”: the carrier here is
 bespoke to the pair (G, H).  What IS reusable is the interface —
 [Bilinear], [tensor_ump] and [tensor_hom_ext] are stated over
 arbitrary [AbObject]s, and they are all any consumer downstream
 (Instance/Ab/Monoidal.v, Construction/Enriched/Ab.v) touches.

 3. THE MEDIATOR COMPUTES.  [tensor_med] is a fixpoint on formal sums,
 so [cmon_map_zero] and [cmon_map_plus] of the factorizing
 homomorphism hold by reflexivity, and every later equation between
 homomorphisms out of (iterated) tensors reduces along it to a
 statement about generators.  [tensor_hom_ext] is the induction that
 finishes such statements; preservation of negation, needed in its
 [ts_neg] case, is Instance/Ab.v's [ab_map_neg] theorem.

 4. UNIVERSES.  Nothing is annotated: like [CMonObject] and [AbObject]
 themselves (Instance/Grp.v's stated policy), the construction is
 universe-polymorphic, and [tsum] lives at the level of the two
 carriers. 

 --------
 书籍：      Mac Lane，《为工作数学家准备的范畴论》，第二版，
 §I.8，印刷版第28–29页（PDF第38–39页） — maclane:I.8:def5
 书籍：      Mac Lane，同上，§VII.1，印刷版第163–164页（PDF第171–172页） — maclane:VII.1:remark1（单体论的解释，
 在本文件的 Instance/Ab/Monoidal.v 中给出）
 nLab：       https://ncatlab.org/nlab/show/tensor+product+of+abelian+groups 
 维基百科：  https://en.wikipedia.org/wiki/Tensor_product 

 由于 Ab-范畴中的复合是双线性的，它可以通过阿贝尔群的张量积来分解：G ⊗ H 是从 G × H 出发的普遍双线性映射的接收者，将双线性映射转换为普通的群同态。本文件为 Instance/Ab.v 的
 [AbObject] 集，以及先集合后等价关系和不依赖公理的情形构建了它：- [tsum] / [ts_eq]：在两个承载集合上进行的形式和，正好以交换群法则和两个双线性方程为商——一种类似于 Instance/Sets/Coend.v 风格的归纳集合商
 - [AbTensor G H : AbObject]：张量积本身
 - [Bilinear]：双线性映射接口，其中 [tensor_gen] 是通用的
 - [tensor_ump]：通过从张量出的同态对双线性映射进行分解，在形式和上进行定义计算
 - [tensor_hom_ext]：来自张量的两个同态在生成元上相同——UMP 的唯一性部分，也是后续每个相干性证明的主力
 - [AbTensor_Functor : Ab ∏ Ab ⟶ Ab]：双函子性，其所有法则都是 [tensor_hom_ext] 的实例

 设计：1. 商是一个归纳关系，反身性可推导。如在 Instance/Sets/Coend.v（以及 Construction/Quotient.v 的 [CongClosure]）中，承载体是形式和的普通归纳，集合等价 [ts_eq] 是一个归纳关系，在群律、两个双线性规则、两个项构造子的合流、点集合等价 [te_gen] 下的饱和性，以及对称/传递性下闭合。反身性是一个引理（[ts_refl]，通过对项的归纳），在使用该关系的归纳原理时，每个地方的归纳原则都减少了一个案例。2. 不经过自由代数绕行。该树没有可以取商的自由阿贝尔群（已在 Construction/ 和 Instance/ 中验证）；直接构建形式和可以使开发自成体系，并使调解器的尊重性体现为对 [ts_eq] 的单次归纳，每条规则由目标的相应律解除——这正是 Mac Lane 所说的“来自 G × H 的双线性映射是 G ⊗ H 的同态”。这放弃了问题草图中“在集合上构建自由阿贝尔群的机制，可以重复使用”的问题：这里的承载对象是为 (G, H) 对量身定制的。可重复使用的是接口——[Bilinear]、[tensor_ump] 和 [tensor_hom_ext] 的表述适用于任意 [AbObject]，并且都可以被任何下游使用者（Instance/Ab/Monoidal.v, Construction/Enriched/Ab.v）调用。3. 调解者进行计算。[tensor_med] 是形式和上的一个不动点，因此因子同态的 [cmon_map_zero] 和 [cmon_map_plus] 可通过自反性成立，并且每一个来自（迭代）张量的同态之间的后续方程都可沿其简化为关于生成元的陈述。[tensor_hom_ext] 是完成此类陈述的归纳；在其 [ts_neg] 情况下所需的否定保持性，是 Instance/Ab.v 的 [ab_map_neg] 定理。

 4. 宇宙。没有任何标注：如 [CMonObject] 和 [AbObject] 本身那样（Instance/Grp.v 所述政策），该构造是宇宙多态的，而 [tsum] 存在于两个载体的层级上。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* * ** Formal sums and the bilinearity quotient / * ** 形式和与双线性商 *)

Section Tensor.

Context (G H : AbObject).

(* Formal sums over the two carriers: generators, zero, sum, negation. / 对两个载体的形式求和：生成元、零、求和、取反。 *)
Inductive tsum : Type :=
  | ts_gen  : carrier G → carrier H → tsum
  | ts_zero : tsum
  | ts_plus : tsum → tsum → tsum
  | ts_neg  : tsum → tsum.

(*
 The quotienting relation: commutative-group laws, bilinearity in each
 variable, congruence, saturation under the point setoids, symmetry and
 transitivity.  Reflexivity is derived (design note 1). 

 --------
 商关系：交换群律，每个变量的双线性，合同性，在点集合等价关系下的饱和，对称性和传递性。反身性是推导出来的（设计注释1）。
*)
Inductive ts_eq : tsum → tsum → Prop :=
  | te_gen {g g' : carrier G} {h h' : carrier H} :
      g ≈ g' → h ≈ h' → ts_eq (ts_gen g h) (ts_gen g' h')
  | te_plus {s s' t t'} :
      ts_eq s s' → ts_eq t t' → ts_eq (ts_plus s t) (ts_plus s' t')
  | te_neg {s s'} : ts_eq s s' → ts_eq (ts_neg s) (ts_neg s')
  | te_assoc (s t u : tsum) :
      ts_eq (ts_plus (ts_plus s t) u) (ts_plus s (ts_plus t u))
  | te_comm (s t : tsum) : ts_eq (ts_plus s t) (ts_plus t s)
  | te_zero_l (s : tsum) : ts_eq (ts_plus ts_zero s) s
  | te_neg_l (s : tsum) : ts_eq (ts_plus (ts_neg s) s) ts_zero
  | te_bilin_l (g g' : carrier G) (h : carrier H) :
      ts_eq (ts_gen (cmon_plus G g g') h)
            (ts_plus (ts_gen g h) (ts_gen g' h))
  | te_bilin_r (g : carrier G) (h h' : carrier H) :
      ts_eq (ts_gen g (cmon_plus H h h'))
            (ts_plus (ts_gen g h) (ts_gen g h'))
  | te_sym {s t} : ts_eq s t → ts_eq t s
  | te_trans {s t u} : ts_eq s t → ts_eq t u → ts_eq s u.

Lemma ts_refl (s : tsum) : ts_eq s s.
Proof.
  induction s.
  - exact (te_gen (reflexivity _) (reflexivity _)).
  - exact (te_trans (te_sym (te_zero_l ts_zero)) (te_zero_l ts_zero)).
  - exact (te_plus IHs1 IHs2).
  - exact (te_neg IHs).
Qed.

Lemma ts_eq_Equivalence : Equivalence ts_eq.
Proof.
  constructor.
  - exact ts_refl.
  - exact (fun s t => te_sym).
  - exact (fun s t u => te_trans).
Qed.

Definition ts_Setoid : Setoid tsum := {|
  equiv        := ts_eq;
  setoid_equiv := ts_eq_Equivalence
|}.

(*
 The tensor product, as an abelian group: the laws are constructors of
 the relation -- and so, since the PR “algebraic carriers are sets”
 (2026-09-17), is its [cmon_prop]: [ts_eq] IS a [Prop], hence its own
 [Prop] mirror, and both implications are the identity. 

 --------
 作为阿贝尔群的张量积：其定律是关系的构造器——因此，由于 PR “代数承载是集合”（2026-09-17），它的 [cmon_prop]：[ts_eq] 是一个 [Prop]，因此它自身具有 [Prop] 镜像，并且这两个蕴含都是恒等式。
*)
Definition AbTensor : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := tsum; is_setoid := ts_Setoid |};
    cmon_zero := ts_zero;
    cmon_plus := ts_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => te_plus Hs Ht;
    cmon_plus_assoc := te_assoc;
    cmon_plus_comm := te_comm;
    cmon_plus_zero_l := te_zero_l;
    (*
 [ts_eq] IS a [Prop]-valued relation, so it is its own [Prop] mirror and
 both implications are the identity. 

 --------
 [ts_eq] 是一个 [Prop] 值的关系，因此它是其自身的 [Prop] 镜像，并且两个蕴涵都是恒等映射。
*)
    cmon_prop := @PropEquiv_of_relation _ ts_Setoid ts_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := ts_neg;
  ab_neg_respects := fun _ _ Hs => te_neg Hs;
  ab_neg_left := te_neg_l
|}.

(* * ** Bilinear maps and the universal property / * ** 双线性映射与泛性质 *)

(*
 A bilinear map into an abelian group K: respectful in each variable and
 additive in each variable.  (Preservation of zero and negation in each
 variable follows, as always for monoid maps between groups, and is not
 demanded.) 

 --------
 一个到阿贝尔群 K 的双线性映射：在每个变量上是线性的并且在每个变量上是可加的。（对每个变量零和取负的保持性质随之而来，就像群之间的幺半群映射一样，并不是强制要求的。）
*)
Record Bilinear (K : AbObject) := {
  bilin_map : carrier G → carrier H → carrier K;
  bilin_respects :
    Proper (equiv ==> equiv ==> equiv) bilin_map;
  bilin_add_l (g g' : carrier G) (h : carrier H) :
    bilin_map (cmon_plus G g g') h
      ≈ cmon_plus K (bilin_map g h) (bilin_map g' h);
  bilin_add_r (g : carrier G) (h h' : carrier H) :
    bilin_map g (cmon_plus H h h')
      ≈ cmon_plus K (bilin_map g h) (bilin_map g h')
}.

Arguments bilin_map {K} _ _ _.
Arguments bilin_respects {K} _.
Arguments bilin_add_l {K} _ _ _ _.
Arguments bilin_add_r {K} _ _ _ _.

(*
 The universal bilinear map: the generator former itself.  (Built with
 the explicit constructor: the record notation would have to inject
 [tsum] into [carrier] of an evar, which unification declines.) 

 --------
 通用双线性映射：生成器本身。(使用显式构造函数构建：记录符号将不得不将 [tsum] 注入一个 evar 的 [carrier] 中，而统一失败。)
*)
Definition tensor_gen : Bilinear AbTensor :=
  @Build_Bilinear AbTensor ts_gen
    (fun _ _ Hg _ _ Hh => te_gen Hg Hh)
    te_bilin_l
    te_bilin_r.

(* The mediator: fold a formal sum through the target's operations. It computes on constructors (design note 3). / 中介者：通过目标的操作折叠一个正式和。它在构造函数上进行计算（设计说明 3）。 *)
Fixpoint tensor_med_fun {K : AbObject} (β : Bilinear K) (s : tsum) :
  carrier K :=
  match s with
  | ts_gen g h  => bilin_map β g h
  | ts_zero     => cmon_zero K
  | ts_plus s t => cmon_plus K (tensor_med_fun β s) (tensor_med_fun β t)
  | ts_neg s    => ab_neg K (tensor_med_fun β s)
  end.

(*
 Respectfulness is one induction over the relation, each rule met by
 the corresponding law of K (design note 2) -- but the induction now runs
 in [Prop].

 Since the PR “algebraic carriers are sets” (2026-09-17) [ts_eq] is a [Prop]
 inductive, so it eliminates only into [Prop] goals, while the conclusion
 `≈` is [Type]-valued.  [apply pequiv_to] first, using the target's own
 [cmon_prop]: that puts the [Prop] goal [pequiv …] in front of the
 elimination, and each branch returns to `≈` with [pequiv_from].  Nothing
 about the argument changes -- each rule is still met by the corresponding
 law of [K] -- and no hypothesis is added, because every [AbObject] now
 carries the field.  Test/ProbeTermModelProp.v pins the refusal of the old
 script.  The intro pattern is NAMED because [apply pequiv_to] in front of
 the elimination changes the automatic names. 

 --------
 尊重是一个关于关系的归纳，每条规则都由 K 的相应定律满足（设计说明 2）——但归纳现在在 [Prop] 中运行。自从 PR “代数载体是集合”（2026-09-17）  [ts_eq] 是一个 [Prop] 归纳类型，因此它只能消解到 [Prop] 目标，而结论 `≈` 是 [Type] 值的。首先使用目标自身的 [cmon_prop] ：这将 [Prop] 目标 [pequiv …] 放在消解前面，并且每个分支都返回到 `≈` 并带有 [pequiv_from] 。关于参数没有任何变化——每条规则仍然由 [K] 的对应定律满足——并且没有添加任何假设，因为每个 [AbObject] 现在都携带了域。Test/ProbeTermModelProp.v 钉住了旧脚本的拒绝。引入模式是 NAMED，因为 [apply pequiv_to] 放在消解前面会改变自动命名。
*)
Lemma tensor_med_respects {K : AbObject} (β : Bilinear K) (s t : tsum) :
  ts_eq s t → tensor_med_fun β s ≈ tensor_med_fun β t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ g g' h h' Hg Hh | s s' t t' _ IH1 _ IH2 | s s' _ IH
    | s t u | s t | s | s | g g' h | g h h'
    | s t _ IH | s t u _ IH1 _ IH2 ]; simpl.
  - apply pequiv_from; exact (bilin_respects β _ _ Hg _ _ Hh).
  - apply pequiv_from.
    exact (cmon_plus_respects K _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from.
    exact (ab_neg_respects K _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from; exact (cmon_plus_assoc K _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm K _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l K _).
  - apply pequiv_from; exact (ab_neg_left K _).
  - apply pequiv_from; exact (bilin_add_l β _ _ _).
  - apply pequiv_from; exact (bilin_add_r β _ _ _).
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

(* The factorization: a bilinear map becomes a homomorphism out of the tensor. Zero- and sum-preservation hold by reflexivity. / 因式分解：一个双线性映射变成从张量出的同态。零和加法的保持由自反性成立。 *)
Program Definition tensor_ump {K : AbObject} (β : Bilinear K) :
  AbHom AbTensor K := {|
  cmon_map := {| morphism := tensor_med_fun β |}
|}.
Next Obligation.
  intros K β s t He; exact (tensor_med_respects β s t He).
Qed.
Next Obligation.
  intros K β; simpl; reflexivity.
Qed.
Next Obligation.
  intros K β s t; simpl; reflexivity.
Qed.

Lemma tensor_ump_gen {K : AbObject} (β : Bilinear K)
  (g : carrier G) (h : carrier H) :
  cmon_map (tensor_ump β) (ts_gen g h) ≈ bilin_map β g h.
Proof.
  simpl; reflexivity.
Qed.

(* The same triangle stated through the universal bilinear map itself: factoring [β] and then evaluating on [tensor_gen] recovers [β]. / 通过通用双线性映射本身所表示的相同三角形：先对 [β] 进行分解，然后在 [tensor_gen] 上求值，可恢复 [β]。 *)
Lemma tensor_ump_tensor_gen {K : AbObject} (β : Bilinear K)
  (g : carrier G) (h : carrier H) :
  cmon_map (tensor_ump β) (bilin_map tensor_gen g h) ≈ bilin_map β g h.
Proof.
  exact (tensor_ump_gen β g h).
Qed.

(* Uniqueness, in its most consumable form: homomorphisms out of the tensor agreeing on generators agree everywhere. The [ts_neg] case is Instance/Ab.v's [ab_map_neg]. / 唯一性，在其最易理解的形式中：从张量出来的同态在生成元上相同，则在任何地方都相同。[ts_neg] 的情况是 Instance/Ab.v 的 [ab_map_neg]。 *)
Lemma tensor_hom_ext {K : AbObject} (f g : AbHom AbTensor K) :
  (∀ (a : carrier G) (b : carrier H),
      cmon_map f (ts_gen a b) ≈ cmon_map g (ts_gen a b)) →
  ∀ s : tsum, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen s; induction s.
  - exact (Hgen c c0).
  - exact (transitivity (cmon_map_zero f)
             (symmetry (cmon_map_zero g))).
  - refine (transitivity (cmon_map_plus f s1 s2) _).
    refine (transitivity _ (symmetry (cmon_map_plus g s1 s2))).
    exact (cmon_plus_respects K _ _ IHs1 _ _ IHs2).
  - refine (transitivity (ab_map_neg f s) _).
    refine (transitivity _ (symmetry (ab_map_neg g s))).
    exact (ab_neg_respects K _ _ IHs).
Qed.

(* The classical statement of the UMP, assembled from the two halves: factorization exists and is unique. / UMP 的经典表述，由两个部分组合而成：分解存在且唯一。 *)
Lemma tensor_ump_unique {K : AbObject} (β : Bilinear K)
  (f : AbHom AbTensor K) :
  (∀ (a : carrier G) (b : carrier H),
      cmon_map f (ts_gen a b) ≈ bilin_map β a b) →
  f ≈ tensor_ump β.
Proof.
  intros Hgen s.
  refine (tensor_hom_ext f (tensor_ump β) _ s).
  intros a b.
  exact (transitivity (Hgen a b) (symmetry (tensor_ump_gen β a b))).
Qed.

End Tensor.

Arguments ts_gen {G H} g h.
Arguments ts_zero {G H}.
Arguments ts_plus {G H} s t.
Arguments ts_neg {G H} s.
Arguments ts_eq {G H} s t.
Arguments ts_refl {G H} s.
Arguments te_gen {G H g g' h h'} _ _.
Arguments te_plus {G H s s' t t'} _ _.
Arguments te_neg {G H s s'} _.
Arguments te_assoc {G H} s t u.
Arguments te_comm {G H} s t.
Arguments te_zero_l {G H} s.
Arguments te_neg_l {G H} s.
Arguments te_bilin_l {G H} g g' h.
Arguments te_bilin_r {G H} g h h'.
Arguments te_sym {G H s t} _.
Arguments te_trans {G H s t u} _ _.

(*
 [ts_eq] is a [Prop] since the PR “algebraic carriers are sets”
 (2026-09-17), and Coq's [reflexivity], [symmetry] and [transitivity]
 dispatch a [Prop]-valued relation to the [Prop] class hierarchy of
 Corelib.Classes.RelationClasses rather than to the [Type]-valued
 CRelationClasses that [ts_eq_Equivalence] inhabits.  The same three laws,
 registered there, keep every existing tactic call working; without it the
 [reflexivity] of [tensor_map_gen] below is refused with “the relation
 ts_eq is not a declared reflexive relation”. 

 --------
 [ts_eq] 是一个 [Prop] 自从 PR “代数载体是集合” (2026-09-17) 以来，Coq 的 [reflexivity]、[symmetry] 和 [transitivity] 将一个 [Prop] 值的关系分派到 Corelib.Classes.RelationClasses 的 [Prop] 类层次，而不是 [ts_eq_Equivalence] 所在的 [Type] 值的 CRelationClasses。相同的三条定律在此注册，保持每个现有的策略调用可用；如果没有它，下面 [tensor_map_gen] 的 [reflexivity] 会因为“关系 ts_eq 不是声明的自反关系”而被拒绝。
*)
#[export] Instance ts_eq_Equivalence_Prop {G H : AbObject} :
  RelationClasses.Equivalence (@ts_eq G H).
Proof.
  constructor.
  - exact ts_refl.
  - exact (fun s t => te_sym).
  - exact (fun s t u => te_trans).
Qed.

#[export] Existing Instance ts_eq_Equivalence.
Arguments AbTensor G H : clear implicits.
Arguments Bilinear G H K : clear implicits.
Arguments bilin_map {G H K} _ _ _.
Arguments bilin_respects {G H K} _.
Arguments bilin_add_l {G H K} _ _ _ _.
Arguments bilin_add_r {G H K} _ _ _ _.
Arguments tensor_gen {G H}.
Arguments tensor_med_fun {G H K} β s.
Arguments tensor_ump {G H K} β.
Arguments tensor_ump_gen {G H K} β g h.
Arguments tensor_hom_ext {G H K} f g _ s.
Arguments tensor_ump_unique {G H K} β f _.

(** ** Bifunctoriality / ** 双函子性 *)

(*
 The arrow action: map the generators and extend.  Bilinearity of the
 composite generator map is the point saturation plus the bilinearity
 rules of the target tensor. 

 --------
 箭头动作：映射生成元并扩展。复合生成元映射的双线性是点饱和加上目标张量的双线性规则。
*)
Program Definition tensor_map {G G' H H' : AbObject}
  (f : AbHom G G') (k : AbHom H H') :
  AbHom (AbTensor G H) (AbTensor G' H') :=
  tensor_ump (@Build_Bilinear G H (AbTensor G' H')
    (fun g h => ts_gen (cmon_map f g) (cmon_map k h)) _ _ _).
Next Obligation.
  intros G G' H H' f k g g' Hg h h' Hh.
  exact (te_gen (proper_morphism (cmon_map f) _ _ Hg)
                (proper_morphism (cmon_map k) _ _ Hh)).
Qed.
Next Obligation.
  intros G G' H H' f k g g' h.
  refine (te_trans (te_gen (cmon_map_plus f g g') (reflexivity _)) _).
  exact (te_bilin_l _ _ _).
Qed.
Next Obligation.
  intros G G' H H' f k g h h'.
  refine (te_trans (te_gen (reflexivity _) (cmon_map_plus k h h')) _).
  exact (te_bilin_r _ _ _).
Qed.

Lemma tensor_map_gen {G G' H H' : AbObject}
  (f : AbHom G G') (k : AbHom H H') (g : carrier G) (h : carrier H) :
  cmon_map (tensor_map f k) (ts_gen g h)
    ≈ ts_gen (cmon_map f g) (cmon_map k h).
Proof.
  simpl; reflexivity.
Qed.

(*
 The bifunctor Ab ∏ Ab ⟶ Ab.  Every law is [tensor_hom_ext] plus a
 computation on generators. 

 --------
 双函子 Ab ∏ Ab ⟶ Ab。每一个定律都是 [tensor_hom_ext] 加上对生成元的计算。
*)
Program Definition AbTensor_Functor : Ab ∏ Ab ⟶ Ab := {|
  fobj := fun p => AbTensor (fst p) (snd p);
  fmap := fun p q f => tensor_map (fst f) (snd f)
|}.
Next Obligation.
  intros [G H] [G' H'] [f k] [f' k'] [Hf Hk]; simpl in *.
  apply (tensor_hom_ext (tensor_map f k) (tensor_map f' k')).
  intros a b.
  exact (te_gen (Hf a) (Hk b)).
Qed.
Next Obligation.
  intros [G H]; simpl.
  apply (tensor_hom_ext (tensor_map cmon_hom_id cmon_hom_id) cmon_hom_id).
  intros a b; simpl.
  exact (ts_refl _).
Qed.
Next Obligation.
  intros [G H] [G' H'] [G'' H''] [f k] [f' k']; simpl.
  apply (tensor_hom_ext
           (tensor_map (cmon_hom_compose f f') (cmon_hom_compose k k'))
           (cmon_hom_compose (tensor_map f k) (tensor_map f' k'))).
  intros a b; simpl.
  exact (ts_refl _).
Qed.
