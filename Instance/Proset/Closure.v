(* * * Preorders are closed under products and functor categories / * * 预序在积和函子范畴下是闭合的 *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Product.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Coq.Lists.List.
Require Import Category.Instance.Two.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §II.3 Exercise 2, printed p. 39 (PDF p. 49) — maclane:II.3:ex2
 — and §II.4 Exercise 4, printed p. 41 (PDF p. 51) —
 maclane:II.4:ex4
 Book:      Fong–Spivak, "Seven Sketches in Compositionality", §1.2.2
 (printed p. 17, PDF pp. 29–30) and §3.5.1 Exercise 3.90
 clause 4 (printed p. 110, PDF p. 122)
 nLab:      https://ncatlab.org/nlab/show/thin+category

 Preorders are exactly the thin categories, and thinness is closed
 under the basic constructions.  The vocabulary is Structure/Thin.v's
 [Thin] (issue #223's file, consumed here per issue #273's own
 correction — not rebuilt), which this change extends with the closure
 kit [Thin_Product]/[thin_natural]/[Thin_Transform]; over it this
 file delivers the two Mac Lane exercises at the [Proset] instances:

 - [PreOrder_prod]/[Proset_prod_iso]: the product of two preorders
 is a preorder, and its thin category is the product of the thin
 categories — II.3 Ex. 2, and Seven Sketches Ex. 3.90 clause 4 in
 the categorical direction.  The supporting lemma "a product of
 thin categories is thin" is Structure/Thin.v's [Thin_Product];
 the iso's own obligations close by thinness directly.
 (Instance/Proset/Order.v's [proset_thin] supplies thinness of
 [Proset] itself.)
 - [Thin_Fun]: a functor category into a thin target is thin — the
 structural half of II.4 Ex. 4
 - [mm_le]/[MonotoneProset]/[Fun_Proset_iso]: the concrete half of
 II.4 Ex. 4 — the functor category between preorders IS the
 preorder of monotone maps ordered pointwise, an isomorphism in
 Cat riding Instance/Proset/Monotone.v's dictionary, whose round
 trips are definitional by record eta
 - [roof_two_hom_dec]: Seven Sketches §1.2.2's worked product, the
 V-shaped [Roof] times the walking arrow [_2] — six objects, and
 ONE total decision procedure that simultaneously enumerates
 every related pair (as hom data) and refutes every unrelated
 one, with the counts (fifteen and twenty-one) machine-checked
 by computation.  Instance/Roof.v draws [RZero] at the TOP with
 arrows pointing down — a correct category diagram that is the
 REVERSE of the book's Hasse convention (the warning is issue
 #273's, recorded here since Roof.v itself does not remark on
 orientation).

 The [Fun_Proset_iso] packaging is the strongest this library states
 for categories compared up to [Functor_Setoid]: an isomorphism in
 [Cat] is the strength of an equivalence of categories
 (Instance/Cat.v's header). 

 --------
 书籍：      Mac Lane，《给工作的数学家的范畴》，第2版，
 §II.3 练习 2，印刷版第39页（PDF第49页）—— maclane:II.3:ex2
 —— 和 §II.4 练习 4，印刷版第41页（PDF第51页）——
 maclane:II.4:ex4
 书籍：      Fong–Spivak，《组合性中的七个范例》，§1.2.2
 （印刷版第17页，PDF第29–30页）和 §3.5.1 练习 3.90
 第4条款（印刷版第110页，PDF第122页）
 nLab：       https://ncatlab.org/nlab/show/thin+category预序正是薄范畴，并且薄性在基本构造下是封闭的。词汇表是 Structure/Thin.v 的 [Thin]（问题 #223 的文件，根据问题 #273 的修正在此使用——未重建），这个更改用闭包工具包 [Thin_Product] / [thin_natural] / [Thin_Transform] 扩展了它；在此基础上，这个文件在 [Proset] 实例上提供了两个 Mac Lane 练习：-  [PreOrder_prod] / [Proset_prod_iso]：两个预序的积是一个预序，其薄范畴是薄范畴的积 — II.3 练习 2，以及《七个草图》练习 3.90 第 4 条（范畴方向）。支持引理“薄范畴的积是薄的”在 Structure/Thin.v 中是 [Thin_Product]；同构自身的义务通过薄性直接封闭。(Instance/Proset/Order.v 中的 [proset_thin] 提供了 [Proset] 本身的薄性。) 
 -  [Thin_Fun]：指向薄对象的函子范畴是薄的 — II.4 练习 4 的结构部分 
 -  [mm_le] / [MonotoneProset] / [Fun_Proset_iso]：II.4 练习的具体部分4 — 预序之间的函子范畴是按点顺序排列的单调映射的预序，是 Cat 中的一个同构，依赖于 Instance/Proset/Monotone.v 的字典，其往返操作通过记录 eta 定义。
 - [roof_two_hom_dec]：Seven Sketches §1.2.2 中的工作积，V 型的 [Roof] 与 walking arrow [_2] 相乘——六个对象，以及一个总的决策程序，同时枚举每一对相关元素（作为 Hom 数据）并反驳每一对不相关元素，其计数（十五和二十一）通过计算机检验。Instance/Roof.v 在顶部绘制 [RZero]，箭头向下——一个正确的类别图，是书中 Hasse 约定的反向（警告来自 issue #273，在此记录，因为 Roof.v 本身没有对方向作出说明）。

 [Fun_Proset_iso] 的包装是该库在 [Functor_Setoid] 之前声明的类别的最强包装：在 [Cat] 中的同构就是类别等价的强度（Instance/Cat.v 的标题）。
*)

(** ** Products: Mac Lane II.3 Ex. 2 / ** 产品：Mac Lane II.3 练习 2 *)

(*
 NOTE: the ∧ below is Category.Lib's Type-valued product notation
 (template-polymorphic, so the body still lands in Prop); its
 witnesses are therefore projected by [fst]/[snd] and built by
 pairing, not [proj1]/[conj]. 

 --------
 注意：下面的 ∧ 是 Category.Lib 的类型值乘积符号（模板多态，所以主体仍然落在 Prop 中）；因此它的证明由 [fst] / [snd] 投影，并由配对构建，而不是由 [proj1] / [conj] 构建。
*)
Definition prod_rel {A B : Type} (R : relation A) (S : relation B) :
  relation (A * B) :=
  fun p q => R (fst p) (fst q) ∧ S (snd p) (snd q).

#[export] Instance PreOrder_prod {A B : Type}
  {R : relation A} {S : relation B}
  (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) : RelationClasses.PreOrder (prod_rel R S).
Proof.
  constructor.
  - intro p; split.
    + exact (@RelationClasses.PreOrder_Reflexive _ _ P (fst p)).
    + exact (@RelationClasses.PreOrder_Reflexive _ _ Q (snd p)).
  - intros p q r [Hpq1 Hpq2] [Hqr1 Hqr2]; split.
    + exact (@RelationClasses.PreOrder_Transitive _ _ P _ _ _ Hpq1 Hqr1).
    + exact (@RelationClasses.PreOrder_Transitive _ _ Q _ _ _ Hpq2 Hqr2).
Qed.

Program Definition Proset_prod_to {A B : Type}
  {R : relation A} {S : relation B} (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) :
  Proset (PreOrder_prod P Q) ⟶ Proset P ∏ Proset Q := {|
  fobj := fun p => p;
  fmap := fun x y (h : R (fst x) (fst y) ∧ S (snd x) (snd y)) =>
    (fst h, snd h)
|}.
Next Obligation.
  intros A B R S P Q x y h h' Hh; split; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x; split; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x y z h h'; split; exact I.
Qed.

Program Definition Proset_prod_from {A B : Type}
  {R : relation A} {S : relation B} (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) :
  Proset P ∏ Proset Q ⟶ Proset (PreOrder_prod P Q) := {|
  fobj := fun p => p;
  fmap := fun x y h =>
    ((fst h, snd h)
      : R (fst x) (fst y) ∧ S (snd x) (snd y))
|}.
Next Obligation.
  intros A B R S P Q x y h h' Hh; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x; exact I.
Qed.
Next Obligation.
  intros A B R S P Q x y z h h'; exact I.
Qed.

(*
 The product preorder's thin category IS the product of the thin
 categories: both functors are the identity on objects, and every
 morphism-level obligation is trivial by thinness on either side. 

 --------
 产品预购的薄范畴是薄范畴的积：两个函子在对象上都是恒等的，并且每个态射层面的约束在任一侧由于薄性都是平凡的。
*)
Program Definition Proset_prod_iso {A B : Type}
  {R : relation A} {S : relation B} (P : RelationClasses.PreOrder R) (Q : RelationClasses.PreOrder S) :
  Proset (PreOrder_prod P Q) ≅[Cat] Proset P ∏ Proset Q := {|
  to   := Proset_prod_to P Q;
  from := Proset_prod_from P Q
|}.
Next Obligation.
  intros A B R S P Q; exists (fun p => iso_id).
  intros x y f; split; exact I.
Qed.
Next Obligation.
  intros A B R S P Q; exists (fun p => iso_id).
  intros x y f; exact I.
Qed.

(* * ** Functor categories: Mac Lane II.4 Ex. 4, structural half / * **函子范畴：Mac Lane II.4 练习 4，结构部分 *)

(*
 A functor category into a thin target is thin: natural
 transformations are compared pointwise, and their components are
 parallel in the target. 

 --------
 一个到薄目标的函子范畴是薄的：自然变换是逐点比较的，它们的分量在目标中是平行的。
*)
Lemma Thin_Fun {C D : Category} (TD : Thin D) : Thin (@Fun C D).
Proof.
  intros F G σ τ x.
  exact (TD _ _ _ _).
Qed.

(* * ** The functor category between preorders, concretely / * ** 预序之间的函子范畴，具体来说 *)

Section MonotoneOrder.

Context {A : Type} {R : relation A} (P : RelationClasses.PreOrder R).
Context {B : Type} {S : relation B} (Q : RelationClasses.PreOrder S).

(* The pointwise order on monotone maps. / 关于单调映射的逐点顺序。 *)
Definition mm_le (f g : @MonotoneFun A R B S) : Prop :=
  ∀ x : A, S (mono_map f x) (mono_map g x).

#[export] Instance mm_le_PreOrder : RelationClasses.PreOrder mm_le.
Proof using Q.
  constructor.
  - intros f x.
    exact (@RelationClasses.PreOrder_Reflexive _ _ Q (mono_map f x)).
  - intros f g h Hfg Hgh x.
    exact (@RelationClasses.PreOrder_Transitive _ _ Q _ _ _ (Hfg x) (Hgh x)).
Qed.

(* The preorder of monotone maps, as a thin category. / 作为薄范畴的单调映射的预序。 *)
Definition MonotoneProset : Category := Proset mm_le_PreOrder.

(*
 The dictionary, functorially: on objects it is
 Instance/Proset/Monotone.v's [monotone_of_Functor]/
 [Functor_of_monotone] pair; on morphisms, a natural transformation
 between functors of prosets is exactly a pointwise-order proof, and
 conversely (Theory/Thin.v's [thin_natural] at the thin target). 

 --------
 词典，从函子角度：在对象上，它是 Instance/Proset/Monotone.v 的 [monotone_of_Functor] / [Functor_of_monotone] 对；在态射上，prosets 函子之间的自然变换恰好是逐点顺序证明，反之亦然（Theory/Thin.v 的 [thin_natural] 在薄目标上）。
*)
Program Definition Fun_Proset_to :
  @Fun (Proset P) (Proset Q) ⟶ MonotoneProset := {|
  fobj := monotone_of_Functor P Q;
  fmap := fun F G σ => fun x => transform σ x
|}.
Next Obligation.
  intros F G σ τ Hστ; exact I.
Qed.
Next Obligation.
  intros F; exact I.
Qed.
Next Obligation.
  intros F G H σ τ; exact I.
Qed.

Program Definition Fun_Proset_from :
  MonotoneProset ⟶ @Fun (Proset P) (Proset Q) := {|
  fobj := Functor_of_monotone P Q;
  fmap := fun f g h =>
    thin_natural (proset_thin Q)
      (Functor_of_monotone P Q f) (Functor_of_monotone P Q g)
      (fun x => h x)
|}.
Next Obligation.
  intros f g h h' Hh x; exact I.
Qed.
Next Obligation.
  intros f x; exact I.
Qed.
Next Obligation.
  intros f g h p q x; exact I.
Qed.

(*
 Mac Lane II.4 Ex. 4, concrete half: the functor category between two
 preorders is the pointwise-ordered preorder of monotone maps.  Both
 object round trips are definitional by record eta (the monoid-side
 one literally, the functor-side one up to the proof fields, which
 [Functor_Setoid]'s natural isomorphisms never inspect); every
 morphism-level obligation is thinness on one side or the other. 

 --------
 Mac Lane II.4 练习 4，具体部分：两个预序之间的函子范畴是单调映射的逐点有序预序。两个对象的往返在定义上都是通过记录 eta 实现的（单子侧的完全是字面定义，函子侧的只是到证明字段为止的定义，[Functor_Setoid] 的自然同构从不检查这些字段）；每一个态射级别的要求都是在某一侧的稀疏性。
*)
Program Definition Fun_Proset_iso :
  @Fun (Proset P) (Proset Q) ≅[Cat] MonotoneProset := {|
  to   := Fun_Proset_to;
  from := Fun_Proset_from
|}.
Next Obligation.
  simpl; exists (fun f => iso_id).
  intros; exact I.
Qed.
Next Obligation.
  simpl; unshelve eexists.
  - intro F.
    unshelve refine
      (@Build_Isomorphism (@Fun (Proset P) (Proset Q))
         (Functor_of_monotone P Q (monotone_of_Functor P Q F)) F
         (thin_natural (proset_thin Q)
            (Functor_of_monotone P Q (monotone_of_Functor P Q F)) F
            (fun x => fmap[F] (@RelationClasses.PreOrder_Reflexive _ _ P x)))
         (thin_natural (proset_thin Q) F
            (Functor_of_monotone P Q (monotone_of_Functor P Q F))
            (fun x => fmap[F] (@RelationClasses.PreOrder_Reflexive _ _ P x)))
         _ _).
    + simpl; intros; exact I.
    + simpl; intros; exact I.
  - simpl; intros; exact I.
Qed.

End MonotoneOrder.

(* * ** Seven Sketches §1.2.2: the worked product Roof ∏ 2 / * ** 七个素描 §1.2.2：加工成品 屋顶 ∏ 2 *)

(*
 The six-object product of the V-shaped preorder with the walking
 arrow.  One decision procedure settles the whole Hasse diagram: for
 every ordered pair of objects it either produces the (unique)
 morphism — enumerating the fifteen related pairs — or refutes it —
 the twenty-one unrelated ones.  The refutations are by inversion on
 the impossible component, with no decidability or axiom imported. 

 --------
 V 形预序与行走箭头的六对象积。 一个判定程序解决了整个 Hasse 图：对于每一对有序对象，它要么生成（唯一的）态射——列出十五个相关的配对——要么否定它——二十一对无关的配对。 否定是通过对不可能的组成部分进行反演实现的，没有引入可判定性或公理。
*)
Definition roof_two_hom_dec :
  ∀ x y : Roof ∏ _2, (x ~> y) + ((x ~> y) → False).
Proof.
  intros [r1 t1] [r2 t2].
  destruct r1, r2, t1, t2;
  first
    [ solve [ left; split; constructor ]
    | solve [ right; intros [f g]; inversion f ]
    | solve [ right; intros [f g]; inversion g ] ].
Defined.

(* Sanity: the decider is exercised at one related and one unrelated pair — the apex reaches the right foot, and nothing climbs back up the V. / 理智：裁决者在一对相关和一对不相关的组合中执行——顶点到达右脚，没有任何东西再次沿着V向上攀爬。 *)
Example roof_two_related :
  ((RZero, TwoX) : Roof ∏ _2) ~> (RPos, TwoY).
Proof.
  exact (ZeroPos, TwoXY).
Qed.

Example roof_two_unrelated :
  (((RPos, TwoX) : Roof ∏ _2) ~> (RNeg, TwoX)) → False.
Proof.
  intros [f g]; inversion f.
Qed.

(* The counts, made load-bearing: the decider is transparent, so the fifteen/twenty-one split computes. / 这些计数被用作承重：决策者是透明的，所以十五/二十一的分割是合理的。 *)
Definition roof_two_objs : list (Roof ∏ _2) :=
  ((RNeg, TwoX) :: (RNeg, TwoY) :: (RZero, TwoX) :: (RZero, TwoY)
     :: (RPos, TwoX) :: (RPos, TwoY) :: nil)%list.

Definition roof_two_related_count : nat :=
  length
    (filter
       (fun p =>
          match roof_two_hom_dec (fst p) (snd p) with
          | inl _ => true
          | inr _ => false
          end)
       (list_prod roof_two_objs roof_two_objs)).

Example roof_two_fifteen : roof_two_related_count = 15%nat := eq_refl.

Example roof_two_twenty_one :
  (length (list_prod roof_two_objs roof_two_objs)
     - roof_two_related_count)%nat = 21%nat := eq_refl.
