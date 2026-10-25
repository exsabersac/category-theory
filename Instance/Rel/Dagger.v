Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Dagger.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Rel.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * Rel: converse, self-duality, and the graph embedding's faithfulness

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.7
   (printed p. 26) [maclane:I.7:construction8]: Rel carries the
   CONVERSE relation R† = { (b, a) | (a, b) ∈ R }, an involution that
   is an anti-homomorphism for the relative product; and Set sits
   inside Rel by taking graphs of functions.
   Awodey, "Category Theory", 2nd ed., §1.9 Exercise 2 (printed
   p. 29) [awodey:1:ex2]: which of these hold?  (a) Rel ≅ Rel^op;
   (b) Sets ≅ Sets^op; (c) P(X) ≅ P(X)^op for a fixed set X.
   nLab: https://ncatlab.org/nlab/show/Rel

   This file completes Instance/Rel.v's disclosed gaps:

   - [Rel_Dagger]: the converse as the first instance of
   Structure/Dagger.v's [DaggerCategory] — the design choice the
   issue left open is resolved toward the general class, since the
   ZX and compact-closed prose already speak of daggers.
   - [Rel_Converse] / [Rel_self_dual_strict] / [Rel_self_dual]: the
   dagger packaged as an identity-on-objects functor Rel ⟶ Rel^op
   and the self-duality at BOTH strengths — strict functor equality
   in StrictCat, the genuine isomorphism of categories Awodey asks
   for, and the ≅[Cat] equivalence reading — Awodey's (a),
   affirmative.
   - [Relation_Functor_Faithful]: functions with pointwise-equal
   graphs are pointwise equal, so Coq really is a WIDE SUBCATEGORY
   of Rel, not merely mapped into it.
   - [Rel_Terminal] / [Rel_Zero]: the empty set is terminal as well
   as initial — the zero-object half Instance/Rel.v recorded as
   missing.
   - [Powerset] / [Powerset_self_dual]: Awodey's (c), affirmative,
   via complementation — over DECIDABLE (bool-valued) subsets, the
   constructive transposition of the classical statement: the
   Prop-valued complement is an involution only up to double
   negation, and a predicate-comparing setoid is equivalent to
   double-negation elimination (the disclosure pattern of
   Instance/Top/Closed.v's [pred_comparison_forces_DNE]).  On
   bool-valued subsets the round trips close by case analysis on
   the membership bit, with no axiom.
   - [Sets_not_self_dual]: Awodey's (b), NEGATIVE, proved: any
   isomorphism Sets ≅ Sets^op in Cat repackages as an equivalence
   ([Cat_Iso_to_Equivalence]), hence a full and faithful functor F;
   fullness reads a would-be element of Sets(F ∅, F 1) back through
   the EMPTY hom-setoid Sets(1, ∅), so carrier (F 1) is empty; and
   then the two points of Sets(1, 2) have vacuously equivalent
   images — every parallel pair into an empty-carrier setoid agrees
   — so faithfulness forces true = false.  All three parts of
   Awodey's exercise are thereby answered: (a) yes, (b) no,
   (c) yes. 

   --------
   * * 关系：对偶、自对偶以及图嵌入的忠实性  

   Mac Lane，《作为工作数学家的范畴》，第2版，§I.7  
   （印刷第26页）[maclane:I.7:construction8]：Rel 承载  
   对偶关系 R† = { (b, a) | (a, b) ∈ R }，它是一种反恒等操作，对相对乘积是一个反同态；而 Set 通过取函数的图嵌入 Rel。  
   Awodey，《范畴论》，第2版，§1.9 练习2（印刷第29页）[awodey:1:ex2]：以下哪些成立？ (a) Rel ≅ Rel^op；  
   (b) Sets ≅ Sets^op；(c) 对于固定集合 X，有 P(X) ≅ P(X)^op。  
   nLab：https://ncatlab.org/nlab/show/Rel  

   本文件完成了 Instance/Rel.v 中公开的空白：- [Rel_Dagger]：作为 Structure/Dagger.v 中 [DaggerCategory] 的第一个实例的逆——问题中留下的设计选择倾向于一般类，因为 ZX 和紧闭形式的文字已经涉及到匕首。  
   - [Rel_Converse] / [Rel_self_dual_strict] / [Rel_self_dual]：作为对象恒等函子的 Rel ⟶ Rel^op 封装的匕首，以及在两种强度下的自对偶性——StrictCat 中的严格函子等式，Awodey 要求的范畴真正同构，以及 ≅ [Cat] 等价读取——Awodey 的 (a)，肯定。  
   - [Relation_Functor_Faithful]：具有点对点相等图的函数是点对点相等的，因此 Coq 实际上是 Rel 的一个宽子范畴，而不仅仅是映射到它中。-  [Rel_Terminal] / [Rel_Zero]：空集既是终对象也是初对象——零对象的一半实例/关系.v 被记录为缺失。 -  [Powerset] / [Powerset_self_dual]：Awodey 的 (c)，肯定地，通过补集实现——在可判定的（布尔值）子集上，是经典命题的构造性对换：Prop 值的补集仅在双重否定下才是自反的，而比较谓词的集合等价于双重否定消去（Instance/Top/Closed.v 中 [pred_comparison_forces_DNE] 的披露模式）。在布尔值子集上，通过对成员位进行情况分析，循环操作接近完成，无需公理。-  [Sets_not_self_dual]：Awodey 的 (b)，否定，证明：任何在 Cat 中的同构 Sets ≅ Sets^op 都可以重新打包为一个等价 ([Cat_Iso_to_Equivalence])，因此得到一个满且忠实的函子 F；满性意味着 Sets(F ∅, F 1) 的一个潜在元素可以通过空同态集 Sets(1, ∅) 回溯，因此载体 (F 1) 是空的；然后 Sets(1, 2) 的两个点具有形式上等价的像——每个映入空载体同态集的平行对都一致——所以忠实性强制 true = false。由此 Awodey 练习的三部分都得到了回答：(a) 是，(b) 否，(c) 是。
*)

(** ** The converse is a dagger / ** 反面是匕首 *)

#[export] Program Instance Rel_Dagger : DaggerCategory Rel := {
  dagger := fun x y (R : x ~{Rel}~> y) (b : y) (a : x) => R a b
}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x y R b a; split; intro H; exact H.
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

(* * ** Self-duality: Rel ≅ Rel^op in Cat (Awodey 1.9.2(a)) / * ** 自对偶性：Rel ≅ Rel^op 在 Cat 中 (Awodey 1.9.2(a)) *)

(*
 The dagger, as an identity-on-objects functor.  [fmap] must be
 [Proper] and functorial with the OPPOSITE composition order — which
 is exactly [dagger_compose].

 HOW STRONG THE SELF-DUALITY IS.  [Cat]'s hom-setoid makes ≅[Cat]
 an EQUIVALENCE of categories (Instance/Cat.v's header); Awodey's
 exercise asks about an isomorphism of categories.  Both are
 delivered below, the two-tier presentation of
 Structure/Groupoid/Inversion.v: [Rel_self_dual_strict] in
 StrictCat — free, both composites being identity-on-objects and
 the round trips holding by strict functor equality — and the
 ≅[Cat] reading [Rel_self_dual]. 

 --------
 匕首，作为一个在对象上恒等的函子。[fmap] 必须是 [Proper]，并且函子性遵循相反的复合顺序——这正是 [dagger_compose]。

 自对偶性有多强。[Cat] 的同态集合使得 ≅ [Cat] 成为范畴的等价（Instance/Cat.v 的标题）；Awodey 的练习问的是范畴的同构。以下都是实现，两层展示的 Structure/Groupoid/Inversion.v：[Rel_self_dual_strict] 在 StrictCat 中——自由的，两个复合都是在对象上恒等，并且通过严格的函子相等维持往返——以及 ≅ [Cat] 阅读 [Rel_self_dual]。
*)
Program Definition Rel_Converse : Rel ⟶ Rel^op := {|
  fobj := fun x => x;
  fmap := fun x y (R : x ~{Rel}~> y) => @dagger Rel Rel_Dagger x y R
|}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

Program Definition Rel_Converse_op : Rel^op ⟶ Rel := {|
  fobj := fun x => x;
  fmap := fun x y (R : x ~{Rel^op}~> y) => @dagger Rel Rel_Dagger y x R
|}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

#[local] Obligation Tactic := cat_simpl.

Program Definition Rel_self_dual_strict : Rel ≅[StrictCat] Rel^op := {|
  to   := Rel_Converse;
  from := Rel_Converse_op
|}.

#[local] Obligation Tactic := idtac.

Program Definition Rel_self_dual : Rel ≅[Cat] Rel^op := {|
  to   := Rel_Converse;
  from := Rel_Converse_op
|}.
Next Obligation.
  exists (fun x => iso_id).
  intros x y R a b; simpl.
  split; intro H.
  - exists b; split; [| constructor ].
    exists a; split; [ constructor | exact H ].
  - destruct H as [e [[e0 [He0 HR]] Hb]].
    destruct He0.
    destruct Hb.
    exact HR.
Qed.
Next Obligation.
  exists (fun x => iso_id).
  intros x y R a b; simpl.
  split; intro H.
  - exists a; split; [ constructor |].
    exists b; split; [ exact H | constructor ].
  - destruct H as [e [He [e0 [HR Hb]]]].
    destruct He.
    destruct Hb.
    exact HR.
Qed.

(* * ** The graph embedding is faithful: Coq is a wide subcategory / * ** 图嵌入是忠实的：Coq 是一个广泛的子范畴 *)

#[export] Instance Relation_Functor_Faithful : Faithful Relation_Functor.
Proof.
  constructor; intros x y f g H a.
  destruct (H a (f a)) as [Hfg _].
  destruct (Hfg (In_singleton _ _)).
  reflexivity.
Qed.

(* * ** The empty set is terminal too, hence a zero object / * ** 空集也是终对象，因此是零对象 *)

#[export] Program Instance Rel_Terminal : @Terminal Rel := {
  terminal_obj := False;
  one := fun _ _ (f : False) => False_rect _ f
}.
Next Obligation. intros x f g a b; contradiction. Qed.

#[export] Program Instance Rel_Zero : ZeroObject Rel := {
  zero_terminal := Rel_Terminal;
  zero_initial  := Rel_Initial;
  zero_coincide := iso_id
}.

(* * ** The powerset order is self-dual (Awodey 1.9.2(c)) / * ** 幂集顺序是自对偶的（Awodey 1.9.2(c)） *)

Section Powerset.

Context (X : Type).

(*
 Decidable subsets of X, ordered by pointwise containment.  The
 bool-valued reading is the constructive transposition of Awodey's
 P(X) (see the header): complementation is then a genuine involution,
 the round trips closing by case analysis on the membership bit. 

 --------
 X 的可判定子集，按逐点包含的顺序排列。布尔值的读法是 Awodey 的 P(X) 的构造性转置（见标题）：补集随后是真正的自反变换，通过对成员位的情况分析完成往返闭合。
*)
Definition psub (A B : X → bool) : Prop :=
  ∀ x : X, A x = true → B x = true.

#[export] Instance psub_preorder : RelationClasses.PreOrder psub.
Proof.
  constructor.
  - intros A x H; exact H.
  - intros A B C H1 H2 x H; exact (H2 x (H1 x H)).
Qed.

Definition Powerset : Category := Proset psub_preorder.

(*
 Complementation is antitone, hence a functor into the opposite
 order; the thin target makes every functor law free. 

 --------
 补集是反单调的，因此是一个指向对立序的函子；薄目标使每个函子定律自由。
*)
Program Definition Powerset_Compl : Powerset ⟶ Powerset^op := {|
  fobj := fun A x => negb (A x);
  fmap := fun A B (H : psub A B) x HB => _
|}.
Next Obligation.
  intros A B H x HB; simpl in HB |- *.
  destruct (A x) eqn:HA.
  - rewrite (H x HA) in HB; discriminate HB.
  - reflexivity.
Qed.
Next Obligation. intros A B f g H; exact I. Qed.
Next Obligation. intros A; exact I. Qed.
Next Obligation. intros A B C f g; exact I. Qed.

Program Definition Powerset_Compl_op : Powerset^op ⟶ Powerset := {|
  fobj := fun A x => negb (A x);
  fmap := fun A B (H : psub B A) x HB => _
|}.
Next Obligation.
  intros A B H x HB; simpl in HB |- *.
  destruct (B x) eqn:HB'.
  - rewrite (H x HB') in HB; discriminate HB.
  - reflexivity.
Qed.
Next Obligation. intros A B f g H; exact I. Qed.
Next Obligation. intros A; exact I. Qed.
Next Obligation. intros A B C f g; exact I. Qed.

Program Definition Powerset_self_dual : Powerset ≅[Cat] Powerset^op := {|
  to   := Powerset_Compl;
  from := Powerset_Compl_op
|}.
Next Obligation.
  unshelve eexists.
  - intro A; unshelve econstructor.
    + intros x H; vm_compute in H |- *; rewrite H; reflexivity.
    + intros x H; vm_compute in H |- *; destruct (A x) eqn:HA;
        [ reflexivity | discriminate H ].
    + exact I.
    + exact I.
  - intros A B H; exact I.
Qed.
Next Obligation.
  unshelve eexists.
  - intro A; unshelve econstructor.
    + intros x H; vm_compute in H |- *; destruct (A x) eqn:HA;
        [ reflexivity | discriminate H ].
    + intros x H; vm_compute in H |- *; rewrite H; reflexivity.
    + exact I.
    + exact I.
  - intros A B H; exact I.
Qed.

End Powerset.

(* * ** Sets is NOT self-dual (Awodey 1.9.2(b)) / * ** 集合不是自对偶的 (Awodey 1.9.2(b)) *)

Definition SEmpty : Sets := {| carrier := False; is_setoid := eq_Setoid False |}.
Definition SUnit  : Sets := {| carrier := unit;  is_setoid := eq_Setoid unit  |}.
Definition SBool  : Sets := {| carrier := bool;  is_setoid := eq_Setoid bool  |}.

#[local] Obligation Tactic := cat_simpl.

Program Definition kbool (b : bool) : SUnit ~{Sets}~> SBool :=
  {| morphism := fun _ => b |}.

(*
 Any Cat-isomorphism repackages as an equivalence, hence a full and
 faithful F : Sets ⟶ Sets^op.  Fullness reads a would-be element of
 Sets(F ∅, F 1) back through the EMPTY hom-setoid Sets(1, ∅), so
 carrier (F 1) is empty; then the two constant maps 1 ⇉ 2 have
 vacuously equivalent images — every parallel pair into an
 empty-carrier setoid agrees — and faithfulness forces true = false. 

 --------
 任何 Cat-同构都可以重新包装为一个等价，因此是一个完全且忠实的 F : Sets ⟶ Sets^op。完全性将 Sets(F ∅, F 1) 的一个可能元素通过空同态集 Sets(1, ∅) 读回来，因此载体 (F 1) 是空的；然后两个恒定映射 1 ⇉ 2 的像在空载体集上自动等价——进入空载体集同态的每一对平行映射都一致——而忠实性则迫使 true = false。
*)
Theorem Sets_not_self_dual : Sets ≅[Cat] Sets^op → False.
Proof.
  intro iso.
  pose (E := Cat_Iso_to_Equivalence iso).
  pose (F := to iso).
  pose proof (Equivalence_Full E)     as HFull.
  pose proof (Equivalence_Faithful E) as HFaith.
  assert (Hno : (F SEmpty ~{Sets}~> F SUnit) → False).
  { intro g. exact (@prefmap _ _ F HFull SUnit SEmpty g tt). }
  assert (He : carrier (F SUnit) → False).
  { intro e. unshelve refine (Hno {| morphism := fun _ => e |}).
    abstract (proper). }
  assert (Hfe : fmap[F] (kbool true) ≈ fmap[F] (kbool false)).
  { intro a. elim (He (fmap[F] (kbool true) a)). }
  pose proof (@fmap_inj _ _ F HFaith SUnit SBool _ _ Hfe tt) as Hc.
  discriminate Hc.
Qed.
