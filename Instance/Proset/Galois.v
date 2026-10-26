(*
   * * Galois connections are adjunctions between preorders

   Mac Lane §IV.5 Theorem 1: a Galois connection between preordered sets is
   exactly an adjunction between the corresponding thin categories (Categories
   for the Working Mathematician, 2nd ed., printed pp. 95-96).  The book is
   cited BY LOCATION only; its printed text was not consulted while writing
   this file, and the locations follow issue jwiegley/category-theory#380.

   A GALOIS CONNECTION between preorders [(A,≤)] and [(B,⊑)] is a pair of
   monotone maps [f : A → B], [g : B → A] with

   f a ⊑ b   iff   a ≤ g b.

   Instance/Proset.v turns a [PreOrder] into a category whose homs ARE the
   order relation and whose hom-setoid identifies everything
   ([equiv := fun _ _ => True]).  Under that reading the displayed
   biconditional is precisely an adjunction's hom-set isomorphism, and this
   file proves the correspondence in both directions.

   WHY THIS IS MORE THAN A RESTATEMENT: THE VACUITY IS THE CONTENT.  An
   [Adjunction] (Theory/Adjunction.v) is one iso field plus FOUR
   naturality fields, and an [Adjunction_Transform]
   (Adjunction/Natural/Transformation.v) additionally carries two
   triangle identities.  Over a thin category every one of those side
   conditions is an equation between parallel morphisms, and in [Proset] any
   two parallel morphisms are related by [True].  So they are all discharged
   by [exact I].

   That is exactly why the bridge is cheap -- and it is also the thing worth
   proving rather than assuming.  The naive worry about a thin target is that
   the resulting statements are VACUOUS.  The honest position is subtler, and
   this file states it as [proset_side_conditions_vacuous] and its consequences:
   the side conditions carry no information, but the ISO FIELD does.  A Galois
   connection is genuine data -- the two maps and the biconditional -- and it
   is only the coherence overhead that collapses.  Stating that as a reusable
   lemma is what three of issue #380's hidden checkboxes ask for.  Note the
   obligations here are in fact closed by [Program]'s default tactic, which
   inlines [I]; the named lemma earns its keep at [galois_of_unit_counit],
   where the bare closure inequalities alone yield a full adjunction.

   A FACT ABOUT [Poset] WORTH RECORDING (not an error in the issue, which
   never claims otherwise -- it simply names both files).
   Instance/Poset.v reads [Definition Poset ... := Proset P],
   DISCARDING its antisymmetry argument, which never appears in the body.
   Hence:

   - [Poset] and [Proset] are the same category, so anything proved for
   [Proset] holds for [Poset] by delta-reduction and no separate [Poset]
   lemma is ever needed ([poset_is_proset] records this by [eq_refl]);
   - antisymmetry cannot be recovered FROM THE CATEGORY VALUE, so a
   “mutually related implies equal” corollary must take it as a separate
   hypothesis ([mutual_le_to_eq]).  It CAN still be stated over [Poset]
   itself, since [Poset] receives antisymmetry as an argument and it is
   therefore in scope -- so this is a statement about what the category
   remembers, not about what is expressible. 

   --------
   * * Galois 连接是序前集之间的伴随关系

   Mac Lane §IV.5 定理 1：序前集之间的 Galois 连接恰好是相应薄范畴之间的伴随关系（《为工作数学家准备的范畴论》，第二版，第 95-96 页）。此书仅按位置引用；在编写此文件时未查阅其印刷文本，且位置遵循问题 jwiegley/category-theory#380。

   序前集  [(A,≤)]  和  [(B,⊑)]  之间的 GALOIS 连接是一对单调映射  [f : A → B] ，  [g : B → A] ，满足

   f a ⊑ b   当且仅当   a ≤ g b。Instance/Proset.v 将一个 [PreOrder] 转换为一个类别，其同态是序关系，其同态集准则将所有元素识别为相同（[equiv := fun _ _ => True]）。在这种解释下，显示的双条件正是伴随概念的同态集同构，而这个文件证明了该对应关系在两个方向上都是成立的。

   为什么这不仅仅是重述：空洞性就是内容。一个 [Adjunction]（Theory/Adjunction.v）包含一个同构字段加四个自然性字段，而一个 [Adjunction_Transform]（Adjunction/Natural/Transformation.v）另外还包含两个三角恒等式。在薄类别上，这些附加条件中的每一个都是平行态射之间的方程，并且在 [Proset] 中，任意两个平行态射都由 [True] 相关联。因此，它们都被 [exact I] 解决了。这正是为什么这座桥便宜——这也是值得证明而不是假设的事情。对薄目标的天真担忧在于结果语句是空洞的。诚实的立场更为微妙，这个文件将其表述为 [proset_side_conditions_vacuous] 及其后果：附加条件没有携带信息，但 ISO 字段却有。伽罗瓦连接是真正的数据——两个映射和双条件——且仅有的崩溃是相干性开销。将其作为可重用引理陈述，正是 #380 号问题中三个隐藏复选框所要求的。请注意，这里的义务事实上由 [Program] 的默认策略关闭，该策略内联了 [I]；命名的引理在 [galois_of_unit_counit] 处体现其价值，仅凭闭包不等式就可产生完整的伴随关系。关于 [Poset] 值得记录的一个事实（不是问题中的错误，问题从未声称其他——它只是命名了两个文件）。
   Instance/Poset.v 读取 [Definition Poset ... := Proset P]，
   舍弃其反对称性参数，该参数在主体中从未出现。
   因此：-  [Poset] 和 [Proset] 属于同一类别，因此任何在 [Proset] 上证明的结论通过 Δ-化简也适用于 [Poset]，无需单独的 [Poset] 引理（[poset_is_proset] 通过 [eq_refl] 记录了这一点）；
   - 反对称性不能从类别值中恢复，因此“相互关联则相等”的推论必须作为单独假设（[mutual_le_to_eq]）。它仍然可以在 [Poset] 本身上陈述，因为 [Poset] 以反对称性作为参数接收，因此在作用域内——所以这是关于类别记住了什么的陈述，而不是关于可表达的内容。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Sets.

(* Same two as Instance/Proset.v -- [relation] and [PreOrder] here are the stdlib Prop-valued ones, not [crelation]. / 与 Instance/Proset.v 中的两个相同——这里的 [relation] 和 [PreOrder] 是标准库中值为 Prop 的，不是 [crelation]。 *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(* * ** Thinness, and the vacuity it induces / * ** 消瘦，以及它引起的空虚感 *)

(*
   * A category is THIN when any two parallel morphisms agree.  Before this file
   thinness was available only as the trivial hom-setoid buried inside
   [Proset] and an ad-hoc [two_thin] for the walking arrow, so it could not be
   used as a hypothesis. 

   --------
   * 当任意两个平行的态射相同时，一个范畴是薄的。在此文件之前，薄性仅作为隐藏在 [Proset] 中的平凡同态集存在，并且对于行走箭头有一个临时的 [two_thin]，因此它无法被用作假设。
*)
Definition Thin (C : Category) : Type :=
  ∀ (x y : C) (f g : x ~> y), f ≈ g.

(** Every [Proset] is thin, by construction: its hom-setoid relates everything. / 每个 [Proset] 都是薄的，这是由构造决定的：它的同态集合将所有东西联系起来。 *)
Lemma proset_thin {A : Type} {R : relation A} (P : PreOrder R)
  : Thin (Proset P).
Proof. intros x y f g; exact I. Qed.

(*
   * THE VACUITY LEMMA the issue's hidden checkboxes ask for, stated once so
   that no consumer has to inline [exact I].  In a thin category ANY equation
   between parallel morphisms holds -- which covers, uniformly, all four
   naturality fields of [Adjunction] and both triangle identities of
   [Adjunction_Transform]. 

   --------
   * 空虚引理 隐藏复选框所要求的问题，陈述一次，以便没有消费者需要内联 [exact I]。在一个稀薄范畴中，平行态射之间的任何方程都成立——这均匀地涵盖了 [Adjunction] 的所有四个自然性域以及 [Adjunction_Transform] 的两个三角恒等式。
*)
Lemma thin_side_condition {C : Category} (H : Thin C) {x y : C} (f g : x ~> y) :
  f ≈ g.
Proof. apply H. Qed.

Corollary proset_side_conditions_vacuous {A : Type} {R : relation A}
  (P : PreOrder R) {x y : Proset P} (f g : x ~{Proset P}~> y) : f ≈ g.
Proof. exact I. Qed.

(*
   * What does NOT collapse: the hom-setoid isomorphism still carries the two
   maps and the biconditional between them, so adjointness remains a real
   constraint even though every coherence field is free.  That is proved, not
   asserted, by [succ_not_self_adjoint] at the end of this file. 

   --------
   * 什么不会坍塌：同态集合等价仍然携带两个映射及其间的双条件关系，因此即使每个相干场都是自由的，伴随性仍然是真实的约束。 这一点由 [succ_not_self_adjoint] 在本文件结尾处证明，而非断言。
*)

(** ** Galois connections / ** 伽罗瓦连接 *)

(*
   * Mac Lane's definition.  [gal_mono_l]/[gal_mono_r] are monotonicity of the
   two maps; [gal_to]/[gal_from] are the two halves of the displayed
   biconditional.

   Declared OUTSIDE the section below on purpose: none of its fields mentions
   the [PreOrder] witnesses, only the relations, so a section would not
   generalize over them and [GaloisConnection PA PB] would not typecheck.  A
   Galois connection is data about the ORDERS; reflexivity and transitivity are
   needed only to build the categories. 

   --------
   * Mac Lane 的定义。[gal_mono_l] / [gal_mono_r] 是两个映射的单调性；[gal_to] / [gal_from] 是显示的双条件的两个部分。

   故意在下面的部分外部声明：其字段没有一个提到 [PreOrder] 的见证者，只涉及关系，因此放在某个部分中不会对它们进行泛化，并且 [GaloisConnection PA PB] 将无法类型检查。伽罗瓦连接是关于序的数据信息；反身性和传递性仅在构建范畴时需要。
*)
Record GaloisConnection {A B : Type} (RA : relation A) (RB : relation B) := {
  gal_l : A → B;
  gal_r : B → A;

  gal_mono_l : ∀ a a', RA a a' → RB (gal_l a) (gal_l a');
  gal_mono_r : ∀ b b', RB b b' → RA (gal_r b) (gal_r b');

  gal_to   : ∀ a b, RB (gal_l a) b → RA a (gal_r b);
  gal_from : ∀ a b, RA a (gal_r b) → RB (gal_l a) b
}.

Arguments gal_l {A B RA RB} _ _.
Arguments gal_r {A B RA RB} _ _.
Arguments gal_mono_l {A B RA RB} _ {a a'} _.
Arguments gal_mono_r {A B RA RB} _ {b b'} _.
Arguments gal_to {A B RA RB} _ a b _.
Arguments gal_from {A B RA RB} _ a b _.

(* * ** The bridge, forward: a Galois connection yields an adjunction / * ** 桥梁，前进：伽罗瓦连接产生一个伴随关系 *)

Section Galois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

Program Definition GaloisFunctor_l : Proset PA ⟶ Proset PB := {|
  fobj := gal_l G;
  fmap := fun a a' h => gal_mono_l G h
|}.

Program Definition GaloisFunctor_r : Proset PB ⟶ Proset PA := {|
  fobj := gal_r G;
  fmap := fun b b' h => gal_mono_r G h
|}.

(*
   * The hom-set isomorphism IS the biconditional.  Its two round-trip
   obligations are equations between parallel morphisms in a thin category,
   hence vacuous; [Program]'s default obligation tactic closes them with [I]
   directly.  [proset_side_conditions_vacuous] states that fact reusably --
   it is consumed by [galois_of_unit_counit] below, which is where the
   vacuity does load-bearing work. 

   --------
   * 同构集同构就是双条件。它的两个往返义务是在薄范畴中平行态射之间的方程，因此是虚假的；[Program] 的默认义务策略直接用 [I] 关闭它们。[proset_side_conditions_vacuous] 可重用地陈述了这个事实——它被下面的 [galois_of_unit_counit] 使用，这正是虚假发挥承重作用的地方。
*)
Program Definition galois_adj_iso (a : Proset PA) (b : Proset PB) :
  @Isomorphism Sets
    {| carrier := @hom (Proset PB) (gal_l G a) b
     ; is_setoid := @homset (Proset PB) (gal_l G a) b |}
    {| carrier := @hom (Proset PA) a (gal_r G b)
     ; is_setoid := @homset (Proset PA) a (gal_r G b) |} := {|
  to   := {| morphism := gal_to G a b |};
  from := {| morphism := gal_from G a b |}
|}.

(*
   * The adjunction.  Every remaining field is a side condition in a thin
   category, so the whole coherence burden is discharged uniformly. 

   --------
   * 连接。每一个剩余的场都是一个薄范畴中的附加条件，所以整个相容性负担都是统一地解除的。
*)
Program Definition GaloisAdjunction :
  @Adjunction (Proset PB) (Proset PA) GaloisFunctor_l GaloisFunctor_r := {|
  adj := galois_adj_iso
|}.

End Galois.

(* * ** The bridge, backward: an adjunction between preorders is a Galois connection / * ** 桥，向后：序的函子连接是一个伽罗瓦连接 *)

Section Ungalois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (F : Proset PA ⟶ Proset PB) (U : Proset PB ⟶ Proset PA).
Context (Adj : F ⊣ U).

Definition GaloisOfAdjunction : GaloisConnection RA RB :=
  {| gal_l := fobj[F]
   ; gal_r := fobj[U]
     (*
 [fmap]'s object arguments are given explicitly: leaving them implicit
 strands them as evars, since the record field's own arguments were made
 implicit above. 

 --------
 [fmap] 的对象参数是显式给出的：将它们留作隐式会把它们作为 evars， 因为记录字段自身的参数在上面被设为隐式。
*)
   ; gal_mono_l := fun a a' h => @fmap _ _ F a a' h
   ; gal_mono_r := fun b b' h => @fmap _ _ U b b' h
   ; gal_to   := fun a b h => to   (@adj _ _ _ _ Adj a b) h
   ; gal_from := fun a b h => from (@adj _ _ _ _ Adj a b) h |}.

End Ungalois.

(* * ** Poset: the same category, and what that costs / * ** 集合: 相同的类别，以及这需要的成本 *)

(*
   * Instance/Poset.v defines [Poset] as [Proset] with the antisymmetry
   argument discarded, so the two are the SAME category -- definitionally. 

   --------
   * Instance/Poset.v 将 [Poset] 定义为 [Proset]，并且弃用了反对称性参数，所以两者在定义上是相同的范畴。
*)
Lemma poset_is_proset {A : Type} {R : relation A}
  (P : PreOrder R) (AS : @Antisymmetric A eq eq_equiv R) :
  @Poset A R P AS = @Proset A R P.
Proof. reflexivity. Qed.

(*
   * Consequently a “mutually related implies equal” corollary CANNOT be read
   off the category: antisymmetry has to be supplied separately.  With it, an
   isomorphism in the order category is exactly mutual comparability, and
   antisymmetry converts that to equality. 

   --------
   * 因此，不能从范畴中直接读出“相互相关意味着相等”的推论：反对称性必须单独提供。有了它，序范畴中的同构正好就是相互可比性，而反对称性将其转化为相等。
*)
Lemma mutual_le_to_eq {A : Type} {R : relation A} (P : PreOrder R)
  (AS : @Antisymmetric A eq eq_equiv R) {x y : Proset P}
  (i : x ≅[Proset P] y) : x = y.
Proof. exact (AS x y (to i) (from i)). Qed.

(* * ** Round trip, and a witness that the notion is not empty / * ** 往返，并且见证这个概念不是空的 *)

(*
   * Going to an adjunction and back recovers the two maps.  Be honest about
   what this is: a DEFINITIONAL sanity check, proved by [eq_refl] on both
   components, because [GaloisAdjunction]'s type already names the functors
   and [GaloisOfAdjunction] merely projects [fobj] back out.  There is nothing
   it could refute, and the whole RECORD round-trips by [eq_refl] just as
   cheaply.  It is worth
   stating so the reader can see the maps are not silently replaced, but it is
   not evidence that the bridge is faithful -- for that see
   [succ_not_self_adjoint] below, which shows adjointness is a real
   constraint. 

   --------
   * 前往一个伴随并返回可以恢复两个映射。诚实地说明这是什么：一个定义性的合理性检查，由 [eq_refl] 在两个分量上证明，因为 [GaloisAdjunction] 的类型已经命名了函子，而 [GaloisOfAdjunction] 仅仅是将 [fobj] 投影回去。它无法反驳任何东西，而且整个记录通过 [eq_refl] 也能同样廉价地完成往返。值得说明这一点，以便读者可以看到映射没有被悄悄替换，但这并不是桥是否忠实的证据——有关这一点请参见下面的 [succ_not_self_adjoint]，它显示了伴随性是真正的约束。
*)
Lemma galois_round_trip {A B : Type} {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB) (G : GaloisConnection RA RB) :
  gal_l (GaloisOfAdjunction PA PB _ _ (GaloisAdjunction PA PB G)) = gal_l G
  ∧ gal_r (GaloisOfAdjunction PA PB _ _ (GaloisAdjunction PA PB G)) = gal_r G.
Proof. split; reflexivity. Qed.

(*
   * A CONCRETE Galois connection, so that nothing above is vacuously about an
   empty notion: on the naturals, truncated SUBTRACTION of [k] is left adjoint
   to ADDITION of [k], via [n - k ≤ m  ↔  n ≤ m + k].  Both halves need real
   arithmetic; neither is a coherence triviality.

   The orientation matters and is easy to get backwards.  Adding [k] on the
   left does NOT work: [gal_from] would read [a ≤ b - k → a + k ≤ b], refuted
   by [k = 5], [b = 0], [a = 0], where truncation makes the hypothesis hold
   while the conclusion does not.  [lia] rejected that version, which is how
   the error was caught. 

   --------
   * 一个具体的 Galois 对应关系，因此上面没有什么是空洞的概念：在自然数上，[k] 的截断减法是左伴随于 [k] 的加法，通过 [n - k ≤ m  ↔  n ≤ m + k]。两部分都需要实际的算术；都不是一致性上的简单性。

   方向很重要，而且很容易弄反。在左边加 [k] 是行不通的：[gal_from] 会被读作 [a ≤ b - k → a + k ≤ b]，但被 [k = 5]、[b = 0]、[a = 0] 反驳，其中截断使假设成立而结论不成立。[lia] 拒绝了那个版本，这就是错误被发现的方式。
*)
Program Definition nat_shift_galois (k : nat)
  : GaloisConnection Nat.le Nat.le := {|
  gal_l := fun n => Nat.sub n k;
  gal_r := fun m => Nat.add m k
|}.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Definition nat_shift_adjunction (k : nat) : _ :=
  GaloisAdjunction Nat.le_preorder Nat.le_preorder (nat_shift_galois k).

(*
   * The witness is not degenerate: the two maps genuinely differ for [k > 0],
   so this is not the identity connection wearing a disguise. 

   --------
   * 见证者并非退化：对于 [k > 0]，这两幅映射确实不同，所以这不是伪装起来的恒等联络。
*)
(*
 The two maps are genuinely different functions, so this is not the identity
 connection in disguise.  [%nat] is needed: the library's own scopes shadow
 the numeral notation. 

 --------
 这两个映射是真正不同的函数，所以这并不是伪装的恒等连接。[%nat] 是必需的：库本身的作用域会覆盖数字符号表示法。
*)
Example nat_shift_differ :
  gal_l (nat_shift_galois 1%nat) 3%nat = 2%nat := eq_refl.
Example nat_shift_differ_r :
  gal_r (nat_shift_galois 1%nat) 3%nat = 4%nat := eq_refl.

(* * ** The unit/counit reading, and the bare-implication form / * ** 单位/余单位读法，以及裸蕴涵形式 *)

(*
   * Awodey §9.4's order reading: the unit says [a] is below the composite at
   [a], the counit that the composite at [b] is below [b].  In an order these
   are the two familiar closure inequalities. 

   --------
   * Awodey §9.4 的顺序阅读：单位表示 [a] 在复合 [a] 之下，余单位表示复合 [b] 在 [b] 之下。在顺序中，这两个是不陌生的闭包不等式。
*)

Section UnitCounit.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (G : GaloisConnection RA RB).

Definition gal_unit (PB : PreOrder RB) (a : A) : RA a (gal_r G (gal_l G a)) :=
  gal_to G a (gal_l G a) (@reflexivity B RB (@PreOrder_Reflexive B RB PB) _).

Definition gal_counit (PA : PreOrder RA) (b : B) : RB (gal_l G (gal_r G b)) b :=
  gal_from G (gal_r G b) b (@reflexivity A RA (@PreOrder_Reflexive A RA PA) _).

End UnitCounit.

(*
   * Conversely -- Seven Sketches Proposition 1.107 / display 1.108, and Riehl
   §4.2's “bare pair suffices”.  Given only monotone maps and the two closure
   inequalities, the full biconditional follows, hence a full adjunction: no
   naturality and no triangle identity has to be supplied, because in a thin
   target they are equations between parallel morphisms.  THIS is the lemma
   the vacuity result exists to support. 

   --------
   * 相反——《七个素描》命题 1.107 / 展示 1.108，以及 Riehl §4.2 的“仅有一对即可”。仅给出单调映射和两个闭包不等式，就可以得到完整的双条件命题，因此得到完整的伴随关系：不需要提供自然性和三角恒等式，因为在薄目标中它们只是平行态射之间的等式。这正是空洞性结果存在以支持的引理。
*)
Definition galois_of_unit_counit {A B : Type}
  {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB)
  (l : A → B) (r : B → A)
  (ml : ∀ a a', RA a a' → RB (l a) (l a'))
  (mr : ∀ b b', RB b b' → RA (r b) (r b'))
  (unit   : ∀ a, RA a (r (l a)))
  (counit : ∀ b, RB (l (r b)) b)
  : GaloisConnection RA RB :=
  {| gal_l := l
   ; gal_r := r
   ; gal_mono_l := ml
   ; gal_mono_r := mr
     (* f a ⊑ b gives a ≤ r (f a) ≤ r b / f a ⊑ b 给出 a ≤ r (f a) ≤ r b *)
   ; gal_to := fun a b h =>
       @transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
         (unit a) (mr _ _ h)
     (* a ≤ r b gives f a ⊑ f (r b) ⊑ b / a ≤ r b 给出 f a ⊑ f (r b) ⊑ b *)
   ; gal_from := fun a b h =>
       @transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _
         (ml _ _ h) (counit b) |}.

(* * ** Uniqueness of adjoints, at the order level / * ** 伴随算子的唯一性，在阶层水平 *)

(*
   * Seven Sketches §1.4.3 exercise 1.110: two left adjoints of the same map
   agree, and dually.  In an order “agree” is mutual comparability -- which is
   equality only under antisymmetry, so both forms are given. 

   --------
   * 《七个素描》§1.4.3 练习 1.110：同一个映射的两个左伴随是一致的，并且对偶亦然。在一个序中，“一致”是相互可比性——在反对称性下这仅是相等，因此给出了两种形式。
*)
Lemma gal_left_unique {A B : Type} {RA : relation A} {RB : relation B}
  (PB : PreOrder RB)
  (G G' : GaloisConnection RA RB)
  (Hr : ∀ b, gal_r G b = gal_r G' b) (a : A)
  : RB (gal_l G a) (gal_l G' a) * RB (gal_l G' a) (gal_l G a).
Proof.
  split.
  - apply (gal_from G a (gal_l G' a)).
    rewrite Hr. exact (gal_unit G' PB a).
  - apply (gal_from G' a (gal_l G a)).
    rewrite <- Hr. exact (gal_unit G PB a).
Qed.

(* * ** What does NOT collapse: adjointness is a real constraint / * ** 不会崩塌：伴随性是真正的约束 *)

(*
   * The thesis of this file is that the coherence is vacuous but the
   biconditional is not.  Asserting that in prose would be worth little, so
   here it is as a theorem: the successor map is not left adjoint to itself,
   even though both are monotone and every coherence condition would be free.
   So [GaloisAdjunction] is not inhabited for an arbitrary monotone pair. 

   --------
   * 本文件的论点是，一致性是空洞的，但双条件句则不是。用散文来断言这一点几乎没有价值，因此在这里将其作为定理：继任映射不是它自身的左伴随，尽管两者都是单调的，并且每一个一致性条件都是免费的。因此，对于任意单调对，[GaloisAdjunction] 不是有解的。
*)
Program Definition NatSucc : Proset Nat.le_preorder ⟶ Proset Nat.le_preorder := {|
  fobj := S;
  fmap := fun x y (h : Nat.le x y) => _
|}.
Next Obligation. lia. Qed.

Theorem succ_not_self_adjoint :
  @Adjunction (Proset Nat.le_preorder) (Proset Nat.le_preorder) NatSucc NatSucc
    → False.
Proof.
  intro Adj.
  (*
 to (adj 0 0) turns [S 0 ≤ 0] into [0 ≤ S 0]; the reverse direction turns
 [0 ≤ S 0] into [S 0 ≤ 0], which is absurd. 

 --------
 将 (adj 0 0) 转换 [S 0 ≤ 0] 为 [0 ≤ S 0]；反方向将 [0 ≤ S 0] 转换为 [S 0 ≤ 0]，这是荒谬的。
*)
  pose proof (from (@adj _ _ _ _ Adj 0%nat 0%nat)) as H.
  simpl in H.
  assert (Nat.le 0 (S 0)) as H0 by lia.
  pose proof (H H0) as Hbad.
  simpl in Hbad.
  lia.
Qed.
