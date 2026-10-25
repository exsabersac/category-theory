(* * * The converse of [Full_Implies_Full_Functor] needs its hypothesis / * * [Full_Implies_Full_Functor] 的逆命题需要它的前提 *)

(*
 Construction/Subcategory.v proves [Full_Functor_Implies_Full] under the
 hypothesis [ShomRespects] — that the selected-morphism predicate is closed
 under the hom-setoid equivalence — and explains why the [Subcategory]
 record does not supply it.  That explanation was a diagnosis of why one
 proof does not go through, not a proof that no proof does.

 This file closes the gap with a counterexample, so the hypothesis is now
 known to be NECESSARY rather than merely convenient.  (The construction is
 due to an audit of the first commit of this work.)

 The ambient category has one object and the natural numbers as its
 morphisms, composed by addition, with two arrows identified exactly when
 both are zero or both are nonzero.  That is a genuine congruence for
 addition and it has two classes, so the hom-setoid is NOT the total
 relation — the counterexample does not cheat by making everything equal.
 The subcategory selects every morphism except 1.  Its inclusion is full as
 a FUNCTOR, because 1 can be replaced by 2, which is retained and
 equivalent to it; but the subcategory is not full as DATA, because 1
 itself is not retained.  That is exactly the failure of [ShomRespects]. 

 --------
 Construction/Subcategory.v 在假设 [ShomRespects]——即所选同态谓词在同态集合等价下是封闭的——的条件下，证明了 [Full_Functor_Implies_Full]，并解释了为什么 [Subcategory] 记录未提供它。这个解释是对为什么一个证明无法成立的诊断，而不是没有证明存在的证明。

 此文件通过一个反例填补了这一空白，因此该假设现在被认为是必要的，而不仅仅是方便的。（该构造源自对本工作首次提交的审计。）环境范畴有一个对象，自然数作为其态射，通过加法组合，当且仅当两个数都是零或都是非零时，这两个箭头才被认定为相同。这是加法的一个真正同余，并且它有两个类，所以同态集合不是全关系——反例不会通过使所有元素相等来作弊。子范畴选择除了1之外的每一个态射。作为一个函子，它的包含是完全的，因为1可以被替换为保留的且与之等价的2；但作为数据，它的子范畴不是完全的，因为1本身没有被保留下来。这正是[ShomRespects]失败的原因。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

Definition nz (n : nat) : bool := match n with O => true | S _ => false end.

Lemma nz_add : forall m n, nz (m + n) = andb (nz m) (nz n).
Proof. destruct m; simpl; auto. Qed.

#[local] Obligation Tactic := idtac.

Program Definition NZ : Category := {|
  obj     := unit;
  hom     := fun _ _ => nat;
  homset  := fun _ _ => {| equiv := fun m n => nz m = nz n |};
  id      := fun _ => 0%nat;
  compose := fun _ _ _ f g => (f + g)%nat
|}.
Next Obligation.
  intros _ _; constructor; congruence.
Qed.
Next Obligation.
  intros a b c ?? H ?? H0; simpl in *; rewrite !nz_add; congruence.
Qed.
Next Obligation. intros ?? f; simpl; reflexivity. Qed.
Next Obligation. intros ?? f; simpl; rewrite PeanoNat.Nat.add_0_r; reflexivity. Qed.
Next Obligation. intros ???? f g h; simpl; rewrite PeanoNat.Nat.add_assoc; reflexivity. Qed.
Next Obligation. intros ???? f g h; simpl; rewrite PeanoNat.Nat.add_assoc; reflexivity. Qed.

(*
 The selection data: every object; the morphisms are every natural number
 EXCEPT 1.  That is closed under + (a sum is 1 only if one summand is 1 and
 the other 0) and contains id = 0. 

 --------
 选择数据：每个对象；态射是每个自然数，除了1。它在加法下封闭（一个和为1仅当一个加数是1而另一个是0）并且包含 id = 0。
*)

Lemma not_one_add : forall m n, m <> 1%nat -> n <> 1%nat -> (m + n)%nat <> 1%nat.
Proof.
  intros [|[|m]] [|[|n]]; simpl; intros H1 H2 Hc;
    try discriminate;
    try (apply H1; reflexivity);
    try (apply H2; reflexivity).
Qed.

Definition NotOne : Subcategory NZ :=
  @Build_Subcategory NZ (fun _ => unit)
    (fun _ _ _ _ f => f <> 1%nat)
    (fun _ _ _ _ _ _ f g Hf Hg => not_one_add f g Hf Hg)
    (fun _ _ => ltac:(discriminate)).

(*
 The inclusion is FULL as a functor: given any f : nat, send it to 2 when it
 is 1 and to itself otherwise.  The result is never 1, and it is ≈ f because
 2 and 1 are both nonzero. 

 --------
 作为函子，这个包含是满的：给定任何 f : nat，当它是 1 时，将其发送到 2，否则发送到自身。结果永远不是 1，并且它与 f ≈ 因为 2 和 1 都是非零的。
*)
Definition pick (f : nat) : nat := if Nat.eqb f 1 then 2%nat else f.

Lemma pick_not_one : forall f, pick f <> 1%nat.
Proof.
  intro f; unfold pick; destruct (Nat.eqb f 1) eqn:E.
  - discriminate.
  - intro Hf; subst f; simpl in E; discriminate.
Qed.

Lemma pick_equiv : forall f, nz (pick f) = nz f.
Proof.
  intro f; unfold pick; destruct (Nat.eqb f 1) eqn:E; auto.
  apply PeanoNat.Nat.eqb_eq in E; subst; reflexivity.
Qed.

Program Definition NotOne_Incl_Full : Functor.Full (Incl NZ NotOne) := {|
  prefmap := fun _ _ g => (pick g; pick_not_one g)
|}.
Next Obligation. intros ?? g; simpl; apply pick_equiv. Qed.

(*
 But the subcategory is NOT Full as data: 1 is a morphism of NZ between
 selected objects that the subcategory does not retain. 

 --------
 但是子类并不是完整的，因为数据：1 是选定对象之间 NZ 的一个态射，而子类不保留它。
*)
Theorem NotOne_not_Full : Subcategory.Full NZ NotOne -> False.
Proof.
  intro HF.
  exact (HF tt tt tt tt 1%nat eq_refl).
Qed.

(*
 Therefore the converse of Full_Implies_Full_Functor is FALSE for a general
 Subcategory record, and ShomRespects (or some equivalent) is genuinely
 required.  Stated as a refutation of the unhypothesised statement: 

 --------
 因此，对于一般的子范畴记录，Full_Implies_Full_Functor 的逆命题是假的，并且确实需要 ShomRespects（或某种等价条件）。用作对未假设陈述的反驳如下：
*)
Theorem converse_without_ShomRespects_is_false :
  (forall (C : Category) (S : Subcategory C),
      Functor.Full (Incl C S) -> Subcategory.Full C S) -> False.
Proof.
  intro Hbad.
  exact (NotOne_not_Full (Hbad NZ NotOne NotOne_Incl_Full)).
Qed.

(* Sanity: the hom-setoid of NZ really is non-degenerate — 0 and 1 are NOT identified — so the counterexample is not the indiscrete cheat. / 理智性：NZ 的同态集合确实是非退化的——0 和 1 并未被认同——所以反例并不是无差别的作弊。 *)
Lemma NZ_setoid_nondegenerate :
  @equiv _ (@homset NZ tt tt) 0%nat 1%nat -> False.
Proof. simpl; discriminate. Qed.

(* And NotOne really fails ShomRespects, as the commit's diagnosis says: 1 ≈ 2 yet 2 is retained and 1 is not. / 而 NotOne 确实让 ShomRespects 失败，正如提交的诊断所说：1 ≈ 2，然而 2 被保留而 1 没有。 *)
Lemma NotOne_not_ShomRespects : ShomRespects NZ NotOne -> False.
Proof.
  intro HR.
  assert (Hne : 2%nat <> 1%nat) by discriminate.
  exact (HR tt tt tt tt 2%nat 1%nat eq_refl Hne eq_refl).
Qed.

