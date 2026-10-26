(* * * No natural isomorphism G ≅ D(G): Mac Lane's remark / * * 没有自然同构 G ≅ D(G)：Mac Lane 的评论 *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Character.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §I.4, printed p. 17 (PDF 27) — maclane:I.4:remark1
 nLab:      https://ncatlab.org/nlab/show/natural+isomorphism

 Mac Lane's remark: although each finite abelian group is isomorphic
 to its own character group, no such family of isomorphisms is
 natural — in the only sense in which the question is well posed,
 naturality over the ISO-ONLY category, where the character functor
 becomes covariant by D' f := D (f⁻¹).  This file makes the negative
 half precise and proves it by one concrete violation.

 - [AbIso]: the groupoid core of Ab (Construction/Groupoid.v's
 [Groupoid], cited not rebuilt)
 - [D']: the covariant character functor on the core,
 D' f := D (f⁻¹)
 - [Z5]: ℤ/5 as an [AbObject] (carrier ℤ, identified modulo 5 —
 the same setoid-as-quotient discipline as [QZ])
 - [alpha]: the automorphism x ↦ 2·x of ℤ/5, with inverse
 x ↦ 3·x
 - [sigma_not_natural]: no isomorphism ℤ/5 ≅ D(ℤ/5) satisfies
 even the single naturality square at [alpha] (strong form;
 [sigma_family_not_natural] instantiates it for families, and
 [no_such_sigma_family] shows the family premise is itself
 uninhabited — ℤ has no nonzero 2-torsion while D(ℤ) does)

 Design:

 1. ONE AUTOMORPHISM SUFFICES.  The issue allows “a concrete
 two-object violation”; the violation here is at the two equal
 endpoints of one automorphism, which is stronger and simpler.
 The arithmetic: naturality of σ at α : x ↦ 2x demands
 σ ∘ α ≈ D(α⁻¹) ∘ σ.  Writing q := σ(1)(1) ∈ ℚ/ℤ, the left side
 evaluates σ(2)(1) = 2q by additivity of σ, and the right
 evaluates σ(1)(3) = 3q by additivity of characters (α⁻¹ is
 x ↦ 3x, since 2·3 = 6 ≡ 1 mod 5).  So 2q ≈ 3q in ℚ/ℤ, hence
 q ≈ 0, hence σ(1) is the zero character; but then
 σ(1) ≈ σ(0) while 1 ≉ 0 in ℤ/5, so σ is not injective —
 contradicting that it is an isomorphism.  This is Mac Lane's
 m² ≡ 1 obstruction in its smallest working clothes: for ℤ/p
 the argument needs an automorphism m with m ≢ m⁻¹, so p = 5
 with m = 2 is the first prime that works (p = 2, 3 have only
 m ≡ ±1, and every additive map already commutes with those).

 2. WHY THE STATEMENT LIVES AT ℤ/5 ALONE.  [sigma_not_natural]
 takes ONE isomorphism ℤ/5 ≅ D(ℤ/5) and the single square at
 [alpha] — not full naturality over [AbIso] (refuting the
 weaker hypothesis is the stronger theorem), and not a family
 over all of Ab (a family premise would make the statement
 vacuous: [no_such_sigma_family] below proves no such family
 exists at all, ℤ against D(ℤ) — an audit catch).  [D'] is
 nonetheless constructed in full, so the covariant reading the
 book names is in the tree, and the square hypothesis is
 literally the to-component of [D']-naturality at [alpha]. 

 --------
 书籍：麦克莱恩，《为工作的数学家准备的范畴论》，第2版，
 §I.4，印刷版第17页（PDF第27页） — maclane:I.4:remark1
 nLab：https://ncatlab.org/nlab/show/natural+isomorphism

 麦克莱恩的备注：虽然每个有限阿贝尔群都同构于它自身的特征群，但没有这样的同构族是自然的——在唯一合适地提出这个问题的意义下，即在仅限同构的范畴上自然性，其中特征函子通过 D' f := D(f⁻¹) 变为协变函子。该文件精确定义了否定的一半，并通过一个具体的违反例子证明了它。-  [AbIso]：Ab 的群族核心（Construction/Groupoid.v 中的 [Groupoid]，已引用未重新构建）
 -  [D']：核心上的共变特征函子，D' f := D (f⁻¹)
 -  [Z5]：ℤ/5 作为一个 [AbObject]（载体 ℤ，模 5 识别——与 [QZ] 相同的同伴集-商纪律）
 -  [alpha]：ℤ/5 的自同构 x ↦ 2·x，其逆为 x ↦ 3·x
 -  [sigma_not_natural]：没有任何同构 ℤ/5 ≅ D(ℤ/5) 即使在 [alpha] 的单个自然性图上也满足（强形式；[sigma_family_not_natural] 对族进行了实例化，[no_such_sigma_family] 证明族前提本身是空的——ℤ 没有非零 2-幂元素，而 D(ℤ) 有）

 设计：1. 一个自同构就足够了。这个问题允许“一个具体的两个对象的违例”；这里的违例出现在一个自同构的两个相等端点，更强且更简单。算术：σ 在 α : x ↦ 2x 的自然而然性要求 σ ∘ α ≈ D(α⁻¹) ∘ σ。设 q := σ(1)(1) ∈ ℚ/ℤ，左边通过 σ 的可加性求值得 σ(2)(1) = 2q，右边通过特征的可加性求值得 σ(1)(3) = 3q（α⁻¹ 是 x ↦ 3x，因为 2·3 = 6 ≡ 1 mod 5）。所以在 ℚ/ℤ 中有 2q ≈ 3q，从而 q ≈ 0，因此 σ(1) 是零特征；但此时 σ(1) ≈ σ(0)，而 1 ≉ 0 在 ℤ/5 中，所以 σ 不是单射——与它是同构矛盾。这是 Mac Lane 的 m² ≡ 1 障碍在其最小工作形式下：对于 ℤ/p，这个论证需要一个满足 m ≢ m⁻¹ 的自同构，因此 p = 5 且 m = 2 是第一个可行的素数（p = 2, 3 仅有 m ≡ ±1，并且每个加法映射已经与这些自同构交换）。2. 为什么该命题只在 ℤ/5 上成立。[sigma_not_natural] 采用了一个同构 ℤ/5 ≅ D(ℤ/5) 以及 [alpha] 处的单个方形——而不是 [AbIso] 上的完全自然性（反驳较弱假设即是较强定理），也不是关于整个 Ab 的族（族前提会使该命题变得空洞：下文 [no_such_sigma_family] 证明这种族根本不存在，ℤ 与 D(ℤ) 相对——这是审计发现）。尽管如此，[D'] 仍然被完整构建，因此书中所称的协变解读在树中存在，并且方形假设字面上是 [D'] 在 [alpha] 处自然性的目标分量。
*)

(* * ** The groupoid core and the covariant character functor / * ** 群幺核与协变特征函子 *)

Definition AbIso : Category := Groupoid Ab.

(*
 D' f := D (f⁻¹): contravariance twisted through inversion makes the
 character functor covariant on the core. 

 --------
 D' f := D (f⁻¹)：通过取逆转扭曲的逆变性使得特征函子在核心上成为协变的。
*)
Program Definition D' : AbIso ⟶ AbIso := {|
  fobj := fun G => D_ob G;
  fmap := fun G H (f : @Isomorphism Ab G H) =>
    {| to   := fmap[D] (from f)
     ; from := fmap[D] (to f) |}
|}.
Next Obligation.
  intros G H f χ a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (iso_to_from f a).
Qed.
Next Obligation.
  intros G H f χ a; simpl.
  apply (proper_morphism (cmon_map χ)).
  exact (iso_from_to f a).
Qed.
Next Obligation.
  intros G H f g Hfg; split.
  - intros χ a; simpl.
    apply (proper_morphism (cmon_map χ)).
    exact (snd Hfg a).
  - intros χ a; simpl.
    apply (proper_morphism (cmon_map χ)).
    exact (fst Hfg a).
Qed.
Next Obligation.
  intros G; split; intros χ a; simpl; apply qz_eq_refl.
Qed.
Next Obligation.
  intros G H K f g; split; intros χ a; simpl; apply qz_eq_refl.
Qed.

(** ** ℤ/5 *)

Definition z5_eq (x y : Z) : Type := { k : Z & (x - y = 5 * k)%Z }.

(*
 [z5_eq] KEEPS its [sigT] -- the witness [k] is computed, and the results
 below read it back out.  The [Prop] mirror it needs since the PR
 “algebraic carriers are sets” (2026-09-17) recovers the witness through a
 DECISION PROCEDURE rather than through the [Prop] proof: divisibility by 5
 is decidable on ℤ, so the left branch supplies the witness outright and the
 right branch contradicts the hypothesis.  No choice principle. 

 --------
 [z5_eq] 保持其 [sigT] —— 见证 [k] 被计算出来，下面的结果会将其读出。PR 所需的 [Prop] 镜像由于“代数载体是集合”（2026-09-17）通过决策程序而不是通过 [Prop] 证明恢复了见证：在 ℤ 上可以判定是否能被 5 整除，因此左分支直接提供见证，而右分支则与假设矛盾。没有选择原理。
*)
Definition z5_peq (x y : Z) : Prop :=
  (exists k : Z, Z.eq (Z.sub x y) (Z.mul 5 k))%type.

Lemma z5_eq_dec (x y : Z) : z5_eq x y + (z5_eq x y → False).
Proof.
  destruct (Z.eq_dec (Z.rem (x - y) 5) 0) as [He|He].
  - left.
    exists (Z.quot (x - y) 5).
    pose proof (Z.quot_rem' (x - y) 5) as Hq.
    lia.
  - right.
    intros [k Hk].
    apply He.
    rewrite Hk, Z.mul_comm.
    apply Z.rem_mul; lia.
Qed.

Lemma z5_eq_refl (x : Z) : z5_eq x x.
Proof. exists 0%Z; lia. Qed.

Lemma z5_eq_sym (x y : Z) : z5_eq x y → z5_eq y x.
Proof. intros [k Hk]; exists (- k)%Z; lia. Qed.

Lemma z5_eq_trans (x y w : Z) : z5_eq x y → z5_eq y w → z5_eq x w.
Proof. intros [k1 H1] [k2 H2]; exists (k1 + k2)%Z; lia. Qed.

(*
 The setoid is NAMED so that [z5_PropEquiv] below can mention it; a field
 of a [Program] record literal cannot refer to a setoid that is still an
 evar while the literal is being elaborated. 

 --------
 集合体被命名，以便下面的 [z5_PropEquiv] 可以提到它；在字面展开期间，[Program] 记录字面量的字段不能引用仍然是 evar 的集合体。
*)
Program Definition z5_setoid : Setoid Z := {| equiv := z5_eq |}.
Next Obligation.
  constructor.
  - exact z5_eq_refl.
  - exact z5_eq_sym.
  - exact z5_eq_trans.
Qed.

Definition z5_PropEquiv : PropEquiv z5_setoid.
Proof.
  unshelve refine (@PropEquiv_of_relation _ z5_setoid z5_peq _ _).
  - intros x y H.
    destruct (z5_eq_dec x y) as [Hd|Hd].
    + exact Hd.
    + exfalso.
      destruct H as [k Hk].
      exact (Hd (existT _ k Hk)).
  - intros x y H.
    destruct H as [k Hk].
    exists k.
    exact Hk.
Defined.

Program Definition Z5 : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := Z;
                      is_setoid := z5_setoid |};
    cmon_zero := 0%Z;
    cmon_plus := Z.add;
    cmon_prop := z5_PropEquiv
  |};
  ab_neg := Z.opp
|}.
Next Obligation.
  intros x x' [k1 H1] y y' [k2 H2].
  exists (k1 + k2)%Z; lia.
Qed.
Next Obligation.
  intros a b c; exists 0%Z; lia.
Qed.
Next Obligation.
  intros a b; exists 0%Z; lia.
Qed.
Next Obligation.
  intro a; exists 0%Z; lia.
Qed.
Next Obligation.
  intros x y [k Hk]; exists (- k)%Z; lia.
Qed.
Next Obligation.
  intro a; exists 0%Z; cbn; lia.
Qed.

(* 1 and 0 are distinct in ℤ/5. / 1 和 0 在 ℤ/5 中是不同的。 *)
Lemma z5_one_neq_zero : z5_eq 1 0 → False.
Proof. intros [k Hk]; lia. Qed.

(* * ** The automorphism x ↦ 2x and the generator character / * ** 自同构 x ↦ 2x 和生成元特征 *)

Program Definition z5_mul (m : Z) : Z5 ~{Ab}~> Z5 := {|
  cmon_map := {| morphism := fun x => (m * x)%Z |}
|}.
Next Obligation.
  intros m x y [k Hk]; exists (m * k)%Z; nia.
Qed.
Next Obligation.
  intro m; exists 0%Z; cbn; lia.
Qed.
Next Obligation.
  intros m a b; exists 0%Z; cbn; lia.
Qed.

(* x ↦ 2x is an isomorphism, with inverse x ↦ 3x (2·3 = 6 ≡ 1). / x ↦ 2x 是一个同构，其逆映射为 x ↦ 3x（2·3 = 6 ≡ 1）。 *)
Program Definition alpha : @Isomorphism Ab Z5 Z5 := {|
  to   := z5_mul 2;
  from := z5_mul 3
|}.
Next Obligation.
  intro x; exists x.
  change ((2 * (3 * x) - x)%Z = (5 * x)%Z).
  lia.
Qed.
Next Obligation.
  intro x; exists x.
  change ((3 * (2 * x) - x)%Z = (5 * x)%Z).
  lia.
Qed.

(* The generator character of ℤ/5: x ↦ x/5 in ℚ/ℤ. / ℤ/5 的生成元：x ↦ x/5 在 ℚ/ℤ 中。 *)
Program Definition chi1 : AbHom Z5 QZ := {|
  cmon_map := {| morphism := fun x : Z => (inject_Z x / 5)%Q |}
|}.
Next Obligation.
  intros x y [k Hk].
  exists k.
  assert (Hx : x = (y + 5 * k)%Z) by lia.
  subst x.
  rewrite inject_Z_plus.
  rewrite inject_Z_mult.
  field.
Qed.
Next Obligation.
  apply qz_of_Qeq; cbn; field.
Qed.
Next Obligation.
  intros a b.
  apply qz_of_Qeq; cbn.
  rewrite inject_Z_plus.
  field.
Qed.

(** ** The violation / ** 违规 *)

(* The arithmetic heart: 2q ≈ 3q in ℚ/ℤ forces q ≈ 0 (subtract). / 算术核心：2q ≈ 3q 在 ℚ/ℤ 中强制 q ≈ 0（相减）。 *)
Lemma qz_two_three_zero (q : Q) :
  qz_eq (q + q) (q + (q + q)) → qz_eq q 0.
Proof.
  intros [z Hz].
  exists (- z)%Z.
  rewrite inject_Z_opp.
  rewrite <- Hz; ring.
Qed.

Section Violation.

Context (s0 : @Isomorphism Ab Z5 (D_ob Z5)).
Context (Hnat : ∀ x : Z,
  cmon_map (to s0) ((2 * x)%Z)
    ≈ char_precomp (z5_mul 3) (cmon_map (to s0) x)).

Set Default Proof Using "All".

Let s : Z5 ~{Ab}~> D_ob Z5 := to s0.
Let q : Q := cmon_map (cmon_map s 1%Z) 1%Z.

(* Doubling on the argument side: σ(2)(1) ≈ q + q. / 在论证方加倍：σ(2)(1) ≈ q + q。 *)
Lemma sigma_two : cmon_map (cmon_map s 2%Z) 1%Z ≈ (q + q)%Q.
Proof.
  exact (cmon_map_plus s 1%Z 1%Z 1%Z).
Qed.

(* Tripling on the value side: σ(1)(3) ≈ q + (q + q). / 在价值方面三倍增长：σ(1)(3) ≈ q + (q + q)。 *)
Lemma sigma_three : cmon_map (cmon_map s 1%Z) 3%Z ≈ (q + (q + q))%Q.
Proof.
  eapply qz_eq_trans.
  - exact (cmon_map_plus (cmon_map s 1%Z) 1%Z 2%Z).
  - apply QZ.(ab_cmon).(cmon_plus_respects); [ apply qz_eq_refl | ].
    exact (cmon_map_plus (cmon_map s 1%Z) 1%Z 1%Z).
Qed.

(* The square at x := 1, evaluated at the group element 1, plus additivity on both sides: 2q ≈ 3q, so q ≈ 0. / 在 x := 1 时的平方，在群元素 1 处计算，再加上双方的加法性：2q ≈ 3q，所以 q ≈ 0。 *)
Lemma q_zero : qz_eq q 0.
Proof.
  apply qz_two_three_zero.
  eapply qz_eq_trans; [ apply qz_eq_sym, sigma_two | ].
  eapply qz_eq_trans; [ exact (Hnat 1%Z 1%Z) | ].
  exact sigma_three.
Qed.

(*
 Multiples of a vanishing value vanish: σ(1)(n) ≈ 0 for the five
 residues, hence — through the mod-5 setoid — for every argument. 

 --------
 消失值的倍数也会消失：σ(1)(n) 对这五个余数近似为 0，因此——通过模 5 集合——对每个参数都是如此。
*)
Lemma sigma_one_zero : ∀ x : Z, qz_eq (cmon_map (cmon_map s 1%Z) x) 0.
Proof.
  assert (Hstep : ∀ n : Z,
    qz_eq (cmon_map (cmon_map s 1%Z) n) 0 →
    qz_eq (cmon_map (cmon_map s 1%Z) (1 + n)%Z) 0).
  { intros n Hn.
    eapply qz_eq_trans.
    - exact (cmon_map_plus (cmon_map s 1%Z) 1%Z n).
    - eapply qz_eq_trans.
      + apply QZ.(ab_cmon).(cmon_plus_respects); [ exact q_zero | exact Hn ].
      + apply qz_of_Qeq; cbn; ring.
  }
  assert (H0 : qz_eq (cmon_map (cmon_map s 1%Z) 0%Z) 0)
    by exact (cmon_map_zero (cmon_map s 1%Z)).
  pose proof (Hstep _ H0) as H1.
  pose proof (Hstep _ H1) as H2.
  pose proof (Hstep _ H2) as H3.
  pose proof (Hstep _ H3) as H4.
  intro x.
  (* x is congruent mod 5 to its remainder r ∈ {0,1,2,3,4} / x 在模 5 下同余于它的余数 r ∈ {0,1,2,3,4} *)
  pose proof (Z.mod_pos_bound x 5 ltac:(lia)) as Hb.
  assert (Hx : z5_eq x (x mod 5)).
  { exists (x / 5)%Z.
    pose proof (Z.div_mod x 5 ltac:(lia)); lia. }
  eapply qz_eq_trans.
  - apply (proper_morphism (cmon_map (cmon_map s 1%Z))), Hx.
  - destruct (Z.eq_dec (x mod 5) 0) as [E|n0]; [ rewrite E; exact H0 |].
    destruct (Z.eq_dec (x mod 5) 1) as [E|n1]; [ rewrite E; exact H1 |].
    destruct (Z.eq_dec (x mod 5) (1 + 1)) as [E|n2]; [ rewrite E; exact H2 |].
    destruct (Z.eq_dec (x mod 5) (1 + (1 + 1))) as [E|n3];
      [ rewrite E; exact H3 |].
    assert (E : (x mod 5 = 1 + (1 + (1 + 1)))%Z) by lia.
    rewrite E; exact H4.
Qed.

(*
 σ identifies 1 and 0, so — being an isomorphism — 1 ≈ 0 in ℤ/5:
 contradiction. 

 --------
 σ 识别 1 和 0，所以——作为同构——1 ≈ 0 在 ℤ/5 中：矛盾。
*)
Theorem sigma_square_violation : False.
Proof.
  apply z5_one_neq_zero.
  (* 1 ≈ from(σ)(σ(1)) ≈ from(σ)(σ(0)) ≈ 0 / 1 ≈ from(σ)(σ(1)) ≈ from(σ)(σ(0)) ≈ 0 *)
  pose proof (iso_from_to s0) as Hfi.
  eapply z5_eq_trans; [ apply z5_eq_sym, (Hfi 1%Z) | ].
  eapply z5_eq_trans; [ | apply (Hfi 0%Z) ].
  apply (proper_morphism (cmon_map (from s0))).
  intro x.
  eapply qz_eq_trans; [ apply (sigma_one_zero x) | ].
  apply qz_eq_sym.
  exact ((cmon_map_zero s) x).
Qed.

End Violation.

(*
 The packaged negative half, in its STRONG form: no isomorphism
 ℤ/5 ≅ D(ℤ/5) satisfies even the single naturality square at the
 automorphism x ↦ 2x — a fortiori, no natural family over the
 iso-only category [AbIso] with respect to [D'] exists. 

 --------
 打包的负半部分，其强形式：没有同构 ℤ/5 ≅ D(ℤ/5) 甚至在自同构 x ↦ 2x 的单个自然性方格下也不成立——更进一步地说，不存在关于 [D'] 的仅同构类别 [AbIso] 的自然族。
*)
Theorem sigma_not_natural (s0 : @Isomorphism Ab Z5 (D_ob Z5)) :
  (∀ x : Z,
     cmon_map (to s0) ((2 * x)%Z)
       ≈ char_precomp (z5_mul 3) (cmon_map (to s0) x)) →
  False.
Proof.
  intros Hnat.
  exact (sigma_square_violation s0 Hnat).
Qed.

(*
 The family form, for the record: any family σ_G : G ≅ D(G) over
 all abelian groups instantiates at ℤ/5.  This corollary's premise
 is in fact ITSELF uninhabited ([no_such_sigma_family] below), which
 is why the single-object statement above is the headline: it is the
 one with applicable content. 

 --------
 家族形式，供记录：任何家族 σ_G : G ≅ D(G) 在所有阿贝尔群上的情况都在 ℤ/5 上实例化。这个推论的前提事实上本身就是空的（下面的 [no_such_sigma_family]），这就是为什么上面的单对象陈述成为标题：它是唯一具有适用内容的陈述。
*)
Corollary sigma_family_not_natural
          (σ : ∀ G : AbObject, @Isomorphism Ab G (D_ob G)) :
  (∀ x : Z,
     cmon_map (to (σ Z5)) ((2 * x)%Z)
       ≈ char_precomp (z5_mul 3) (cmon_map (to (σ Z5)) x)) →
  False.
Proof.
  intros Hnat.
  exact (sigma_not_natural (σ Z5) Hnat).
Qed.

(* * ** Not even the objects match up globally / * ** 甚至对象在全球范围内都不匹配 *)

(*
 Away from finite groups the single-dual identification is already impossible
 already at the level of bare isomorphism: ℤ has no nonzero
 2-torsion, while D(ℤ) does — the half-character n ↦ n/2.  So a
 family σ_G : G ≅ D(G) over ALL abelian groups does not exist,
 independently of any naturality demand. 

 --------
 远离有限群时，单重对偶的识别在裸同构的层面上已经不可能：ℤ 没有非零的 2-挠性，而 D(ℤ) 有 —— 半特征 n ↦ n/2。因此，存在覆盖所有阿贝尔群的族 σ_G : G ≅ D(G) 是不可能的，这与任何自然性要求无关。
*)

Definition ZZ : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := {| cmon_setoid := {| carrier := Z;
                                    is_setoid := eq_Setoid Z |};
                  cmon_zero := 0%Z;
                  cmon_plus := Z.add;
                  (* ℤ's `≈` here IS Coq's [eq], already a [Prop]. / ℤ 的 `≈` 这里是 Coq 的 [eq]，已经是一个 [Prop]。 *)
                  cmon_prop := eq_PropEquiv Z |};
    ab_neg := Z.opp |}.
  - intros x x' Hx y y' Hy.
    assert (Hx' : x = x') by exact Hx.
    assert (Hy' : y = y') by exact Hy.
    rewrite Hx', Hy'; reflexivity.
  - intros x y z; simpl; lia.
  - intros x y; simpl; lia.
  - intros x; simpl; lia.
  - intros x y Hxy.
    assert (Hxy2 : x = y) by exact Hxy.
    rewrite Hxy2; reflexivity.
  - intros x; simpl; lia.
Defined.

(* The half-character n ↦ n/2 of ℤ. / 整数集 ℤ 的半字符映射 n ↦ n/2。 *)
Definition chi_half : AbHom ZZ QZ.
Proof.
  unshelve notypeclasses refine
    (@Build_CMonHom ZZ QZ
       (@Build_SetoidMorphism
          (carrier (cmon_setoid ZZ)) _ (carrier (cmon_setoid QZ)) _
          (fun n : Z => (inject_Z n / 2)%Q) _) _ _).
  - intros x y Hxy.
    assert (Hxy' : x = y) by exact Hxy.
    rewrite Hxy'; apply qz_eq_refl.
  - apply qz_of_Qeq; reflexivity.
  - intros x y; apply qz_of_Qeq; simpl.
    rewrite inject_Z_plus; field.
Defined.

(* It is 2-torsion in D(ℤ)… / 它在 D(ℤ) 中是 2-挠性… *)
Lemma chi_half_double_zero :
  cmon_plus (D_ob ZZ) chi_half chi_half ≈ cmon_zero (D_ob ZZ).
Proof.
  intro n; simpl.
  apply (fun H => qz_eq_trans _ _ _ H (qz_eq_refl 0)).
  exists n; field.
Qed.

(* …but not itself zero… / ……但本身不为零…… *)
Lemma chi_half_nonzero : (chi_half ≈ cmon_zero (D_ob ZZ)) → False.
Proof.
  intro H; destruct (H 1%Z) as [z Hz].
  unfold Qeq in Hz; simpl in Hz; lia.
Qed.

(* …while ℤ itself has no nonzero 2-torsion. / …而 ℤ 本身没有非零的 2-挠元素。 *)
Lemma ZZ_no_2_torsion (m : carrier (cmon_setoid ZZ)) :
  cmon_plus ZZ m m ≈ cmon_zero ZZ → m ≈ cmon_zero ZZ.
Proof.
  intro H.
  change ((m + m)%Z = 0%Z) in H.
  change (m = 0%Z).
  lia.
Qed.

(*
 Hence no family of isomorphisms σ_G : G ≅ D(G) exists over all of
 Ab — the family corollary's premise is uninhabited, which is
 exactly why [sigma_not_natural] is stated at ℤ/5. 

 --------
 因此，不存在一个在整个 Ab 上的同构族 σ_G : G ≅ D(G) —— 这个族的推论前提是空的，这正是为什么 [sigma_not_natural] 在 ℤ/5 上被陈述的原因。
*)
Theorem no_such_sigma_family :
  (∀ G : AbObject, @Isomorphism Ab G (D_ob G)) → False.
Proof.
  intro sigma.
  pose (f := to (sigma ZZ)).
  pose (g := from (sigma ZZ)).
  pose (m := cmon_map g chi_half).
  assert (Hfm : cmon_map f m ≈ chi_half)
    by exact (iso_to_from (sigma ZZ) chi_half).
  assert (Hd : cmon_map f (cmon_plus ZZ m m) ≈ cmon_zero (D_ob ZZ)).
  { transitivity (cmon_plus (D_ob ZZ) (cmon_map f m) (cmon_map f m)).
    - exact (cmon_map_plus f m m).
    - transitivity (cmon_plus (D_ob ZZ) chi_half chi_half).
      + exact (cmon_plus_respects (D_ob ZZ) _ _ Hfm _ _ Hfm).
      + exact chi_half_double_zero. }
  assert (Hm0 : m ≈ cmon_zero ZZ).
  { apply ZZ_no_2_torsion.
    transitivity (cmon_map g (cmon_map f (cmon_plus ZZ m m))).
    - symmetry; exact (iso_from_to (sigma ZZ) (cmon_plus ZZ m m)).
    - transitivity (cmon_map g (cmon_zero (D_ob ZZ))).
      + apply (proper_morphism (cmon_map g)); exact Hd.
      + exact (cmon_map_zero g). }
  apply chi_half_nonzero.
  transitivity (cmon_map f m).
  - symmetry; exact Hfm.
  - transitivity (cmon_map f (cmon_zero ZZ)).
    + apply (proper_morphism (cmon_map f)); exact Hm0.
    + exact (cmon_map_zero f).
Qed.
