Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.
Require Import Category.Theory.Lawvere.Model.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Lawvere.

Generalizable All Variables.

(**
* Sets-models of a Lawvere theory: the underlying-set functor

    nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
    Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

    A model of a Lawvere theory [T] in [Sets] has an underlying set: the
    value of the model at the generic object [law_of_nat 1].  Evaluation
    at [law_of_nat 1] is a functor [ev1 : Models T Sets ⟶ Sets] — on a
    natural transformation it takes the component at [law_of_nat 1], and
    the functor laws hold componentwise.

    ** Faithfulness and the reachability hypothesis

    Classically [ev1] is faithful: a morphism of models is determined by
    its underlying function, because every object of the theory is a
    finite power of the generic object and models preserve those powers
    ("products separate points").  In this library [LawvereTheory]
    mirrors the relaxed shape of [Construction/PROP.v]'s [PROP] class:
    [law_of_nat] is NOT required to be surjective on objects, so a
    theory may contain an object unreachable from the naturals, and two
    distinct transformations may agree at every [law_of_nat n] while
    differing at the junk object — the bare faithfulness statement does
    not hold at this generality.  Following the SAFT precedent
    (hypothesis-as-data, since the library has no smallness machinery),
    we take reachability as an explicit hypothesis:

        reach : ∀ x : law_cat T, { n : nat & law_of_nat n = x }

    This is the honest reading forced by the PROP-style relaxation, not
    a weakening of the theorem: for skeletal theories — the classical
    notion, where the objects literally are the natural numbers — it is
    satisfied by [eq_refl], as [FinSetOp_reach] below witnesses for the
    base theory [FinSetOp_Lawvere].

--------
* Lawvere 理论的集合模型：基础集合函子

nLab：https://ncatlab.org/nlab/show/Lawvere+theory
维基百科：https://en.wikipedia.org/wiki/Lawvere_theory

在 [Sets] 中，Lawvere 理论 [T] 的一个模型具有一个基础集合：模型在泛对象 [law_of_nat 1] 上的值。在 [law_of_nat 1] 上的求值是一个函子 [ev1 : Models T Sets ⟶ Sets] ——对于自然变换，它取 [law_of_nat 1] 处的分量，并且函子法则在分量上成立。

** 忠实性与可达性假设

传统上，[ev1] 是忠实的：模型的一个态射由其底层函数决定，因为理论的每个对象都是泛对象的有限幂，并且模型保持这些幂（“积区分点”）。在这个库中，[LawvereTheory] 反映了 [Construction/PROP.v] 的 [PROP] 类的放松形式：[law_of_nat] 不要求在对象上是满射，因此一个理论可能包含一个从自然数不可达的对象，并且两个不同的变换可能在每个 [law_of_nat n] 上都一致，而在垃圾对象上不同——单纯的忠实性声明在这种一般情况下不成立。遵循 SAFT 的先例（假设即数据，因为该库没有小性机制），我们将可达性作为一个明确的假设:

reach : ∀ x : law_cat T, { n : nat & law_of_nat n = x }

这是由 PROP 风格松弛强制产生的诚实解读，而不是定理的削弱：对于骨架理论——经典概念，其中对象实际上是自然数——它由 [eq_refl] 满足，正如下面 [FinSetOp_reach] 对基理论 [FinSetOp_Lawvere] 的证明所显示的那样。
*)

(**
** Products separate points

    Two morphisms into a product that agree after both projections are
    equal — immediate from the uniqueness half of [ump_products].  Stated
    for an arbitrary cartesian category; below it is used in [Sets].

--------
** 积的分离点

两个映射到一个积上的态射，如果在两个投影之后结果相同，则它们相等——这是 [ump_products] 的唯一性部分直接得出的。对于任意笛卡尔范畴来说，这是成立的；在下面它被用于 [Sets]。
*)

Lemma prod_separates {C : Category} `{@Cartesian C} {x y z : C}
  (h k : x ~> y × z) :
  exl ∘ h ≈ exl ∘ k → exr ∘ h ≈ exr ∘ k → h ≈ k.
Proof.
  intros Hl Hr.
  rewrite (snd (ump_products (exl ∘ k) (exr ∘ k) h) (Hl, Hr)).
  symmetry.
  apply (snd (ump_products (exl ∘ k) (exr ∘ k) k)).
  split; reflexivity.
Qed.

(** ** The underlying-set functor / ** 基础集合函子 *)

Section Ev1.

Context (T : LawvereTheory).

(**
Evaluation at the generic object [law_of_nat 1]: a model goes to its
    underlying set, a morphism of models (a natural transformation) to
    its component at [law_of_nat 1].  The functor laws are componentwise
    instances of the laws of the functor category.

--------
在通用对象 [law_of_nat 1] 上的评估：一个模型映射到其底层集合，一个模型的态射（一个自然变换）映射到其在 [law_of_nat 1] 处的分量。函子定律是函子范畴定律的分量实例。
*)

Program Definition ev1 : Models T Sets ⟶ Sets := {|
  fobj := fun M => `1 M (law_of_nat 1%nat);
  fmap := fun F G τ => transform (`1 τ) (law_of_nat 1%nat)
|}.
Next Obligation.
  simpl; intros.
  pose proof (@fmap_id _ _ x (law_of_nat 1%nat)) as HH.
  simpl in HH; apply HH.
Qed.

(**
** Faithfulness of the underlying-set functor

    Under the reachability hypothesis, a morphism of [Sets]-models is
    determined by its component at [law_of_nat 1]: the component at
    [law_pow n] is pinned down by induction on [n] — at [0] because maps
    into (an object isomorphic to) the terminal object are equal, at
    [S k] because the target model's product comparison is an iso and
    products separate points — and [law_pow_one] plus [reach] transport
    the agreement to every object.

--------
** 基础集合函子（underlying-set functor）的忠实性

在可达性假设下，[Sets] 模型的一个态射由其在 [law_of_nat 1] 处的分量决定：在 [law_pow n] 处的分量通过对 [n] 的归纳确定——在 [0] 处因为映射到（与终对象同构的对象）是相等的，在 [S k] 处因为目标模型的积比较是同构且积能区分点——并且 [law_pow_one] 加上 [reach] 将一致性传递到每个对象。
*)

Context (reach : ∀ x : @law_cat T, { n : nat & law_of_nat n = x }).

Theorem ev1_Faithful : Faithful ev1.
Proof using T reach.
  construct.
  destruct x as [F [FC FT]], y as [G [GC GT]], f as [τ ?], g as [σ ?].
  simpl in X.
  change (transform τ (law_of_nat 1%nat) ≈ transform σ (law_of_nat 1%nat)) in X.
  assert (HA : ∀ A : @law_cat T, transform τ A ≈ transform σ A).
  { intro A.
    destruct (reach A) as [n e]; destruct e.
    rewrite <- (law_pow_one n).
    induction n as [|k IH].
    - (* n = 0: both components are maps into G 1 ≅ 1, hence equal / n = 0：两个分量都是映射到 G 1 ≅ 1，因此相等 *)
      simpl law_pow.
      pose proof (@one_unique Sets Sets_Terminal _
        (from (@fobj_one_iso _ _ G _ _ GT)
           ∘ transform τ (@terminal_obj _ (@law_terminal T)))
        (from (@fobj_one_iso _ _ G _ _ GT)
           ∘ transform σ (@terminal_obj _ (@law_terminal T)))) as Hone.
      rewrite <- (id_left (transform τ (@terminal_obj _ (@law_terminal T)))).
      rewrite <- (iso_to_from (@fobj_one_iso _ _ G _ _ GT)).
      rewrite <- comp_assoc.
      rewrite Hone.
      rewrite comp_assoc.
      rewrite (iso_to_from (@fobj_one_iso _ _ G _ _ GT)).
      exact (id_left (transform σ (@terminal_obj _ (@law_terminal T)))).
    - (* n = S k: compare through the product iso G (1 × pow k) ≅ G 1 × G (pow k) / n = S k：通过积 iso G (1 × pow k) ≅ G 1 × G (pow k) 进行比较 *)
      simpl law_pow.
      rewrite <- (id_left (transform τ
        (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k)))).
      rewrite <- (@prod_in_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
      rewrite <- comp_assoc.
      assert (Hout :
        @prod_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)
          ∘ transform τ
              (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))
        ≈[Sets] @prod_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)
          ∘ transform σ
              (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
      { apply prod_separates.
        - rewrite !comp_assoc.
          rewrite <- (@fmap_exl _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
          rewrite (naturality τ _ _
            (@exl _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          rewrite (naturality σ _ _
            (@exl _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          now rewrite X.
        - rewrite !comp_assoc.
          rewrite <- (@fmap_exr _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
          rewrite (naturality τ _ _
            (@exr _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          rewrite (naturality σ _ _
            (@exr _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k))).
          now rewrite IH. }
      rewrite Hout.
      rewrite comp_assoc.
      rewrite (@prod_in_out _ _ G _ _ GC (law_of_nat 1%nat) (law_pow k)).
      exact (id_left (transform σ
        (@product_obj _ (@law_cartesian T) (law_of_nat 1%nat) (law_pow k)))). }
  simpl in HA; apply HA.
Qed.

End Ev1.

(**
** Reachability for the base theory

    For the skeletal base theory [FinSetOp_Lawvere] the objects of the
    underlying category literally are the natural numbers and
    [law_of_nat] is the identity, so reachability holds by [eq_refl] —
    the hypothesis of [ev1_Faithful] costs nothing on the classical
    notion of Lawvere theory.

--------
** 基础理论的可达性

对于骨干基础理论 [FinSetOp_Lawvere]，底层范畴的对象实际上是自然数，并且 [law_of_nat] 是恒等式，因此通过 [eq_refl] 可得可达性——[ev1_Faithful] 的假设在经典的 Lawvere 理论概念上是不费力的。
*)

Definition FinSetOp_reach :
  ∀ x : @law_cat FinSetOp_Lawvere, { n : nat & law_of_nat n = x } :=
  fun x => (x; eq_refl).
