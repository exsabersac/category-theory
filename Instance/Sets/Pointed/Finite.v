Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pointed.

Generalizable All Variables.

(* * * Finite pointed sets: the unconditional witness / * * 有限有向集合：无条件的见证 *)

(*
 nLab:      https://ncatlab.org/nlab/show/decidable+equality
 nLab:      https://ncatlab.org/nlab/show/finite+set
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer 1998, §I.7 (printed p. 26)

 Instance/Sets/Pointed.v proves two halves of Mac Lane's proposition over
 explicit hypotheses — decidable image membership for the splitting of a
 monic, an enumerated domain plus a decidable codomain for the splitting of
 an epic — because without them the statements are not constructively
 available ("every epimorphism splits" being the axiom of choice).  This
 file discharges all of them at once, for the class where they are free:
 finite pointed sets with decidable equality.

 [pointed_image_dec] is the general bridge — an enumerated domain and a
 decidable codomain make image membership decidable, by running the
 first-preimage search and reading off the answer — after which
 [finite_monic_split] and [finite_epic_split] state the two halves with no
 hypotheses beyond finiteness.  [pointed_balanced] needed none to begin
 with.

 The witnesses are the two-element pointed set [PointedBool] ([bool] pointed
 at [false]) and the three-element [PointedThree] ([option bool] pointed at
 [None]), both under Leibniz equality.  THE TWO SPLITTINGS COMPUTE: the
 retraction of a concrete monic and the section of a concrete epic are
 evaluated at each point by [reflexivity], which is why the two splitting
 theorems of Instance/Sets/Pointed.v end in [Defined].  That claim is
 scoped deliberately, and an audit of the first commit was right to
 insist on the scope: the inverse produced by [pointed_balanced] does NOT
 reduce, because that theorem ends in [Qed] and is opaque, so the closing
 section's [pointed_swap_inverse_at_true] is proved by an algebraic
 argument rather than by computation.  The section is the
 more instructive of the two, since it exhibits both branches of the
 construction: the basepoint is sent to the basepoint by fiat, and [true] to
 the FIRST element of the enumeration lying over it.

 Non-vacuity is settled here as well: [bool_to_three] is monic and not epic,
 [three_to_bool] is epic and not monic, so neither implication of
 [pointed_balanced] is trivial, and the basepoint-fixing [pointed_swap] of
 [PointedThree] is invertible purely by being both — no inverse was
 supplied to the theorem. 

 --------
 nLab：       https://ncatlab.org/nlab/show/decidable+equality
 nLab：       https://ncatlab.org/nlab/show/finite+set
 书籍：      Mac Lane，《为工作中的数学家准备的范畴论》，第二版，
 Springer 1998，第I.7节（印刷页26）

 Instance/Sets/Pointed.v 在明确假设下证明了 Mac Lane 命题的两半——单射的分解需要可判定的像成员资格，满射的分解需要枚举的定义域加上可判定的值域——因为没有这些，陈述在构造上是不可用的（“每个满射都可分解”是选择公理）。这个文件一次性解决了它们全部，对于这些假设为自由的类：具有可判定相等性的有限指点集合。[pointed_image_dec] 是一般桥——一个可枚举的定义域和一个可判定的值域使得图像成员资格可判定，通过运行第一次原像搜索并读取答案——之后 [finite_monic_split] 和 [finite_epic_split] 陈述了两半部分，没有超出有限性的假设。[pointed_balanced] 从一开始就不需要任何假设。见证者是两个元素的指向集合 [PointedBool]（指向 [false] 的 [bool]）和三个元素的 [PointedThree]（指向 [None] 的 [option bool]），两者都在莱布尼茨等式下。两个拆分计算：一个具体单射的收缩和一个具体满射的截面在每个点上由 [reflexivity] 评估，这就是为什么 Instance/Sets/Pointed.v 的两个拆分定理都以 [Defined] 结束。该声明是有意限定作用域的，并且对第一个提交的审计坚持作用域是正确的：由 [pointed_balanced] 生成的逆不化简，因为该定理以 [Qed] 结束且是不可简的，因此闭合截面的 [pointed_swap_inverse_at_true] 是通过代数论证而非计算证明的。该节是两个中更具指导性的，因为它展示了构造的两个分支：基点通过规定映射到基点，而 [true] 映射到枚举中位于其上的第一个元素。

 非空性在这里也得以确定：[bool_to_three] 是单态而非满态，[three_to_bool] 是满态而非单态，因此 [pointed_balanced] 的任意一个蕴含都不是平凡的，而通过固定基点的 [pointed_swap] 对 [PointedThree] 的同构性纯粹是由于同时具备单态和满态——定理并没有提供逆映射。
*)

(** ** Discharging the hypotheses / ** 排除假设 *)

(*
 Transporting between `≈` at a discrete setoid and Coq's `=`.  Both
 directions are the identity function — [eq_Setoid]'s `≈` IS `=` — but
 naming them lets [discriminate] and [f_equal] be used directly. 

 --------
 在离散的集合论集合 `≈` 与 Coq 的 `=` 之间进行传输。两个方向都是恒等函数——[eq_Setoid] 的 `≈` 是 `=`——但为它们命名可以直接使用 [discriminate] 和 [f_equal]。
*)
Definition eq_of_equiv {A : Type} {x y : A}
  (H : @equiv A (eq_Setoid A) x y) : x = y := H.

Definition equiv_of_eq {A : Type} {x y : A}
  (H : x = y) : @equiv A (eq_Setoid A) x y := H.

(*
 From an enumerated domain and a decidable codomain, image membership is
 decidable: run the search, and read the answer off it.  This is the
 hypothesis of [pointed_monic_split], discharged. 

 --------
 从一个可列举的域和一个可判定的陪域，像的归属是可判定的：运行搜索，并从中读取答案。这是 [pointed_monic_split] 的假设，已解除。
*)
Definition pointed_image_dec {X Y : PointedSetoid} (f : PointedMorphism X Y)
  (deq : DecidableEquiv Y) (E : PointedEnumeration X) : ImageDecidable f.
Proof.
  intro b.
  destruct (pointed_search f deq (enum_list E) b) as [a|] eqn:Hs.
  - left.
    exists a.
    exact (pointed_search_correct f deq (enum_list E) b a Hs).
  - right.
    intros [a Ha].
    exact (pointed_search_complete f deq (enum_list E) b a
             (enum_covers E a) Ha Hs).
Defined.

(* Decidability of the basepoint is a special case of decidability of `≈`. / 基点的可判定性是 `≈` 可判定性的一个特例。 *)
Definition DecidablePt_of_DecidableEquiv {Z : PointedSetoid}
  (deq : DecidableEquiv Z) : DecidablePt Z := fun z => deq z (pt Z).

(*
 Between finite pointed sets the two splitting halves of Mac Lane's
 proposition hold with no further hypotheses. 

 --------
 在有限有基点集合之间，Mac Lane 命题的两个分拆部分在没有进一步假设的情况下成立。
*)
Definition finite_monic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (E : PointedEnumeration X) (deq : DecidableEquiv Y) : Monic f → Section f :=
  fun Hm => pointed_monic_split f (pointed_image_dec f deq E) Hm.

Definition finite_epic_split {X Y : PointedSetoid} (f : X ~{PointedSets}~> Y)
  (E : PointedEnumeration X) (deq : DecidableEquiv Y) : Epic f → Retraction f :=
  fun He => pointed_epic_split f deq E He.

(* * *** Two concrete finite pointed sets / * *** 两个具体的有限有向集合 *)

(* The two-element pointed set: [bool] pointed at [false]. / 这个二元指向集合：[bool] 指向 [false]。 *)
Definition PointedBool : PointedSetoid := {|
  pointed_setoid := {| carrier := bool ; is_setoid := eq_Setoid bool |};
  pt := false
|}.

(* The three-element pointed set: [option bool] pointed at [None]. / 三元素有尖指向的集合：[option bool] 指向 [None]。 *)
Definition PointedThree : PointedSetoid := {|
  pointed_setoid := {| carrier   := option bool
                     ; is_setoid := eq_Setoid (option bool) |};
  pt := Datatypes.None
|}.

Definition PointedBool_deq : DecidableEquiv PointedBool.
Proof.
  intros x y.
  destruct x, y.
  - left; reflexivity.
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - left; reflexivity.
Defined.

Definition PointedThree_deq : DecidableEquiv PointedThree.
Proof.
  intros x y.
  destruct x as [[|]|], y as [[|]|].
  - left; reflexivity.
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - left; reflexivity.
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - right; intro H; discriminate (eq_of_equiv H).
  - left; reflexivity.
Defined.

Definition PointedBool_enum : PointedEnumeration PointedBool.
Proof.
  refine (Build_PointedEnumeration PointedBool
            (Datatypes.cons false (Datatypes.cons true Datatypes.nil)) _).
  intro x.
  destruct x.
  - right; left; reflexivity.
  - left; reflexivity.
Defined.

Definition PointedThree_enum : PointedEnumeration PointedThree.
Proof.
  refine (Build_PointedEnumeration PointedThree
            (Datatypes.cons Datatypes.None
              (Datatypes.cons (Datatypes.Some false)
                (Datatypes.cons (Datatypes.Some true) Datatypes.nil))) _).
  intro x.
  destruct x as [[|]|].
  - right; right; left; reflexivity.
  - right; left; reflexivity.
  - left; reflexivity.
Defined.

(*
 Basepoint decidability at each of the two objects — the object-level form
 of the hypothesis [pointed_part_equivalence] asks for globally. 

 --------
 在每个对象上的基点可判定性——假设 [pointed_part_equivalence] 所要求的全局对象级形式。
*)
Definition PointedBool_dec_pt : DecidablePt PointedBool :=
  DecidablePt_of_DecidableEquiv PointedBool_deq.

Definition PointedThree_dec_pt : DecidablePt PointedThree :=
  DecidablePt_of_DecidableEquiv PointedThree_deq.

(* * *** Concrete maps between them, and the theorems exercised / * *** 它们之间的具体映射，以及所运用的定理 *)

(*
 A map between discrete setoids is respectful for free, so these concrete
 morphisms are built by direct record application rather than through
 [Program]. 

 --------
 离散集合之间的映射是自动保留的，所以这些具体的态射是通过直接应用记录构建的，而不是通过 [Program] 构建的。
*)
Definition eq_setoid_map {A B : Type} (f : A -> B) :
  @SetoidMorphism A (eq_Setoid A) B (eq_Setoid B) :=
  {| morphism        := f
   ; proper_morphism := fun x y H => equiv_of_eq (f_equal f (eq_of_equiv H)) |}.

(* [false ↦ None], [true ↦ Some false]: injective, not surjective. / [false ↦ None]，[true ↦ Some false]：单射，非满射。 *)
Definition bool_to_three_fun (b : bool) : option bool :=
  match b with
  | true => Datatypes.Some false
  | false => Datatypes.None
  end.

Definition bool_to_three_map := eq_setoid_map bool_to_three_fun.

Definition bool_to_three : PointedBool ~{PointedSets}~> PointedThree.
Proof.
  refine (Build_PointedMorphism PointedBool PointedThree bool_to_three_map _).
  reflexivity.
Defined.

(* [None ↦ false], [Some _ ↦ true]: surjective, not injective. / [None ↦ false]，[Some _ ↦ true]：满射，非单射。 *)
Definition three_to_bool_fun (o : option bool) : bool :=
  match o with
  | Datatypes.Some _ => true
  | Datatypes.None => false
  end.

Definition three_to_bool_map := eq_setoid_map three_to_bool_fun.

Definition three_to_bool : PointedThree ~{PointedSets}~> PointedBool.
Proof.
  refine (Build_PointedMorphism PointedThree PointedBool three_to_bool_map _).
  reflexivity.
Defined.

Lemma bool_to_three_injective : PointedInjective bool_to_three.
Proof.
  intros a b H.
  destruct a, b.
  - reflexivity.
  - discriminate (eq_of_equiv H).
  - discriminate (eq_of_equiv H).
  - reflexivity.
Qed.

Definition bool_to_three_monic : Monic bool_to_three :=
  fst (pointed_monic_iff bool_to_three) bool_to_three_injective.

Lemma three_to_bool_surjective : PointedSurjective three_to_bool.
Proof.
  intro b.
  destruct b.
  - exists (Datatypes.Some false).
    reflexivity.
  - exists Datatypes.None.
    reflexivity.
Qed.

Definition three_to_bool_epic : Epic three_to_bool :=
  fst (pointed_epic_iff three_to_bool) three_to_bool_surjective.

(* Non-vacuity, in both directions: a monic that is not epic, and an epic that is not monic. Set_* is therefore genuinely not balanced-by-triviality — [pointed_balanced] has content. / 非空性，双向存在：一个单射但不是满射，一个满射但不是单射。因此，Set_* 真的不是通过平凡性平衡的 — [pointed_balanced] 有内容。 *)
Lemma bool_to_three_not_epic : ¬ Epic bool_to_three.
Proof.
  intro He.
  destruct (pointed_epic_surjective bool_to_three He (Datatypes.Some true))
    as [a Ha].
  destruct a; discriminate (eq_of_equiv Ha).
Qed.

Lemma three_to_bool_not_monic : ¬ Monic three_to_bool.
Proof.
  intro Hm.
  pose proof (snd (pointed_monic_iff three_to_bool) Hm) as Hinj.
  pose proof (Hinj (Datatypes.Some false) (Datatypes.Some true)
                (equiv_of_eq (@eq_refl bool true))) as H.
  discriminate (eq_of_equiv H).
Qed.

(* The retraction of the monic, COMPUTED by [finite_monic_split]: the two points of the image go to their preimages, and the point outside the image goes to the basepoint. / 单曲线的收缩，由 [finite_monic_split] 计算：图像的两个点回到它们的原像，图像外的点回到基点。 *)
Definition bool_to_three_retraction : PointedThree ~{PointedSets}~> PointedBool :=
  @section PointedSets PointedBool PointedThree bool_to_three
    (finite_monic_split bool_to_three PointedBool_enum PointedThree_deq
       bool_to_three_monic).

Example bool_to_three_retraction_pt :
  bool_to_three_retraction Datatypes.None = false.
Proof. reflexivity. Qed.

Example bool_to_three_retraction_hit :
  bool_to_three_retraction (Datatypes.Some false) = true.
Proof. reflexivity. Qed.

Example bool_to_three_retraction_miss :
  bool_to_three_retraction (Datatypes.Some true) = false.
Proof. reflexivity. Qed.

(*
 The section of the epic, COMPUTED by [finite_epic_split]: the basepoint is
 sent to the basepoint by fiat, and [true] to the FIRST element of the
 enumeration of [PointedThree] lying over it. 

 --------
 由 [finite_epic_split] 计算的史诗部分：基点被命令映射到基点，而 [true] 被映射到位于其上的 [PointedThree] 枚举的第一个元素。
*)
Definition three_to_bool_section : PointedBool ~{PointedSets}~> PointedThree :=
  @retract PointedSets PointedThree PointedBool three_to_bool
    (finite_epic_split three_to_bool PointedThree_enum PointedBool_deq
       three_to_bool_epic).

Example three_to_bool_section_pt :
  three_to_bool_section false = Datatypes.None.
Proof. reflexivity. Qed.

Example three_to_bool_section_true :
  three_to_bool_section true = Datatypes.Some false.
Proof. reflexivity. Qed.

(* * *** [pointed_balanced] at a concrete bimorphism / * *** [pointed_balanced] 在混凝土双态映射处 *)

(*
 The basepoint-fixing exchange of the two free points of [PointedThree].
 The name carries the [pointed_] prefix because Structure/Cartesian.v
 already exports a generic [swap] combinator for cartesian products; the
 two are unrelated and must not shadow one another. 

 --------
 两个自由点的基点固定交换 [PointedThree]。
 这个名字带有 [pointed_] 前缀，因为 Structure/Cartesian.v 已经导出了一个用于笛卡尔积的通用 [swap] 组合子；两者无关，且不能互相遮蔽。
*)
Definition pointed_swap_fun (o : option bool) : option bool :=
  match o with
  | Datatypes.Some b => Datatypes.Some (negb b)
  | Datatypes.None => Datatypes.None
  end.

Definition pointed_swap_map := eq_setoid_map pointed_swap_fun.

Definition pointed_swap : PointedThree ~{PointedSets}~> PointedThree.
Proof.
  refine (Build_PointedMorphism PointedThree PointedThree pointed_swap_map _).
  reflexivity.
Defined.

Lemma pointed_swap_injective : PointedInjective pointed_swap.
Proof.
  intros a b H.
  destruct a as [[|]|], b as [[|]|]; try reflexivity;
  discriminate (eq_of_equiv H).
Qed.

Lemma pointed_swap_surjective : PointedSurjective pointed_swap.
Proof.
  intro o.
  destruct o as [[|]|].
  - exists (Datatypes.Some false).
    reflexivity.
  - exists (Datatypes.Some true).
    reflexivity.
  - exists Datatypes.None.
    reflexivity.
Qed.

(*
 A concrete corollary of the balance theorem: this map is invertible for no
 reason other than being monic and epic — no inverse was supplied. 

 --------
 平衡定理的一个具体推论：这个映射可逆，仅仅是因为它是单射和满射——没有提供逆映射。
*)
Definition pointed_swap_isomorphism : IsIsomorphism pointed_swap :=
  snd (pointed_balanced pointed_swap)
    (fst (pointed_monic_iff pointed_swap) pointed_swap_injective,
     fst (pointed_epic_iff pointed_swap) pointed_swap_surjective).

(*
 The inverse the theorem produced, exercised at a point: its value is forced
 by the right-inverse law together with injectivity. 

 --------
 在某一点上应用产生的定理的逆：它的值由右逆律和单射性共同决定。
*)
Example pointed_swap_inverse_at_true :
  @two_sided_inverse PointedSets PointedThree PointedThree pointed_swap pointed_swap_isomorphism
    (Datatypes.Some true) ≈ Datatypes.Some false.
Proof.
  apply pointed_swap_injective.
  transitivity (Datatypes.Some true).
  - exact (@is_right_inverse PointedSets PointedThree PointedThree pointed_swap
             pointed_swap_isomorphism (Datatypes.Some true)).
  - reflexivity.
Qed.
