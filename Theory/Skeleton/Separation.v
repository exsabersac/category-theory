Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** * Skeletality separates equivalence from isomorphism of categories / * 骨架性将范畴的等价与同构区分开 *)

(*
nLab: https://ncatlab.org/nlab/show/skeleton
   nLab: https://ncatlab.org/nlab/show/principle+of+equivalence

   Awodey asks (Category Theory, 1st ed., §7.10, Exercise 11, p. 188) which
   properties of categories respect equivalence, and for one that is
   invariant under isomorphism of categories but not under equivalence.
   Skeletality is the canonical answer, and this file supplies the negative
   half as a theorem: [skeletality_is_not_equivalence_invariant] exhibits
   the terminal category [1], which is skeletal, equivalent to the
   indiscrete category on [bool], which is not.  The positive half —
   skeletality IS carried along an isomorphism of categories — is
   [Skeletal_StrictCat_invariant] in Theory/Skeleton.v, where it belongs
   because it needs no witnesses.  Together they turn the prose of
   Theory/Equivalence.v (“skeletality is not equivalence-invariant”) into a
   pair of proofs.

   The same pair does double duty for Awodey's Exercise 12 (p. 188), which
   asks for a skeletal subcategory equivalent to a given category:
   [Indiscrete_bool_Skeleton] supplies a genuine, non-trivial [Skeleton]
   datum for a category that is NOT skeletal, and
   [Indiscrete_bool_skeleton_is_One] then identifies its skeleton with [1]
   on the nose — an isomorphism in [StrictCat], not merely an equivalence,
   obtained by feeding two equivalences to
   [skeletal_equivalence_is_isomorphism].  This is the in-tree witness
   docs/INHABITATION.md records for the [Skeleton] record: the chosen
   representative is named outright ([true]), so nothing here smuggles a
   choice principle, and no existence claim is made for an arbitrary
   category.

   [One_Skeletal] and [Two_Skeletal] round out the small witnesses;
   [Two_Skeletal] in particular gives Instance/Two.v's header, which calls a
   Boolean algebra “a skeletal thin finitely-cocomplete star-autonomous”
   category, a companion theorem about [_2] itself.

   WHY A SEPARATE FILE.  Theory/Skeleton.v is already a heavyweight Theory
   module (see its header); the witnesses here additionally need
   Instance/Discrete/Reconstruct.v for [Indiscrete] and Instance/Two.v for
   [_2], neither of which any consumer of the core theory has reason to
   pull in.  This is the split rationale Instance/Discrete/Reconstruct.v
   records for itself.

--------
nLab：https://ncatlab.org/nlab/show/skeleton
nLab：https://ncatlab.org/nlab/show/principle+of+equivalence

Awodey 在《范畴论》（第一版，第7.10节，练习11，第188页）中询问哪些范畴的性质保持等价，并询问一个在范畴同构下不变但在等价下不变的性质。骨架性是标准答案，而这个文件以定理的形式提供了负面的一半：[skeletality_is_not_equivalence_invariant] 展示了终范畴 [1]，它是骨架的，并且与 [bool] 上的无辨析范畴等价，但后者不是。正面的一半——骨架性确实在范畴同构下保持——在 Theory/Skeleton.v 中的 [Skeletal_StrictCat_invariant]，它属于那里，因为它不需要证据。两者结合，将 Theory/Equivalence.v 中的文字描述（“骨架性不是等价不变的”）转化为一对证明。

同一对用于 Awodey 的练习 12（第 188 页），该练习要求给出一个等价的骨架子范畴：[Indiscrete_bool_Skeleton] 为一个非骨架范畴提供了一个真实的、非平凡的 [Skeleton] 数据，然后 [Indiscrete_bool_skeleton_is_One] 将其骨架精确地确定为 [1]——在 [StrictCat] 中的同构，而不仅仅是等价，这是通过将两个等价输入 [skeletal_equivalence_is_isomorphism] 获得的。这是在树内的见证，docs/INHABITATION.md 记录了 [Skeleton] 记录：选定的代表已明确命名（[true]），因此这里没有引入选择原理，也没有对任意范畴作存在性声明。

[One_Skeletal] 和 [Two_Skeletal] 完成了小证据的补充；[Two_Skeletal] 尤其给出了 Instance/Two.v 的头部，该头部将布尔代数称为“一个骨架化的瘦有限余完备的星自律”范畴，这是关于 [_2] 本身的一个伴随定理。

为什么要单独文件。Theory/Skeleton.v 已经是一个重量级的理论模块（参见其头部）；这里的见证者还需要 Instance/Discrete/Reconstruct.v 来支持 [Indiscrete]，以及 Instance/Two.v 来支持 [_2]，而核心理论的任何使用者都没有理由去引入这两个文件。这就是 Instance/Discrete/Reconstruct.v 为自己记录的拆分理由。
*)

(** ** Small skeletal categories / ** 小型骨骼范畴 *)

Lemma One_Skeletal : Skeletal _1.
Proof. intros x y _; now destruct x, y. Qed.

(*
[_2] has no arrow [TwoY ~> TwoX], so its only isomorphisms are the
   identities.

--------
[_2] 没有箭头 [TwoY ~> TwoX]，因此它的唯一同构是恒等映射。
*)

Lemma Two_Skeletal : Skeletal _2.
Proof.
  intros [] [] i; try reflexivity.
  - destruct (TwoHom_Y_X_absurd (from i)).
  - destruct (TwoHom_Y_X_absurd (to i)).
Qed.

(** ** The indiscrete category on [bool] is not skeletal / ** [bool] 上的不连续范畴不是骨架范畴 *)

Program Definition Indiscrete_iso {A : Type} (x y : A) :
  @Isomorphism (Indiscrete A) x y := {| to := tt; from := tt |}.

Lemma Indiscrete_bool_not_Skeletal : Skeletal (Indiscrete bool) → False.
Proof.
  intro SK.
  pose proof (SK true false (Indiscrete_iso true false)) as H.
  discriminate.
Qed.

(** ** ... yet it is equivalent to the terminal category / ** ... 然而它等同于终端范畴 *)

Program Definition Pick : _1 ⟶ Indiscrete bool := {|
  fobj := fun _ => true;
  fmap := fun _ _ _ => tt
|}.

(*
[poly_unit] has no definitional eta, so the unit component is given by a
   [match] rather than by [fun _ => iso_id].  Both obligations end in
   [Defined] to keep the equivalence transparent; unlike
   [skeleton_inclusion_is_equivalence], whose [Defined] is what makes
   [skel_reflect_obj] hold by [reflexivity], nothing here depends on it.

--------
[poly_unit] 没有定义的 eta，因此单位组件由 [match] 给出，而不是由 [fun _ => iso_id] 给出。两个义务都以 [Defined] 结束，以保持等价性透明；不像 [skeleton_inclusion_is_equivalence]，其 [Defined] 是使 [skel_reflect_obj] 通过 [reflexivity] 成立的原因，这里没有任何依赖于它的内容。
*)

Program Definition One_Indiscrete_Equivalence :
  EquivalenceOfCategories Pick := {| quasi_inverse := Erase (Indiscrete bool) |}.
Next Obligation.
  exists (fun x => Indiscrete_iso true x).
  intros x y f; now destruct f.
Defined.
Next Obligation.
  exists (fun x => match x as u return (Isomorphism (C:=_1) u ttt) with
                   | ttt => iso_id end).
  intros x y f; now destruct x, y, f.
Defined.

(*
Awodey §7.10 Exercise 11, negative half.  The statement mentions neither
   [Cat] nor [StrictCat] on purpose: phrasing it as an isomorphism in [Cat]
   would bump a universe level for no gain.

--------
Awodey §7.10 练习 11，负半。该陈述故意未提及 [Cat] 或 [StrictCat]：将其表述为 [Cat] 中的同构将无益地提高宇宙层级。
*)

Theorem skeletality_is_not_equivalence_invariant :
  { C : Category & { D : Category &
      ((C ≃ D) * Skeletal C * (Skeletal D → False))%type } }.
Proof.
  exists _1, (Indiscrete bool).
  split; [split|].
  - exact (Pick; One_Indiscrete_Equivalence).
  - exact One_Skeletal.
  - exact Indiscrete_bool_not_Skeletal.
Defined.

(** ** Awodey §7.10 Exercise 12: a skeleton of a non-skeletal category / ** Awodey §7.10 练习 12：一个非骨架范畴的骨架 *)

Program Definition Indiscrete_bool_Sub : Subcategory (Indiscrete bool) := {|
  sobj := fun x => x = true;
  shom := fun x y ox oy f => True
|}.

Section IndiscreteWitness.
#[local] Obligation Tactic := idtac.

(*
The uniqueness obligation needs no decidability of [bool] equality: the
   based path space [y = true] is contractible, so [destruct] on the
   membership proof closes it.

--------
唯一性义务不需要 [bool] 相等的可判定性：基路径空间 [y = true] 是可收缩的，因此在成员资格证明上的 [destruct] 会将其闭合。
*)

Program Definition Indiscrete_bool_Skeleton : Skeleton (Indiscrete bool) := {|
  skel_sub  := Indiscrete_bool_Sub;
  skel_full := fun x y ox oy f => I;
  skel_rep  := fun _ => (true; @eq_refl bool true);
  skel_iso  := fun x => Indiscrete_iso x true;
  skel_uniq := _
|}.
Next Obligation.
  intros x a i; destruct a as [y b]; simpl in *; now destruct b.
Qed.

End IndiscreteWitness.

Example Indiscrete_bool_skeleton_has_one_object :
  ∀ X Y : skel_cat Indiscrete_bool_Skeleton, X = Y.
Proof. intros [x a] [y b]; simpl in *; destruct a, b; reflexivity. Qed.

(*
The capstone: the skeleton of the indiscrete category on [bool] IS the
   point, on the nose — an isomorphism of categories, not merely an
   equivalence.

--------
压轴之作：[bool] 上不可分割范畴的骨架正是关键，恰到好处——是范畴的同构，而不仅仅是等价。
*)

Definition Indiscrete_bool_skeleton_is_One :
  skel_cat Indiscrete_bool_Skeleton ≅[StrictCat] _1 :=
  let e : skel_cat Indiscrete_bool_Skeleton ≃ _1 :=
    Equivalence_trans (skeleton_equivalence Indiscrete_bool_Skeleton)
      (Equivalence_sym (Pick; One_Indiscrete_Equivalence)) in
  skeletal_equivalence_is_isomorphism
    (skeleton_is_skeletal Indiscrete_bool_Skeleton) One_Skeletal (`1 e) (`2 e).
