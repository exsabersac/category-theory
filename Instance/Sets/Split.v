Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * A section/retraction pair in Sets that is not an isomorphism / * * 在集合中的一个节/收回对，但不是同构 *)

(*
 nLab:      https://ncatlab.org/nlab/show/split+monomorphism
 nLab:      https://ncatlab.org/nlab/show/split+epimorphism
 Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

 Fong and Spivak, “Seven Sketches in Compositionality” (CUP, 2019), §3.2.5
 Example 3.34, printed p. 89.  CITED BY LOCATION; the printed text was not
 consulted and no sentence of it is reproduced here.  The library's book
 catalog describes the example as exhibiting a one-sided inverse pair in
 sets and observing that neither map is an isomorphism
 (doc/plan/books/ledger.tsv, id 7sketches:3.2.5:example3.34).

 Theory/Morphisms/Classes.v arranges the morphism classes in the inclusion
 diagram

 Iso ⊆ SplitMono ⊆ Mono
 Iso ⊆ SplitEpi  ⊆ Epi

 and proves all four inclusions ([split_mono_in_mono],
 [split_epi_in_epi], [iso_in_split_mono], [iso_in_split_epi]).
 Nothing there says any inclusion is STRICT, and showing Iso ⊆ SplitMono
 proper needs an actual split mono with no inverse.  The tree did not have
 one for [Sets].  Construction/Karoubi.v manufactures splittings
 generically ([karoubi_idem_splits]), but only from a GIVEN idempotent, and
 never exhibits one that is provably not an identity, so the
 non-invertibility conclusion is never drawn there.  The nearest concrete
 pair, [pick_true]/[collapse] at Instance/Sets.v,500, is built to refute
 the cancellation converses (Mac Lane §I.5 Exercise 1) and is not carried as
 far as invertibility.

 The pair below separates both classes at once: a two-element setoid
 included into a three-element one, and a retraction folding the extra
 point back.  One composite is the identity, the other provably is not, and
 non-invertibility is settled by evaluating at the extra point. 

 --------
 nLab：       https://ncatlab.org/nlab/show/split+monomorphism 
 nLab：       https://ncatlab.org/nlab/show/split+epimorphism 
 维基百科：  https://en.wikipedia.org/wiki/Section_(category_theory) 

 Fong 和 Spivak，《组合性中的七个素描》（CUP，2019），§3.2.5
 示例 3.34，印刷页 89。引用自位置；未查阅印刷文本，也未在此处复制任何句子。图书馆的图书目录描述该示例为展示集合中的单边逆对，并指出两者映射都不是同构
 (doc/plan/books/ledger.tsv, id 7sketches:3.2.5:example3.34)。

 Theory/Morphisms/Classes.v 将映射类排列在包含图中

 Iso ⊆ SplitMono ⊆ Mono
 Iso ⊆ SplitEpi  ⊆ Epi并证明所有四个包含关系（[split_mono_in_mono], [split_epi_in_epi], [iso_in_split_mono], [iso_in_split_epi]）。
 那里没有说明任何包含关系是严格的，而要显示 Iso ⊆ SplitMono proper，需要一个没有逆的实际分裂单态。[Sets] 的树中没有这样的例子。Construction/Karoubi.v 通用地生成拆分（[karoubi_idem_splits]），但仅来自给定的幂等元，而且从未展示一个可以证明非身份的拆分，因此在那里从未得出不可逆的结论。最近的具体示例对 [pick_true] / [collapse] 在 Instance/Sets.v,500 中，构建它是为了反驳取消律的逆命题（Mac Lane §I.5 练习 1），并没有进一步涉及可逆性。下面的这一对同时分离了两个类：一个包含在三元素集合中的二元素集合，以及将多余点折回的收缩。一个复合是恒等的，另一个可以证明不是，而且通过在多余点处求值可以确定不可逆性。
*)

(* ------------------------------------------------------------------------ *)
(** ** The two objects / ** 这两个物体 *)

(*
 The two-element setoid is the one Instance/Sets.v already carries;
 this is a notation for it, not a second copy. 

 --------
 这个两元素集合等价类是 Instance/Sets.v 已经包含的；这是它的一个符号表示，而不是第二份副本。
*)
Notation sets_two := bool_setoid_object.

(*
 The three-element setoid: [option bool] under Coq's `=`, via [eq_Setoid]
 (Lib/Setoid.v).  The carriers are chosen so that every case analysis
 below is a plain [destruct] and every refutation a plain [discriminate]. 

 --------
 三元素集合：[option bool] 在 Coq 的 `=` 下，通过 [eq_Setoid] (Lib/Setoid.v)。载体的选择是为了使下面的每个情况分析都是一个普通的 [destruct]，每个反驳都是一个普通的 [discriminate]。
*)
Definition sets_three@{t u} : SetoidObject@{t u} :=
  {| carrier := option bool ; is_setoid := eq_Setoid@{t} (option bool) |}.

(*
 The carriers really do have two and three inhabitants, and both halves of
 that claim are proved: the enumerations are exhaustive, and the listed
 values are pairwise distinct.  Neither half implies the other -- an
 exhaustive list is only an upper bound on the count -- so the packages
 [sets_two_card] and [sets_three_card] below carry them together.

 Distinctness is stated with `=`, and that is the right relation rather
 than a lapse from the library's `≈` discipline: these are equations
 between ELEMENTS of a carrier, not between morphisms, and both objects are
 DISCRETE -- [sets_three] carries [eq_Setoid] (Lib/Setoid.v) and
 [bool_setoid_object] (Instance/Sets.v) carries that same record
 written out -- so `=` IS the equivalence of the object, and refuting it
 refutes equality in [Sets] and not merely equality of representatives. 

 --------
 载体确实有两个和三个成员，并且该声明的两个部分都得到了证明：列举是详尽的，而且列出的值两两不同。两个部分都不意味着另一个——详尽的列表只是数量的上限——因此下面的包 [sets_two_card] 和 [sets_three_card] 一起承载它们。通过 `=` 表示区分性，这才是正确的关系，而不是库中 `≈` 规范的偏差：这些是承载体元素之间的方程，而不是态射之间的方程，并且两个对象都是离散的——[sets_three] 承载 [eq_Setoid]（Lib/Setoid.v）并且 [bool_setoid_object]（Instance/Sets.v）承载相同的记录书写形式——因此 `=` 就是对象的等价性，反驳它就反驳 [Sets] 中的相等性，而不仅仅是代表元的相等性。
*)

Lemma sets_two_enum (b : bool) : (b = true) ∨ (b = false).
Proof. destruct b; [ now left | now right ]. Qed.

Lemma sets_two_distinct : (true = false) → False.
Proof. discriminate. Qed.

Lemma sets_three_enum (o : option bool) :
  (o = None) ∨ (o = Some true) ∨ (o = Some false).
Proof.
  destruct o as [[|] |].
  - right; now left.
  - right; right; reflexivity.
  - now left.
Qed.

Lemma sets_three_distinct :
  ((None = Some true) → False)
  * ((None = Some false) → False)
  * ((Some true = Some false) → False).
Proof. repeat split; discriminate. Qed.

(*
 The counts, packaged.  The refutations further down re-derive what they
 need by [discriminate] rather than projecting out of these, a
 [discriminate] being shorter than the projection that would replace it. 

 --------
 计数，已打包。下面的驳斥通过[discriminate]重新推导出所需内容，而不是从这些中投影，[discriminate]比将取代它的投影要短。
*)

Definition sets_two_card :
  (∀ b : bool, (b = true) ∨ (b = false))
  * ((true = false) → False) :=
  (sets_two_enum, sets_two_distinct).

Definition sets_three_card :
  (∀ o : option bool, (o = None) ∨ (o = Some true) ∨ (o = Some false))
  * (((None = Some true) → False)
     * ((None = Some false) → False)
     * ((Some true = Some false) → False)) :=
  (sets_three_enum, sets_three_distinct).

(* ------------------------------------------------------------------------ *)
(** ** The two maps / ** 两张地图 *)

(*
 The inclusion is [Some].  The only feature of it the proofs below use is
 that it misses [None]. 

 --------
 包含的是 [Some]。下面证明中使用的它的唯一特征是它缺少 [None]。
*)
Program Definition sets_incl23 : sets_two ~{Sets}~> sets_three := {|
  morphism := @Some bool
|}.

(* The retraction undoes [Some] and folds the missed point [None] onto [true], so it identifies [None] with [Some true]. / 撤回会撤销 [Some] 并将遗漏点 [None] 折叠到 [true] 上，因此它将 [None] 与 [Some true] 识别为同一。 *)
Definition option_fold (o : option bool) : bool :=
  match o with
  | Some b => b
  | None   => true
  end.

Program Definition sets_retr32 : sets_three ~{Sets}~> sets_two := {|
  morphism := option_fold
|}.

(* ------------------------------------------------------------------------ *)
(** ** One composite is the identity / ** 一个复合是恒等式 *)

Lemma sets_retr_incl : sets_retr32 ∘[Sets] sets_incl23 ≈ id{Sets}.
Proof. intro b; now destruct b. Qed.

(*
 Hence the inclusion is a split mono and the retraction a split epi, both
 witnessed by the SAME equation -- this is the shape Theory/Morphisms.v
 names [Section] and [Retraction]. 

 --------
 因此，该包含是一个分裂单态，而收缩是一个分裂满态，两者都由相同的方程见证 —— 这是形状理论/态射.v中的名称 [Section] 和 [Retraction]。
*)

Definition sets_incl23_Section : Section sets_incl23 :=
  Build_Section _ _ sets_incl23 sets_retr32 sets_retr_incl.

Definition sets_retr32_Retraction : Retraction sets_retr32 :=
  Build_Retraction _ _ sets_retr32 sets_incl23 sets_retr_incl.

(* ------------------------------------------------------------------------ *)
(* * ** The other composite provably is not the identity / * ** 另一个复合显然不是恒等映射 *)

(*
 At [None] the round trip lands on [Some true]: the retraction folds [None]
 onto [true] and the inclusion cannot recover it. 

 --------
 在 [None]，往返行程降落在 [Some true]：收缩折叠 [None] 到 [true]，并且包含无法恢复它。
*)

Lemma sets_incl_retr_not_id :
  sets_incl23 ∘[Sets] sets_retr32 ≈ id{Sets} → False.
Proof. intro H; discriminate (H None). Qed.

(*
 So this splitting's idempotent is not an identity -- which is exactly what
 the generic Karoubi construction never exhibits. 

 --------
 所以这个分裂的幂等性不是一个恒等式——这正是泛卡鲁比构造从未表现出的。
*)
Lemma sets_incl_retr_idempotent :
  Idempotent (sets_incl23 ∘[Sets] sets_retr32).
Proof.
  exact (split_pair_idempotent sets_retr32 sets_incl23 sets_retr_incl).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Neither map is an isomorphism / ** 两个映射都不是同构 *)

(*
 The inclusion misses [None], so no right inverse can reach it: whatever
 value a candidate inverse returns there, [Some] of it is not [None]. 

 --------
 该包含遗漏了 [None]，因此没有右逆可以达到它：无论候选逆在那里返回什么值，它的 [Some] 都不是 [None]。
*)

Lemma sets_incl23_not_iso : IsIsomorphism sets_incl23 → False.
Proof. intros [t Hr _]; discriminate (Hr None). Qed.

(* The retraction identifies [None] with [Some true], so no left inverse can separate them again. / 该收回将 [None] 与 [Some true] 识别为相同，因此没有左逆可以再次将它们分开。 *)

Lemma sets_retr32_not_iso : IsIsomorphism sets_retr32 → False.
Proof.
  intros [u _ Hl].
  pose proof (Hl None) as H1.
  pose proof (Hl (Some true)) as H2.
  simpl in H1, H2.
  rewrite H1 in H2.
  discriminate.
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The class inclusions of Theory/Morphisms/Classes.v are strict / * ** Theory/Morphisms/Classes.v 的类包含是严格的 *)

(*
 [iso_in_split_mono] and [iso_in_split_epi] send IsoClass into
 SplitMonoClass and SplitEpiClass.  Each package below exhibits a morphism
 in the larger class and refutes its membership in the smaller one, so both
 inclusions are strict. 

 --------
 [iso_in_split_mono] 和 [iso_in_split_epi] 将 IsoClass 送入 SplitMonoClass 和 SplitEpiClass。下面的每个包都展示了大类中的一个态射，并反驳它属于小类，因此两个包含都是严格的。
*)

Definition sets_split_mono_not_iso :
  @SplitMonoClass Sets sets_two sets_three sets_incl23
  * (@IsoClass Sets sets_two sets_three sets_incl23 → False) :=
  (sets_incl23_Section, sets_incl23_not_iso).

Definition sets_split_epi_not_iso :
  @SplitEpiClass Sets sets_three sets_two sets_retr32
  * (@IsoClass Sets sets_three sets_two sets_retr32 → False) :=
  (sets_retr32_Retraction, sets_retr32_not_iso).

(*
 The Seven Sketches example in full: a one-sided inverse pair whose other
 composite provably is not an identity, with neither map invertible. 

 --------
 完整的七草图示例：一个单边逆对，其另一复合可证明不是恒等映射，并且两个映射都不可逆。
*)
Definition sets_split_pair_not_iso :
  (sets_retr32 ∘[Sets] sets_incl23 ≈ id{Sets})
  * ((sets_incl23 ∘[Sets] sets_retr32 ≈ id{Sets}) → False)
  * (IsIsomorphism sets_incl23 → False)
  * (IsIsomorphism sets_retr32 → False) :=
  (sets_retr_incl, sets_incl_retr_not_id,
   sets_incl23_not_iso, sets_retr32_not_iso).

(* ------------------------------------------------------------------------ *)
(** ** Both maps are regular / ** 两张地图都是常规的 *)

(* Tying the example back to Mac Lane §I.5 Exercise 7: a one-sided inverse is already a pseudoinverse, so each map of the pair is regular even though neither is invertible. / 将这一例子与 Mac Lane §I.5 练习 7 联系起来：一个单边逆已经是伪逆，因此即使两者都不可逆，这对映射中的每一个都是正规映射。 *)

Definition sets_incl23_regular : RegularMorphism sets_incl23 :=
  regular_of_section _ sets_incl23_Section.

Definition sets_retr32_regular : RegularMorphism sets_retr32 :=
  regular_of_retraction _ sets_retr32_Retraction.
