Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(*
   * * The core functor, and its adjunction with the inclusion 

   --------
   * * 核心函子及其与包含函子的伴随关系
*)

(*
 nLab:      https://ncatlab.org/nlab/show/core
 nLab:      https://ncatlab.org/nlab/show/Grpd
 Wikipedia: https://en.wikipedia.org/wiki/Core_(group_theory)

 Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,
 Example 4.1.15, printed p. 137 (PDF pp. 157-158)

 Construction/Groupoid.v builds the core of ONE category:
 [Groupoid C] has the objects of C and the isomorphisms of C as its
 morphisms.  This file makes that construction a functor
 [Core : Cat ⟶ Grpd] and proves it right adjoint to the inclusion
 [Grpd_Incl : Grpd ⟶ Cat] of Instance/Grpd.v.

 The morphism part is forced.  A functor F : C ⟶ D carries isomorphisms
 to isomorphisms -- Theory/Functor.v's [fobj_iso] is exactly that
 statement, as a [Proper] instance -- so [CoreMap F] is F restricted to
 the isomorphisms, sending x ≅ y to F x ≅ F y componentwise.  [CoreMap]
 below writes that two-field isomorphism out directly instead of
 projecting it from [fobj_iso], so that its two inverse laws are named
 obligations here.  The object part needs [IsGroupoid (Groupoid C)];
 that lemma is already in-tree, as Structure/Groupoid.v's
 [core_is_groupoid], and is reused rather than reproved.

 The adjunction is the universal property of the core: for a groupoid G,
 every functor G ⟶ C lands in the isomorphisms of C, so it factors
 through [Groupoid C], and uniquely.  The forward transpose is
 [core_lift]: it re-reads F : G ⟶ C as a functor into [Groupoid C] by
 pairing F f with F of the chosen inverse of f.  The backward transpose
 is post-composition with [ForgetCore C : Groupoid C ⟶ C], which takes an
 isomorphism to its [to] component.  What makes the two mutually inverse
 is that a functor into a core is DETERMINED by its [to] components
 ([core_functor_from] below): the [from] component of P f is forced to be
 the [to] component of P (f⁻¹), by uniqueness of inverses.

 The result is delivered as a `≈`-level [Adjunction] over the CATEGORY
 [Grpd], through Theory/Adjunction.v's [Build_Adjunction'] -- not as a
 per-object factorization statement.  Both of the naturality squares
 [Build_Adjunction'] asks for are witnessed by the IDENTITY natural
 isomorphism: the two functors being compared agree on objects and in
 their [to] components, so [cat] closes those halves.  Only the [from]
 halves need an argument, and only for the first square
 ([to_adj_nat_l]); it is there that the one genuine lemma of the file,
 [functor_ginv], is used.  The second ([to_adj_nat_r]) is componentwise
 identical on both sides.

 Not delivered here: the LEFT adjoint.  The category of fractions, which
 universally inverts every morphism, is not built in any part, so the
 adjoint triple Fractions ⊣ Incl ⊣ Core is exhibited only on its
 right-hand side. 

 --------
 nLab:       https://ncatlab.org/nlab/show/core 
 nLab:       https://ncatlab.org/nlab/show/Grpd 
 维基百科:  https://en.wikipedia.org/wiki/Core_(group_theory) 

 书籍: Riehl, 《Category Theory in Context》, Dover 2016, §4.1,
 示例 4.1.15, 印刷页码 p. 137 (PDF 页码 pp. 157-158)

 Construction/Groupoid.v 构建了 ONE 范畴的核心:
 [Groupoid C]  具有 C 的对象和 C 的同构作为其态射。该文件将该构造变为函子
 [Core : Cat ⟶ Grpd]  并证明它是包含
 [Grpd_Incl : Grpd ⟶ Cat]  Instance/Grpd.v 的右伴随。态射部分是强制的。函子 F : C ⟶ D 将同构映射到同构 —— Theory/Functor.v 的 [fobj_iso] 正是这个命题，作为 [Proper] 的一个实例 —— 因此 [CoreMap F] 是 F 限制在同构上，逐分量地将 x ≅ y 映射为 F x ≅ F y。下面的 [CoreMap] 直接写出了这个双域同构，而不是从 [fobj_iso] 投影出来，因此它的两个逆律在这里被命名为义务。对象部分需要 [IsGroupoid (Groupoid C)]；那个引理已经在树中，即 Structure/Groupoid.v 的 [core_is_groupoid]，并且被重复使用而不是重新证明。伴随是核心的普遍性质：对于一个群套 G，
 每一个函子 G ⟶ C 都会落入 C 的同构中，因此它通过 [Groupoid C] 唯一分解。前向转置是 [core_lift]：它将 F : G ⟶ C 重新读取为进入 [Groupoid C] 的函子，通过将 F f 与 f 的选定逆的 F 配对。后向转置是与 [ForgetCore C : Groupoid C ⟶ C] 后合成，它将一个同构映射到它的 [to] 分量。使两者互为逆的是，进入核心的函子由其 [to] 分量决定（见下文 [core_functor_from]）：P f 的 [from] 分量被迫等于 P(f⁻¹) 的 [to] 分量，这是由逆的唯一性决定的。结果作为一个`≈`级别的[Adjunction]通过CATEGORY [Grpd]，从Theory/Adjunction.v的[Build_Adjunction']提供——而不是作为每个对象的分解陈述。自然性方格[Build_Adjunction']要求的两者由IDENTITY自然同构证明：被比较的两个函子在对象上以及其[to]组成部分上都一致，因此[cat]闭合了那些部分。只有[from]部分需要论证，并且只针对第一个方格（[to_adj_nat_l]）；在这里使用了文件中唯一的真正引理[functor_ginv]。第二个方格（[to_adj_nat_r]）在各个组成部分上两边都是相同的。未在此处给出：左伴随。分式的范畴，其普遍地逆转每个态射，在任何部分都未构建，因此伴随三重 Fractions ⊣ Incl ⊣ Core 仅在其右侧展示。
*)

(*
   * ** Functors between groupoids preserve the chosen inverse

   [IsGroupoid] carries a CHOSEN inverse for each arrow, so "F preserves
   inverses" is not a tautology: it says the choice made in B at [fmap[F] f]
   agrees, up to `≈`, with the image of the choice made in A at f.  It does,
   because both are inverses of the same arrow and inverses are unique
   (Structure/Groupoid.v's [ginv_unique_r], which is Eilenberg and
   Mac Lane's Lemma 1.4 read at the chosen inverse). 

   --------
   * ** 群族之间的函子保持选定的逆元

   [IsGroupoid] 为每个箭头提供了一个选定的逆元，因此“F 保持逆元”并不是同义反复：它说明在 B 中对 [fmap[F] f] 所做的选择与在 A 中对 f 所做选择的映像在 `≈` 下是一致的。确实如此，因为它们都是同一箭头的逆元，而逆元是唯一的（Structure/Groupoid.v 的 [ginv_unique_r]，即以所选逆元解读的 Eilenberg 和 Mac Lane 的引理 1.4）。
*)

Lemma functor_ginv {A B : Category} (HA : IsGroupoid A) (HB : IsGroupoid B)
      (F : A ⟶ B) {x y : A} (f : x ~> y) :
  fmap[F] (ginv HA f) ≈ ginv HB (fmap[F] f).
Proof.
  symmetry.
  apply ginv_unique_r.
  rewrite <- fmap_comp.
  rewrite ginv_right.
  apply fmap_id.
Qed.

(*
 In the core the chosen inverse is [iso_sym] ON THE NOSE, not merely up to
 `≈`: [core_is_groupoid] hands [Build_IsIsomorphism] the term [iso_sym f]
 and [ginv] projects it straight back out.  Recorded as an [Example] at
 [eq_refl], the strongest available reading. 

 --------
 在核心中，选择的逆向是 [iso_sym] 精确无误，而不仅仅是到 `≈`：[core_is_groupoid] 手 [Build_IsIsomorphism] 术语 [iso_sym f] ，并且 [ginv] 将其直接投射回去。记录为 [Example] 在 [eq_refl] ，这是可用的最强读数。
*)

Example core_ginv_eq {C : Category} {x y : Groupoid C} (f : x ~> y) :
  ginv (core_is_groupoid C) f = iso_sym f := eq_refl.

(*
   * ** Isomorphisms of the core

   An isomorphism of C is a morphism of [Groupoid C]; it is moreover an
   ISOMORPHISM of [Groupoid C], with [iso_sym] as its inverse.  This is
   [core_is_groupoid] packaged as `≅` rather than as [IsIsomorphism], and
   it is what turns a natural isomorphism between functors into C into one
   between the corresponding functors into [Groupoid C]. 

   --------
   * ** 核的同构

   C 的同构是 [Groupoid C] 的一个态射；此外，它也是 [Groupoid C] 的一个同构，其逆为 [iso_sym]。 这就是 [core_is_groupoid] 以 `≅` 的形式打包，而不是以 [IsIsomorphism] 的形式，并且它将函子之间的自然同构在 C 中转换为相应函子之间的同构到 [Groupoid C]。
*)

Program Definition core_iso {D : Category} {a b : D} (i : a ≅ b) :
  a ≅[Groupoid D] b := {|
  to          := i;
  from        := iso_sym i;
  iso_to_from := iso_sym_right_inverse i;
  iso_from_to := iso_sym_left_inverse i
|}.

(** ** The core of a functor / ** 函子的核心 *)

Program Definition CoreMap {C D : Category} (F : C ⟶ D) :
  Groupoid C ⟶ Groupoid D := {|
  fobj := fun x => F x;
  fmap := fun _ _ f => {| to := fmap[F] (to f); from := fmap[F] (from f) |}
|}.
Next Obligation.
  rewrite <- fmap_comp, iso_to_from.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp, iso_from_to.
  apply fmap_id.
Qed.
Next Obligation.
  intros f g [Hto Hfrom]; split; simpl.
  - now rewrite Hto.
  - now rewrite Hfrom.
Qed.
(*
 The [fmap_id] obligation is discharged by the ambient [cat_simpl]; only
 [fmap_comp] survives it. 

 --------
 [fmap_id] 的义务由周围的 [cat_simpl] 解除；只有 [fmap_comp] 存续它。
*)
Next Obligation. split; simpl; apply fmap_comp. Qed.

(*
 The core of a natural isomorphism.  [Cat]'s hom-setoid is
 [Functor_Setoid], so F ≈ F' is a natural isomorphism; each component is
 an isomorphism of D, hence a morphism of [Groupoid D], and [core_iso]
 promotes it to an isomorphism THERE.  The naturality square is checked
 twice, once in each component of the isomorphism, the [from] half being
 the given square read at f⁻¹. 

 --------
 自然同构的核心。[Cat] 的 hom-集是 [Functor_Setoid]，所以 F ≈ F' 是一个自然同构；每个分量都是 D 的同构，因此是 [Groupoid D] 的一个态射，而 [core_iso] 将其提升为 THERE 的同构。自然性方形被检查两次，每个同构的分量检查一次，[from] 半部分是按照 f⁻¹ 阅读的给定方形。
*)

Lemma CoreMap_respects {C D : Category} (F F' : C ⟶ D) :
  F ≈ F' → CoreMap F ≈ CoreMap F'.
Proof.
  intros [n Hn].
  exists (fun x => core_iso (n x)).
  intros x y f; split; simpl.
  - apply (Hn _ _ (to f)).
  - rewrite (Hn _ _ (from f)).
    now rewrite comp_assoc.
Qed.

Program Definition Core : Cat ⟶ Grpd := {|
  fobj := fun C => ((Groupoid C; core_is_groupoid C) : Grpd);
  fmap := fun _ _ F => (CoreMap F; I)
|}.
(*
 Only [fmap_respects] survives the ambient [cat_simpl]; the two functor
 laws of [Core] are the identity natural isomorphism on both sides and it
 discharges them. 

 --------
 只有 [fmap_respects] 能在环境 [cat_simpl] 中存活；[Core] 的两个函子律在两边都是恒等自然同构，并且它消解它们。
*)
Next Obligation.
  intros F F1 HF; simpl.
  now apply CoreMap_respects.
Qed.

(* * ** The counit: reading an isomorphism as a morphism / * **余单位：将同构视为一个态射 *)

(*
 [ForgetCore C] is the counit of the adjunction below at C, up to `≈` --
 [core_counit_is_ForgetCore] measures that.  It is the inclusion of the
 core back into C: identity on objects, and the [to] component on
 morphisms.  It is not an inclusion in the sense of
 Construction/Subcategory.v -- the core is a subcategory of C only up to
 the choice of inverse carried by each arrow -- and it is faithful
 precisely because an isomorphism is determined by its [to] component
 (Theory/Isomorphism.v's [to_equiv_implies_iso_equiv]). 

 --------
 [ForgetCore C] 是下列伴随在 C 处的余单元，直到 `≈` -- [core_counit_is_ForgetCore] 测量它。它是将核心包含回 C：对对象取恒等，对态射取 [to] 分量。它并不是 Construction/Subcategory.v 意义上的包含——核心只是 C 的一个子范畴，仅仅取决于每个箭头所带的逆的选择——并且它是忠实的，正是因为一个同构由其 [to] 分量（Theory/Isomorphism.v 的 [to_equiv_implies_iso_equiv]）确定。
*)

Program Definition ForgetCore (C : Category) : Groupoid C ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => to f
|}.

Lemma ForgetCore_Faithful (C : Category) : Faithful (ForgetCore C).
Proof.
  construct.
  now apply to_equiv_implies_iso_equiv.
Qed.

(*
   * ** The forward transpose

   A functor out of a groupoid factors through the core.  The factoring
   functor sends f to the isomorphism whose [to] is F f and whose [from] is
   F of the chosen inverse of f; the two inverse laws are the images under
   F of [ginv_right] and [ginv_left]. 

   --------
   * ** 前向转置

   从群族到函子通过核心进行分解。该分解函子将 f 映射为一个同构，其 [to] 是 F f，[from] 是 f 的选定逆元的 F 映射；两个逆元法则是 F 在 [ginv_right] 和 [ginv_left] 下的像。
*)

Program Definition core_lift {G : Category} (HG : IsGroupoid G)
        {C : Category} (F : G ⟶ C) : G ⟶ Groupoid C := {|
  fobj := fun x => F x;
  fmap := fun _ _ f => {| to := fmap[F] f; from := fmap[F] (ginv HG f) |}
|}.
Next Obligation.
  rewrite <- fmap_comp, ginv_right.
  apply fmap_id.
Qed.
Next Obligation.
  rewrite <- fmap_comp, ginv_left.
  apply fmap_id.
Qed.
Next Obligation.
  intros f g Hfg; split; simpl.
  - now rewrite Hfg.
  - (* [ginv_respects] is what carries `≈` under the chosen inverse. / [ginv_respects] 是在所选逆运算下承载 `≈` 的东西。 *)
    now rewrite Hfg.
Qed.
Next Obligation.
  split; simpl.
  - apply fmap_id.
  - rewrite ginv_id.
    apply fmap_id.
Qed.
Next Obligation.
  split; simpl.
  - apply fmap_comp.
  - rewrite ginv_comp.
    apply fmap_comp.
Qed.

(*
 The [from] component of a functor into a core is not free data: it is
 forced to be the [to] component at the inverse arrow.  This is
 [functor_ginv] read at [core_is_groupoid], whose chosen inverse is
 [iso_sym] ([core_ginv_eq] above), taken in its [to] component. 

 --------
 函子进入核心的 [from] 分量不是自由数据：它被迫成为逆箭头处的 [to] 分量。这是在 [core_is_groupoid] 读取的 [functor_ginv]，其选定的逆是 [iso_sym]（上文的 [core_ginv_eq]），取其 [to] 分量。
*)

Lemma core_functor_from {G : Category} (HG : IsGroupoid G) {C : Category}
      (P : G ⟶ Groupoid C) {x y : G} (f : x ~> y) :
  to (fmap[P] (ginv HG f)) ≈ from (fmap[P] f).
Proof.
  exact (fst (functor_ginv HG (core_is_groupoid C) P f)).
Qed.

(** ** The two round trips / ** 两次往返 *)

Lemma core_lift_forget {G : Category} (HG : IsGroupoid G) {C : Category}
      (F : G ⟶ C) : ForgetCore C ◯ core_lift HG F ≈ F.
Proof.
  exists (fun x => @iso_id C (F x)).
  intros x y f; simpl; cat.
Qed.

Lemma forget_core_lift {G : Category} (HG : IsGroupoid G) {C : Category}
      (P : G ⟶ Groupoid C) : core_lift HG (ForgetCore C ◯ P) ≈ P.
Proof.
  exists (fun x => @iso_id (Groupoid C) (P x)).
  intros x y f; split; simpl.
  - cat.
  - rewrite core_functor_from.
    cat.
Qed.

(*
 Transporting the forward transpose along a natural isomorphism of its
 argument.  Same shape as [CoreMap_respects]: the [to] half is the given
 naturality square, the [from] half is that square read at the chosen
 inverse. 

 --------
 沿着其参数的自然同构传输前向转置。形状与 [CoreMap_respects] 相同：[to] 部分是给定的自然性方格，[from] 部分是以选择的逆读取的该方格。
*)

Lemma core_lift_respects {G : Category} (HG : IsGroupoid G) {C : Category}
      (F F' : G ⟶ C) : F ≈ F' → core_lift HG F ≈ core_lift HG F'.
Proof.
  intros [n Hn].
  exists (fun x => core_iso (n x)).
  intros x y f; split; simpl.
  - apply (Hn _ _ f).
  - rewrite (Hn _ _ (ginv HG f)).
    now rewrite comp_assoc.
Qed.

(** ** The adjunction Incl ⊣ Core / ** 附着 Incl ⊣ Core *)

(*
 Riehl §4.1, Example 4.1.15, right-hand half.  The hom-setoid isomorphism
 is [core_lift] one way and post-composition with [ForgetCore] the other,
 and the two naturality squares are the two [to_adj_nat_*] fields
 Theory/Adjunction.v's [Build_Adjunction'] asks for -- the other two are
 derived there. 

 --------
 Riehl §4.1，例 4.1.15，右半部分。Hom-集合等价同构的一条方向是 [core_lift]，另一条方向是与 [ForgetCore] 后合成，而两个自然性方格是 [to_adj_nat_*] 域，Theory/Adjunction.v 的 [Build_Adjunction'] 需要的——另外两个在那里推导出来。
*)

Definition Incl_Core_Adjunction : Adjunction Grpd_Incl Core.
Proof.
  unshelve eapply Build_Adjunction'.
  - intros G C.
    unshelve eapply Isomorphism.Build_Isomorphism.
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun F => (core_lift (`2 G) F; I)).
      * abstract (intros F F' HF; simpl; now apply core_lift_respects).
    + unshelve eapply Sets.Build_SetoidMorphism.
      * exact (fun P => ForgetCore C ◯ `1 P).
      * abstract (intros P Q HPQ; simpl;
                  exact (Compose_respects (ForgetCore C) (ForgetCore C)
                           (Equivalence_Reflexive _) _ _ HPQ)).
    + abstract (intro P; simpl; apply forget_core_lift).
    + abstract (intro F; simpl; exact (core_lift_forget (`2 G) F)).
  - abstract (intros G G' C f g; simpl;
              exists (fun x => @iso_id (Groupoid C) (f (`1 g x)));
              intros x y h; split; simpl;
              [ cat
              | rewrite id_left, id_right;
                apply fmap_respects;
                apply (functor_ginv (`2 G) (`2 G') (`1 g) h) ]).
  - abstract (intros G C C' f g; simpl;
              exists (fun x => @iso_id (Groupoid C') (f (g x)));
              intros x y h; split; simpl; cat).
Defined.

(*
   * ** The universal property, spelled out

   Riehl's phrasing of the same fact: "because functors preserve
   isomorphisms, any functor out of a groupoid factors uniquely through the
   core".  This is the adjunction read at one object, and it is derived FROM
   the adjunction's two round trips rather than proved again -- the
   adjunction is the theorem, this is its restatement.  Uniqueness is up to
   `≈`, which for functors into [Groupoid C] is natural isomorphism, not
   equality: that is the strongest reading [Cat]'s hom-setoid supports. 

   --------
   * ** 通用性质，详细说明

   Riehl 对同一事实的表述：“因为函子保持同构，从群族到其他范畴的任何函子都可以唯一地通过其核心分解。”这是在一个对象上读取的伴随性，它是从伴随的两次往返导出的，而不是再次证明——伴随是定理，这是它的重述。唯一性是指在 `≈` 下，对于进入 [Groupoid C] 的函子，这里意味着自然同构，而不是相等：这是 [Cat] 的同态集支持的最强说法。
*)

Theorem core_factorization {G : Grpd} {C : Category} (F : `1 G ⟶ C) :
  { P : `1 G ⟶ Groupoid C
  & (ForgetCore C ◯ P ≈ F) *
    (∀ Q : `1 G ⟶ Groupoid C, ForgetCore C ◯ Q ≈ F → Q ≈ P) }.
Proof.
  exists (core_lift (`2 G) F).
  split.
  - apply core_lift_forget.
  - intros Q HQ.
    rewrite <- (forget_core_lift (`2 G) Q).
    now apply core_lift_respects.
Qed.

(*
 The counit of the adjunction is the inclusion of the core back into C,
 as it must be: [counit] is the backward transpose of the identity, and
 the backward transpose is post-composition with [ForgetCore]. 

 --------
 挨配的余单位是将核心包含回 C，正如它必须的那样：[counit] 是恒等映射的向后转置，并且向后转置是与 [ForgetCore] 的后合成。
*)

Example core_counit_is_ForgetCore (C : Cat) :
  @counit Cat Grpd Grpd_Incl Core Incl_Core_Adjunction C ≈ ForgetCore C.
Proof. apply fun_equiv_id_right. Qed.

(*
 The unit sends an arrow of a groupoid to itself regarded as an
 isomorphism -- that is exactly [core_lift] applied to the identity
 functor. 

 --------
 该单位将一个群的箭头发送到其自身，视为一个同构——这正是 [core_lift] 应用于恒等函子。
*)

Example core_unit_is_core_lift_Id (G : Grpd) :
  `1 (@unit Cat Grpd Grpd_Incl Core Incl_Core_Adjunction G)
    ≈ core_lift (`2 G) Id.
Proof. reflexivity. Qed.
