Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Natural.Transformation.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The op involution as a functor on Cat

   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   §II.2 (printed p. 33) [maclane:II.2:construction1]: sending each
   category to its opposite and each functor T to T^op is a COVARIANT
   endofunctor of the category of categories, and applying it twice
   is the identity — the duality involution on Cat.
   Riehl, "Category Theory in Context", §1.3 Example 1.3.14(vi)
   [riehl:1.3:example14].
   nLab: https://ncatlab.org/nlab/show/opposite+category

   The pieces have long been in tree — [Opposite], [Opposite_Functor],
   [Opposite_Transform], each with a definitional involution — but no
   bundled [Functor] ever had [Opposite] as its object map.  [Op]
   below is that functor, with [Op_invol : Op ◯ Op ≈ Id], and
   [Op_Strict] the [StrictCat] variant whose laws hold at strict
   functor equality.

   THE 2-CELL CAVEAT, recorded per the issue: oppositization REVERSES
   natural transformations ([Opposite_Transform] sends F ⟹ G to
   G^op ⟹ F^op), so the honest 2-categorical statement is that op is
   a 2-functor Cat^co ⟶ Cat.  The 1-categorical instance below works
   precisely because Cat's hom-equivalence consists of INVERTIBLE
   2-cells ([Functor_Setoid]'s componentwise isomorphisms): a natural
   isomorphism F ≅ G induces F^op ≅ G^op by taking each component's
   INVERSE — [fmap_respects]'s proof does exactly that — whereas a
   non-invertible transformation would come out backwards.

   THE INVOLUTION'S STRENGTH.  (C^op)^op = C holds DEFINITIONALLY at
   an abstract category — record eta makes [eq_refl] typecheck — and
   only the opaque CONSTANT [op_invol] declines to unfold.  The
   identity-on-objects functors [op_invol_to]/[op_invol_from] and the
   packaged [op_invol_iso] are therefore conveniences for downstream
   quotability, not necessities ([iso_id] alone would close
   [Op_invol]); the strict involution [Op_Strict_invol] closes with
   [eq_refl] object components outright.

   RIEHL'S EXERCISE 1.3.v rides the same collapse: the hom-setoid
   bijections (C^op ⟶ D) ≅ (C ⟶ D^op) and (C ⟶ D) ≅ (C^op ⟶ D^op)
   ([op_flip_iso], [op_conjugate_iso]) are oppositization composed
   with the double-op navigation functors, with the 2-cell reversal
   absorbed exactly as in [Op]'s respectfulness. 

   --------
   * * Cat 上的对偶算子作为函子

   Mac Lane，《为工作数学家而写的范畴论》，第2版，
   §II.2（印刷页33） [maclane:II.2:construction1]：将每个范畴映射到它的对偶范畴，将每个函子 T 映射到 T^op，是范畴的范畴上的协变端函子，并且两次应用它是恒等函子——即 Cat 上的对偶 involution。
   Riehl，《上下文中的范畴论》，§1.3 示例 1.3.14(vi)
   [riehl:1.3:example14]。
   nLab：https://ncatlab.org/nlab/show/opposite+category

   这些部分早已存在于树状结构中——[Opposite]，[Opposite_Functor]，
   [Opposite_Transform]，每个都有一个定义性的 involution——但是没有
   打包好的 [Functor] 曾将 [Opposite] 作为它的对象映射。以下的 [Op]
   是那个函子，带有 [Op_invol : Op ◯ Op ≈ Id]，以及
   [Op_Strict] 是 [StrictCat] 变体，其规律在严格的函子等式下成立。2-单元警告，根据该问题记录：取对偶会逆转自然变换（[Opposite_Transform] 将 F ⟹ G 发送为 G^op ⟹ F^op），因此诚实的 2-范畴表述是 op 是一个 2-函子 Cat^co ⟶ Cat。下面的一类范畴实例之所以可行，正是因为 Cat 的 Hom 等价由可逆 2-单元组成（[Functor_Setoid] 的分量同构）：自然同构 F ≅ G 通过取每个分量的逆而诱导出 F^op ≅ G^op — [fmap_respects] 的证明正是如此 — 而非可逆变换则会出现反向。反演的力量。(C^op)^op = C 在抽象范畴上是定义上的成立——记录 eta 使 [eq_refl] 类型检查通过——而且只有不透明的常量 [op_invol] 拒绝展开。因此，将对象保持不变的函子 [op_invol_to] / [op_invol_from] 以及打包的 [op_invol_iso] 只是为下游引用方便，而不是必需的（仅 [iso_id] 就可以闭合 [Op_invol]）；严格反演 [Op_Strict_invol] 则直接用 [eq_refl] 的对象组件闭合。

   RIEHL 的练习 1.3.v 也遵循同样的崩塌：Hom 集合的双射 (C^op ⟶ D) ≅ (C ⟶ D^op) 和 (C ⟶ D) ≅ (C^op ⟶ D^op) ([op_flip_iso], [op_conjugate_iso]) 是通过对偶化结合双反演导航函子建立的，其中 2-胞元的反转完全如 [Op] 的尊重性所吸收。
*)

(* * ** Double-opposite, navigated definitionally / * ** 双重相反，按定义进行导航 *)

Program Definition op_invol_to {C : Category} :
  Opposite (Opposite C) ⟶ C := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros C x y f g Hfg; exact Hfg. Qed.
Next Obligation. intros C x; simpl; reflexivity. Qed.
Next Obligation. intros C x y z f g; simpl; reflexivity. Qed.

Program Definition op_invol_from {C : Category} :
  C ⟶ Opposite (Opposite C) := {|
  fobj := fun x => x;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros C x y f g Hfg; exact Hfg. Qed.
Next Obligation. intros C x; simpl; reflexivity. Qed.
Next Obligation. intros C x y z f g; simpl; reflexivity. Qed.

(** ** The op endofunctor of Cat / ** Cat 的对偶函子 *)

Program Definition Op : Cat ⟶ Cat := {|
  fobj := fun C : Category => Opposite C;
  fmap := fun C D (F : C ⟶ D) => Opposite_Functor F
|}.
Next Obligation.
  (*
 A natural isomorphism F ≅ G yields F^op ≅ G^op with INVERSE
 components — the 2-cell reversal, tamed by invertibility: the
 coherence square is the original one read at the flipped arrow. 

 --------
 自然同构 F ≅ G 会产生 F^op ≅ G^op，且具有逆组件——2-胞逆转，由可逆性约束：相干方形就是将原来的方形按照反向箭头读取的结果。
*)
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intro C; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D E F G; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

(** ** The involution / ** 内卷 *)

(*
 The component at C: an isomorphism of categories (in Cat's
 equivalence sense) between (C^op)^op and C, with identity round
 trips. 

 --------
 在 C 处的分量：在（Cat 的等价意义下）在 (C^op)^op 和 C 之间的范畴同构，具有恒等往返。
*)
Program Definition op_invol_iso {C : Category} :
  @Isomorphism Cat (Opposite (Opposite C)) C := {|
  to := op_invol_to;
  from := op_invol_from
|}.
Next Obligation.
  intro C.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intro C.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

Theorem Op_invol : Op ◯ Op ≈ Id[Cat].
Proof.
  exists (fun C : Category => op_invol_iso).
  intros C D F; simpl.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

(** ** The strict variant / ** 严格变体 *)

(*
 The StrictCat variant: same maps, laws at strict functor
 equality. 

 --------
 StrictCat 变体：相同的映射，在严格函子相等下的法律。
*)
Program Definition Op_Strict : StrictCat ⟶ StrictCat := {|
  fobj := fun C : Category => Opposite C;
  fmap := fun C D (F : C ⟶ D) => Opposite_Functor F
|}.
Next Obligation.
  intros C D F G [e He].
  exists e.
  intros x y f; simpl.
  (*
 The op reading swaps which side each transport lands on; freeing
 the two arrow terms lets the object equalities collapse, after
 which the original coherence at the flipped arrow is literal. 

 --------
 操作读取会交换每个传输着陆的侧面；释放两个箭头项可以使对象等式消解，之后在翻转的箭头上的原始一致性是字面的。
*)
  pose proof (He y x f) as K; revert K.
  generalize (fmap[G] f).
  generalize (fmap[F] f).
  destruct (e x), (e y); simpl.
  intros h g K; exact K.
Qed.
Next Obligation.
  intro C.
  exists (fun x => eq_refl).
  intros x y f; simpl; reflexivity.
Qed.
Next Obligation.
  intros C D E F G.
  exists (fun x => eq_refl).
  intros x y f; simpl; reflexivity.
Qed.

(*
 The strict involution, with eq_refl object components — the record
 eta of Category makes the double opposite definitional. 

 --------
 严格的自反变换，带有 eq_refl 对象组件——Category 的记录 eta 使双重对立成为定义性的。
*)
Theorem Op_Strict_invol :
  @equiv _ (@Functor_StrictEq_Setoid StrictCat StrictCat)
         (Op_Strict ◯ Op_Strict) (Id[StrictCat]).
Proof.
  exists (fun C : Category => eq_refl).
  intros C D F.
  unfold Logic.transport, Logic.transport_r; simpl.
  exists (fun x => eq_refl).
  intros x y f; simpl.
  reflexivity.
Qed.

(* * ** Riehl's Exercise 1.3.v: the hom-setoid bijections / * ** Riehl 的练习 1.3.v：同态集合双射 *)

Program Definition op_flip_iso (C D : Category) :
  @Isomorphism Sets
    {| carrier := Opposite C ⟶ D ; is_setoid := @Functor_Setoid _ _ |}
    {| carrier := C ⟶ Opposite D ; is_setoid := @Functor_Setoid _ _ |} := {|
  to := {| morphism := fun F => Opposite_Functor F ◯ op_invol_from |};
  from := {| morphism := fun G => op_invol_to ◯ Opposite_Functor G |}
|}.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D G.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D F.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.

Program Definition op_conjugate_iso (C D : Category) :
  @Isomorphism Sets
    {| carrier := C ⟶ D ; is_setoid := @Functor_Setoid _ _ |}
    {| carrier := Opposite C ⟶ Opposite D
     ; is_setoid := @Functor_Setoid _ _ |} := {|
  to := {| morphism := fun F => Opposite_Functor F |};
  from := {| morphism := fun G =>
               op_invol_to ◯ Opposite_Functor G ◯ op_invol_from |}
|}.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D F G [iso Hiso].
  exists (fun x => Isomorphism_Opposite (iso x)).
  intros x y f; simpl.
  first [ exact (Hiso y x f)
        | rewrite comp_assoc; exact (Hiso y x f)
        | rewrite <- comp_assoc; exact (Hiso y x f) ].
Qed.
Next Obligation.
  intros C D G.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
Next Obligation.
  intros C D F.
  exists (fun x => iso_id).
  intros a b f; simpl; cat.
Qed.
