Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Cat.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Theory.Bicategory.Mates.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Cat.Bicategory.Adjunction.
Require Import Category.Instance.Two.
Require Import Category.Instance.One.

Generalizable All Variables.

(* * * The conjugate bijection is the mates bijection at identity bounding cells / * * 共轭双射是在单位边界单元处的伴随双射 *)

(*
 nLab: https://ncatlab.org/nlab/show/mate

 Adjunction/Conjugate.v develops Mac Lane §IV.7 in ordinary-category
 vocabulary, with no bicategorical machinery, so that it applies to
 categories of any size.  This file reconciles that development with
 Theory/Bicategory/Mates.v [mate], of which it is the case where both
 bounding 1-cells are identities.

 Two things have to be arranged.  First, the types differ: an ordinary
 σ : F' ⟹ F is not a 2-cell F' ◯ Id ⟹ Id ◯ F, because the two functor
 records carry different [fmap_respects], [fmap_id] and [fmap_comp]
 fields, which are data here and which record eta cannot identify.  The four padding transformations [Cat_conj_padL],
 [Cat_conj_unpadL], [Cat_conj_padR] and [Cat_conj_unpadR] are the identity
 on components and mediate, and each pair is an isomorphism in Sets
 ([Cat_conj_padL_iso], [Cat_conj_unpadR_iso]).  Second, the bridge is taken
 through the TRANSPARENT Instance/Cat/Bicategory/Adjunction.v
 [Cat_Adjunction_BicatAdjunction], never through that file's
 [Cat_BicatAdjunction_Adjunction_iff], which is Type-valued data closed
 with Qed: nothing about the record it returns reduces, so a consumer
 cannot compute with it.  Through the transparent constructor the unit and
 counit of the reconstructed BicatAdjunction are definitionally the
 caller's own, and [Cat_conj_mate_component] reduces to [reflexivity] after
 Instance/Cat/Bicategory/Adjunction.v [Cat_mate_unfold_raw] and the
 transpose-unit collapse [to_adj_unit].  The neighbouring
 variant [Cat_mate_unfold] is deliberately not used: it phrases the
 transpose through the reconstructed adjunction rather than the caller's
 own, which agree only up to ≈.

 [Cat_mate_inv_unfold_raw] is the dual of [Cat_mate_unfold_raw] and is
 proved here because the tree carries no [mate_inv] component lemma.  It
 is stated at full generality, arbitrary bounding functors, matching its
 donor; its eventual home is beside that donor in the donor file.

 The last section is the boundary that keeps [conjugate_invertible_iff] of
 Adjunction/Conjugate.v from being read too widely.  With the bounding
 1-cells identities the conjugate of a POINTWISE invertible 2-cell is
 pointwise invertible (Adjunction/Conjugate.v's [conjugate_invertible_iff];
 invertibility in the functor categories is deliberately not stated
 there); with a non-identity bounding functor not even that survives, and
 [mate_of_iso_not_invertible] witnesses that rather than asserting it.  The
 bounding functor is [Erase _2] : _2 ⟶ 1, the square is the identity 2-cell
 of Erase _2 ◯ Id, and its mate has a component TwoX ~> TwoY whose inverse
 would be an arrow TwoY ~> TwoX, refuted by Instance/Two.v
 [TwoHom_Y_X_absurd].  Two honest notes on the witness.  The invertible
 2-cell is an identity: that is a natural isomorphism, which is all Riehl
 §4.3(iv) asks for, but a non-identity one is not obtainable here, since
 the hom-category [_2, 1] is a singleton and _2 has no non-identity
 isomorphisms (Instance/Two.v [TwoXY_not_iso]).  And
 [boundary_mate_component] holds by Instance/Two.v [Two_thin], which
 identifies every pair of parallel arrows of _2, so it records the mate's
 TYPE and is not a computation. 

 --------
 nLab:  https://ncatlab.org/nlab/show/mate

 Adjunction/Conjugate.v 在普通范畴的词汇中展开了 Mac Lane §IV.7，没有使用双范畴的工具，因此它适用于任何大小的范畴。这个文件将该发展与 Theory/Bicategory/Mates.v [mate] 调和，其中两端的 1-箭头都是恒等映射的情况。有两件事必须安排。首先，类型不同：一个普通的 σ : F' ⟹ F 不是一个 2-cell F' ◯ Id ⟹ Id ◯ F，因为两个函子记录携带不同的 [fmap_respects]、[fmap_id] 和 [fmap_comp] 字段，这些字段在这里是数据，而记录 eta 无法识别它们。四个填充转换 [Cat_conj_padL]、[Cat_conj_unpadL]、[Cat_conj_padR] 和 [Cat_conj_unpadR] 在组件和中介上是恒等的，并且每对在集合中是同构（[Cat_conj_padL_iso]、[Cat_conj_unpadR_iso]）。其次，桥梁是通过 TRANSPARENT Instance/Cat/Bicategory/Adjunction.v [Cat_Adjunction_BicatAdjunction] 取得的，而不是通过该文件的 [Cat_BicatAdjunction_Adjunction_iff]，它是使用 Qed 封闭的 Type 值数据：它返回的记录没有任何可化简的内容，因此使用者无法对其进行计算。通过透明构造函数，重构的 BicatAdjunction 的单位和余单位在定义上就是调用者自己的，并且 [Cat_conj_mate_component] 在 Instance/Cat/Bicategory/Adjunction.v 之后简化为 [reflexivity] [Cat_mate_unfold_raw]，并且转置单位坍塌 [to_adj_unit]。邻近变体 [Cat_mate_unfold] 是故意不使用的：它表达的是通过重构的伴随而不是调用者自己的转置，这两者仅在 ≈ 下相等。

 [Cat_mate_inv_unfold_raw] 是 [Cat_mate_unfold_raw] 的对偶，并且在此处证明，因为该树没有 [mate_inv] 分量引理。它以完全一般性陈述，任意界定函子，与其提供者相匹配；它最终将位于提供者文件中提供者旁边。最后一节是边界，它防止 Adjunction/Conjugate.v 的 [conjugate_invertible_iff] 被过度读取。通过绑定的 1-胞身份，点对点可逆 2-胞的共轭也是点对点可逆的（Adjunction/Conjugate.v 的 [conjugate_invertible_iff]；函子范畴中的可逆性故意没有在那里说明）；使用非身份的绑定函子，甚至连那一点也无法保留，而 [mate_of_iso_not_invertible] 作为证据而不是断言。绑定函子是 [Erase _2] : _2 ⟶ 1，方格是 Erase _2 ◯ Id 的身份 2-胞，它的对应体有一个分量 TwoX ~> TwoY，其逆将是一个箭头 TwoY ~> TwoX，而 Instance/Two.v 的 [TwoHom_Y_X_absurd] 否定了这一点。关于该证据，有两条实话的注解。可逆的 2-胞是一个恒等：也就是说它是一个自然同构，这正是 Riehl §4.3(iv) 所要求的，但在这里无法得到非恒等的同构，因为同态范畴 [_2, 1] 是单元素的，并且 _2 没有非恒等的同构（Instance/Two.v [TwoXY_not_iso]）。而 [boundary_mate_component] 由 Instance/Two.v [Two_thin] 保持，它识别了 _2 的每一对平行箭头，因此它记录了伴随的类型，并不是一个计算。
*)

(* ---- the missing dual of Cat_mate_unfold_raw ---- / ---- Cat_mate_unfold_raw 的缺失双重 ---- *)

Section MateInvUnfold.

Context {x y x' y' : Category}.
Context {F  : x  ⟶ y } {U  : y  ⟶ x } (Af  : BicatAdjunction (B:=Cat_Bicategory) F  U ).
Context {F' : x' ⟶ y'} {U' : y' ⟶ x'} (Af' : BicatAdjunction (B:=Cat_Bicategory) F' U').
Context {a : x ⟶ x'} {b : y ⟶ y'}.
Context (t : a ◯ U ⟹ U' ◯ b).

Theorem Cat_mate_inv_unfold_raw (Z : x) :
  transform[mate_inv Af Af' t] Z
    ≈ adj_counit (B:=Cat_Bicategory) F' U' (fobj[b] (fobj[F] Z))
        ∘ fmap[F'] (transform[t] (fobj[F] Z)
             ∘ fmap[a] (adj_unit (B:=Cat_Bicategory) F U Z)).
Proof.
  simpl.
  rewrite !fmap_id.
  rewrite ?id_left, ?id_right.
  reflexivity.
Qed.

End MateInvUnfold.

(* ---- padding and agreement ---- / ---- 填充和协议 ---- *)

Section Agreement.

Context {C D : Category}.
Context {F  : D ⟶ C} {U  : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context (A  : F  ⊣ U).
Context (A' : F' ⊣ U').

#[local] Obligation Tactic := idtac.

Program Definition Cat_conj_padL (σ : F' ⟹ F) : (F' ◯ Id) ⟹ (Id ◯ F) :=
  {| transform := fun x => transform[σ] x |}.
Next Obligation. intros σ x y f; apply (naturality σ). Qed.
Next Obligation. intros σ x y f; apply (naturality_sym σ). Qed.

Program Definition Cat_conj_unpadL (s : (F' ◯ Id) ⟹ (Id ◯ F)) : F' ⟹ F :=
  {| transform := fun x => transform[s] x |}.
Next Obligation. intros s x y f; apply (naturality s). Qed.
Next Obligation. intros s x y f; apply (naturality_sym s). Qed.

Program Definition Cat_conj_padR (τ : U ⟹ U') : (Id ◯ U) ⟹ (U' ◯ Id) :=
  {| transform := fun a => transform[τ] a |}.
Next Obligation. intros τ a b g; apply (naturality τ). Qed.
Next Obligation. intros τ a b g; apply (naturality_sym τ). Qed.

Program Definition Cat_conj_unpadR (t : (Id ◯ U) ⟹ (U' ◯ Id)) : U ⟹ U' :=
  {| transform := fun a => transform[t] a |}.
Next Obligation. intros t a b g; apply (naturality t). Qed.
Next Obligation. intros t a b g; apply (naturality_sym t). Qed.

Definition Cat_conj_mate (σ : F' ⟹ F) : U ⟹ U' :=
  Cat_conj_unpadR
    (mate (Cat_Adjunction_BicatAdjunction A)
          (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
          (Cat_conj_padL σ)).

Definition Cat_conj_mate_inv (τ : U ⟹ U') : F' ⟹ F :=
  Cat_conj_unpadL
    (mate_inv (Cat_Adjunction_BicatAdjunction A)
              (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
              (Cat_conj_padR τ)).

Theorem Cat_conj_mate_component (σ : F' ⟹ F) (Z : C) :
  transform[mate (Cat_Adjunction_BicatAdjunction A)
                 (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
                 (Cat_conj_padL σ)] Z
    ≈ transform[conj_mate A A' σ] Z.
Proof.
  rewrite Cat_mate_unfold_raw.
  simpl.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite ?fmap_id, ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem Cat_conj_mate_agrees (σ : F' ⟹ F) :
  Cat_conj_mate σ ≈ conj_mate A A' σ.
Proof. intro Z; apply Cat_conj_mate_component. Qed.

Theorem Cat_conj_mate_inv_component (τ : U ⟹ U') (Z : D) :
  transform[mate_inv (Cat_Adjunction_BicatAdjunction A)
                     (Cat_Adjunction_BicatAdjunction A') (a:=Id[D]) (b:=Id[C])
                     (Cat_conj_padR τ)] Z
    ≈ transform[conj_mate_inv A A' τ] Z.
Proof.
  rewrite Cat_mate_inv_unfold_raw.
  simpl.
  rewrite (from_adj_counit (H:=A')).
  rewrite ?fmap_id, ?id_left, ?id_right.
  reflexivity.
Qed.

Theorem Cat_conj_mate_inv_agrees (τ : U ⟹ U') :
  Cat_conj_mate_inv τ ≈ conj_mate_inv A A' τ.
Proof. intro Z; apply Cat_conj_mate_inv_component. Qed.

(*
 the pad/unpad pair as a Sets isomorphism, so that conjugate_bijection is
 literally mate_iso conjugated by padding 

 --------
 将 pad/unpad 对视为 Sets 的同构，因此 conjugate_bijection 字面上是通过填充共轭的 mate_iso
*)

Program Definition Cat_conj_padL_iso :
  @Isomorphism Sets (conj_dom (F:=F) (F':=F'))
                    (@mate_dom Cat_Bicategory D C D C F F' Id Id) := {|
  to   := {| morphism := Cat_conj_padL |};
  from := {| morphism := Cat_conj_unpadL |}
|}.
Next Obligation. intros s1 s2 Hs x; exact (Hs x). Qed.
Next Obligation. intros s1 s2 Hs x; exact (Hs x). Qed.
Next Obligation. intros s x; reflexivity. Qed.
Next Obligation. intros s x; reflexivity. Qed.

Program Definition Cat_conj_unpadR_iso :
  @Isomorphism Sets (@mate_cod Cat_Bicategory D C D C U U' Id Id)
                    (conj_cod (U:=U) (U':=U')) := {|
  to   := {| morphism := Cat_conj_unpadR |};
  from := {| morphism := Cat_conj_padR |}
|}.
Next Obligation. intros t1 t2 Ht a; exact (Ht a). Qed.
Next Obligation. intros t1 t2 Ht a; exact (Ht a). Qed.
Next Obligation. intros t a; reflexivity. Qed.
Next Obligation. intros t a; reflexivity. Qed.

Theorem conjugate_bijection_is_mate_iso (σ : F' ⟹ F) :
  to (conjugate_bijection A A') σ
    ≈ to Cat_conj_unpadR_iso
        (to (mate_iso (Cat_Adjunction_BicatAdjunction A)
                      (Cat_Adjunction_BicatAdjunction A')
                      (a:=Id[D]) (b:=Id[C]))
            (to Cat_conj_padL_iso σ)).
Proof. intro Z; symmetry; apply Cat_conj_mate_component. Qed.

End Agreement.

(*
 ---- the boundary: with non-identity bounding cells the mate of an
 invertible 2-cell need not be invertible ---- 

 --------
 ---- 边界：对于非恒等边界单元，可逆二元单元的伴随不必可逆 ----
*)

Program Definition ConstY : _1 ⟶ _2 := {|
  fobj := fun _ => TwoY;
  fmap := fun _ _ _ => id
|}.

Definition twoTerm (x : TwoObj) : x ~{_2}~> TwoY :=
  match x with
  | TwoX => TwoXY
  | TwoY => TwoIdY
  end.

Program Definition adjE : Erase _2 ⊣ ConstY :=
  Build_Adjunction' (F:=Erase _2) (U:=ConstY)
    (fun x y => {| to   := {| morphism := fun _ => twoTerm x |}
                 ; from := {| morphism := fun _ => ttt |} |}) _ _.
Next Obligation. now apply Two_thin. Qed.
Next Obligation. now destruct x0. Qed.
Next Obligation. now apply Two_thin. Qed.
Next Obligation. now apply Two_thin. Qed.

Definition BAf  : BicatAdjunction (B:=Cat_Bicategory) (Id[_2]) (Id[_2]) :=
  Cat_Adjunction_BicatAdjunction Adjunction_Id.

Definition BAf' : BicatAdjunction (B:=Cat_Bicategory) (Erase _2) ConstY :=
  Cat_Adjunction_BicatAdjunction adjE.

Definition boundary_square : (Erase _2 ◯ Id[_2]) ⟹ (Erase _2 ◯ Id[_2]) := nat_id.

Program Definition boundary_square_iso :
  @IsIsomorphism (@bicat Cat_Bicategory _2 _1) _ _ boundary_square :=
  {| two_sided_inverse := boundary_square |}.

Definition boundary_mate :=
  mate BAf BAf' (a:=Id[_2]) (b:=Erase _2) boundary_square.

Theorem mate_of_iso_not_invertible :
  @IsIsomorphism (@bicat Cat_Bicategory _2 _2) _ _ boundary_mate → False.
Proof.
  intro H.
  exact (TwoHom_Y_X_absurd
           (transform[two_sided_inverse (IsIsomorphism:=H)] TwoX)).
Qed.

Theorem boundary_mate_component (Z : _2) :
  transform[boundary_mate] Z ≈ twoTerm Z.
Proof.
  unfold boundary_mate.
  rewrite Cat_mate_unfold_raw.
  now apply Two_thin.
Qed.
