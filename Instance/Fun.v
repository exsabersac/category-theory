Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section Fun.

Context {C : Category}.
Context {D : Category}.

(*
 Wikipedia: https://en.wikipedia.org/wiki/Functor_category

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the functor category的来源与用途

   nLab:  https://ncatlab.org/nlab/show/category+of+presheaves
   nLab:  https://ncatlab.org/nlab/show/Yoneda+embedding
   nLab:  https://ncatlab.org/nlab/show/Godement+product
   SEP:   https://plato.stanford.edu/entries/category-theory/
   Paper: Eilenberg, Mac Lane, "General Theory of Natural Equivalences",

   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Fun : Category := {|
  obj     := C ⟶ D;                 (* objects are functors C ⟶ D *)
  hom     := @Transform C D;        (* morphisms are natural transformations *)
  id      := @nat_id C D;           (* identity natural transformation *)
  compose := @nat_compose C D;      (* vertical composition of nat-transes *)

  compose_respects := @nat_compose_respects C D
|}.

End Fun.

Notation "[ C , D ]" := (@Fun C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "[[[ C , D ]]]( F , G )" := ({| carrier   := @hom (@Fun C D) F G
                                       ; is_setoid := @homset (@Fun C D) F G |})
  (at level 90, right associativity, format "[[[ C ,  D ]]]( F , G )") : homset_scope.

(* The 范畴 laws restated directly `[C, D]`: left/right 恒等 and
 associativity vertical 复合, each holding componentwise D. （已译） *)

Corollary nat_id_left C D (F G : C ⟶ D) (N : F ⟹ G) :
  nat_id ∙ N ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_id_right C D (F G : C ⟶ D) (N : F ⟹ G) :
  N ∙ nat_id ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_comp_assoc C D (F G H J : C ⟶ D)
          (M : H ⟹ J) (N : G ⟹ H) (O : F ⟹ G) :
  M ∙ (N ∙ O) ≈[Fun] (M ∙ N) ∙ O.
Proof. unfold nat_compose; simpl; intros; cat. Qed.

(*
   本节说明自然变换、函子、分配律相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma whisker_right_id A B C (F : A ⟶ B) (G : B ⟶ C) : id{Fun} ⊲ F ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_id A B C (F : A ⟶ B) (G : B ⟶ C) : G ⊳ id{Fun} ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_dist A B C (F : A ⟶ B) (G H J : B ⟶ C)
      (η : G ⟹ H) (θ : H ⟹ J) : (θ ⊲ F) ∙ (η ⊲ F) ≈ (θ ∙ η) ⊲ F.
Proof. simpl; intros; cat. Qed.

Lemma whisker_right_dist A B C (F G H : A ⟶ B) (J : B ⟶ C)
      (η : F ⟹ G) (θ : G ⟹ H) : (J ⊳ θ) ∙ (J ⊳ η) ≈ J ⊳ (θ ∙ η).
Proof. simpl; intros; cat. now rewrite fmap_comp. Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition nat_λ {A B} (F : A ⟶ B) : F ◯ Id ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_right.
  - apply fun_id_right_sym.
  - apply fun_id_right_and_sym.
  - apply fun_id_right_sym_and.
Defined.

Definition nat_ρ {A B} (F : A ⟶ B) : Id ◯ F ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_left.
  - apply fun_id_left_sym.
  - apply fun_id_left_and_sym.
  - apply fun_id_left_sym_and.
Defined.

Definition nat_α {A B C D} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
  H ◯ (G ◯ F) ≅[Fun] (H ◯ G) ◯ F.
Proof.
  construct.
  - apply fun_comp_assoc.
  - apply fun_comp_assoc_sym.
  - apply fun_comp_assoc_and_sym.
  - apply fun_comp_assoc_sym_and.
Defined.

Lemma whisker_left_right A B C (F G : A ⟶ B) (H J : B ⟶ C)
      (η : F ⟹ G) (θ : H ⟹ J) :
  (J ⊳ η) ∙ (θ ⊲ F) ≈ (θ ⊲ G) ∙ (H ⊳ η).
Proof. simpl; intros; cat; apply naturality. Qed.

Lemma whisker_flip A B C (F : A ⟶ B) (G : B ⟶ C) :
  (to (nat_λ G) ⊲ F) ∙ to (nat_α F Id G) ≈ G ⊳ (to (nat_ρ F)).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_right_comp
      A B C D (F : A ⟶ B) (G : B ⟶ C) (H J : C ⟶ D) (η : H ⟹ J) :
  to (nat_α F G J) ∙ η ⊲ (G ◯ F) ≈ (η ⊲ G) ⊲ F ∙ to (nat_α F G H).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_left_comp
      A B C D (F G : A ⟶ B) (H : B ⟶ C) (J : C ⟶ D) (η : F ⟹ G) :
  to (nat_α G H J) ∙ J ⊳ (H ⊳ η) ≈ (J ◯ H) ⊳ η ∙ to (nat_α F H J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_assoc
      A B C D (F : A ⟶ B) (G H : B ⟶ C) (J : C ⟶ D) (η : G ⟹ H) :
  to (nat_α F H J) ∙ J ⊳ (η ⊲ F) ≈ (J ⊳ η) ⊲ F ∙ to (nat_α F G J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_nat_α A B C D E (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (J : D ⟶ E) :
  (to (nat_α G H J) ⊲ F ∙ to (nat_α F (H ◯ G) J)) ∙ (J ⊳ (to (nat_α F G H)))
    ≈ to (nat_α F G (J ◯ H)) ∙ to (nat_α (G ◯ F) H J).
Proof. simpl; intros; cat. Qed.

(* nLab: https://ncatlab.org/nlab/show/pointed+endofunctor

 A pointed endofunctor is endofunctor `F : C ⟶ C` equipped natural
 transformation `point : Id ⟹ F` from 恒等 函子.（已译） *)

Class Pointed {C : Category} (F : C ⟶ C) := {
  point : Id ⟹ F                        (* the point η : Id ⟹ F *)
}.

(*
   本节说明自然变换、单子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class WellPointed `{@Pointed C F} := {
  well_pointed :
    (F ⊳ point) ∙ from (nat_λ _) ≈ (point ⊲ F) ∙ from (nat_ρ _)
}.

(*
   nLab: https://ncatlab.org/nlab/show/natural+isomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Natural_transformation#Natural_isomorphism

   本节说明自然变换、函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem Functor_Setoid_Nat_Iso `(F : C ⟶ D) (G : C ⟶ D) :
  F ≅[Fun] G  ↔  F ≈ G.
Proof.
  split; intros; simpl.
  - given (iso : ∀ x : C, F x ≅ G x). {
      intros; isomorphism; simpl; intros.
      - apply X.
      - apply (X⁻¹).
      - abstract (srewrite (iso_to_from X); cat).
      - abstract (srewrite (iso_from_to X); cat).
    }
    exists iso; simpl in *; intros.
    abstract
      (rewrite <- comp_assoc;
       rewrite (naturality[to X]);
       rewrite comp_assoc;
       srewrite (iso_from_to X); cat).
  - destruct X.
    isomorphism; simpl; intros.
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
    + abstract
        (rewrite fmap_id;
         apply iso_to_from).
    + abstract
        (rewrite fmap_id;
         apply iso_from_to).
Defined.

(* The two directions [Functor_Setoid_Nat_Iso] standalone conversions:
 natural 同构 gives 函子 equality, vice versa. （已译） *)

Definition iso_equiv {C D : Category} {f g : C ⟶ D} :
  f ≅[Fun] g → f ≈ g := fst (Functor_Setoid_Nat_Iso _ _).

Definition equiv_iso {C D : Category} {f g : C ⟶ D} :
  f ≈ g → f ≅[Fun] g := snd (Functor_Setoid_Nat_Iso _ _).
