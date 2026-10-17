Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.

(*
   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Theory.Monad.
Require Import Category.Construction.FAlg.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * The covariant and contravariant power-set functors on [Sets] *)

(*
   nLab:      https://ncatlab.org/nlab/show/power+set
   Wikipedia: https://en.wikipedia.org/wiki/Power_set

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** Universe placement, stated precisely *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The predicate setoid [P X] *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Powerset_obj@{o so} (X : SetoidObject@{o o}) :
  SetoidObject@{so so} :=
  {| carrier   := SetoidMorphism@{so so so} (Setoid_Lift@{o so} X)
                                            PropSetoid@{o so}
   ; is_setoid := @SetoidMorphism_Setoid@{so so so}
                    (Setoid_Lift@{o so} X) PropSetoid@{o so} |}.

(* Membership is application of the predicate; this lemma is the [≈]-respect
   of a subset, in the form the proofs below want it. *)
Lemma Powerset_mem_respects@{o so} {X : SetoidObject@{o o}}
  (S : carrier (Powerset_obj@{o so} X)) {x y : carrier X}
  (H : @equiv _ (is_setoid X) x y) : S x → S y.
Proof. exact (fst (@proper_morphism _ _ _ _ S x y H)). Defined.

(* ------------------------------------------------------------------------ *)
(** ** The lifting functor [Sets_Lift] *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Sets_Lift@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       Setoid_Lift@{o so} (@SetoidMorphism_Lift@{o so}) _ _ _).
  - (* fmap respects ≈: pointwise agreement is unchanged by the lift *)
    intros X Y f g H a; exact (H a).
  - (* fmap_id *)
    intros X a; reflexivity.
  - (* fmap_comp *)
    intros X Y Z f g a; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The direct image, and the covariant functor *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Powerset_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_obj@{o so} X)) :
  carrier (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ y, ∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y) _).
  intros y y' Hyy'; split; intros [x [Hx Hfx]]; exists x; split.
  - exact Hx.
  - now transitivity y.
  - exact Hx.
  - transitivity y'; [exact Hfx | now symmetry].
Defined.

(* Taking direct images is itself a setoid map on subsets: equivalent
   subsets have equivalent images. *)
Definition Powerset_map@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_obj@{o so} Y)) (is_setoid (Powerset_obj@{o so} Y))
       (λ S, Powerset_image@{o so} f S) _).
  intros S T HST y; split; intros [x [Hx Hfx]]; exists x; split.
  - exact (fst (HST x) Hx).
  - exact Hfx.
  - exact (snd (HST x) Hx).
  - exact Hfx.
Defined.

Lemma Powerset_map_respects@{o so} {X Y : SetoidObject@{o o}}
  (f g : X ~{Sets@{o so}}~> Y) (H : f ≈ g) :
  Powerset_map@{o so} f ≈ Powerset_map@{o so} g.
Proof.
  intros S y; split; intros [x [Hx Hfx]]; exists x; split.
  - exact Hx.
  - transitivity (f x); [ now symmetry | exact Hfx ].
  - exact Hx.
  - transitivity (g x); [ exact (H x) | exact Hfx ].
Qed.

(* Functoriality.  [fmap_id]: the direct image along the identity of [S] is
   the [≈]-saturation of [S], which is [S] itself because subsets respect
   [≈]. *)
Lemma Powerset_map_id@{o so} {X : SetoidObject@{o o}} :
  Powerset_map@{o so} (@id Sets@{o so} X) ≈ @setoid_morphism_id@{so so so}
                                              (Powerset_obj@{o so} X).
Proof.
  intros S y; split.
  - intros [x [Hx Hxy]]; exact (Powerset_mem_respects S Hxy Hx).
  - intro Hy; exists y; split; [ exact Hy | reflexivity ].
Qed.

(* [fmap_comp]: the image along a composite is the image of the image; the
   intermediate witness is [g x]. *)
Lemma Powerset_map_comp@{o so} {X Y Z : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> Z) (g : X ~{Sets@{o so}}~> Y) :
  Powerset_map@{o so} (f ∘[Sets@{o so}] g)
    ≈ @setoid_morphism_compose@{so so so}
        (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y) (Powerset_obj@{o so} Z)
        (Powerset_map@{o so} f) (Powerset_map@{o so} g).
Proof.
  intros S z; split.
  - intros [x [Hx Hfg]].
    exists (g x); split.
    + exists x; split; [ exact Hx | reflexivity ].
    + exact Hfg.
  - intros [y [[x [Hx Hgy]] Hfz]].
    exists x; split.
    + exact Hx.
    + transitivity (f y); [ exact (proper_morphism f _ _ Hgy) | exact Hfz ].
Qed.

(* The covariant power-set functor, at the cross-universe type argued for in
   the header. *)
Definition Powerset@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       Powerset_obj@{o so} (@Powerset_map@{o so}) _ _ _).
  - intros X Y f g H; exact (Powerset_map_respects@{o so} f g H).
  - intros X; exact (@Powerset_map_id@{o so} X).
  - intros X Y Z f g; exact (@Powerset_map_comp@{o so} X Y Z f g).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_fmap_image@{o so sso} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_obj@{o so} X)) :
  fmap[Powerset@{o so sso}] f S = Powerset_image@{o so} f S.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The inverse image, and the contravariant functor *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Powerset_preimage@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_obj@{o so} X)) :
  carrier (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ y, T (f y)) _).
  intros y y' Hyy'.
  exact (@proper_morphism _ _ _ _ T (f y) (f y')
           (proper_morphism f _ _ Hyy')).
Defined.

Definition Powerset_comap@{o so} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_obj@{o so} Y)) (is_setoid (Powerset_obj@{o so} Y))
       (λ T, Powerset_preimage@{o so} f T) _).
  intros T U HTU y; exact (HTU (f y)).
Defined.

Lemma Powerset_comap_respects@{o so} {X Y : SetoidObject@{o o}}
  (f g : Y ~{Sets@{o so}}~> X) (H : f ≈ g) :
  Powerset_comap@{o so} f ≈ Powerset_comap@{o so} g.
Proof.
  intros T y; split; intro Ht.
  - exact (Powerset_mem_respects T (H y) Ht).
  - exact (Powerset_mem_respects T (symmetry (H y)) Ht).
Qed.

Lemma Powerset_comap_id@{o so} {X : SetoidObject@{o o}} :
  Powerset_comap@{o so} (@id Sets@{o so} X)
    ≈ @setoid_morphism_id@{so so so} (Powerset_obj@{o so} X).
Proof. intros T x; split; intro Ht; exact Ht. Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_comap_comp@{o so} {X Y Z : SetoidObject@{o o}}
  (f : Z ~{Sets@{o so}}~> Y) (g : Y ~{Sets@{o so}}~> X) :
  Powerset_comap@{o so} (g ∘[Sets@{o so}] f)
    ≈ @setoid_morphism_compose@{so so so}
        (Powerset_obj@{o so} X) (Powerset_obj@{o so} Y) (Powerset_obj@{o so} Z)
        (Powerset_comap@{o so} f) (Powerset_comap@{o so} g).
Proof. intros T z; split; intro Ht; exact Ht. Qed.

(* The contravariant power-set functor. *)
Definition Powerset_op@{o so sso} :
  @Functor (Sets@{o so})^op Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor (Sets@{o so})^op Sets@{so sso}
       Powerset_obj@{o so}
       (fun (X Y : SetoidObject@{o o}) (f : Y ~{Sets@{o so}}~> X) =>
          Powerset_comap@{o so} f) _ _ _).
  - intros X Y f g H; exact (Powerset_comap_respects@{o so} f g H).
  - intros X; exact (@Powerset_comap_id@{o so} X).
  - intros X Y Z f g; exact (@Powerset_comap_comp@{o so} X Y Z f g).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_op_fmap_preimage@{o so sso} {X Y : SetoidObject@{o o}}
  (f : Y ~{Sets@{o so}}~> X) (T : carrier (Powerset_obj@{o so} X)) :
  fmap[Powerset_op@{o so sso}] (f : X ~{(Sets@{o so})^op}~> Y) T
    = Powerset_preimage@{o so} f T.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The singleton transformation *)

(* The subset {a}, as a predicate: [λ x, a ≈ x]. *)
Definition Powerset_singleton_pred@{o so} {X : SetoidObject@{o o}}
  (a : carrier X) : carrier (Powerset_obj@{o so} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ x, @equiv _ (is_setoid X) a x) _).
  intros x x' Hxx'; split; intro H.
  - now transitivity x.
  - transitivity x'; [ exact H | now symmetry ].
Defined.

Definition Powerset_singleton_map@{o so} {X : SetoidObject@{o o}} :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} X) (Powerset_obj@{o so} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (λ a, Powerset_singleton_pred@{o so} a) _).
  intros a a' Haa' x.
  (*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  assert (Ha : @equiv _ (is_setoid X) a a') by exact Haa'.
  split; intro H.
  - exact (transitivity (symmetry Ha) H).
  - exact (transitivity Ha H).
Defined.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_image_singleton@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a : carrier X) :
  Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
    ≈ Powerset_singleton_pred@{o so} (f a).
Proof.
  intro y; simpl; split.
  - intros [x [Hax Hfy]].
    transitivity (f x); [ exact (proper_morphism f _ _ Hax) | exact Hfy ].
  - intro Hfa; exists a; split; [ reflexivity | exact Hfa ].
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_Singleton@{o so sso} :
  @Transform Sets@{o so} Sets@{so sso} Sets_Lift@{o so sso} Powerset@{o so sso}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{so sso}
       Sets_Lift@{o so sso} Powerset@{o so sso}
       (fun X => @Powerset_singleton_map@{o so} X) _).
  intros X Y f a.
  exact (Powerset_image_singleton@{o so} f a).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity: the direct image is not a relabelling *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Distinct points have distinct singletons, and equivalent points have
   equivalent ones: [Powerset_singleton_pred] is injective up to [≈].  This
   is what turns a statement about points into a statement about subsets. *)
Lemma Powerset_singleton_faithful@{o so} {X : SetoidObject@{o o}}
  (a b : carrier X) :
  Powerset_singleton_pred@{o so} a ≈ Powerset_singleton_pred@{o so} b
    ↔ @equiv _ (is_setoid X) a b.
Proof.
  split.
  - intro H.
    exact (symmetry (fst (H a) (reflexivity a))).
  - intros Hab x; simpl; split; intro H.
    + transitivity a; [ now symmetry | exact H ].
    + transitivity b; [ exact Hab | exact H ].
Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Powerset_injective_reflects@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y)
  (Hinj : ∀ a b : carrier X, f a ≈ f b → @equiv _ (is_setoid X) a b)
  (S T : carrier (Powerset_obj@{o so} X))
  (H : Powerset_image@{o so} f S ≈ Powerset_image@{o so} f T) : S ≈ T.
Proof.
  intro x; split; intro Hx.
  - destruct (fst (H (f x)) (existT _ x (Hx, reflexivity (f x))))
      as [x' [Hx' Hfx']].
    exact (Powerset_mem_respects T (Hinj x' x Hfx') Hx').
  - destruct (snd (H (f x)) (existT _ x (Hx, reflexivity (f x))))
      as [x' [Hx' Hfx']].
    exact (Powerset_mem_respects S (Hinj x' x Hfx') Hx').
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Powerset_merges_fibre@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a b : carrier X) :
  Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
    ≈ Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)
  ↔ f a ≈ f b.
Proof.
  split.
  - intro H.
    apply (fst (Powerset_singleton_faithful@{o so} (f a) (f b))).
    transitivity (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)).
    { symmetry; exact (Powerset_image_singleton@{o so} f a). }
    transitivity (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)).
    { exact H. }
    exact (Powerset_image_singleton@{o so} f b).
  - intro H.
    transitivity (Powerset_singleton_pred@{o so} (f a)).
    { exact (Powerset_image_singleton@{o so} f a). }
    transitivity (Powerset_singleton_pred@{o so} (f b)).
    { exact (snd (Powerset_singleton_faithful@{o so} (f a) (f b)) H). }
    symmetry.
    exact (Powerset_image_singleton@{o so} f b).
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Powerset_not_injective_on_subsets@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (a b : carrier X)
  (Hab : @equiv _ (is_setoid X) a b → False) (Hf : f a ≈ f b) :
  (Powerset_singleton_pred@{o so} a ≈ Powerset_singleton_pred@{o so} b
     → False)
  ∧ (Powerset_image@{o so} f (Powerset_singleton_pred@{o so} a)
       ≈ Powerset_image@{o so} f (Powerset_singleton_pred@{o so} b)).
Proof.
  split.
  - intro H.
    exact (Hab (fst (Powerset_singleton_faithful@{o so} a b) H)).
  - exact (snd (Powerset_merges_fibre@{o so} f a b) Hf).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Sanity: [FinSet]-sized computations *)

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition fin_setoid_object (n : nat) : SetoidObject :=
  {| carrier := Fin.t n ; is_setoid := Fin_Setoid |}.

(* Every function between discrete setoids is a setoid map: [≈] is [=] on
   both sides, so respectfulness is [f_equal]. *)
Definition fin_map {m n : nat} (f : Fin.t m → Fin.t n) :
  fin_setoid_object m ~{Sets}~> fin_setoid_object n :=
  @Build_SetoidMorphism _ (is_setoid (fin_setoid_object m))
                        _ (is_setoid (fin_setoid_object n))
                        f (fun x y H => f_equal f H).

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin32 (i : Fin.t 3) : Fin.t 2 :=
  Fin.caseS' i (fun _ => Fin.t 2) Fin.F1
    (fun j => Fin.caseS' j (fun _ => Fin.t 2) Fin.F1
                (fun _ => Fin.FS Fin.F1)).

Example fin32_at_0 : fin32 Fin.F1 = Fin.F1 := eq_refl.
Example fin32_at_1 : fin32 (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example fin32_at_2 : fin32 (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

(* The three elements of [Fin.t 3] used below are pairwise distinct, and so
   are the two elements of [Fin.t 2]: the carriers are not collapsing. *)
Lemma fin3_0_ne_1 : @Fin.F1 2 = Fin.FS Fin.F1 → False.
Proof. discriminate. Qed.

Lemma fin2_0_ne_1 : @Fin.F1 1 = Fin.FS Fin.F1 → False.
Proof. discriminate. Qed.

(* WITNESS 1 (merging along a non-injective map).  {0} and {1} are distinct
   subsets of the three-element set... *)
Lemma fin32_singletons_distinct :
  Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 3) (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  exact (fin3_0_ne_1 (fst (Powerset_singleton_faithful _ _) H)).
Qed.

(* ... but [fmap[Powerset] fin32] sends them to the same subset {0}. *)
Lemma fin32_images_merge :
  fmap[Powerset] (fin_map fin32)
      (Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1)
    ≈ fmap[Powerset] (fin_map fin32)
        (Powerset_singleton_pred (X:=fin_setoid_object 3) (Fin.FS Fin.F1)).
Proof.
  exact (snd (Powerset_merges_fibre (fin_map fin32) Fin.F1 (Fin.FS Fin.F1))
             eq_refl).
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fin32_third_image_distinct :
  fmap[Powerset] (fin_map fin32)
      (Powerset_singleton_pred (X:=fin_setoid_object 3) Fin.F1)
    ≈ fmap[Powerset] (fin_map fin32)
        (Powerset_singleton_pred (X:=fin_setoid_object 3)
           (Fin.FS (Fin.FS Fin.F1)))
  → False.
Proof.
  intro H.
  exact (fin2_0_ne_1
           (fst (Powerset_merges_fibre (fin_map fin32) Fin.F1
                   (Fin.FS (Fin.FS Fin.F1))) H)).
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin3_sub01 : carrier (Powerset_obj (fin_setoid_object 3)).
Proof.
  unshelve refine {| morphism := fun i : Fin.t 3 =>
                       (i = Fin.F1) ∨ (i = Fin.FS Fin.F1) |}.
  intros x y ->; split; intro H; exact H.
Defined.

Lemma fin32_image_sub01 :
  fmap[Powerset] (fin_map fin32) fin3_sub01
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1.
Proof.
  intro y; split.
  - intros [i [Hi Hfi]].
    destruct Hi as [H0 | H1].
    + rewrite <- Hfi, H0; reflexivity.
    + rewrite <- Hfi, H1; reflexivity.
  - intro Hy.
    exists Fin.F1; split.
    + exact (Datatypes.inl eq_refl).
    + exact Hy.
Qed.

Lemma fin32_image_sub01_proper_subset :
  fmap[Powerset] (fin_map fin32) fin3_sub01 (Fin.FS Fin.F1) → False.
Proof.
  intro H.
  exact (fin2_0_ne_1 (fst (fin32_image_sub01 (Fin.FS Fin.F1)) H)).
Qed.

(* [fin3_sub01] really does have exactly two elements, and they are
   distinct: nothing below rests on it accidentally collapsing. *)
Lemma fin3_sub01_has_0 : fin3_sub01 Fin.F1.
Proof. exact (Datatypes.inl eq_refl). Qed.

Lemma fin3_sub01_has_1 : fin3_sub01 (Fin.FS Fin.F1).
Proof. exact (Datatypes.inr eq_refl). Qed.

Lemma fin3_sub01_lacks_2 : fin3_sub01 (Fin.FS (Fin.FS Fin.F1)) → False.
Proof. intros [H | H]; discriminate. Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fin3_sub01_not_singleton (a : Fin.t 3) :
  fin3_sub01 ≈ Powerset_singleton_pred (X:=fin_setoid_object 3) a → False.
Proof.
  intro H.
  assert (H0 : a = Fin.F1) by exact (fst (H Fin.F1) fin3_sub01_has_0).
  assert (H1 : a = Fin.FS Fin.F1)
    by exact (fst (H (Fin.FS Fin.F1)) fin3_sub01_has_1).
  exact (fin3_0_ne_1 (eq_trans (eq_sym H0) H1)).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin3_case (P : Fin.t 3 → Type)
  (H0 : P Fin.F1) (H1 : P (Fin.FS Fin.F1))
  (H2 : P (Fin.FS (Fin.FS Fin.F1))) : ∀ i : Fin.t 3, P i.
Proof.
  intro i.
  apply (Fin.caseS' i P H0); intro j.
  apply (Fin.caseS' j (fun j => P (Fin.FS j)) H1); intro k.
  apply (Fin.caseS' k (fun k => P (Fin.FS (Fin.FS k))) H2); intro l.
  exact (Fin.case0 (fun l => P (Fin.FS (Fin.FS (Fin.FS l)))) l).
Defined.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fin32_preimage_sng0 :
  fmap[Powerset_op] (fin_map fin32 : fin_setoid_object 2
                       ~{(Sets)^op}~> fin_setoid_object 3)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1)
    ≈ fin3_sub01.
Proof.
  refine (fin3_case
            (fun i => fmap[Powerset_op] (fin_map fin32 : fin_setoid_object 2
                          ~{(Sets)^op}~> fin_setoid_object 3)
                        (Powerset_singleton_pred
                           (X:=fin_setoid_object 2) Fin.F1) i
                      ↔ fin3_sub01 i) _ _ _).
  - split; intro H.
    + exact (Datatypes.inl eq_refl).
    + exact eq_refl.
  - split; intro H.
    + exact (Datatypes.inr eq_refl).
    + exact eq_refl.
  - split; intro H.
    + discriminate H.
    + destruct H; discriminate.
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fin_const0 : Fin.t 2 → Fin.t 2 := fun _ => Fin.F1.

Lemma fin_const0_image :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) Fin.F1.
Proof.
  exact (Powerset_image_singleton (fin_map fin_const0) (Fin.FS Fin.F1)).
Qed.

(* The direct image MOVES the subset {1} to {0}; the identity functor's
   action would have left it where it was. *)
Lemma Powerset_image_moves :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  apply fin2_0_ne_1.
  apply (fst (Powerset_singleton_faithful
                (X:=fin_setoid_object 2) Fin.F1 (Fin.FS Fin.F1))).
  transitivity (fmap[Powerset] (fin_map fin_const0)
                  (Powerset_singleton_pred (X:=fin_setoid_object 2)
                     (Fin.FS Fin.F1))).
  { symmetry; exact fin_const0_image. }
  exact H.
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fin_const0_preimage_empty (y : Fin.t 2) :
  fmap[Powerset_op] (fin_map fin_const0 : fin_setoid_object 2
                       ~{(Sets)^op}~> fin_setoid_object 2)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1)) y
  → False.
Proof. intro H; exact (fin2_0_ne_1 (eq_sym H)). Qed.

Lemma fin_const0_image_inhabited :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
      Fin.F1.
Proof. exact (snd (fin_const0_image Fin.F1) (reflexivity _)). Qed.

Theorem Powerset_direct_ne_inverse :
  fmap[Powerset] (fin_map fin_const0)
      (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
    ≈ fmap[Powerset_op] (fin_map fin_const0 : fin_setoid_object 2
                           ~{(Sets)^op}~> fin_setoid_object 2)
        (Powerset_singleton_pred (X:=fin_setoid_object 2) (Fin.FS Fin.F1))
  → False.
Proof.
  intro H.
  exact (fin_const0_preimage_empty Fin.F1
           (fst (H Fin.F1) fin_const0_image_inhabited)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The second carrier: [Prop]-valued subsets, and a genuine endofunctor *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Propositional truncation, impredicatively.  [∀ Q : Prop, (A → Q) → Q] is
   a [Prop] whatever universe [A] lives in, which is exactly what keeps the
   power set at level [o]. *)
Definition Powerset_squash@{o} (A : Type@{o}) : Prop := ∀ Q : Prop, (A → Q) → Q.

Definition Powerset_squash_intro@{o} {A : Type@{o}} (a : A) :
  Powerset_squash@{o} A := fun Q k => k a.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_Prop_truth_equiv@{o} : crelation@{o o} Prop :=
  λ P Q : Prop, (P → Q) /\ (Q → P).

Lemma Powerset_Prop_truth_equivalence@{o} :
  Equivalence@{o o} Powerset_Prop_truth_equiv@{o}.
Proof.
  unfold Powerset_Prop_truth_equiv; constructor.
  - intro P; split; intro H; exact H.
  - intros P Q [HPQ HQP]; split; assumption.
  - intros P Q R [HPQ HQP] [HQR HRQ]; split; intro H; auto.
Qed.

Definition Powerset_Prop_truth@{o} : SetoidObject@{o o} :=
  {| carrier   := Prop
   ; is_setoid := {| equiv        := Powerset_Prop_truth_equiv@{o}
                   ; setoid_equiv := Powerset_Prop_truth_equivalence@{o} |} |}.

(* A truncated subset of [X] is a [≈]-respecting [Prop]-valued predicate —
   that is, a [SetoidMorphism] into [Powerset_Prop_truth], compared
   pointwise by [SetoidMorphism_Setoid], exactly as [Powerset_obj] is
   compared.  No lift appears: domain and codomain are both at [o]. *)
Definition Powerset_Prop_obj@{o} (X : SetoidObject@{o o}) : SetoidObject@{o o} :=
  {| carrier   := SetoidMorphism@{o o o} X Powerset_Prop_truth@{o}
   ; is_setoid := @SetoidMorphism_Setoid@{o o o} X Powerset_Prop_truth@{o} |}.

(* The direct image, truncated: [y] belongs to [f S] when SOME [x ∈ S] has
   [f x ≈ y], with the "some" squashed. *)
Definition Powerset_Prop_image@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier Y) (is_setoid Y) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ y, Powerset_squash@{o}
               (∃ x : carrier X, S x ∧ @equiv _ (is_setoid Y) (f x) y)) _).
  intros y y' Hyy'; split; intros H Q k; apply H; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hx.
  - now transitivity y.
  - transitivity y'; [ exact Hfx | now symmetry ].
Defined.

(* Equivalent subsets have equivalent images. *)
Definition Powerset_Prop_map@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) :
  SetoidMorphism@{o o o} (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (carrier (Powerset_Prop_obj@{o} Y)) (is_setoid (Powerset_Prop_obj@{o} Y))
       (λ S, Powerset_Prop_image@{o} f S) _).
  intros S T HST y; split; intros H Q k; apply H; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hfx.
  - exact (proj1 (HST x) Hx).
  - exact (proj2 (HST x) Hx).
Defined.

(* [fmap_respects]. *)
Lemma Powerset_Prop_map_respects@{o} {X Y : SetoidObject@{o o}}
  (f g : SetoidMorphism@{o o o} X Y) (H : f ≈ g) :
  Powerset_Prop_map@{o} f ≈ Powerset_Prop_map@{o} g.
Proof.
  intros S y; split; intros Hs Q k; hnf in Hs; apply Hs; intros [x [Hx Hfx]];
    apply k; exists x; split; try exact Hx.
  - transitivity (f x); [ now symmetry | exact Hfx ].
  - transitivity (g x); [ exact (H x) | exact Hfx ].
Qed.

(* [fmap_id]: as for the proof-relevant carrier, the image of [S] along the
   identity is the [≈]-saturation of [S], which is [S] because subsets
   respect [≈]. *)
Lemma Powerset_Prop_map_id@{o} {X : SetoidObject@{o o}} :
  Powerset_Prop_map@{o} (@setoid_morphism_id@{o o o} X)
    ≈ @setoid_morphism_id@{o o o} (Powerset_Prop_obj@{o} X).
Proof.
  intros S y; split; intro H.
  - hnf in H; apply H; intros [x [Hx Hxy]].
    exact (proj1 (@proper_morphism _ _ _ _ S x y Hxy) Hx).
  - exact (Powerset_squash_intro@{o} (existT _ y (H, reflexivity y))).
Qed.

(* [fmap_comp]: the intermediate witness is [g x], and the truncation goes
   through because the goal is a [Prop] at every step. *)
Lemma Powerset_Prop_map_comp@{o} {X Y Z : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} Y Z) (g : SetoidMorphism@{o o o} X Y) :
  Powerset_Prop_map@{o} (@setoid_morphism_compose@{o o o} X Y Z f g)
    ≈ @setoid_morphism_compose@{o o o}
        (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
        (Powerset_Prop_obj@{o} Z)
        (Powerset_Prop_map@{o} f) (Powerset_Prop_map@{o} g).
Proof.
  intros S z; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hx Hfg]]; apply k; exists (g x); split.
    + exact (Powerset_squash_intro@{o} (existT _ x (Hx, reflexivity (g x)))).
    + exact Hfg.
  - intros [y [Hy Hfz]]; hnf in Hy; apply Hy; intros [x [Hx Hgy]]; apply k;
      exists x; split; [ exact Hx | ].
    transitivity (f y); [ exact (proper_morphism f _ _ Hgy) | exact Hfz ].
Qed.

(* THE ENDOFUNCTOR.  Domain and codomain are the same category, at the same
   universes — which is the whole point of this section. *)
Definition Powerset_Prop@{o so} : @Functor Sets@{o so} Sets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{o so}
       Powerset_Prop_obj@{o} (@Powerset_Prop_map@{o}) _ _ _).
  - intros X Y f g H; exact (Powerset_Prop_map_respects@{o} f g H).
  - intros X; exact (@Powerset_Prop_map_id@{o} X).
  - intros X Y Z f g; exact (@Powerset_Prop_map_comp@{o} X Y Z f g).
Defined.

(* As with [Powerset_fmap_image]: the two sides are the very same term, so
   the equality is Leibniz (=) rather than ≈, on the Functor/Bifunctor.v
   precedent. *)
Lemma Powerset_Prop_fmap_image@{o so} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) (S : carrier (Powerset_Prop_obj@{o} X)) :
  fmap[Powerset_Prop@{o so}] f S = Powerset_Prop_image@{o} f S.
Proof. reflexivity. Qed.

(* The truncated singleton {a}: [λ x, Powerset_squash (a ≈ x)]. *)
Definition Powerset_Prop_singleton_pred@{o} {X : SetoidObject@{o o}}
  (a : carrier X) : carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, Powerset_squash@{o} (@equiv _ (is_setoid X) a x)) _).
  intros x x' Hxx'; split; intros H Q k; apply H; intro Ha; apply k.
  - now transitivity x.
  - transitivity x'; [ exact Ha | now symmetry ].
Defined.

Definition Powerset_Prop_singleton_map@{o} {X : SetoidObject@{o o}} :
  SetoidMorphism@{o o o} X (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X)
       (carrier (Powerset_Prop_obj@{o} X)) (is_setoid (Powerset_Prop_obj@{o} X))
       (λ a, Powerset_Prop_singleton_pred@{o} a) _).
  intros a a' Haa' x; split; intros H Q k; hnf in H; apply H; intro Hx; apply k.
  - transitivity a; [ now symmetry | exact Hx ].
  - transitivity a'; [ exact Haa' | exact Hx ].
Defined.

(* The naturality square, componentwise: the direct image of a singleton is
   the singleton of the image, and truncation respects that because the
   existential over a singleton collapses. *)
Lemma Powerset_Prop_image_singleton@{o} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) (a : carrier X) :
  Powerset_Prop_image@{o} f (Powerset_Prop_singleton_pred@{o} a)
    ≈ Powerset_Prop_singleton_pred@{o} (f a).
Proof.
  intro y; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hax Hfy]]; hnf in Hax; apply Hax; intro Ha; apply k.
    transitivity (f x); [ exact (proper_morphism f _ _ Ha) | exact Hfy ].
  - intro Hfa; apply k; exists a; split;
      [ exact (Powerset_squash_intro@{o} (reflexivity a)) | exact Hfa ].
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_Prop_Singleton@{o so} :
  @Transform Sets@{o so} Sets@{o so} (@Id Sets@{o so}) Powerset_Prop@{o so}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{o so}
       (@Id Sets@{o so}) Powerset_Prop@{o so}
       (fun X => @Powerset_Prop_singleton_map@{o} X) _).
  intros X Y f a.
  exact (Powerset_Prop_image_singleton@{o} f a).
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The blocked consumers, unblocked *)

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Powerset_Prop_Monad_statement : Type := @Monad Sets Powerset_Prop.

Definition Powerset_Prop_FAlg : Category := FAlg Powerset_Prop.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity for the truncated carrier *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_Prop_singleton_faithful@{o} {X : SetoidObject@{o o}}
  (a b : carrier X)
  (H : Powerset_Prop_singleton_pred@{o} a ≈ Powerset_Prop_singleton_pred@{o} b) :
  Powerset_squash@{o} (@equiv _ (is_setoid X) a b).
Proof.
  intros Q k.
  assert (Hba : Powerset_squash@{o} (@equiv _ (is_setoid X) b a))
    by exact (proj1 (H a) (Powerset_squash_intro@{o} (reflexivity a))).
  apply Hba; intro Hb; apply k; now symmetry.
Qed.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_Prop_fin_object@{o} (n : nat) : SetoidObject@{o o} :=
  {| carrier   := Fin.t n
   ; is_setoid :=
       {| equiv        := @eq (Fin.t n)
        ; setoid_equiv :=
            {| Equivalence_Reflexive  := @eq_refl (Fin.t n)
             ; Equivalence_Symmetric  := @eq_sym (Fin.t n)
             ; Equivalence_Transitive := @eq_trans (Fin.t n) |} |} |}.

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Powerset_Prop_singletons_distinct@{o} :
  Powerset_Prop_singleton_pred@{o} (X:=Powerset_Prop_fin_object@{o} 2) Fin.F1
    ≈ Powerset_Prop_singleton_pred@{o} (X:=Powerset_Prop_fin_object@{o} 2)
        (Fin.FS Fin.F1)
  → False.
Proof.
  intro H.
  exact (Powerset_Prop_singleton_faithful@{o} _ _ H False fin2_0_ne_1).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Relating the two carriers *)

(*
   本节说明 Powerset 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_truncate_map@{o so} {X : SetoidObject@{o o}} :
  SetoidMorphism@{so so so} (Powerset_obj@{o so} X)
                            (Setoid_Lift@{o so} (Powerset_Prop_obj@{o} X)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier (Powerset_obj@{o so} X)) (is_setoid (Powerset_obj@{o so} X))
       (carrier (Powerset_Prop_obj@{o} X))
       (Setoid_Lift_instance@{o so} (is_setoid (Powerset_Prop_obj@{o} X)))
       (fun S => _) _).
  - unshelve refine
      (@Build_SetoidMorphism@{o o o}
         (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
         (λ x, Powerset_squash@{o} (S x)) _).
    intros x x' Hxx'; split; intros H Q k; apply H; intro Hs; apply k.
    + exact (fst (@proper_morphism _ _ _ _ S x x' Hxx') Hs).
    + exact (snd (@proper_morphism _ _ _ _ S x x' Hxx') Hs).
  - intros S T HST x; split; intros H Q k; hnf in H; apply H; intro Hs; apply k.
    + exact (fst (HST x) Hs).
    + exact (snd (HST x) Hs).
Defined.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_Prop_Lift@{o so sso} : @Functor Sets@{o so} Sets@{so sso}.
Proof.
  unshelve refine
    (@Build_Functor Sets@{o so} Sets@{so sso}
       (fun X => Setoid_Lift@{o so} (Powerset_Prop_obj@{o} X))
       (fun X Y f => @SetoidMorphism_Lift@{o so}
                       (Powerset_Prop_obj@{o} X) (Powerset_Prop_obj@{o} Y)
                       (Powerset_Prop_map@{o} f)) _ _ _).
  - intros X Y f g H S; exact (Powerset_Prop_map_respects@{o} f g H S).
  - intros X S; exact (@Powerset_Prop_map_id@{o} X S).
  - intros X Y Z f g S; exact (@Powerset_Prop_map_comp@{o} X Y Z f g S).
Defined.

(* Same-term equalities, closed by [reflexivity], on the
   Functor/Bifunctor.v precedent: [Powerset_Prop_Lift] is the lift of
   [Powerset_Prop], object-wise and morphism-wise. *)
Lemma Powerset_Prop_Lift_obj@{o so sso} (X : SetoidObject@{o o}) :
  Powerset_Prop_Lift@{o so sso} X = Setoid_Lift@{o so} (Powerset_Prop@{o so} X).
Proof. reflexivity. Qed.

Lemma Powerset_Prop_Lift_fmap@{o so sso} {X Y : SetoidObject@{o o}}
  (f : X ~{Sets@{o so}}~> Y) :
  fmap[Powerset_Prop_Lift@{o so sso}] f
    = @SetoidMorphism_Lift@{o so} (Powerset_Prop_obj@{o} X)
        (Powerset_Prop_obj@{o} Y) (fmap[Powerset_Prop@{o so}] f).
Proof. reflexivity. Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Powerset_truncate@{o so sso} :
  @Transform Sets@{o so} Sets@{so sso}
    Powerset@{o so sso} Powerset_Prop_Lift@{o so sso}.
Proof.
  unshelve refine
    (@Build_Transform' Sets@{o so} Sets@{so sso}
       Powerset@{o so sso} Powerset_Prop_Lift@{o so sso}
       (fun X => @Powerset_truncate_map@{o so} X) _).
  intros X Y f S y; split; intros H Q k; hnf in H; apply H.
  - intros [x [Hx Hfx]]; hnf in Hx; apply Hx; intro Hs; apply k;
      exists x; split; [ exact Hs | exact Hfx ].
  - intros [x [Hx Hfx]]; apply k; exists x; split;
      [ exact (Powerset_squash_intro@{o} Hx) | exact Hfx ].
Defined.
