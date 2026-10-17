Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.

Generalizable All Variables.

(** * The cross-universe subobject classifier of [Sets] *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Subobject_classifier

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** Lifting setoids one universe up *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Classifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition equiv_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  crelation@{so so} A := λ a b, @equiv A S a b.

Definition reflexive_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Reflexive@{so so} (equiv_lift@{o so} S) :=
  λ a, @Equivalence_Reflexive _ _ (@setoid_equiv _ S) a.

Definition symmetric_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Symmetric@{so so} (equiv_lift@{o so} S) :=
  λ a b Hab, @Equivalence_Symmetric _ _ (@setoid_equiv _ S) a b Hab.

Definition transitive_lift@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Transitive@{so so} (equiv_lift@{o so} S) :=
  λ a b c Hab Hbc, @Equivalence_Transitive _ _ (@setoid_equiv _ S) a b c Hab Hbc.

Definition Setoid_Lift_instance@{o so} {A : Type@{o}} (S : Setoid@{o o} A) :
  Setoid@{so so} A :=
  {| equiv        := equiv_lift@{o so} S
   ; setoid_equiv :=
       {| Equivalence_Reflexive  := reflexive_lift@{o so} S
        ; Equivalence_Symmetric  := symmetric_lift@{o so} S
        ; Equivalence_Transitive := transitive_lift@{o so} S |} |}.

Definition Setoid_Lift@{o so} (X : SetoidObject@{o o}) : SetoidObject@{so so} :=
  {| carrier   := carrier X
   ; is_setoid := Setoid_Lift_instance@{o so} (is_setoid X) |}.

(* A setoid morphism between level-o setoids re-typechecks between their
   lifts: carrier function and respectfulness are reused verbatim. *)
Definition SetoidMorphism_Lift@{o so} {X Y : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} X Y) :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} X) (Setoid_Lift@{o so} Y) :=
  @Build_SetoidMorphism@{so so so}
    (carrier X) (Setoid_Lift_instance@{o so} (is_setoid X))
    (carrier Y) (Setoid_Lift_instance@{o so} (is_setoid Y))
    (λ a, f a)
    (λ a b Hab, @proper_morphism _ _ _ _ f a b Hab).

(* ------------------------------------------------------------------------ *)
(** ** The truth-value object, one universe up *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PropSetoid_equiv@{o so} : crelation@{so so} Type@{o} :=
  λ P Q : Type@{o}, P ↔ Q.

Lemma PropSetoid_equivalence@{o so} :
  Equivalence@{so so} PropSetoid_equiv@{o so}.
Proof. unfold PropSetoid_equiv; equivalence. Qed.

Definition PropSetoid@{o so} : SetoidObject@{so so} :=
  {| carrier   := Type@{o}
   ; is_setoid := {| equiv        := PropSetoid_equiv@{o so}
                   ; setoid_equiv := PropSetoid_equivalence@{o so} |} |}.

(* The point true : 1 ~> Ω, selecting the (canonically) inhabited truth
   value [poly_unit].  Any inhabited type would do, up to iffT. *)
Definition sets_true@{o so} :
  SetoidMorphism@{so so so} unit_setoid_object@{so so} PropSetoid@{o so}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       poly_unit@{so} unit_setoid@{so so}
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ _, poly_unit@{o}) _).
  intros ? ? ?; split; intros ?; exact ttt.
Defined.

(* The terminal map: every setoid maps to the singleton. *)
Definition sets_to_unit@{so} {X : SetoidObject@{so so}} :
  SetoidMorphism@{so so so} X unit_setoid_object@{so so} :=
  @Build_SetoidMorphism@{so so so}
    (carrier X) (is_setoid X)
    poly_unit@{so} unit_setoid@{so so}
    (λ _, ttt) (λ _ _ _, eq_refl).

(* ------------------------------------------------------------------------ *)
(** ** The characteristic map *)

(*
   本节说明 Classifier 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition char_setoid@{o so} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) :
  SetoidMorphism@{so so so} (Setoid_Lift@{o so} B) PropSetoid@{o so}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       (carrier B) (Setoid_Lift_instance@{o so} (is_setoid B))
       Type@{o} (is_setoid PropSetoid@{o so})
       (λ b, ∃ a : carrier A, @equiv _ (is_setoid B) (m a) b) _).
  intros b b' Hbb'; split; intros [a Ha]; exists a.
  - transitivity b.
    + exact Ha.
    + exact Hbb'.
  - transitivity b'.
    + exact Ha.
    + now symmetry.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The classifying pullback square *)

(*
   本节说明拉回/推出、子对象、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sets_char_pullback@{o so sso} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) (Hm : @Monic Sets@{o so} A B m) :
  @IsPullback Sets@{so sso}
    (Setoid_Lift@{o so} B) unit_setoid_object@{so so} PropSetoid@{o so}
    (char_setoid@{o so} m) sets_true@{o so}
    (Setoid_Lift@{o so} A)
    (SetoidMorphism_Lift@{o so} m) sets_to_unit@{so}.
Proof.
  pose proof (snd (injectivity_is_monic m) Hm) as inj.
  constructor.
  - (* the square commutes: for a : A, "m a is in the image of m" iff ⊤ *)
    intro a; split.
    + intros _; exact ttt.
    + intros _; exists a; reflexivity.
  - (* the universal property *)
    intros Q q1 q2 Hq.
    simpl in Hq.
    (* Each x : Q comes with the truth of "q1 x is in the image of m";
       extracting its witness defines the mediator.  Monicity makes the
       extraction respect ≈. *)
    given (u : SetoidMorphism@{so so so} Q (Setoid_Lift@{o so} A)). {
      unshelve refine
        (@Build_SetoidMorphism@{so so so}
           (carrier Q) (is_setoid Q)
           (carrier A) (Setoid_Lift_instance@{o so} (is_setoid A))
           (λ x, `1 (snd (Hq x) ttt)) _).
      intros x y Hxy.
      apply inj.
      transitivity (q1 x).
      { exact (`2 (snd (Hq x) ttt)). }
      transitivity (q1 y).
      { now apply (proper_morphism q1). }
      symmetry.
      exact (`2 (snd (Hq y) ttt)).
    }
    unshelve refine {| unique_obj := u |}.
    + split.
      * intro x; simpl.
        exact (`2 (snd (Hq x) ttt)).
      * intro x; simpl.
        now destruct (q2 x).
    + intros v [Hv1 Hv2] x.
      apply inj.
      transitivity (q1 x).
      { exact (`2 (snd (Hq x) ttt)). }
      symmetry.
      exact (Hv1 x).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Uniqueness of the characteristic map *)

(*
   本节说明拉回/推出、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sets_char_unique@{o so sso} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B)
  (chi : Setoid_Lift@{o so} B ~{Sets@{so sso}}~> PropSetoid@{o so})
  (H : @IsPullback Sets@{so sso}
         (Setoid_Lift@{o so} B) unit_setoid_object@{so so} PropSetoid@{o so}
         chi sets_true@{o so}
         (Setoid_Lift@{o so} A)
         (SetoidMorphism_Lift@{o so} m) sets_to_unit@{so}) :
  chi ≈[Sets@{so sso}] char_setoid@{o so} m.
Proof.
  intro b.
  split.
  - (* χ b holds → b is in the image of m *)
    intro t.
    given (Q : SetoidObject@{so so}). {
      unshelve refine
        {| carrier   := ∃ b' : carrier B, chi b'
         ; is_setoid :=
             {| equiv := λ p q, @equiv _ (is_setoid B) (`1 p) (`1 q) |} |}.
      constructor; repeat intro.
      - reflexivity.
      - now symmetry.
      - etransitivity; eauto.
    }
    given (q1 : Q ~{Sets@{so sso}}~> Setoid_Lift@{o so} B). {
      unshelve refine
        (@Build_SetoidMorphism@{so so so}
           (carrier Q) (is_setoid Q)
           (carrier B) (Setoid_Lift_instance@{o so} (is_setoid B))
           (λ p, `1 p) (λ p q Hpq, Hpq)).
    }
    assert (Hcone : chi ∘[Sets@{so sso}] q1
                      ≈ sets_true@{o so} ∘[Sets@{so sso}] sets_to_unit@{so}). {
      intro p; split.
      - intros _; exact ttt.
      - intros _; exact (`2 p).
    }
    pose proof (is_pullback_ump H Q q1 sets_to_unit@{so} Hcone) as U.
    exists (unique_obj U (b; t)).
    exact (fst (unique_property U) (b; t)).
  - (* b is in the image of m → χ b holds *)
    intros [a Ha].
    exact (fst (@proper_morphism _ _ _ _ chi (m a) b Ha)
               (snd (is_pullback_commutes H a) ttt)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The one-level shadow: the classified subobject *)

(*
   本节说明拉回/推出、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem sets_char_subobject@{o so} {A B : SetoidObject@{o o}}
  (m : A ~{Sets@{o so}}~> B) (Hm : @Monic Sets@{o so} A B m) :
  @equiv _ (@SubObj_Setoid Sets@{o so} B)
    (@Build_SubObj Sets@{o so} B A m Hm)
    (@Build_SubObj Sets@{o so} B (Sets_Image m) (Sets_Image_mono m)
       (Sets_Image_mono_monic m)).
Proof.
  pose proof (snd (injectivity_is_monic m) Hm) as inj.
  (* the inverse of the epi leg, available because m is monic *)
  given (h : Sets_Image m ~{Sets@{o so}}~> A). {
    unshelve refine {| morphism := λ p, `1 `2 p |}.
    intros p q Hpq.
    apply inj.
    transitivity (`1 p).
    { exact (`2 `2 p). }
    transitivity (`1 q).
    { exact Hpq. }
    symmetry.
    exact (`2 `2 q).
  }
  given (iso : A ≅[Sets@{o so}] Sets_Image m). {
    unshelve refine {| to := Sets_Image_epi m; from := h |}.
    - (* epi ∘ h ≈ id, compared on first components *)
      intro p.
      exact (`2 `2 p).
    - (* h ∘ epi ≈ id, on the nose *)
      intro a.
      reflexivity.
  }
  exists iso.
  exact (Sets_Image_comm m).
Defined.

(** ** The lift is inert for epicness *)

(*
   本节说明核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The constantly-true probe: the terminal map followed by [sets_true]. *)
Definition sets_all_true@{o so sso} (X : SetoidObject@{so so}) :
  X ~{Sets@{so sso}}~> PropSetoid@{o so} :=
  sets_true@{o so} ∘[Sets@{so sso}] sets_to_unit@{so}.

Theorem lifted_epic_implies_epic@{o so sso} {A B : SetoidObject@{o o}}
  (h : A ~{Sets@{o so}}~> B)
  (H : @Epic@{sso so} Sets@{so sso}
         (Setoid_Lift@{o so} A) (Setoid_Lift@{o so} B)
         (SetoidMorphism_Lift@{o so} h)) :
  @Epic@{so o} Sets@{o so} A B h.
Proof.
  apply (surjective_implies_epic@{so o} h).
  intro b.
  assert (Hcomm :
    char_setoid@{o so} h ∘[Sets@{so sso}] SetoidMorphism_Lift@{o so} h
      ≈ sets_all_true@{o so sso} (Setoid_Lift@{o so} B)
          ∘[Sets@{so sso}] SetoidMorphism_Lift@{o so} h). {
    intro a; split.
    - intros _; exact ttt.
    - intros _; exists a; reflexivity.
  }
  exact (snd (@epic _ _ _ _ H PropSetoid@{o so}
                (char_setoid@{o so} h)
                (sets_all_true@{o so sso} (Setoid_Lift@{o so} B))
                Hcomm b) ttt).
Qed.

Theorem epic_implies_lifted_epic@{o so sso} {A B : SetoidObject@{o o}}
  (h : A ~{Sets@{o so}}~> B) (H : @Epic@{so o} Sets@{o so} A B h) :
  @Epic@{sso so} Sets@{so sso}
    (Setoid_Lift@{o so} A) (Setoid_Lift@{o so} B)
    (SetoidMorphism_Lift@{o so} h).
Proof.
  constructor; intros z g1 g2 Hg b.
  destruct (epic_implies_surjective@{so o} h H b) as [a Ha].
  rewrite <- Ha.
  exact (Hg a).
Qed.
