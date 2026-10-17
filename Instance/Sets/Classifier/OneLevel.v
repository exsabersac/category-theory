Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

   (*
   本节说明子对象、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sets_in_image@{o} {u x : SetoidObject@{o o}}
  (m : SetoidMorphism@{o o o} u x) (b : carrier x) : Type@{o} :=
  ∃ a : carrier u, @equiv _ (is_setoid x) (m a) b.

Definition triv_rel@{o} (P : Type@{o}) : crelation@{o o} P :=
  fun _ _ => poly_unit@{o}.

Lemma triv_equivalence@{o} (P : Type@{o}) : Equivalence@{o o} (triv_rel@{o} P).
Proof. unfold triv_rel; constructor; repeat intro; exact ttt. Qed.

Definition SubOne@{o} (P : Type@{o}) : SetoidObject@{o o} :=
  {| carrier := P
   ; is_setoid := {| equiv := triv_rel@{o} P
                   ; setoid_equiv := triv_equivalence@{o} P |} |}.

Definition subone_incl@{o so} (P : Type@{o}) :
  SubOne@{o} P
    ~{Sets@{o so}}~> (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o} P (is_setoid (SubOne@{o} P))
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       (fun _ => ttt) _).
  intros ? ? ?; reflexivity.
Defined.

Lemma subone_incl_monic@{o so} (P : Type@{o}) :
  @Monic Sets@{o so} (SubOne@{o} P)
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) (subone_incl@{o so} P).
Proof. constructor; intros z g1 g2 _ ?; exact ttt. Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive poly_bool@{u} : Type@{u} := ptrue | pfalse.

Definition BoolSetoid@{o} : SetoidObject@{o o} :=
  {| carrier := poly_bool@{o} ; is_setoid := eq_Setoid@{o} poly_bool@{o} |}.

Definition DecImage@{o so} :=
  ∀ (u x : SetoidObject@{o o}) (m : u ~{Sets@{o so}}~> x),
    @Monic Sets@{o so} u x m →
    ∀ b : carrier x, sets_in_image@{o} m b + (sets_in_image@{o} m b -> False).

Definition Untruncate@{o} := ∀ P : Type@{o}, Powerset_squash@{o} P -> P.

Definition IEM@{o} := ∀ P : Type@{o}, P + (P -> False).

Definition untruncate_of_IEM@{o} (E : IEM@{o}) : Untruncate@{o} :=
  fun P H => match E P with
             | inl p => p
             | inr N => match H False (fun p => N p) with end
             end.
Definition DecImage_of_IEM@{o so} (E : IEM@{o}) : DecImage@{o so} :=
  fun u x m M b => E (sets_in_image@{o} m b).

Definition IEM_of_DecImage@{o so} (D : DecImage@{o so}) : IEM@{o}.
Proof.
  intro P.
  destruct (D (SubOne@{o} P)
              (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
              (subone_incl@{o so} P) (subone_incl_monic@{o so} P) ttt)
    as [ H | N ].
  - left. exact (projT1 H).
  - right. intro p. apply N. exists p. reflexivity.
Defined.

Definition DecImage_iff_IEM@{o so} :
  (DecImage@{o so} -> IEM@{o}) * (IEM@{o} -> DecImage@{o so}) :=
  (IEM_of_DecImage@{o so}, DecImage_of_IEM@{o so}).

Record SmallClassifierExt@{o} : Type@{o+1} := {
  sce_Om : SetoidObject@{o o};
  sce_t  : carrier sce_Om;
  sce_w  : Type@{o} -> carrier sce_Om;
  sce_intro : ∀ P : Type@{o}, P -> @equiv _ (is_setoid sce_Om) (sce_w P) sce_t;
  sce_elim  : ∀ P : Type@{o}, @equiv _ (is_setoid sce_Om) (sce_w P) sce_t -> P;
  sce_ext   : ∀ v v' : carrier sce_Om,
                (@equiv _ (is_setoid sce_Om) v sce_t
                   -> @equiv _ (is_setoid sce_Om) v' sce_t) ->
                (@equiv _ (is_setoid sce_Om) v' sce_t
                   -> @equiv _ (is_setoid sce_Om) v sce_t) ->
                @equiv _ (is_setoid sce_Om) v v'
}.

Definition subone_pt@{o so} {x : SetoidObject@{o o}} (b : carrier x) :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) ~{Sets@{o so}}~> x.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       (carrier x) (is_setoid x) (fun _ => b) _).
  intros ? ? ?; reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 OneLevel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ---- the converse: a small classifier gives a SubobjectClassifier ---- *)

Definition sce_truth@{o so} (S : SmallClassifierExt@{o}) :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    ~{Sets@{o so}}~> sce_Om@{o} S.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       (carrier (sce_Om@{o} S)) (is_setoid (sce_Om@{o} S))
       (fun _ => sce_t@{o} S) _).
  intros ? ? ?; reflexivity.
Defined.

Definition sce_char@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) : x ~{Sets@{o so}}~> sce_Om@{o} S.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier x) (is_setoid x)
       (carrier (sce_Om@{o} S)) (is_setoid (sce_Om@{o} S))
       (fun b => sce_w@{o} S (sets_in_image@{o} m b)) _).
  intros b b' Hbb'.
  apply (sce_ext@{o} S).
  - intro Hv. apply (sce_intro@{o} S).
    destruct (sce_elim@{o} S _ Hv) as [a Ha].
    exists a. now transitivity b.
  - intro Hv. apply (sce_intro@{o} S).
    destruct (sce_elim@{o} S _ Hv) as [a Ha].
    exists a. transitivity b'; [ exact Ha | now symmetry ].
Defined.

Definition sets_monic_inj@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m) :
  ∀ a a' : carrier u, m a ≈ m a' -> a ≈ a' :=
  snd (injectivity_is_monic m) M.

Definition sce_pullback@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  @IsPullback Sets@{o so} x
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) (sce_Om@{o} S)
    (sce_char@{o so} S m M) (sce_truth@{o so} S)
    u m (@one Sets@{o so} Sets_Terminal@{so o} u).
Proof.
  constructor.
  - intro a; simpl.
    apply (sce_intro@{o} S). exists a. reflexivity.
  - intros Q q1 q2 Hq.
    assert (Him : ∀ z : carrier Q, sets_in_image@{o} m (q1 z)).
    { intro z. apply (sce_elim@{o} S).
      specialize (Hq z); simpl in Hq. exact Hq. }
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine
        (@Build_SetoidMorphism@{o o o}
           (carrier Q) (is_setoid Q) (carrier u) (is_setoid u)
           (fun z => projT1 (Him z)) _).
      intros z z' Hzz'.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | ].
      transitivity (q1 z').
      * exact (proper_morphism q1 _ _ Hzz').
      * symmetry; exact (projT2 (Him z')).
    + split.
      * intro z; simpl. exact (projT2 (Him z)).
      * intro z; simpl. destruct (q2 z); reflexivity.
    + intros v [Hv1 Hv2] z; simpl.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | symmetry; exact (Hv1 z) ].
Defined.

Definition sce_char_unique@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (h : x ~{Sets@{o so}}~> sce_Om@{o} S)
  (HP : @IsPullback Sets@{o so} x
          (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) (sce_Om@{o} S)
          h (sce_truth@{o so} S) u m
          (@one Sets@{o so} Sets_Terminal@{so o} u)) :
  h ≈ sce_char@{o so} S m M.
Proof.
  intro b.
  destruct HP as [Hc Hu].
  apply (sce_ext@{o} S).
  - intro Hb.
    apply (sce_intro@{o} S).
    unshelve epose proof
      (Hu (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
          (subone_pt@{o so} b)
          (@one Sets@{o so} Sets_Terminal@{so o} _) _) as U.
    { intro z; simpl; destruct z; exact Hb. }
    destruct (unique_property U) as [U1 _].
    exists (unique_obj U ttt). exact (U1 ttt).
  - intro Hw.
    destruct (sce_elim@{o} S _ Hw) as [a Ha].
    transitivity (h (m a)).
    + symmetry; exact (proper_morphism h _ _ Ha).
    + exact (Hc a).
Qed.

Definition classifier_of_small@{o so} (S : SmallClassifierExt@{o}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  @Build_SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
    (sce_Om@{o} S) (sce_truth@{o so} S)
    (fun u x m M => sce_char@{o so} S m M)
    (fun u x m M => sce_pullback@{o so} S m M)
    (fun u x m M h HP => sce_char_unique@{o so} S m M h HP).

Lemma subone_respects@{o so} (P Q : Type@{o}) (f : P -> Q) (g : Q -> P) :
  @equiv _ (@SubObj_Setoid Sets@{o so}
              (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
    (@Build_SubObj Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
       (SubOne@{o} P) (subone_incl@{o so} P) (subone_incl_monic@{o so} P))
    (@Build_SubObj Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
       (SubOne@{o} Q) (subone_incl@{o so} Q) (subone_incl_monic@{o so} Q)).
Proof.
  unshelve refine (existT _ _ _).
  - unshelve refine {| to := _ ; from := _ |}.
    + unshelve refine (@Build_SetoidMorphism@{o o o} P
        (is_setoid (SubOne@{o} P))
        Q (is_setoid (SubOne@{o} Q)) f _). intros ? ? ?; exact ttt.
    + unshelve refine (@Build_SetoidMorphism@{o o o} Q
        (is_setoid (SubOne@{o} Q))
        P (is_setoid (SubOne@{o} P)) g _). intros ? ? ?; exact ttt.
    + intro z; exact ttt.
    + intro z; exact ttt.
  - intro z; reflexivity.
Qed.

(* ---- forward: a SubobjectClassifier gives a small one ---- *)

Definition sce_of_w@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (P : Type@{o}) : carrier (@Ω Sets@{o so} Sets_Terminal@{so o} HS) :=
  @char Sets@{o so} Sets_Terminal@{so o} HS (SubOne@{o} P)
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (subone_incl@{o so} P) (subone_incl_monic@{o so} P) ttt.

Lemma sce_of_intro@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (P : Type@{o}) : P ->
  @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
    (sce_of_w@{o so} HS P)
    (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt).
Proof.
  intro p.
  exact (is_pullback_commutes
           (@char_pullback Sets@{o so} Sets_Terminal@{so o} HS _ _
              (subone_incl@{o so} P) (subone_incl_monic@{o so} P)) p).
Qed.

Lemma sce_of_elim@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (P : Type@{o}) :
  @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
    (sce_of_w@{o so} HS P)
    (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt) -> P.
Proof.
  intro Ht.
  pose proof (is_pullback_ump
    (@char_pullback Sets@{o so} Sets_Terminal@{so o} HS _ _
       (subone_incl@{o so} P) (subone_incl_monic@{o so} P))
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (@id Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
    (@one Sets@{o so} Sets_Terminal@{so o}
       (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))) as U.
  unshelve epose proof (U _) as U'.
  { intro z; destruct z; exact Ht. }
  exact (unique_obj U' ttt).
Qed.

Lemma subone_pt_classifies@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (v : carrier (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) :
  @IsPullback Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    (@Ω Sets@{o so} Sets_Terminal@{so o} HS)
    (subone_pt@{o so} v) (@truth Sets@{o so} Sets_Terminal@{so o} HS)
    (SubOne@{o} (@equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
                   (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)))
    (subone_incl@{o so} _) (@one Sets@{o so} Sets_Terminal@{so o} _).
Proof.
  constructor.
  - intro p; simpl. exact p.
  - intros Q q1 q2 Hq.
    assert (Hz : ∀ z : carrier Q,
             @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
               (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)).
    { intro z; specialize (Hq z); simpl in Hq.
      destruct (q2 z); exact Hq. }
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine (@Build_SetoidMorphism@{o o o}
        (carrier Q) (is_setoid Q) _ (is_setoid (SubOne@{o} _)) Hz _).
      intros ? ? ?; exact ttt.
    + split; intro z; simpl; destruct (q1 z); try destruct (q2 z); reflexivity.
    + intros vv _ z; exact ttt.
Qed.

Lemma sce_of_ext@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  (v v' : carrier (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
  (f : @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt) ->
       @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt))
  (g : @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt) ->
       @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
         (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)) :
  @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v v'.
Proof.
  assert (Hv : @equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
                 (sce_of_w@{o so} HS
                    (@equiv _
                       (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
                       v (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)))).
  { exact (@char_unique Sets@{o so} Sets_Terminal@{so o} HS _ _
             (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
             (subone_pt@{o so} v) (subone_pt_classifies@{o so} HS v) ttt). }
  assert (Hv' : @equiv _
                 (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
                 (sce_of_w@{o so} HS
                    (@equiv _
                       (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS))
                       v' (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)))).
  { exact (@char_unique Sets@{o so} Sets_Terminal@{so o} HS _ _
             (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
             (subone_pt@{o so} v') (subone_pt_classifies@{o so} HS v') ttt). }
  transitivity (sce_of_w@{o so} HS
    (@equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v
       (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt))); [ exact Hv | ].
  transitivity (sce_of_w@{o so} HS
    (@equiv _ (is_setoid (@Ω Sets@{o so} Sets_Terminal@{so o} HS)) v'
       (@truth Sets@{o so} Sets_Terminal@{so o} HS ttt)));
    [ | symmetry; exact Hv' ].
  exact (@char_respects Sets@{o so} Sets_Terminal@{so o} HS _ _ _
           (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
           (subone_incl@{o so} _) (subone_incl_monic@{o so} _)
           (subone_respects@{o so} _ _ f g) ttt).
Qed.

Definition small_of_classifier@{o so}
  (HS : @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}) :
  SmallClassifierExt@{o} :=
  {| sce_Om := @Ω Sets@{o so} Sets_Terminal@{so o} HS
   ; sce_t := @truth Sets@{o so} Sets_Terminal@{so o} HS ttt
   ; sce_w := sce_of_w@{o so} HS
   ; sce_intro := sce_of_intro@{o so} HS
   ; sce_elim := sce_of_elim@{o so} HS
   ; sce_ext := sce_of_ext@{o so} HS |}.

Definition classifier_iff_small@{o so} :
  (@SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
     -> SmallClassifierExt@{o})
  * (SmallClassifierExt@{o}
     -> @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o})
  := (small_of_classifier@{o so}, classifier_of_small@{o so}).

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* [Sets_Classifier] is the issue's Verification-block name.  Its Ω is
   [Powerset_Omega] and its truth [Powerset_truth_point], both by
   [eq_refl]; the hypothesis is used exactly once, in [sce_elim].
   [small_of_IEM] is Seven Sketches' Ω_Set = 𝔹 as a small classifier.（标题）（已译） *)

Definition small_of_untruncate@{o} (U : Untruncate@{o}) :
  SmallClassifierExt@{o}.
Proof.
  unshelve refine
    {| sce_Om := Powerset_Omega@{o} ; sce_t := Powerset_truth_point@{o}
     ; sce_w := fun P => Powerset_squash@{o} P |}.
  - intros P p; unfold Powerset_Prop_truth_equiv; split; intros _.
    + exact I.
    + exact (Powerset_squash_intro@{o} p).
  - intros P Hp; unfold Powerset_Prop_truth_equiv in Hp.
    exact (U P (proj2 Hp I)).
  - intros v v' f g; unfold Powerset_Prop_truth_equiv in *; split.
    + intro Hv. exact (proj2 (f (conj (fun _ => I) (fun _ => Hv))) I).
    + intro Hv. exact (proj2 (g (conj (fun _ => I) (fun _ => Hv))) I).
Defined.

Definition Sets_Classifier@{o so} (U : Untruncate@{o}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  classifier_of_small@{o so} (small_of_untruncate@{o} U).

Example sets_classifier_omega@{o so} (U : Untruncate@{o}) :
  @Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U)
    = Powerset_Omega@{o} := eq_refl.

Example sets_classifier_truth@{o so} (U : Untruncate@{o}) :
  @truth Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) ttt
    = Powerset_truth_point@{o} := eq_refl.

Definition small_of_IEM@{o} (E : IEM@{o}) : SmallClassifierExt@{o}.
Proof.
  unshelve refine
    {| sce_Om := BoolSetoid@{o} ; sce_t := ptrue@{o}
     ; sce_w := fun P => match E P with
                         | inl _ => ptrue@{o} | inr _ => pfalse@{o} end |}.
  - intros P p; simpl.
    destruct (E P) as [_|N]; [ reflexivity | exfalso; exact (N p) ].
  - intros P Hp; simpl in Hp.
    destruct (E P) as [p|_]; [ exact p | discriminate Hp ].
  - intros v v' f g; simpl in *.
    destruct v; destruct v'; try reflexivity.
    + symmetry; exact (f eq_refl).
    + exact (g eq_refl).
Defined.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 OneLevel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SetsDec@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) : Type@{o} :=
  ∀ b : carrier x, sets_in_image@{o} m b + (sets_in_image@{o} m b -> False).

Definition dec_truth@{o so} :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun _ => ptrue@{o}) _).
  intros ? ? ?; reflexivity.
Defined.

Definition char_of_dec@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) : x ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier x) (is_setoid x)
       poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun b => match d b with inl _ => ptrue | inr _ => pfalse end) _).
  intros b b' Hbb'.
  destruct (d b) as [[a Ha] | N]; destruct (d b') as [[a' Ha'] | N'].
  - reflexivity.
  - exfalso. apply N'. exists a. now transitivity b.
  - exfalso. apply N. exists a'.
    transitivity b'; [ exact Ha' | now symmetry ].
  - reflexivity.
Defined.

Lemma char_of_dec_image@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (a : carrier u) :
  char_of_dec@{o so} m M d (m a) = ptrue@{o}.
Proof.
  simpl; unfold char_of_dec; simpl.
  destruct (d (m a)) as [ _ | N ].
  - reflexivity.
  - exfalso. apply N. exists a. reflexivity.
Qed.

Lemma char_of_dec_true_inv@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (b : carrier x) :
  char_of_dec@{o so} m M d b = ptrue@{o} -> sets_in_image@{o} m b.
Proof.
  simpl; unfold char_of_dec; simpl.
  destruct (d b) as [ H | N ].
  - intros _; exact H.
  - intro Hc; discriminate Hc.
Qed.

Lemma char_of_dec_iff@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (b : carrier x) :
  (char_of_dec@{o so} m M d b ≈ dec_truth@{o so} ttt)
    ↔ sets_in_image@{o} m b.
Proof.
  split.
  - exact (char_of_dec_true_inv@{o so} m M d b).
  - intros [a Ha].
    transitivity (char_of_dec@{o so} m M d (m a)).
    + symmetry; exact (proper_morphism (char_of_dec@{o so} m M d) _ _ Ha).
    + exact (char_of_dec_image@{o so} m M d a).
Qed.

Definition char_of_dec_pullback@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) :
  @IsPullback Sets@{o so} x
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) BoolSetoid@{o}
    (char_of_dec@{o so} m M d) dec_truth@{o so}
    u m (@one Sets@{o so} Sets_Terminal@{so o} u).
Proof.
  constructor.
  - intro a; simpl. exact (char_of_dec_image@{o so} m M d a).
  - intros Q q1 q2 Hq.
    assert (Him : ∀ z : carrier Q, sets_in_image@{o} m (q1 z))
      by (intro z; exact (char_of_dec_true_inv@{o so} m M d (q1 z) (Hq z))).
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine
        (@Build_SetoidMorphism@{o o o}
           (carrier Q) (is_setoid Q) (carrier u) (is_setoid u)
           (fun z => projT1 (Him z)) _).
      intros z z' Hzz'.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | ].
      transitivity (q1 z').
      * exact (proper_morphism q1 _ _ Hzz').
      * symmetry; exact (projT2 (Him z')).
    + split.
      * intro z; simpl. exact (projT2 (Him z)).
      * intro z; simpl. destruct (q2 z); reflexivity.
    + intros v [Hv1 Hv2] z; simpl.
      apply (sets_monic_inj@{o so} m M).
      transitivity (q1 z); [ exact (projT2 (Him z)) | symmetry; exact (Hv1 z) ].
Defined.

Lemma char_of_dec_unique@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (M : @Monic Sets@{o so} u x m)
  (d : SetsDec@{o so} m) (h : x ~{Sets@{o so}}~> BoolSetoid@{o})
  (HP : @IsPullback Sets@{o so} x
          (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) BoolSetoid@{o}
          h dec_truth@{o so} u m (@one Sets@{o so} Sets_Terminal@{so o} u)) :
  h ≈ char_of_dec@{o so} m M d.
Proof.
  intro b.
  destruct HP as [Hc Hu].
  assert (Him : ∀ a : carrier u, h (m a) = ptrue@{o}) by exact Hc.
  destruct (h b) eqn:Hb.
  - unshelve epose proof
      (Hu (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
          (subone_pt@{o so} b)
          (@one Sets@{o so} Sets_Terminal@{so o} _) _) as U.
    { intro t; simpl; exact Hb. }
    destruct (unique_property U) as [U1 _].
    assert (Hin : sets_in_image@{o} m b).
    { exists (unique_obj U ttt). exact (U1 ttt). }
    simpl; unfold char_of_dec; simpl.
    destruct (d b) as [ _ | N ].
    + reflexivity.
    + exfalso; exact (N Hin).
  - simpl; unfold char_of_dec; simpl.
    destruct (d b) as [ [a Ha] | _ ].
    + exfalso.
      assert (Hhb : h (m a) = h b) by exact (proper_morphism h _ _ Ha).
      rewrite (Him a) in Hhb; rewrite Hb in Hhb; discriminate Hhb.
    + reflexivity.
Qed.

Definition Sets_Classifier_dec@{o so} (D : DecImage@{o so}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  @Build_SubobjectClassifier Sets@{o so} Sets_Terminal@{so o}
    BoolSetoid@{o} dec_truth@{o so}
    (fun u x m M => char_of_dec@{o so} m M (D u x m M))
    (fun u x m M => char_of_dec_pullback@{o so} m M (D u x m M))
    (fun u x m M h HP => char_of_dec_unique@{o so} m M (D u x m M) h HP).

Example sets_classifier_dec_omega@{o so} (D : DecImage@{o so}) :
  @Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D)
    = BoolSetoid@{o} := eq_refl.

Example sets_classifier_dec_truth@{o so} (D : DecImage@{o so}) :
  @truth Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D) ttt
    = ptrue@{o} := eq_refl.

Example sets_classifier_dec_char@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D) u x m M
    = char_of_dec@{o so} m M (D u x m M) := eq_refl.

Definition Sets_Classifier_IEM@{o so} (E : IEM@{o}) :
  @SubobjectClassifier Sets@{o so} Sets_Terminal@{so o} :=
  Sets_Classifier@{o so} (untruncate_of_IEM@{o} E).

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 OneLevel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Example bridge_pointwise@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M b
    = Powerset_squash@{o} (char_setoid@{o so} m b) := eq_refl.

(* 相关说明。 （已译） *)
Example bridge_value@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M b
    = Powerset_squash@{o} (sets_in_image@{o} m b) := eq_refl.

(* the cross-universe char's value IS sets_in_image *)
Example bridge_char_setoid@{o so} {u x : SetoidObject@{o o}}
  (m : u ~{Sets@{o so}}~> x) (b : carrier x) :
  char_setoid@{o so} m b = sets_in_image@{o} m b := eq_refl.

Definition sets_squash_mor@{o so sso} :
  PropSetoid@{o so} ~{Sets@{so sso}}~> Setoid_Lift@{o so} Powerset_Omega@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{so so so}
       Type@{o} (is_setoid PropSetoid@{o so})
       (carrier Powerset_Omega@{o})
       (Setoid_Lift_instance@{o so} (is_setoid Powerset_Omega@{o}))
       (fun P => Powerset_squash@{o} P) _).
  intros P Q [f g]; split.
  - intro H. exact (H (Powerset_squash@{o} Q)
                      (fun p => Powerset_squash_intro@{o} (f p))).
  - intro H. exact (H (Powerset_squash@{o} P)
                      (fun q => Powerset_squash_intro@{o} (g q))).
Defined.

Lemma bridge_record_equiv@{o so sso} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  SetoidMorphism_Lift@{o so}
    (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M)
    ≈[Sets@{so sso}] sets_squash_mor@{o so sso}
        ∘[Sets@{so sso}] char_setoid@{o so} m.
Proof. intro b; simpl; split; intro H; exact H. Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Lemma classifier_of_small_char_iff@{o so} (S : SmallClassifierExt@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} Sets_Terminal@{so o} (classifier_of_small@{o so} S)
     u x m M b
     ≈ @truth Sets@{o so} Sets_Terminal@{so o}
         (classifier_of_small@{o so} S) ttt)
    ↔ sets_in_image@{o} m b.
Proof.
  split.
  - exact (sce_elim@{o} S (sets_in_image@{o} m b)).
  - exact (sce_intro@{o} S (sets_in_image@{o} m b)).
Qed.

Definition sets_classifier_char_iff@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) u x m M b
     ≈ @truth Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) ttt)
    ↔ sets_in_image@{o} m b
  := classifier_of_small_char_iff@{o so} (small_of_untruncate@{o} U) m M b.

Definition sets_classifier_dec_char_iff@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D)
     u x m M b
     ≈ @truth Sets@{o so} Sets_Terminal@{so o}
         (Sets_Classifier_dec@{o so} D) ttt)
    ↔ sets_in_image@{o} m b
  := char_of_dec_iff@{o so} m M (D u x m M) b.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明拉回/推出、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sets_truth_subobject@{o so} (U : Untruncate@{o}) :
  @SubObj Sets@{o so}
    (@Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U)) :=
  @truth_subobject Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U).

Definition sets_char_roundtrip@{o so} (U : Untruncate@{o})
  {x : SetoidObject@{o o}}
  (h : x ~{Sets@{o so}}~> @Ω Sets@{o so} Sets_Terminal@{so o}
                             (Sets_Classifier@{o so} U)) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) _ _
    (sub_mono (@sub_reindex Sets@{o so} Sets_HasPullbacks@{so o}
                 (@Ω Sets@{o so} Sets_Terminal@{so o}
                    (Sets_Classifier@{o so} U)) x h
                 (sets_truth_subobject@{o so} U)))
    (sub_is_monic (@sub_reindex Sets@{o so} Sets_HasPullbacks@{so o}
                 (@Ω Sets@{o so} Sets_Terminal@{so o}
                    (Sets_Classifier@{o so} U)) x h
                 (sets_truth_subobject@{o so} U)))
    ≈ h
  := @classifier_char_roundtrip Sets@{o so} Sets_Terminal@{so o}
       Sets_HasPullbacks@{so o} (Sets_Classifier@{o so} U) x h.

Definition sets_pullback_roundtrip@{o so} (U : Untruncate@{o})
  {x : SetoidObject@{o o}} (s : @SubObj Sets@{o so} x) :
  @sub_reindex Sets@{o so} Sets_HasPullbacks@{so o}
    (@Ω Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U)) x
    (@char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier@{o so} U) _ _
       (sub_mono s) (sub_is_monic s))
    (sets_truth_subobject@{o so} U)
    ≈ s
  := @classifier_pullback_roundtrip Sets@{o so} Sets_Terminal@{so o}
       Sets_HasPullbacks@{so o} (Sets_Classifier@{o so} U) x s.

(* ------------------------------------------------------------------------ *)
(* * ** (J) A concrete decidable mono, no global 假设 （已译） *)

(*
   本节说明子对象、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dec_false@{o so} :
  (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    ~{Sets@{o so}}~> BoolSetoid@{o}.
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       _ (is_setoid (@terminal_obj Sets@{o so} Sets_Terminal@{so o}))
       poly_bool@{o} (is_setoid BoolSetoid@{o})
       (fun _ => pfalse@{o}) _).
  intros ? ? ?; reflexivity.
Defined.

Lemma point_monic@{o so} {x : SetoidObject@{o o}}
  (p : (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) ~{Sets@{o so}}~> x) :
  @Monic Sets@{o so} _ x p.
Proof.
  constructor; intros z g1 g2 _ w.
  destruct (g1 w), (g2 w); reflexivity.
Qed.

Definition dec_false_dec@{o so} : SetsDec@{o so} dec_false@{o so}.
Proof.
  intro b; destruct b.
  - right; intros [a Ha]; simpl in Ha; discriminate Ha.
  - left; exists ttt; reflexivity.
Defined.

Definition char_false@{o so} : BoolSetoid@{o} ~{Sets@{o so}}~> BoolSetoid@{o} :=
  char_of_dec@{o so} dec_false@{o so} (point_monic@{o so} dec_false@{o so})
    dec_false_dec@{o so}.

Example char_false_at_false@{o so} :
  char_false@{o so} pfalse@{o} = ptrue@{o} := eq_refl.

Example char_false_at_true@{o so} :
  char_false@{o so} ptrue@{o} = pfalse@{o} := eq_refl.

Lemma ptrue_neq_pfalse@{o} : ptrue@{o} = pfalse@{o} -> False.
Proof. intro H; discriminate H. Qed.

Lemma dec_false_not_iso@{o so} :
  @IsIsomorphism Sets@{o so} _ _ dec_false@{o so} -> False.
Proof.
  intros [g Hr _].
  exact (ptrue_neq_pfalse@{o} (symmetry (Hr ptrue@{o}))).
Qed.

Example char_of_dec_from_DecImage@{o so} (D : DecImage@{o so}) :
  @char Sets@{o so} Sets_Terminal@{so o} (Sets_Classifier_dec@{o so} D) _ _
    dec_false@{o so} (point_monic@{o so} dec_false@{o so})
  = char_of_dec@{o so} dec_false@{o so} (point_monic@{o so} dec_false@{o so})
      (D _ _ dec_false@{o so} (point_monic@{o so} dec_false@{o so})) := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 OneLevel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition finset_classifier_classifies (n : obj[FinSet]) :
  @Isomorphism Sets
    {| carrier := @SubObj FinSet n |}
    {| carrier := n ~{FinSet}~> @Ω FinSet FinSet_Terminal FinSet_Classifier |}
  := @classifier_classifies FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier n.

Example finset_classifier_omega_is_two :
  @Ω FinSet FinSet_Terminal FinSet_Classifier = 2%nat := eq_refl.

Definition fin_incl_1_2 : 1%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.

Lemma fin_incl_1_2_monic : @Monic FinSet 1%nat 2%nat fin_incl_1_2.
Proof.
  apply finset_monic_iff_injective.
  intros a b _; rewrite (fin1_unique a), (fin1_unique b); reflexivity.
Qed.

Example finset_char_at_F1 :
  @char FinSet FinSet_Terminal FinSet_Classifier 1%nat 2%nat
    fin_incl_1_2 fin_incl_1_2_monic Fin.F1 = fin_true := eq_refl.

Example finset_char_at_FS :
  @char FinSet FinSet_Terminal FinSet_Classifier 1%nat 2%nat
    fin_incl_1_2 fin_incl_1_2_monic (Fin.FS Fin.F1) = fin_false := eq_refl.

(*
   本节说明 OneLevel 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example iem_routes_omega@{o so} (E : IEM@{o}) :
  @Ω Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E))
  = @Ω Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) := eq_refl.

Example iem_routes_char@{o so} (E : IEM@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E)) u x m M b
  = @char Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) u x m M b
  := eq_refl.

Example iem_routes_truth@{o so} (E : IEM@{o}) :
  @truth Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E))
  = @truth Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) := eq_refl.

Example iem_routes_truth_pt@{o so} (E : IEM@{o}) :
  @truth Sets@{o so} Sets_Terminal@{so o}
     (classifier_of_small@{o so} (small_of_IEM@{o} E)) ttt
  = @truth Sets@{o so} Sets_Terminal@{so o}
     (Sets_Classifier_dec@{o so} (DecImage_of_IEM@{o so} E)) ttt := eq_refl.
