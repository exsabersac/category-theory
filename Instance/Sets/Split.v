Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * A section/retraction pair Sets not 同构 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/split+epimorphism
 Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The two objects *)

(* The two-element setoid one Instance/Sets.v already carries;
 这是 notation it, not second copy. （已译） *)
Notation sets_two := bool_setoid_object.

(*
   本节说明 Split 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_three@{t u} : SetoidObject@{t u} :=
  {| carrier := option bool ; is_setoid := eq_Setoid@{t} (option bool) |}.

(*
   本节说明 Split 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
   本节说明 Split 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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
(** ** The two maps *)

(* The 含入 [Some]. The feature it proofs below use is
 it misses [None]. （已译） *)
Program Definition sets_incl23 : sets_two ~{Sets}~> sets_three := {|
  morphism := @Some bool
|}.

(* 相关说明。 （已译） *)
Definition option_fold (o : option bool) : bool :=
  match o with
  | Some b => b
  | None   => true
  end.

Program Definition sets_retr32 : sets_three ~{Sets}~> sets_two := {|
  morphism := option_fold
|}.

(* ------------------------------------------------------------------------ *)
(** ** One composite is the identity *)

Lemma sets_retr_incl : sets_retr32 ∘[Sets] sets_incl23 ≈ id{Sets}.
Proof. intro b; now destruct b. Qed.

(* Hence 含入 split mono retraction split epi, both
 witnessed SAME equation -- 这是 shape Theory/Morphisms.v
 names [Section] [Retraction]. （已译） *)

Definition sets_incl23_Section : Section sets_incl23 :=
  Build_Section _ _ sets_incl23 sets_retr32 sets_retr_incl.

Definition sets_retr32_Retraction : Retraction sets_retr32 :=
  Build_Retraction _ _ sets_retr32 sets_incl23 sets_retr_incl.

(* ------------------------------------------------------------------------ *)
(* * ** The other 复合 provably not 恒等 （已译） *)

(* At [None] round trip lands [Some true]: retraction folds [None]
 onto [true] 含入 cannot recover it. （已译） *)

Lemma sets_incl_retr_not_id :
  sets_incl23 ∘[Sets] sets_retr32 ≈ id{Sets} → False.
Proof. intro H; discriminate (H None). Qed.

(* So splitting's idempotent not 恒等 -- exactly what
 generic Karoubi construction never exhibits. （已译） *)
Lemma sets_incl_retr_idempotent :
  Idempotent (sets_incl23 ∘[Sets] sets_retr32).
Proof.
  exact (split_pair_idempotent sets_retr32 sets_incl23 sets_retr_incl).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Neither map is an isomorphism *)

(* The inclusion misses [None], so no right inverse can reach it: whatever
   value a candidate inverse returns there, [Some] of it is not [None]. *)

Lemma sets_incl23_not_iso : IsIsomorphism sets_incl23 → False.
Proof. intros [t Hr _]; discriminate (Hr None). Qed.

(* 相关说明。 （已译） *)

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
(* 相关说明。 （已译） *)

(*
   本节说明 Split 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sets_split_mono_not_iso :
  @SplitMonoClass Sets sets_two sets_three sets_incl23
  * (@IsoClass Sets sets_two sets_three sets_incl23 → False) :=
  (sets_incl23_Section, sets_incl23_not_iso).

Definition sets_split_epi_not_iso :
  @SplitEpiClass Sets sets_three sets_two sets_retr32
  * (@IsoClass Sets sets_three sets_two sets_retr32 → False) :=
  (sets_retr32_Retraction, sets_retr32_not_iso).

(* The Seven Sketches example full: one-sided inverse pair whose other
 复合 provably not 恒等, neither map invertible. （已译） *)
Definition sets_split_pair_not_iso :
  (sets_retr32 ∘[Sets] sets_incl23 ≈ id{Sets})
  * ((sets_incl23 ∘[Sets] sets_retr32 ≈ id{Sets}) → False)
  * (IsIsomorphism sets_incl23 → False)
  * (IsIsomorphism sets_retr32 → False) :=
  (sets_retr_incl, sets_incl_retr_not_id,
   sets_incl23_not_iso, sets_retr32_not_iso).

(* ------------------------------------------------------------------------ *)
(** ** Both maps are regular *)

(* 相关说明。 （已译） *)

Definition sets_incl23_regular : RegularMorphism sets_incl23 :=
  regular_of_section _ sets_incl23_Section.

Definition sets_retr32_regular : RegularMorphism sets_retr32 :=
  regular_of_retraction _ sets_retr32_Retraction.
