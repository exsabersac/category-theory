Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Open Scope category_scope.

(* * * The 范畴 setoids elementary topos （已译） *)

(*
 Book:      Mac Lane, ibid., Appendix "Foundations", §App.1, printed
 nLab:      https://ncatlab.org/nlab/show/topos
 Wikipedia: https://en.wikipedia.org/wiki/Topos

   本文件给出 topos 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** (A) The three bundles *)

Definition Sets_Topos@{o so} (U : Untruncate@{o}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  {| topos_terminal   := Sets_Terminal@{so o}
   ; topos_cartesian  := Sets_Cartesian@{so o}
   ; topos_pullbacks  := Sets_HasPullbacks@{so o}
   ; topos_closed     := Sets_Closed@{so o}
   ; topos_classifier := Sets_Classifier@{o so} U |}.

Definition Sets_Topos_dec@{o so} (D : DecImage@{o so}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  {| topos_terminal   := Sets_Terminal@{so o}
   ; topos_cartesian  := Sets_Cartesian@{so o}
   ; topos_pullbacks  := Sets_HasPullbacks@{so o}
   ; topos_closed     := Sets_Closed@{so o}
   ; topos_classifier := Sets_Classifier_dec@{o so} D |}.

Definition Sets_Topos_IEM@{o so} (E : IEM@{o}) :
  ElementaryTopos@{so so o} Sets@{o so} :=
  Sets_Topos@{o so} (untruncate_of_IEM@{o} E).

Example sets_topos_terminal (U : Untruncate) :
  @topos_terminal Sets (Sets_Topos U) = Sets_Terminal := eq_refl.
Example sets_topos_cartesian (U : Untruncate) :
  @topos_cartesian Sets (Sets_Topos U) = Sets_Cartesian := eq_refl.
Example sets_topos_pullbacks (U : Untruncate) :
  @topos_pullbacks Sets (Sets_Topos U) = Sets_HasPullbacks := eq_refl.
Example sets_topos_closed (U : Untruncate) :
  @topos_closed Sets (Sets_Topos U) = Sets_Closed := eq_refl.
Example sets_topos_classifier (U : Untruncate) :
  @topos_classifier Sets (Sets_Topos U) = Sets_Classifier U := eq_refl.
Example sets_topos_dec_classifier (D : DecImage) :
  @topos_classifier Sets (Sets_Topos_dec D) = Sets_Classifier_dec D := eq_refl.

(* * ** (B) App.1 clause (a): 终对象 one-element set,
 clause (b): pullback [a → 1 ← b] [a × b] （已译） *)

Example app1_terminal_carrier (U : Untruncate) :
  carrier (@terminal_obj Sets (@topos_terminal Sets (Sets_Topos U)))
  = poly_unit := eq_refl.

Example app1_terminal_is_donor (U : Untruncate) :
  @terminal_obj Sets (@topos_terminal Sets (Sets_Topos U))
  = @terminal_obj Sets Sets_Terminal := eq_refl.

(* "any set with just one element can serve as a terminal object 1" *)
Lemma app1_terminal_singleton
  (t : carrier (@terminal_obj Sets Sets_Terminal)) : t = ttt.
Proof. destruct t; reflexivity. Qed.

(* 相关说明。 （已译） *)
Definition PBONE@{o so} (a b : obj[Sets@{o so}]) :=
  @pullback Sets@{o so} Sets_HasPullbacks@{so o} a b
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) one one.

Definition pbone@{o so} (a b : obj[Sets@{o so}]) : obj[Sets@{o so}] :=
  Pull _ _ (PBONE@{o so} a b).

Definition pbone_fst@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> a := pullback_fst _ _ (PBONE@{o so} a b).

Definition pbone_snd@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> b := pullback_snd _ _ (PBONE@{o so} a b).

Definition pbone_to_prod@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ~{Sets@{o so}}~> a × b :=
  pbone_fst@{o so} a b △ pbone_snd@{o so} a b.

(* 相关说明。 （已译） *)
Definition pbone_sq@{o so} (a b : obj[Sets@{o so}]) :
  one ∘ exl ≈ one ∘ (exr : a × b ~{Sets@{o so}}~> b).
Proof.
  intro p; destruct ((one[a] ∘ exl) p);
    destruct ((one[b] ∘ (exr : a × b ~{Sets@{o so}}~> b)) p); reflexivity.
Defined.

Definition pbone_from_prod@{o so} (a b : obj[Sets@{o so}]) :
  a × b ~{Sets@{o so}}~> pbone@{o so} a b :=
  unique_obj (ump_pullbacks _ _ (PBONE@{o so} a b) (a × b) exl exr
                (pbone_sq@{o so} a b)).

Definition pullback_over_one_is_product@{o so} (a b : obj[Sets@{o so}]) :
  pbone@{o so} a b ≅ a × b.
Proof.
  unshelve refine {| to := pbone_to_prod@{o so} a b
                   ; from := pbone_from_prod@{o so} a b |}.
  - destruct (unique_property
                (ump_pullbacks _ _ (PBONE@{o so} a b) (a × b) exl exr
                   (pbone_sq@{o so} a b))) as [H1 H2].
    intro p; split; [ exact (H1 p) | exact (H2 p) ].
  - intro p; split; reflexivity.
Defined.

(* "with projections given factors b": four leg
 equations, at setoid 关系. （已译） *)
Lemma pbone_to_exl (a b : obj[Sets]) :
  exl ∘ pbone_to_prod a b ≈ pbone_fst a b.
Proof. intro p; reflexivity. Qed.

Lemma pbone_to_exr (a b : obj[Sets]) :
  exr ∘ pbone_to_prod a b ≈ pbone_snd a b.
Proof. intro p; reflexivity. Qed.

Lemma pbone_from_fst (a b : obj[Sets]) :
  pbone_fst a b ∘ pbone_from_prod a b ≈ exl.
Proof.
  exact (fst (unique_property
                (ump_pullbacks _ _ (PBONE a b) (a × b) exl exr
                   (pbone_sq a b)))).
Qed.

Lemma pbone_from_snd (a b : obj[Sets]) :
  pbone_snd a b ∘ pbone_from_prod a b ≈ exr.
Proof.
  exact (snd (unique_property
                (ump_pullbacks _ _ (PBONE a b) (a × b) exl exr
                   (pbone_sq a b)))).
Qed.

(* The mediator REDUCES: Instance/Sets/Pullback.v's [Sets_IsPullback] is
 [Defined], so pullback's 普遍性质 computes. （已译） *)
Example pbone_from_computes (a b : obj[Sets]) :
  pbone_from_prod a b = sets_pb_med one one exl exr (pbone_sq a b) := eq_refl.

(* 相关说明。 （已译） *)
Example app1_pullback_is_topos_pullback (U : Untruncate) (a b : obj[Sets]) :
  @pullback Sets (@topos_pullbacks Sets (Sets_Topos U)) a b
    (@terminal_obj Sets (@topos_terminal Sets (Sets_Topos U))) one one
  = PBONE a b := eq_refl.

(* 相关说明。 （已译） *)

(* Mac Lane's "any set 2 consisting two 对象, 1 0", the
 decidable route. （已译） *)
Example app1_omega_dec (D : DecImage) :
  @Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D)) = BoolSetoid
  := eq_refl.
Example app1_omega_dec_carrier (D : DecImage) :
  carrier (@Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D)))
  = poly_bool := eq_refl.
Example app1_truth_dec (D : DecImage) :
  @truth Sets _ (@topos_classifier Sets (Sets_Topos_dec D)) ttt = ptrue
  := eq_refl.

(* and truncation route's own truth-value 对象 （已译） *)
Example app1_omega_U (U : Untruncate) :
  @Ω Sets _ (@topos_classifier Sets (Sets_Topos U)) = Powerset_Omega
  := eq_refl.
Example app1_truth_U (U : Untruncate) :
  @truth Sets _ (@topos_classifier Sets (Sets_Topos U)) ttt
  = Powerset_truth_point := eq_refl.

(* 相关说明。 （已译） *)
Definition app1_truth_monic (U : Untruncate) :
  @Monic Sets _ _ (@truth Sets _ (@topos_classifier Sets (Sets_Topos U)))
  := @truth_monic Sets _ _.

(* 相关说明。 （已译） *)
Definition app1_char_rule_dec@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} _
     (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) u x m M b
     ≈ @truth Sets@{o so} _
         (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) ttt)
    ↔ sets_in_image@{o} m b
  := sets_classifier_dec_char_iff@{o so} D m M b.

Definition app1_char_rule_U@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  (@char Sets@{o so} _
     (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M b
     ≈ @truth Sets@{o so} _
         (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) ttt)
    ↔ sets_in_image@{o} m b
  := sets_classifier_char_iff@{o so} U m M b.

Example app1_char_dec_strict@{o so} (D : DecImage@{o so})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :
  @char Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos_dec@{o so} D)) u x m M
  = char_of_dec@{o so} m M (D u x m M) := eq_refl.

Example app1_char_U_strict@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) (b : carrier x) :
  @char Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M b
  = Powerset_squash@{o} (sets_in_image@{o} m b) := eq_refl.

(* 相关说明。 （已译） *)
Definition app1_classifying_square@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :=
  @char_pullback Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M.

Definition app1_classifying_unique@{o so} (U : Untruncate@{o})
  {u x : SetoidObject@{o o}} (m : u ~{Sets@{o so}}~> x)
  (M : @Monic Sets@{o so} u x m) :=
  @char_unique Sets@{o so} _
    (@topos_classifier Sets@{o so} (Sets_Topos@{o so} U)) u x m M.

(* 相关说明。 （已译） *)

(* Mac Lane's "P b, set all subsets s b" -- definitional, not
 同构. See header why two records coincide. （已译） *)
Example app1_pow_is_powerset (U : Untruncate) (b : obj[Sets]) :
  @Pow Sets (Sets_Topos U) b = Powerset_Prop_obj b := eq_refl.

Example app1_pow_carrier (U : Untruncate) (b : obj[Sets]) :
  carrier (@Pow Sets (Sets_Topos U) b)
  = SetoidMorphism b Powerset_Prop_truth := eq_refl.

(* 相关说明。 （已译） *)
Example app1_pow_dec_carrier (D : DecImage) (b : obj[Sets]) :
  carrier (@Pow Sets (Sets_Topos_dec D) b) = SetoidMorphism b BoolSetoid
  := eq_refl.

(* 相关说明。 （已译） *)
Example app1_eval_is_application (U : Untruncate) (b : obj[Sets])
  (s : carrier (@Pow Sets (Sets_Topos U) b)) (x : carrier b) :
  @eval Sets Sets_Cartesian Sets_Closed b
        (@Ω Sets _ (@topos_classifier Sets (Sets_Topos U))) (s, x) = s x
  := eq_refl.

Example app1_eval_dec_is_application (D : DecImage) (b : obj[Sets])
  (s : carrier (@Pow Sets (Sets_Topos_dec D) b)) (x : carrier b) :
  @eval Sets Sets_Cartesian Sets_Closed b
        (@Ω Sets _ (@topos_classifier Sets (Sets_Topos_dec D))) (s, x) = s x
  := eq_refl.
