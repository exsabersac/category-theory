Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sieve.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Pullback.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Fun.Classifier.

Open Scope category_scope.

(** * Presheaf categories are elementary toposes *)

(*
 Book:      Awodey, Category Theory (1st ed., Carnegie Mellon
 Book:      Fong & Spivak, Seven Sketches in Compositionality, §7.3,
 nLab:      https://ncatlab.org/nlab/show/presheaf+topos
 nLab:      https://ncatlab.org/nlab/show/topos
 Wikipedia: https://en.wikipedia.org/wiki/Topos

   本文件给出 topos 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** (A) The four bundles *)

(* [(C^op)^op = C] by conversion: what makes the covariant reading a
   [:=] rather than a transport. *)
Example psh_op_invol (C : Category) : (C^op)^op = C := eq_refl.

Definition Presheaf_Topos@{o h so} (C : Category@{o h h})
  (UT : Untruncate@{h}) : ElementaryTopos ([C^op, Sets@{h so}]) := {|
  topos_terminal   := Functor_Category_Terminal Sets_Terminal;
  topos_cartesian  := Functor_Category_Cartesian (C^op) Sets Sets_Cartesian;
  topos_pullbacks  := Fun_HasPullbacks Sets_HasPullbacks;
  topos_closed     := Functor_Category_Closed C;
  topos_classifier := Fun_Classifier UT
|}.

Definition Presheaf_Topos_IEM@{o h so} (C : Category@{o h h})
  (Em : IEM@{h}) : ElementaryTopos ([C^op, Sets@{h so}]) :=
  Presheaf_Topos@{o h so} C (untruncate_of_IEM Em).

(* Seven Sketches §7.3 footnote 5: "The category of functors C → Set is
   also a topos: use C^op as the defining site." *)
Definition Copresheaf_Topos@{o h so} (C : Category@{o h h})
  (UT : Untruncate@{h}) : ElementaryTopos ([C, Sets@{h so}]) :=
  Presheaf_Topos@{o h so} (C^op) UT.

Definition Copresheaf_Topos_IEM@{o h so} (C : Category@{o h h})
  (Em : IEM@{h}) : ElementaryTopos ([C, Sets@{h so}]) :=
  Copresheaf_Topos@{o h so} C (untruncate_of_IEM Em).

(** ** (B) The five fields, and the two derived objects, read back *)

Section Readback.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universes ro rh rso.
Context (C : Category@{ro rh rh}) (UT : Untruncate@{rh}).

Example psh_topos_terminal :
  @topos_terminal _ (Presheaf_Topos C UT)
  = @Functor_Category_Terminal (C^op) Sets Sets_Terminal := eq_refl.

Example psh_topos_cartesian :
  @topos_cartesian _ (Presheaf_Topos C UT)
  = @Functor_Category_Cartesian (C^op) Sets Sets_Cartesian := eq_refl.

Example psh_topos_pullbacks :
  @topos_pullbacks _ (Presheaf_Topos C UT)
  = @Fun_HasPullbacks (C^op) Sets Sets_HasPullbacks := eq_refl.

Example psh_topos_closed :
  @topos_closed _ (Presheaf_Topos C UT) = Functor_Category_Closed C
  := eq_refl.

Example psh_topos_classifier :
  @topos_classifier _ (Presheaf_Topos C UT) = Fun_Classifier UT := eq_refl.

(* The exponential IS Awodey's display-(8.5) presheaf.  This is the
   issue's reviewer check that it is proved rather than postulated. *)
Example psh_topos_exponent (P Q : C^op ⟶ Sets) :
  @exponent_obj _ _ (@topos_closed _ (Presheaf_Topos C UT)) P Q
  = PshExp P Q := eq_refl.

(* Ω is Awodey's presheaf of sieves, and truth his total sieve. *)
Example psh_topos_omega :
  @Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))
  = Sieve_Presheaf C := eq_refl.

Example psh_topos_truth :
  @truth ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))
  = sieve_truth C := eq_refl.

(* Mac Lane's Axiom 9 object, unfolded: the power object of a presheaf
   is its exponential by Ω. *)
Example psh_topos_pow (P : C^op ⟶ Sets) :
  @Pow ([C^op, Sets]) (Presheaf_Topos C UT) P
  = PshExp P (Sieve_Presheaf C) := eq_refl.

(* The terminal presheaf is the one Instance/Fun/Exponential.v names. *)
Example psh_terminal_is_donor :
  @topos_terminal _ (Presheaf_Topos C UT) = presheaf_terminal C := eq_refl.

(* The chosen pullback is the pointwise one.  The category must be
   written out in the two arrows, or elaboration stalls. *)
Example psh_pullback_is_donor (F G H : C^op ⟶ Sets)
  (a : F ~{[C^op, Sets]}~> H) (b : G ~{[C^op, Sets]}~> H) :
  @pullback ([C^op, Sets]) (@topos_pullbacks _ (Presheaf_Topos C UT))
    F G H a b
  = Fun_Pullback Sets_HasPullbacks a b := eq_refl.

(* The covariant reading is not a parallel construction: its closed and
   classifier fields ARE the tree's own covariant donors. *)
Example copsh_topos_closed :
  @topos_closed _ (Copresheaf_Topos C UT) = Functor_Category_Closed_cov C
  := eq_refl.

Example copsh_topos_classifier :
  @topos_classifier _ (Copresheaf_Topos C UT) = Fun_Classifier_cov UT
  := eq_refl.

(*
   本节说明 Topos 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example copsh_is_psh_at_op (C : Category) (UT : Untruncate) :
  Copresheaf_Topos C UT = Presheaf_Topos (C^op) UT := eq_refl.

Example psh_is_copsh_at_op (C : Category) (UT : Untruncate) :
  Copresheaf_Topos (C^op) UT = Presheaf_Topos C UT := eq_refl.

Example copsh_iem_is_psh_iem_at_op (C : Category) (Em : IEM) :
  Copresheaf_Topos_IEM C Em = Presheaf_Topos_IEM (C^op) Em := eq_refl.

(** ** (C) Awodey's three displays *)

(* "t : 1 → Ω, namely, at each C, the 'total sieve': t_C = {f : · → C}." *)
Example psh_truth_is_total_sieve (c : C)
  (u : carrier (fobj[@terminal_obj ([C^op, Sets])
                       (@topos_terminal _ (Presheaf_Topos C UT))] c)) :
  transform[@truth ([C^op, Sets]) _
              (@topos_classifier _ (Presheaf_Topos C UT))] c u
  = @total_sieve C c := eq_refl.

(*
   本节说明 Topos 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example psh_char_is_awodey_sieve (E U : C^op ⟶ Sets) (theta : U ⟹ E)
  (M : @Monic ([C^op, Sets]) U E theta) (c d : C)
  (e : carrier (fobj[E] c)) (f : d ~{C}~> c) :
  sieve_mem (transform[@char ([C^op, Sets]) _
                         (@topos_classifier _ (Presheaf_Topos C UT))
                         U E theta M] c e) f
  = Powerset_squash (∃ x : carrier (fobj[U] d),
                       transform[theta] d x ≈ fmap[E] f e) := eq_refl.

(* "and given h : D → C let h* : Ω(C) → Ω(D) be defined by:
    h*(S) = {g : · → D | h ∘ g ∈ S}."  The arrow must be ascribed into
   [C^op]; see the spelling note in the header. *)
Example psh_omega_is_restriction (c d : C) (h : d ~{C}~> c) (S : Sieve c) :
  fmap[@Ω ([C^op, Sets]) _ (@topos_classifier _ (Presheaf_Topos C UT))]
      (h : c ~{C^op}~> d) S
  = sieve_restrict h S := eq_refl.

End Readback.
