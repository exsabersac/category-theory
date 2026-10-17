Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.

Generalizable All Variables.

(** * Natural transformations between group homomorphisms are conjugations *)

(*
   nLab:      https://ncatlab.org/nlab/show/delooping
   nLab:      https://ncatlab.org/nlab/show/automorphism+2-group
   Wikipedia: https://en.wikipedia.org/wiki/Inner_automorphism
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Awodey, "Category Theory", 2nd ed., Oxford Logic Guides 52,
   Book:      Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
   Book:      Riehl, "Category Theory in Context", Exercise 1.4.ii,

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/automorphism+2-group
   Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",

   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(** ** Functors between deloopings are monoid homomorphisms *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Deloop_map {M N : MonObject} (f : MonHom M N) :
  Deloop M ⟶ Deloop N :=
  @Build_Functor (Deloop M) (Deloop N)
    (fun _ => ttt)                              (* nothing to choose on objects *)
    (fun _ _ a => f a)                          (* an arrow is an element *)
    (fun _ _ => mon_map_respects f)
    (fun _ => mon_map_unit f)                   (* fmap id ≈ id  is  f 1 ≈ 1 *)
    (fun _ _ _ a b => mon_map_op f a b).        (* fmap (a ∘ b) is f (a · b) *)

(* And the other half: a functor between deloopings is a homomorphism, its
   action on the single hom-set.  Again every homomorphism law is a functor
   law by projection. *)
Definition Deloop_unmap {M N : MonObject} (F : Deloop M ⟶ Deloop N) :
  MonHom M N := {|
  mon_map          := fun a => @fmap _ _ F ttt ttt a;
  mon_map_respects := @fmap_respects _ _ F ttt ttt;
  mon_map_unit     := @fmap_id _ _ F ttt;
  mon_map_op       := fun a b => @fmap_comp _ _ F ttt ttt ttt a b
|}.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Deloop_unmap_map {M N : MonObject} (f : MonHom M N) :
  Deloop_unmap (Deloop_map f) = f := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Deloop_map_unmap_fmap {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (a : carrier M) :
  @fmap _ _ (Deloop_map (Deloop_unmap F)) ttt ttt a = @fmap _ _ F ttt ttt a
  := eq_refl.

Example Deloop_map_unmap_fobj {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (x : Deloop M) : fobj[Deloop_map (Deloop_unmap F)] x = fobj[F] x.
Proof. destruct (fobj[F] x); reflexivity. Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Deloop_map_distinct {M N : MonObject} (f g : MonHom M N) (a : carrier M) :
  (f a = g a → False) → Deloop_map f = Deloop_map g → False.
Proof.
  intros Hne Heq.
  apply Hne.
  exact (f_equal
           (fun F : Deloop M ⟶ Deloop N => (@fmap _ _ F ttt ttt a : carrier N))
           Heq).
Qed.

(** ** The composition-order convention, checked *)

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example deloop_compose_mon_op (N : MonObject) :
  @compose (Deloop N) ttt ttt ttt = @mon_op N := eq_refl.

(** ** The characterization, for monoids *)

Section Intertwining.

Context {M N : MonObject}.
Context (F G : Deloop M ⟶ Deloop N).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Intertwines (h : carrier N) : Type :=
  ∀ a : carrier M, mon_op (Deloop_unmap G a) h ≈ mon_op h (Deloop_unmap F a).

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition transform_intertwines (n : F ⟹ G) : Intertwines (transform n ttt) :=
  naturality n ttt ttt.

(*
   本节说明自然变换相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition intertwines_transform (h : carrier N) (I : Intertwines h) : F ⟹ G.
Proof.
  refine (@Build_Transform' _ _ F G (fun _ => h) _).
  intros x y a.
  destruct x, y.
  exact (I a).
Defined.

(* The component of the transformation built from h is h, by [eq_refl]. *)
Example intertwines_transform_component (h : carrier N) (I : Intertwines h) :
  transform (intertwines_transform h I) ttt = h := eq_refl.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem transform_iff_intertwines : (F ⟹ G) ↔ ∃ h : carrier N, Intertwines h.
Proof.
  split.
  - intro n.
    exists (transform n ttt).
    exact (transform_intertwines n).
  - intros [h I].
    exact (intertwines_transform h I).
Defined.

(** ** The correspondence at the level of setoids *)

(*
   本节说明同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Intertwiner : Type := ∃ h : carrier N, Intertwines h.

Program Definition Intertwiner_Setoid : Setoid Intertwiner := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - now transitivity (`1 y).
Qed.

Definition Deloop_Transforms : SetoidObject := {|
  carrier   := F ⟹ G;
  is_setoid := Transform_Setoid
|}.

Definition Deloop_Intertwiners : SetoidObject := {|
  carrier   := Intertwiner;
  is_setoid := Intertwiner_Setoid
|}.

(* A transformation to its component, with the naturality square read as the
   intertwining condition. *)
Program Definition transform_intertwiner :
  Deloop_Transforms ~{Sets}~> Deloop_Intertwiners := {|
  morphism := fun n => existT _ (transform n ttt) (transform_intertwines n)
|}.
Next Obligation.
  intros n1 n2 Hn.
  exact (Hn ttt).
Qed.

(* And back. *)
Program Definition intertwiner_transform :
  Deloop_Intertwiners ~{Sets}~> Deloop_Transforms := {|
  morphism := fun p => intertwines_transform (`1 p) (`2 p)
|}.
Next Obligation.
  intros p q Hpq x; simpl.
  exact Hpq.
Qed.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition transform_intertwiner_iso :
  Deloop_Transforms ≅[Sets] Deloop_Intertwiners := {|
  to   := transform_intertwiner;
  from := intertwiner_transform
|}.
Next Obligation.
  intro p; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n x; simpl.
  destruct x.
  reflexivity.
Qed.

End Intertwining.

Arguments Intertwines {M N} F G h.
Arguments Intertwiner {M N} F G.

(** ** The characterization, for groups: Mac Lane §I.4 Exercise 3 *)

Section GroupConjugation.

Context {M : MonObject}.
Context {Grp : GrpObject}.
Context (F G : Deloop M ⟶ Deloop Grp).

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Conjugates (h : carrier Grp) : Type :=
  ∀ a : carrier M,
    Deloop_unmap G a ≈ mon_op (mon_op h (Deloop_unmap F a)) (grp_inv h).

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example conjugates_is_conjugation (h : carrier Grp) :
  Conjugates h
    = ∀ a : carrier M,
        Deloop_unmap G a
          ≈ conjugate (Deloop_IsGroupoid Grp) (x:=ttt) (x':=ttt)
              h (Deloop_unmap F a)
  := eq_refl.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma intertwines_conjugates (h : carrier Grp) :
  Intertwines F G h → Conjugates h.
Proof.
  intros I a.
  rewrite <- (I a).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

Lemma conjugates_intertwines (h : carrier Grp) :
  Conjugates h → Intertwines F G h.
Proof.
  intros Cj a.
  rewrite (Cj a).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_l.
  now rewrite mon_op_unit_r.
Qed.

Lemma conjugates_iff_intertwines (h : carrier Grp) :
  Conjugates h ↔ Intertwines F G h.
Proof.
  split.
  - apply conjugates_intertwines.
  - apply intertwines_conjugates.
Defined.

End GroupConjugation.

Arguments Conjugates {M Grp} F G h.

(** ** The set of conjugating elements *)

Section ConjugatorIso.

Context {M : MonObject}.
Context {Grp : GrpObject}.
Context (F G : Deloop M ⟶ Deloop Grp).

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Conjugator : Type := ∃ h : carrier Grp, Conjugates F G h.

Program Definition Conjugator_Setoid : Setoid Conjugator := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - now symmetry.
  - now transitivity (`1 y).
Qed.

Definition Deloop_Conjugators : SetoidObject := {|
  carrier   := Conjugator;
  is_setoid := Conjugator_Setoid
|}.

(* A transformation to its component, read as a conjugating element. *)
Program Definition transform_conjugator :
  Deloop_Transforms F G ~{Sets}~> Deloop_Conjugators := {|
  morphism := fun n => existT _ (transform n ttt)
    (intertwines_conjugates F G _ (transform_intertwines F G n))
|}.
Next Obligation.
  intros n1 n2 Hn.
  exact (Hn ttt).
Qed.

(* And back. *)
Program Definition conjugator_transform :
  Deloop_Conjugators ~{Sets}~> Deloop_Transforms F G := {|
  morphism := fun p => intertwines_transform F G (`1 p)
    (conjugates_intertwines F G (`1 p) (`2 p))
|}.
Next Obligation.
  intros p q Hpq x; simpl.
  exact Hpq.
Qed.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition transform_conjugator_iso :
  Deloop_Transforms F G ≅[Sets] Deloop_Conjugators := {|
  to   := transform_conjugator;
  from := conjugator_transform
|}.
Next Obligation.
  intro p; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n x; simpl.
  destruct x.
  reflexivity.
Qed.

End ConjugatorIso.

Arguments Conjugator {M Grp} F G.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition transform_conjugator_hom {B C : GrpObject} (S T : MonHom B C) :
  Deloop_Transforms (Deloop_map S) (Deloop_map T)
    ≅[Sets] Deloop_Conjugators (Deloop_map S) (Deloop_map T) :=
  transform_conjugator_iso (Deloop_map S) (Deloop_map T).

(* Right cancellation in a group, the one piece of group arithmetic used
   below that is not already in Construction/Deloop.v. *)
Lemma grp_cancel_r {Grp : GrpObject} (a b c : carrier Grp) :
  mon_op a c ≈ mon_op b c → a ≈ b.
Proof.
  intro H.
  rewrite <- (mon_op_unit_r a), <- (grp_inv_r c), mon_op_assoc, H.
  rewrite <- mon_op_assoc, grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

(* Conjugation by h⁻¹ runs the other way.  This is the computation Awodey's
   consequence rests on, isolated from the transformation that carries it. *)
Lemma conjugates_inverse {M : MonObject} {Grp : GrpObject}
  (F G : Deloop M ⟶ Deloop Grp) (h : carrier Grp) :
  Conjugates F G h → Conjugates G F (grp_inv h).
Proof.
  intro Cj.
  apply intertwines_conjugates.
  intro a.
  apply (grp_cancel_r _ _ h).
  rewrite <- !mon_op_assoc.
  rewrite grp_inv_l, mon_op_unit_r.
  rewrite (conjugates_intertwines F G h Cj a).
  rewrite mon_op_assoc, grp_inv_l.
  now rewrite mon_op_unit_l.
Qed.

(*
   本节说明自然变换、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem transform_iff_conjugate {B C : GrpObject} (S T : MonHom B C) :
  (Deloop_map S ⟹ Deloop_map T)
    ↔ ∃ h : carrier C,
        ∀ g : carrier B, T g ≈ mon_op (mon_op h (S g)) (grp_inv h).
Proof.
  split.
  - intro n.
    destruct (fst (transform_iff_intertwines (Deloop_map S) (Deloop_map T)) n)
      as [h I].
    exists h.
    exact (intertwines_conjugates (Deloop_map S) (Deloop_map T) h I).
  - intros [h C'].
    apply (snd (transform_iff_intertwines (Deloop_map S) (Deloop_map T))).
    exists h.
    exact (conjugates_intertwines (Deloop_map S) (Deloop_map T) h C').
Defined.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem transform_iff_conjugate_SWAPPED {B C : GrpObject} (S T : MonHom B C) :
  (Deloop_map S ⟹ Deloop_map T)
    ↔ ∃ h : carrier C,
        ∀ g : carrier B, S g ≈ mon_op (mon_op h (T g)) (grp_inv h).
Proof.
  split.
  - intro n.
    destruct (fst (transform_iff_conjugate S T) n) as [h Cj].
    exists (grp_inv h).
    exact (conjugates_inverse (Deloop_map S) (Deloop_map T) h Cj).
  - intros [h Cj].
    apply (snd (transform_iff_conjugate S T)).
    exists (grp_inv h).
    exact (conjugates_inverse (Deloop_map T) (Deloop_map S) h Cj).
Defined.

(** ** Awodey §7.7: the functor category is a groupoid *)

(*
   本节说明自然变换、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Fun_ginv {C D : Category} (GD : IsGroupoid D) {F K : C ⟶ D}
  (n : F ⟹ K) : K ⟹ F.
Proof.
  refine (@Build_Transform' _ _ K F (fun x => ginv GD (transform n x)) _).
  intros x y f.
  symmetry.
  apply (ginv_move_r GD).
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc, ginv_left.
  now rewrite id_left.
Defined.

Definition Fun_IsGroupoid {C D : Category} (GD : IsGroupoid D) :
  IsGroupoid ([C, D]).
Proof.
  intros F K n.
  refine (@Build_IsIsomorphism ([C, D]) F K n (Fun_ginv GD n) _ _).
  - intro x; simpl.
    rewrite fmap_id.
    apply ginv_right.
  - intro x; simpl.
    rewrite fmap_id.
    apply ginv_left.
Defined.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Deloop_Fun_IsGroupoid (M : MonObject) (Grp : GrpObject) :
  IsGroupoid ([Deloop M, Deloop Grp]) :=
  Fun_IsGroupoid (Deloop_IsGroupoid Grp).

(* Awodey's invertibility sentence, named — "Clearly, every such arrow
   ϑ : f → g has an inverse ϑ⁻¹ : g → f (conjugation by h⁻¹)", which stands
   in both editions (2nd ed. p. 167, 1st ed. p. 175): every natural
   transformation between two functors into the delooping of a group is
   invertible.  This is [Deloop_Fun_IsGroupoid] read at one transformation. *)
Definition deloop_transform_invertible {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  @IsIsomorphism ([Deloop M, Deloop Grp]) F G n :=
  Deloop_Fun_IsGroupoid M Grp F G n.

(* And the inverse really is conjugation by h⁻¹, in two steps.  First, its
   component is the group inverse of the component, on the nose: no
   transport, no rewriting, [eq_refl]. *)
Example deloop_ginv_component {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  transform (ginv (Deloop_Fun_IsGroupoid M Grp) n) ttt
    = grp_inv (transform n ttt) := eq_refl.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma deloop_ginv_conjugates {M : MonObject} {Grp : GrpObject}
  {F G : Deloop M ⟶ Deloop Grp} (n : F ⟹ G) :
  Conjugates G F (grp_inv (transform n ttt)).
Proof.
  apply conjugates_inverse.
  apply intertwines_conjugates.
  exact (transform_intertwines F G n).
Qed.

(** ** The first trap: the statement is empty over an abelian target *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma abelian_conjugates_agree {M : MonObject} {Grp : GrpObject}
  (F G : Deloop M ⟶ Deloop Grp) (h : carrier Grp)
  (comm : ∀ a b : carrier Grp, mon_op a b ≈ mon_op b a)
  (Cj : Conjugates F G h) :
  ∀ a : carrier M, Deloop_unmap G a ≈ Deloop_unmap F a.
Proof.
  intro a.
  rewrite (Cj a).
  rewrite (comm h (Deloop_unmap F a)).
  rewrite <- mon_op_assoc.
  rewrite grp_inv_r.
  now rewrite mon_op_unit_r.
Qed.

(* Z/2 and Z/3 — the only groups the tree had until Structure/Groupoid.v
   added S3 — are both abelian, so by the lemma above neither can display a
   conjugation that moves anything. *)
Lemma Bool_Xor_abelian :
  ∀ a b : carrier Bool_Xor_Grp, mon_op a b ≈ mon_op b a.
Proof. intros [|] [|]; reflexivity. Qed.

Lemma Z3_abelian : ∀ a b : carrier Z3_Grp, mon_op a b ≈ mon_op b a.
Proof. intros [| |] [| |]; reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Bool_conjugates_agree {M : MonObject}
  (F G : Deloop M ⟶ Deloop Bool_Xor_Grp) (h : carrier Bool_Xor_Grp)
  (Cj : Conjugates F G h) :
  ∀ a : carrier M, Deloop_unmap G a ≈ Deloop_unmap F a.
Proof. exact (abelian_conjugates_agree F G h Bool_Xor_abelian Cj). Qed.

(** ** A nonabelian witness *)

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition S3_involution_hom (x : S3) (Hx : S3_mul x x = S3_e) :
  MonHom Bool_Xor S3_Mon := {|
  mon_map := fun b => if b then x else S3_e
|}.
Next Obligation.                        (* the unit goes to the unit *)
  intros x Hx.
  reflexivity.
Qed.
Next Obligation.                        (* and the product to the product *)
  intros x Hx a b.
  destruct x, a, b; simpl; try reflexivity; discriminate Hx.
Qed.

Definition S3_hom_e : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_e eq_refl.
Definition S3_hom_a : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_a eq_refl.
Definition S3_hom_c : MonHom Bool_Xor S3_Mon := S3_involution_hom S3_c eq_refl.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition S3_conjugator_noncentral :
  mon_op (m:=S3_Mon) S3_r S3_a ≈ mon_op (m:=S3_Mon) S3_a S3_r → False :=
  S3_not_abelian.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_hom_conjugate :
  @Conjugates Bool_Xor S3_Grp (Deloop_map S3_hom_a) (Deloop_map S3_hom_c) S3_r.
Proof. intros [|]; reflexivity. Qed.

(* So a natural transformation between the two homomorphisms exists, built
   through the backward direction of the theorem. *)
Definition S3_conjugating_transform :
  Deloop_map S3_hom_a ⟹ Deloop_map S3_hom_c :=
  snd (@transform_iff_conjugate Bool_Xor_Grp S3_Grp S3_hom_a S3_hom_c)
      (existT _ S3_r S3_hom_conjugate).

(* Its single component is the conjugating element r itself, by [eq_refl] —
   the backward direction of the theorem puts h in as the component and
   nothing intervenes. *)
Example S3_conjugating_transform_component :
  transform S3_conjugating_transform ttt = S3_r := eq_refl.

(* And it is not degenerate: the two homomorphisms it relates are different,
   so the conjugation genuinely moves one to the other. *)
Theorem S3_conjugation_moves :
  (∀ g : carrier Bool_Xor, S3_hom_a g ≈ S3_hom_c g) → False.
Proof.
  intro H.
  specialize (H true).
  discriminate H.
Qed.

(*
   本节说明 Transform 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary S3_conjugation_needs_nonabelian :
  (∀ a b : carrier S3_Grp, mon_op a b ≈ mon_op b a) → False.
Proof.
  intro comm.
  apply S3_conjugation_moves.
  intro g.
  symmetry.
  exact (@abelian_conjugates_agree Bool_Xor S3_Grp
           (Deloop_map S3_hom_a) (Deloop_map S3_hom_c) S3_r comm
           S3_hom_conjugate g).
Qed.

(** ** Awodey's second sentence: a groupoid, but not a group *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Deloop_S3_two_objects :
  Deloop_map S3_hom_a = Deloop_map S3_hom_c → False.
Proof.
  apply (Deloop_map_distinct S3_hom_a S3_hom_c true).
  discriminate.
Qed.

Definition Deloop_Fun_S3 : Category := [Deloop Bool_Xor_Grp, Deloop S3_Grp].

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition deloop_equivalence_connected {C : Category} {N : MonObject}
  (F : C ⟶ Deloop N) (E : EquivalenceOfCategories F) : Connected C.
Proof.
  pose proof (Equivalence_Full E) as Ful.
  intros x y.
  apply hom_zigzag.
  exact (@prefmap _ _ F Ful x y mon_unit).
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_no_transform_trivial :
  (Deloop_map S3_hom_e ⟹ Deloop_map S3_hom_a) → False.
Proof.
  intro n.
  destruct (fst (transform_iff_intertwines
                   (Deloop_map S3_hom_e) (Deloop_map S3_hom_a)) n) as [h I].
  specialize (I true).
  simpl in I.
  destruct h; discriminate I.
Qed.

(* Hence it is not connected — a zig-zag between those two objects would
   collapse, the category being a groupoid, to an arrow between them. *)
Theorem Deloop_Fun_S3_not_connected : Connected Deloop_Fun_S3 → False.
Proof.
  intro K.
  apply S3_no_transform_trivial.
  exact (zigzag_hom (Deloop_Fun_IsGroupoid Bool_Xor_Grp S3_Grp)
           (K (Deloop_map S3_hom_e) (Deloop_map S3_hom_a))).
Qed.

(*
   本节说明幺半群、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Deloop_Fun_S3_not_deloop (N : MonObject) (F : Deloop_Fun_S3 ⟶ Deloop N)
  (E : EquivalenceOfCategories F) : False.
Proof.
  exact (Deloop_Fun_S3_not_connected (deloop_equivalence_connected F E)).
Qed.

Corollary Deloop_Fun_S3_not_deloop_rev (N : MonObject)
  (F : Deloop N ⟶ Deloop_Fun_S3) (E : EquivalenceOfCategories F) : False.
Proof.
  exact (Deloop_Fun_S3_not_deloop N (@quasi_inverse _ _ F E)
           (@EquivalenceOfCategories_sym _ _ F E)).
Qed.
