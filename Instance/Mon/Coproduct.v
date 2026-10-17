Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book: Awodey, "Category Theory", 1st ed. (CMU pre-print, Sept 2005),
 nLab:      https://ncatlab.org/nlab/show/free+product
 nLab:      https://ncatlab.org/nlab/show/coproduct
 Wikipedia: https://en.wikipedia.org/wiki/Free_product

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Local Notation MonS := (@Mon Sets Sets_Product_Monoidal).

(** ** Setoid monoids at the element level *)

Definition mon_ob (M : MonS) : SetoidObject := `1 M.

Definition mon_mul (M : MonS) (a b : carrier (mon_ob M))
  : carrier (mon_ob M) :=
  @mu Sets Sets_Product_Monoidal _ (`2 M) (a, b).

Definition mon_one (M : MonS) : carrier (mon_ob M) :=
  @eta Sets Sets_Product_Monoidal _ (`2 M) ttt.

Lemma mon_mul_resp (M : MonS) :
  Proper (equiv ==> equiv ==> equiv) (mon_mul M).
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism (@mu Sets Sets_Product_Monoidal _ (`2 M))
           (a, b) (a', b') (Ha, Hb)).
Qed.

#[local] Existing Instance mon_mul_resp.

Lemma mon_mul_assoc (M : MonS) (a b c : carrier (mon_ob M)) :
  mon_mul M (mon_mul M a b) c ≈ mon_mul M a (mon_mul M b c).
Proof. exact (@mu_assoc Sets Sets_Product_Monoidal _ (`2 M) ((a, b), c)). Qed.

Lemma mon_one_l (M : MonS) (a : carrier (mon_ob M)) :
  mon_mul M (mon_one M) a ≈ a.
Proof. exact (@mu_unit_left Sets Sets_Product_Monoidal _ (`2 M) (ttt, a)). Qed.

Lemma mon_one_r (M : MonS) (a : carrier (mon_ob M)) :
  mon_mul M a (mon_one M) ≈ a.
Proof. exact (@mu_unit_right Sets Sets_Product_Monoidal _ (`2 M) (a, ttt)). Qed.

Definition mon_fun {M N : MonS} (f : M ~{MonS}~> N)
  : carrier (mon_ob M) → carrier (mon_ob N) := `1 f.

Lemma mon_fun_resp {M N : MonS} (f : M ~{MonS}~> N) :
  Proper (equiv ==> equiv) (mon_fun f).
Proof. exact (proper_morphism (`1 f)). Qed.

#[local] Existing Instance mon_fun_resp.

Lemma mon_fun_mul {M N : MonS} (f : M ~{MonS}~> N)
      (a b : carrier (mon_ob M)) :
  mon_fun f (mon_mul M a b) ≈ mon_mul N (mon_fun f a) (mon_fun f b).
Proof. exact (@hom_mu Sets Sets_Product_Monoidal _ _ _ _ _ (`2 f) (a, b)). Qed.

Lemma mon_fun_one {M N : MonS} (f : M ~{MonS}~> N) :
  mon_fun f (mon_one M) ≈ mon_one N.
Proof. exact (@hom_eta Sets Sets_Product_Monoidal _ _ _ _ _ (`2 f) ttt). Qed.

(** ** Smart constructors *)

Program Definition mk_mon_obj (S : SetoidObject)
        (one : carrier S) (op : carrier S → carrier S → carrier S)
        (opr : Proper (equiv ==> equiv ==> equiv) op)
        (oassoc : ∀ a b c, op (op a b) c ≈ op a (op b c))
        (ol : ∀ a, op one a ≈ a)
        (orr : ∀ a, op a one ≈ a) : MonS :=
  (S : obj[Sets];
   {| mu  := {| morphism := fun p => op (fst p) (snd p) |}
    ; eta := {| morphism        := fun _ => one
              ; proper_morphism := fun _ _ _ => reflexivity one |} |}).
Next Obligation.
  intros S one op opr oassoc ol orr p q [Hp Hq]; simpl.
  now apply opr.
Qed.
Next Obligation.
  intros S one op opr oassoc ol orr [[a b] c]; simpl.
  apply oassoc.
Qed.
Next Obligation.
  intros S one op opr oassoc ol orr [u a]; simpl.
  apply ol.
Qed.
Next Obligation.
  intros S one op opr oassoc ol orr [a u]; simpl.
  apply orr.
Qed.

Program Definition mk_mon_hom {M N : MonS}
        (f : carrier (mon_ob M) → carrier (mon_ob N))
        (fp : Proper (equiv ==> equiv) f)
        (fm : ∀ a b, f (mon_mul M a b) ≈ mon_mul N (f a) (f b))
        (fu : f (mon_one M) ≈ mon_one N) : M ~{MonS}~> N :=
  (({| morphism := f |} : mon_ob M ~{Sets}~> mon_ob N); _).
Next Obligation.
  intros M N f fp fm fu.
  unshelve econstructor.
  - intros [a b]; simpl; apply fm.
  - intros []; simpl; apply fu.
Qed.

(** * The free product M * N *)

Section FreeProduct.

Context (M N : MonS).

(* Formal words: a letter from either side, a formal unit, a formal
   product.  No alternation and no reduction are built in; both are
   imposed by the congruence below. *)
Inductive FPTerm : Type :=
  | fp_inl : carrier (mon_ob M) → FPTerm
  | fp_inr : carrier (mon_ob N) → FPTerm
  | fp_one : FPTerm
  | fp_mul : FPTerm → FPTerm → FPTerm.

(* The generated congruence, in four groups: saturation under the two
   source setoids plus congruence for the product; symmetry and
   transitivity (reflexivity is DERIVED, see [fp_refl]); the three
   monoid laws; and the four clauses that make each injection a
   homomorphism — adjacent same-side letters multiply, and each
   summand's unit becomes THE unit. *)
Inductive fp_eq : FPTerm → FPTerm → Type :=
  | fe_inl {a b} : a ≈ b → fp_eq (fp_inl a) (fp_inl b)
  | fe_inr {a b} : a ≈ b → fp_eq (fp_inr a) (fp_inr b)
  | fe_mul {s s' t t'} :
      fp_eq s s' → fp_eq t t' → fp_eq (fp_mul s t) (fp_mul s' t')
  | fe_sym {s t} : fp_eq s t → fp_eq t s
  | fe_trans {s t u} : fp_eq s t → fp_eq t u → fp_eq s u
  | fe_assoc s t u :
      fp_eq (fp_mul (fp_mul s t) u) (fp_mul s (fp_mul t u))
  | fe_one_l s : fp_eq (fp_mul fp_one s) s
  | fe_one_r s : fp_eq (fp_mul s fp_one) s
  | fe_lmul a b :
      fp_eq (fp_mul (fp_inl a) (fp_inl b)) (fp_inl (mon_mul M a b))
  | fe_rmul a b :
      fp_eq (fp_mul (fp_inr a) (fp_inr b)) (fp_inr (mon_mul N a b))
  | fe_lone : fp_eq (fp_inl (mon_one M)) fp_one
  | fe_rone : fp_eq (fp_inr (mon_one N)) fp_one.

(* Reflexivity is derived rather than assumed: the letter cases go to the
   source setoids, the product case to the induction hypotheses, and the
   unit case is [fe_one_l] at [fp_one] composed with its own symmetry. *)
Lemma fp_refl (s : FPTerm) : fp_eq s s.
Proof.
  induction s.
  - apply fe_inl; reflexivity.
  - apply fe_inr; reflexivity.
  - exact (fe_trans (fe_sym (fe_one_l fp_one)) (fe_one_l fp_one)).
  - now apply fe_mul.
Qed.

Definition FPSetoid : Setoid FPTerm := {|
  equiv        := fp_eq;
  setoid_equiv := Build_Equivalence fp_eq fp_refl (@fe_sym) (@fe_trans)
|}.

Definition FPCarrier : SetoidObject := {|
  carrier   := FPTerm;
  is_setoid := FPSetoid
|}.

Definition FreeProd : MonS :=
  mk_mon_obj FPCarrier fp_one fp_mul
    (fun _ _ Hs _ _ Ht => fe_mul Hs Ht)
    fe_assoc fe_one_l fe_one_r.

Definition fp_injl : M ~{MonS}~> FreeProd :=
  @mk_mon_hom M FreeProd fp_inl (fun _ _ H => fe_inl H)
    (fun a b => fe_sym (fe_lmul a b)) fe_lone.

Definition fp_injr : N ~{MonS}~> FreeProd :=
  @mk_mon_hom N FreeProd fp_inr (fun _ _ H => fe_inr H)
    (fun a b => fe_sym (fe_rmul a b)) fe_rone.

Section Mediator.

Context (Q : MonS).
Context (f : M ~{MonS}~> Q).
Context (g : N ~{MonS}~> Q).

(* Evaluation of a formal word in a competing monoid.  A [Fixpoint], so
   [fp_merge]'s two homomorphism laws hold DEFINITIONALLY — the
   Instance/Grp/Pushout.v payoff. *)
Fixpoint fp_eval (s : FPTerm) : carrier (mon_ob Q) :=
  match s with
  | fp_inl a   => mon_fun f a
  | fp_inr b   => mon_fun g b
  | fp_one     => mon_one Q
  | fp_mul s t => mon_mul Q (fp_eval s) (fp_eval t)
  end.

Lemma fp_eval_resp : ∀ s t, fp_eq s t → fp_eval s ≈ fp_eval t.
Proof.
  intros s t H.
  induction H; simpl.
  - now apply mon_fun_resp.
  - now apply mon_fun_resp.
  - now apply mon_mul_resp.
  - now symmetry.
  - now transitivity (fp_eval t).
  - apply mon_mul_assoc.
  - apply mon_one_l.
  - apply mon_one_r.
  - symmetry; apply mon_fun_mul.
  - symmetry; apply mon_fun_mul.
  - apply mon_fun_one.
  - apply mon_fun_one.
Qed.

Definition fp_merge : FreeProd ~{MonS}~> Q :=
  @mk_mon_hom FreeProd Q fp_eval (fun _ _ H => fp_eval_resp _ _ H)
    (fun _ _ => reflexivity _) (reflexivity _).

Lemma fp_merge_unique (h : FreeProd ~{MonS}~> Q)
      (Hl : ∀ a, mon_fun h (fp_inl a) ≈ mon_fun f a)
      (Hr : ∀ b, mon_fun h (fp_inr b) ≈ mon_fun g b) :
  ∀ s, mon_fun h s ≈ fp_eval s.
Proof.
  intro s.
  induction s; simpl.
  - apply Hl.
  - apply Hr.
  - exact (mon_fun_one h).
  - transitivity (mon_mul Q (mon_fun h s1) (mon_fun h s2)).
    + exact (mon_fun_mul h s1 s2).
    + now apply mon_mul_resp.
Qed.

End Mediator.

End FreeProduct.

(** * The free product IS the binary coproduct of Mon(Sets) *)

#[export] Program Instance Mon_Sets_Cocartesian : @Cocartesian MonS := {|
  product_obj := FreeProd;
  fork        := fun Q A B f g => fp_merge A B Q f g;
  exl         := fun A B => fp_injl A B;
  exr         := fun A B => fp_injr A B
|}.
Next Obligation.
  intros Q A B f f' Hf g g' Hg s.
  induction s as [a | b | | s1 IH1 s2 IH2]; simpl.
  - exact (Hf a).
  - exact (Hg b).
  - reflexivity.
  - now apply mon_mul_resp.
Qed.
Next Obligation.
  intros Q A B f g h.
  split.
  - intro Hh.
    split.
    + intro a; exact (Hh (fp_inl A B a)).
    + intro b; exact (Hh (fp_inr A B b)).
  - intros [Hl Hr].
    exact (fp_merge_unique A B Q f g h Hl Hr).
Qed.

(** ** The Cocartesian vocabulary computes to the construction *)

Example coprod_is_FreeProd (A B : MonS) :
  @Coprod MonS Mon_Sets_Cocartesian A B = FreeProd A B := eq_refl.

Example inl_is_fp_injl (A B : MonS) :
  @inl MonS Mon_Sets_Cocartesian A B = fp_injl A B := eq_refl.

Example inr_is_fp_injr (A B : MonS) :
  @inr MonS Mon_Sets_Cocartesian A B = fp_injr A B := eq_refl.

Example merge_is_fp_merge (A B Q : MonS)
        (f : A ~{MonS}~> Q) (g : B ~{MonS}~> Q) :
  @merge MonS Mon_Sets_Cocartesian Q A B f g = fp_merge A B Q f g := eq_refl.

(** * Non-degeneracy, in general: both injections split

    Each injection has a retraction with NO hypothesis on A or B — the
    copairing of the identity with the constant map at the unit — hence
    is monic, hence injective on elements.  So the congruence collapses
    neither factor, for every pair of monoids. *)

Definition mon_const (A B : MonS) : A ~{MonS}~> B :=
  @mk_mon_hom A B (fun _ => mon_one B)
    (fun _ _ _ => reflexivity (mon_one B))
    (fun _ _ => symmetry (mon_one_l B (mon_one B)))
    (reflexivity (mon_one B)).

Lemma triv_eta (a : poly_unit) : ttt = a.
Proof. now destruct a. Qed.

Definition TrivObj : SetoidObject :=
  {| carrier := poly_unit; is_setoid := unit_setoid |}.

Definition TrivMon : MonS :=
  mk_mon_obj TrivObj ttt (fun _ _ => ttt)
    (fun _ _ _ _ _ _ => eq_refl)
    (fun _ _ _ => eq_refl) triv_eta triv_eta.

#[export] Program Instance Mon_Sets_Initial : @Initial MonS := {|
  terminal_obj := TrivMon;
  one          := fun A => mon_const TrivMon A
|}.
Next Obligation.
  intros A f g u.
  destruct u.
  transitivity (mon_one A).
  - exact (mon_fun_one f).
  - symmetry; exact (mon_fun_one g).
Qed.

Definition fp_retl (A B : MonS) : FreeProd A B ~{MonS}~> A :=
  fp_merge A B A (@id MonS A) (mon_const B A).

Definition fp_retr (A B : MonS) : FreeProd A B ~{MonS}~> B :=
  fp_merge A B B (mon_const A B) (@id MonS B).

Lemma fp_retl_injl (A B : MonS) :
  fp_retl A B ∘[MonS] fp_injl A B ≈ @id MonS A.
Proof. intro a; reflexivity. Qed.

Lemma fp_retr_injr (A B : MonS) :
  fp_retr A B ∘[MonS] fp_injr A B ≈ @id MonS B.
Proof. intro b; reflexivity. Qed.

Definition fp_injl_Section (A B : MonS) : Section (fp_injl A B) :=
  {| section := fp_retl A B; section_comp := fp_retl_injl A B |}.

Definition fp_injr_Section (A B : MonS) : Section (fp_injr A B) :=
  {| section := fp_retr A B; section_comp := fp_retr_injr A B |}.

Theorem fp_injections_Monic (A B : MonS) :
  Monic (fp_injl A B) * Monic (fp_injr A B).
Proof.
  exact (sections_are_monic _ _ _ (fp_injl_Section A B),
         sections_are_monic _ _ _ (fp_injr_Section A B)).
Qed.

Theorem fp_inl_injective (A B : MonS) (a a' : carrier (mon_ob A)) :
  fp_eq A B (fp_inl A B a) (fp_inl A B a') → a ≈ a'.
Proof.
  intro H.
  exact (fp_eval_resp A B A (@id MonS A) (mon_const B A) _ _ H).
Qed.

Theorem fp_inr_injective (A B : MonS) (b b' : carrier (mon_ob B)) :
  fp_eq A B (fp_inr A B b) (fp_inr A B b') → b ≈ b'.
Proof.
  intro H.
  exact (fp_eval_resp A B B (mon_const A B) (@id MonS B) _ _ H).
Qed.

(** * A non-degenerate witness: (N,+) * (N,+)

    The free product of two copies of the free monoid on one generator is
    the free monoid on two letters, so the probe into (list bool, ++,
    nil) sending the left generator to [true] and the right to [false]
    is faithful enough to separate.  Nothing below could be proved by
    induction on [fp_eq]: a NEGATIVE fact about a generated congruence is
    reachable only by mapping OUT of the quotient, which is what
    [fp_eval_resp] does. *)

Definition NatObj : SetoidObject :=
  {| carrier := nat; is_setoid := eq_Setoid nat |}.

Definition NatMon : MonS.
Proof.
  unshelve refine (mk_mon_obj NatObj 0%nat Nat.add _ _ _ _).
  - intros a b c; simpl; induction a; simpl;
      [ reflexivity | now rewrite IHa ].
  - intro a; reflexivity.
  - intro a; simpl; induction a; simpl;
      [ reflexivity | now rewrite IHa ].
Defined.

(* Concatenation is spelled out rather than taken from Coq.Lists.List:
   importing that module would bring [list_scope]'s bracket and [++]
   notations into a file whose ambient scope is the library's, and the
   whole of what is needed here is five lines. *)
Fixpoint bapp (l m : list bool) : list bool :=
  match l with
  | Datatypes.nil        => m
  | Datatypes.cons x l' => Datatypes.cons x (bapp l' m)
  end.

Definition bnil : list bool := @Datatypes.nil bool.

Definition bword2 (x y : bool) : list bool :=
  @Datatypes.cons bool x (@Datatypes.cons bool y bnil).

Lemma bapp_assoc (l m n : list bool) :
  bapp (bapp l m) n = bapp l (bapp m n).
Proof. induction l; simpl; [ reflexivity | now rewrite IHl ]. Qed.

Lemma bapp_nil_r (l : list bool) : bapp l bnil = l.
Proof. induction l; simpl; [ reflexivity | now rewrite IHl ]. Qed.

Definition ListObj : SetoidObject :=
  {| carrier := list bool; is_setoid := eq_Setoid (list bool) |}.

Definition ListBoolMon : MonS.
Proof.
  unshelve refine (mk_mon_obj ListObj bnil bapp _ _ _ _).
  - intros l m n; exact (bapp_assoc l m n).
  - intro l; reflexivity.
  - intro l; exact (bapp_nil_r l).
Defined.

Fixpoint brepeat (x : bool) (n : nat) : list bool :=
  match n with
  | O    => bnil
  | S m => @Datatypes.cons bool x (brepeat x m)
  end.

Lemma brepeat_add (x : bool) (m n : nat) :
  brepeat x (m + n)%nat = bapp (brepeat x m) (brepeat x n).
Proof. induction m; simpl; [ reflexivity | now rewrite IHm ]. Qed.

Definition rep_hom (x : bool) : NatMon ~{MonS}~> ListBoolMon.
Proof.
  unshelve refine (@mk_mon_hom NatMon ListBoolMon (brepeat x) _ _ _).
  - intros m n; exact (brepeat_add x m n).
  - reflexivity.
Defined.

Definition fp_probe : FreeProd NatMon NatMon ~{MonS}~> ListBoolMon :=
  fp_merge NatMon NatMon ListBoolMon (rep_hom true) (rep_hom false).

Definition wl : FPTerm NatMon NatMon := fp_inl NatMon NatMon 1%nat.
Definition wr : FPTerm NatMon NatMon := fp_inr NatMon NatMon 1%nat.
Definition wlr : FPTerm NatMon NatMon := fp_mul NatMon NatMon wl wr.
Definition wrl : FPTerm NatMon NatMon := fp_mul NatMon NatMon wr wl.

Example fp_probe_wl : mon_fun fp_probe wl = brepeat true 1%nat := eq_refl.
Example fp_probe_wr : mon_fun fp_probe wr = brepeat false 1%nat := eq_refl.

Example fp_probe_wlr : mon_fun fp_probe wlr = bword2 true false := eq_refl.
Example fp_probe_wrl : mon_fun fp_probe wrl = bword2 false true := eq_refl.

Theorem fp_generators_distinct : fp_eq NatMon NatMon wl wr → False.
Proof.
  intro H.
  assert (Hq : brepeat true 1%nat = brepeat false 1%nat).
  { exact (fp_eval_resp NatMon NatMon ListBoolMon
             (rep_hom true) (rep_hom false) _ _ H). }
  discriminate Hq.
Qed.

Theorem fp_generators_do_not_commute :
  fp_eq NatMon NatMon wlr wrl → False.
Proof.
  intro H.
  assert (Hq : bword2 true false = bword2 false true).
  { exact (fp_eval_resp NatMon NatMon ListBoolMon
             (rep_hom true) (rep_hom false) _ _ H). }
  discriminate Hq.
Qed.

Theorem fp_word_not_left (n : nat) :
  fp_eq NatMon NatMon wlr (fp_inl NatMon NatMon n) → False.
Proof.
  intro H.
  assert (Hq : bword2 true false = brepeat true n).
  { exact (fp_eval_resp NatMon NatMon ListBoolMon
             (rep_hom true) (rep_hom false) _ _ H). }
  destruct n as [| [| n]]; discriminate Hq.
Qed.

Theorem fp_word_not_right (n : nat) :
  fp_eq NatMon NatMon wlr (fp_inr NatMon NatMon n) → False.
Proof.
  intro H.
  assert (Hq : bword2 true false = brepeat false n).
  { exact (fp_eval_resp NatMon NatMon ListBoolMon
             (rep_hom true) (rep_hom false) _ _ H). }
  destruct n; discriminate Hq.
Qed.

(** * Control: a trivial factor is absorbed *)

Example initial_is_TrivMon :
  @initial_obj MonS Mon_Sets_Initial = TrivMon := eq_refl.

Theorem fp_trivial_absorbs (A : MonS) (a : carrier (mon_ob A))
        (u : carrier (mon_ob TrivMon)) :
  fp_eq A TrivMon
    (fp_mul A TrivMon (fp_inl A TrivMon a) (fp_inr A TrivMon u))
    (fp_inl A TrivMon a).
Proof.
  destruct u.
  eapply fe_trans.
  - apply fe_mul.
    + apply fp_refl.
    + apply fe_rone.
  - apply fe_one_r.
Qed.

Definition fp_trivial_iso (A : MonS) :
  @Isomorphism MonS (FreeProd A TrivMon) A :=
  @coprod_zero_r MonS Mon_Sets_Cocartesian Mon_Sets_Initial A.

Definition fp_trivial_iso_l (A : MonS) :
  @Isomorphism MonS (FreeProd TrivMon A) A :=
  @coprod_zero_l MonS Mon_Sets_Cocartesian Mon_Sets_Initial A.

(** * Strength measurements *)

Section Strength.

Context (A B Q : MonS).
Context (f : A ~{MonS}~> Q).
Context (g : B ~{MonS}~> Q).

Example fp_carrier_strict : mon_ob (FreeProd A B) = FPCarrier A B := eq_refl.

Example fp_mul_strict (s t : FPTerm A B) :
  mon_mul (FreeProd A B) s t = fp_mul A B s t := eq_refl.

Example fp_one_strict : mon_one (FreeProd A B) = fp_one A B := eq_refl.

Example fp_injl_strict : mon_fun (fp_injl A B) = fp_inl A B := eq_refl.
Example fp_injr_strict : mon_fun (fp_injr A B) = fp_inr A B := eq_refl.

Example fp_beta_l_strict (a : carrier (mon_ob A)) :
  mon_fun (fp_merge A B Q f g) (fp_inl A B a) = mon_fun f a := eq_refl.

Example fp_beta_r_strict (b : carrier (mon_ob B)) :
  mon_fun (fp_merge A B Q f g) (fp_inr A B b) = mon_fun g b := eq_refl.

(* The composite's underlying FUNCTION is [f]'s on the nose (eta for
   functions); the underlying SetoidMorphism RECORD is not, its
   [proper_morphism] field being rebuilt by [setoid_morphism_compose] —
   see the header's list of refuted strict attempts. *)
Example fp_beta_l_fun :
  mon_fun (fp_merge A B Q f g ∘[MonS] fp_injl A B) = mon_fun f := eq_refl.

Example fp_beta_r_fun :
  mon_fun (fp_merge A B Q f g ∘[MonS] fp_injr A B) = mon_fun g := eq_refl.

(* The three coproduct equations, at [≈], inherited from the instance. *)
Corollary fp_merge_inl :
  @merge MonS Mon_Sets_Cocartesian Q A B f g ∘[MonS] @inl MonS _ A B ≈ f.
Proof. exact (@inl_merge MonS Mon_Sets_Cocartesian Q A B f g). Qed.

Corollary fp_merge_inr :
  @merge MonS Mon_Sets_Cocartesian Q A B f g ∘[MonS] @inr MonS _ A B ≈ g.
Proof. exact (@inr_merge MonS Mon_Sets_Cocartesian Q A B f g). Qed.

Corollary fp_merge_eta :
  @merge MonS Mon_Sets_Cocartesian
    (@Coprod MonS Mon_Sets_Cocartesian A B) A B
    (@inl MonS Mon_Sets_Cocartesian A B)
    (@inr MonS Mon_Sets_Cocartesian A B)
  ≈ @id MonS (@Coprod MonS Mon_Sets_Cocartesian A B).
Proof. exact (@merge_inl_inr MonS Mon_Sets_Cocartesian A B). Qed.

End Strength.

Example fp_trivial_iso_computes (A : MonS) (a : carrier (mon_ob A)) :
  mon_fun (to (fp_trivial_iso A)) (fp_inl A TrivMon a) = a := eq_refl.
