Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Smgrp.
Require Import Category.Instance.Smgrp.Word.
Require Import Category.Instance.Mon.Word.

Generalizable All Variables.

(** * W₀-algebras as strings of operations ν₀, ν₁, … *)

(*
 Book: Riehl, "Category Theory in Context", Example 5.2.6(iii),
 nLab: https://ncatlab.org/nlab/show/free+monoid
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** Families ν₀, ν₁, …: ν₀ an element, and #470's [NAry] for n ≥ 1 *)

Record NAry0@{o} (X : SetoidObject@{o o}) : Type@{o} := {
  nu_zero : X;
  nu_pos : NAry@{o} X
}.

Arguments nu_zero {X} _.
Arguments nu_pos {X} _.

(* νₙ : Xⁿ → X for every n ≥ 0. *)
Definition nu0@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X) (n : nat) :
  Tup0@{o} X n → X :=
  match n as n0 return Tup0 X n0 → X with
  | O => fun _ => nu_zero ν
  | S n' => nu (nu_pos ν) n'
  end.

(* The family read on W₀ X = lists: the copairing ∐_{n≥0} Xⁿ → X. *)
Definition nu0_list@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (l : list X) : X :=
  nu0 ν (length l) (list_to_tup0 l).

Example nu0_list_nil@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X) :
  nu0_list ν word0 = nu_zero ν := eq_refl.

Example nu0_list_letter@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (x : X) : nu0_list ν (word1 x) = nu (nu_pos ν) 0 x := eq_refl.

Example nu0_list_pair@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (x y : X) : nu0_list ν (word2 x y) = nu (nu_pos ν) 1 (x, y) := eq_refl.

Lemma nu0_list_respects@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (l l' : list X) : word_eq l l' → nu0_list ν l ≈ nu0_list ν l'.
Proof.
  intro H; destruct H as [|a b u v Hab Huv]; [ reflexivity | ].
  exact (nu_respects (nu_pos ν) _ _ _ _ (list_to_tup_respects a b u v Hab Huv)).
Qed.

(* A morphism of families: f νₙ = ν'ₙ fⁿ for every n ≥ 0. *)
Definition NAry0_hom@{o so} {X Y : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (ν' : NAry0@{o} Y) (f : X ~{Sets@{o so}}~> Y) : Type@{o} :=
  (f (nu_zero ν) ≈ nu_zero ν') * NAry_hom (nu_pos ν) (nu_pos ν') f.

(* ν on the list of a tuple is ν on the tuple, up to ≈ (the length of the
   list is stuck on n, so not on the nose). *)
Lemma nu0_list_tup_to_list@{o} {X : SetoidObject@{o o}} (ν : NAry0@{o} X)
  (n : nat) (t : Tup@{o} X n) :
  nu0_list ν (tup_to_list n t) ≈ nu (nu_pos ν) n t.
Proof.
  unfold nu0_list.
  pose proof (list_to_tup_tup_to_list n t) as K.
  destruct (tup_to_list n t) as [|a l]; [ contradiction | ].
  exact (nu_respects (nu_pos ν) _ _ _ _ K).
Qed.

(* Leibniz: mapping the letters of a tuple. *)
Lemma tmap_tup_to_list@{o} {X Y : SetoidObject@{o o}} (f : X → Y)
  (n : nat) (t : Tup@{o} X n) :
  wmap (X := X) (Y := Y) f (tup_to_list n t) = tup_to_list n (tmap f n t).
Proof. induction n as [|n IH]; simpl; [ reflexivity | now rewrite IH ]. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The two conditions, and the correspondence with W₀-algebras *)

Section W0Systems.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

(* ν₁ = 1 is #470's [nu_unit] of the positive part.  (2): for every word of
   words, ν of the values of the inner words is ν of their concatenation,
   which IS μ ([W0_join_fun]), νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk}. *)
Definition nu0_assoc@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X) :
  Type@{o} :=
  ∀ ww : list (list X),
    nu0_list ν (wmap (X := WordObj X) (Y := X) (nu0_list ν) ww)
      ≈ nu0_list ν (wconcat ww).

(* An algebra gives a family: ν₀ = α⟨⟩ and ν_{n+1}(x1, …) = α⟨x1 …⟩. *)
Definition alg_NAry0@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) : NAry0@{o} X :=
  {| nu_zero := t_alg[α] Datatypes.nil
   ; nu_pos := {| nu := fun n t => t_alg[α] (tup_to_list n t)
                ; nu_respects := fun n m t u H =>
                    proper_morphism (t_alg[α]) _ _
                      (tup_to_list_respects n m t u H) |} |}.

Example alg_NAry0_zero@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) :
  nu_zero (alg_NAry0 α) = t_alg[α] word0 := eq_refl.

Example alg_NAry0_at@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (n : nat) (t : Tup@{o} X n) :
  nu (nu_pos (alg_NAry0 α)) n t = t_alg[α] (tup_to_list n t) := eq_refl.

(* ν₀ is the unit of the monoid of the algebra, and ν₂ its
   multiplication. *)
Example alg_nu0_is_unit@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) :
  nu_zero (alg_NAry0 α) = mon_one (alg_monoid α) := eq_refl.

Example alg_nu2_is_mul@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (a b : X) :
  nu (nu_pos (alg_NAry0 α)) 1 (a, b) = mon_mul (alg_monoid α) a b
  := eq_refl.

(* The family read back on lists is the structure map, up to ≈. *)
Lemma alg_nu0_list@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (l : list X) :
  nu0_list (alg_NAry0 α) l ≈ t_alg[α] l.
Proof.
  destruct l as [|a l]; [ reflexivity | ].
  unfold nu0_list; simpl.
  rewrite (tup_to_list_list_to_tup a l). reflexivity.
Qed.

(* ν₁ = 1, from the unit law. *)
Lemma alg_NAry0_unit@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) : nu_unit (nu_pos (alg_NAry0 α)).
Proof. intro x. exact (alg_unit α x). Qed.

(* (2), from the action law. *)
Lemma alg_NAry0_assoc@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) : nu0_assoc (alg_NAry0 α).
Proof.
  intro ww.
  transitivity
    (t_alg[α] (wmap (X := WordObj X) (Y := X) (nu0_list (alg_NAry0 α)) ww)).
  { apply alg_nu0_list. }
  transitivity (t_alg[α] (wmap (X := WordObj X) (Y := X) (t_alg[α]) ww)).
  { apply (proper_morphism (t_alg[α])).
    clear. induction ww as [|w ww IH]; simpl; [ exact we_nil | ].
    exact (we_cons _ _ _ _ (alg_nu0_list α w) IH). }
  transitivity (t_alg[α] (wconcat ww)).
  { exact (alg_action α ww). }
  symmetry. apply alg_nu0_list.
Qed.

(* "νₙ is the n-fold product" in the monoid of the algebra. *)
Lemma alg_nu_is_fold@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (n : nat) (t : Tup0@{o} X n) :
  nu0 (alg_NAry0 α) n t
    ≈ free_mon_extend (L := alg_monoid α) (fun s => s) (tup0_to_list n t).
Proof.
  destruct n as [|n]; [ reflexivity | ].
  simpl. symmetry. exact (alg_fold α (tup_to_list n t)).
Qed.

(* A family with ν₁ = 1 and (2) is an algebra: its structure map is the
   copairing [nu0_list], its unit law IS ν₁ = 1 by conversion, and its
   action law is (2) modulo [W0_map]. *)
Definition NAry0_alg@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) :
  @TAlgebra Sets@{o so} W0F W0 X.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} W0F W0 X
       {| morphism := nu0_list ν |} _ _).
  - intros l l' H. exact (nu0_list_respects ν l l' H).
  - intro x. exact (Hu x).
  - intro ww. simpl.
    transitivity
      (nu0_list ν (wmap (X := WordObj X) (Y := X) (nu0_list ν) ww)).
    + apply nu0_list_respects. exact (W0_map _ ww).
    + exact (Ha ww).
Defined.

Example NAry0_alg_map@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) (l : list X) :
  t_alg[NAry0_alg ν Hu Ha] l = nu0_list ν l := eq_refl.

(* Family → algebra → family: ν₀ on the nose, ν_{n+1} at ≈ only (the
   length of the list of a tuple is stuck on n). *)
Example NAry0_rt_zero@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) :
  nu_zero (alg_NAry0 (NAry0_alg ν Hu Ha)) = nu_zero ν := eq_refl.

Example NAry0_rt_pos_pair@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) (a b : X) :
  nu (nu_pos (alg_NAry0 (NAry0_alg ν Hu Ha))) 1 (a, b)
    = nu (nu_pos ν) 1 (a, b) := eq_refl.

Lemma NAry0_rt_pos@{+} {X : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν) (n : nat) (t : Tup@{o} X n) :
  nu (nu_pos (alg_NAry0 (NAry0_alg ν Hu Ha))) n t ≈ nu (nu_pos ν) n t.
Proof. exact (nu0_list_tup_to_list ν n t). Qed.

(* Algebra → family → algebra: the structure map, up to ≈. *)
Lemma alg_round_trip0@{+} {X : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) :
  t_alg[NAry0_alg (alg_NAry0 α) (alg_NAry0_unit α) (alg_NAry0_assoc α)]
    ≈ t_alg[α].
Proof. intro l. exact (alg_nu0_list α l). Qed.

(* The morphism clause, both ways: an algebra map commutes with every νₙ,
   n ≥ 0, and conversely. *)
Lemma alg_hom_NAry0_hom@{+} {X Y : obj[Sets@{o so}]}
  (α : @TAlgebra Sets@{o so} W0F W0 X) (β : @TAlgebra Sets@{o so} W0F W0 Y)
  (f : X ~{Sets@{o so}}~> Y) :
  f ∘ t_alg[α] ≈ t_alg[β] ∘ fmap[W0F] f →
  NAry0_hom (alg_NAry0 α) (alg_NAry0 β) f.
Proof.
  intro H. split.
  - transitivity (t_alg[β] (fmap[W0F] f Datatypes.nil)); [ exact (H _) | ].
    apply (proper_morphism (t_alg[β])). exact (W0_map f _).
  - intros n t. simpl.
    transitivity (t_alg[β] (fmap[W0F] f (tup_to_list n t)));
      [ exact (H _) | ].
    apply (proper_morphism (t_alg[β])).
    rewrite <- (tmap_tup_to_list f n t). exact (W0_map f _).
Qed.

Lemma NAry0_hom_alg_hom@{+} {X Y : obj[Sets@{o so}]} (ν : NAry0@{o} X)
  (ν' : NAry0@{o} Y) (Hu : nu_unit (nu_pos ν)) (Ha : nu0_assoc ν)
  (Hu' : nu_unit (nu_pos ν')) (Ha' : nu0_assoc ν')
  (f : X ~{Sets@{o so}}~> Y) :
  NAry0_hom ν ν' f →
  f ∘ t_alg[NAry0_alg ν Hu Ha] ≈ t_alg[NAry0_alg ν' Hu' Ha'] ∘ fmap[W0F] f.
Proof.
  intros [H0 Hn] l. simpl.
  transitivity (nu0_list ν' (wmap f l)).
  - destruct l as [|a l]; [ exact H0 | ].
    unfold nu0_list; simpl.
    transitivity
      (nu (nu_pos ν') (length l) (tmap f (length l) (list_to_tup a l)));
      [ exact (Hn _ _) | ].
    apply (nu_respects (nu_pos ν')).
    clear. revert a; induction l as [|b l IH]; intro a; simpl;
      [ reflexivity | ].
    split; [ reflexivity | exact (IH b) ].
  - apply nu0_list_respects. apply word_eq_sym. exact (W0_map f l).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The systems ⟨S, ν₀, ν₁, …⟩ as a category, isomorphic to Set^{W₀} *)

Record W0System@{+} : Type@{so} := {
  ws0_set : obj[Sets@{o so}];
  ws0_nu : NAry0@{o} ws0_set;
  ws0_unit : nu_unit (nu_pos ws0_nu);
  ws0_assoc : nu0_assoc ws0_nu
}.

Definition W0SystemHom@{+} (A B : W0System) : Type@{o} :=
  { f : ws0_set A ~{Sets@{o so}}~> ws0_set B
  & NAry0_hom (ws0_nu A) (ws0_nu B) f }.

Definition W0SystemHom_Setoid@{+} (A B : W0System) :
  Setoid@{o o} (W0SystemHom A B).
Proof.
  refine {| equiv := fun f g =>
              @equiv _ (@homset Sets@{o so} (ws0_set A) (ws0_set B))
                (`1 f) (`1 g) |}.
  constructor.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h H1 H2. transitivity (`1 g); assumption.
Defined.

Definition W0System_id@{+} (A : W0System) : W0SystemHom A A.
Proof.
  exists (@setoid_morphism_id@{o o o} (ws0_set A)). split.
  - reflexivity.
  - intros n t. apply (nu_respects (nu_pos (ws0_nu A))).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
Defined.

Definition W0System_compose@{+} {A B C : W0System}
  (f : W0SystemHom B C) (g : W0SystemHom A B) : W0SystemHom A C.
Proof.
  exists (@setoid_morphism_compose@{o o o} _ _ _ (`1 f) (`1 g)). split.
  - simpl. transitivity (`1 f (nu_zero (ws0_nu B))).
    + apply (proper_morphism (`1 f)). exact (fst (`2 g)).
    + exact (fst (`2 f)).
  - intros n t. simpl.
    transitivity (`1 f (nu (nu_pos (ws0_nu B)) n (tmap (`1 g) n t))).
    + apply (proper_morphism (`1 f)). exact (snd (`2 g) n t).
    + transitivity
        (nu (nu_pos (ws0_nu C)) n (tmap (`1 f) n (tmap (`1 g) n t))).
      * exact (snd (`2 f) n _).
      * apply (nu_respects (nu_pos (ws0_nu C))).
        exact (tup_eq_sym _ _ _ _ (tmap_comp (`1 f) (`1 g) n t)).
Defined.

(* The category of Mac Lane's systems ⟨S, ν₀, ν₁, …⟩. *)
Definition W0Sys@{+} : Category@{so o o}.
Proof.
  unshelve refine
    {| obj     := W0System
     ; hom     := W0SystemHom
     ; homset  := W0SystemHom_Setoid
     ; id      := W0System_id
     ; compose := @W0System_compose |}.
  - intros A B C f f' Hf g g' Hg a. simpl.
    transitivity (`1 f (`1 g' a)).
    + apply (proper_morphism (`1 f)). exact (Hg a).
    + exact (Hf _).
  - intros A B f a. reflexivity.
  - intros A B f a. reflexivity.
  - intros A B C D f g h a. reflexivity.
  - intros A B C D f g h a. reflexivity.
Defined.

Definition W0Sys_to_EM@{+} : W0Sys ⟶ W0Alg.
Proof.
  unshelve refine
    (@Build_Functor W0Sys W0Alg
       (fun A => existT _ (ws0_set A)
                   (NAry0_alg (ws0_nu A) (ws0_unit A) (ws0_assoc A)))
       (fun A B f =>
          @Build_TAlgebraHom Sets@{o so} W0F W0 (ws0_set A) (ws0_set B)
            (NAry0_alg (ws0_nu A) (ws0_unit A) (ws0_assoc A))
            (NAry0_alg (ws0_nu B) (ws0_unit B) (ws0_assoc B))
            (`1 f)
            (NAry0_hom_alg_hom _ _ _ _ _ _ (`1 f) (`2 f)))
       _ _ _).
  - intros A B f g H a. exact (H a).
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

Definition EM_to_W0Sys@{+} : W0Alg ⟶ W0Sys.
Proof.
  unshelve refine
    (@Build_Functor W0Alg W0Sys
       (fun x => {| ws0_set := projT1 x
                  ; ws0_nu := alg_NAry0 (projT2 x)
                  ; ws0_unit := alg_NAry0_unit (projT2 x)
                  ; ws0_assoc := alg_NAry0_assoc (projT2 x) |})
       (fun x y f =>
          existT _ (t_alg_hom[f])
            (alg_hom_NAry0_hom (projT2 x) (projT2 y) (t_alg_hom[f])
               (@t_alg_hom_commutes _ _ _ _ _ _ _ f)))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The algebra round trip through the systems, with the identity as its
   component. *)
Definition W0Sys_EM_counit_iso@{+} (x : W0Alg) :
  @Isomorphism W0Alg (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism W0Alg (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x) x
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x)) (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} W0F W0 (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] l);
      [ exact (alg_nu0_list (projT2 x) l) | ].
    apply (proper_morphism (t_alg[projT2 x])).
    symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
  - intro l. simpl.
    transitivity (t_alg[projT2 x] (fmap[W0F] id l)).
    + apply (proper_morphism (t_alg[projT2 x])).
      symmetry. exact (@fmap_id _ _ W0F (projT1 x) l).
    + symmetry. exact (alg_nu0_list (projT2 x) _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The system round trip, with the identity as its component. *)
Definition W0Sys_EM_unit_iso@{+} (A : W0Sys) :
  @Isomorphism W0Sys (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism W0Sys (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A) A
       (existT _ (@setoid_morphism_id@{o o o} (ws0_set A)) _)
       (existT _ (@setoid_morphism_id@{o o o} (ws0_set A)) _) _ _).
  - split; [ reflexivity | ].
    intros n t. simpl.
    transitivity (nu (nu_pos (ws0_nu A)) n t);
      [ exact (nu0_list_tup_to_list (ws0_nu A) n t) | ].
    apply (nu_respects (nu_pos (ws0_nu A))).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
  - split; [ reflexivity | ].
    intros n t. simpl.
    transitivity (nu (nu_pos (ws0_nu A)) n (tmap (fun x => x) n t)).
    + apply (nu_respects (nu_pos (ws0_nu A))).
      exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
    + symmetry. exact (nu0_list_tup_to_list (ws0_nu A) n _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The systems ⟨S, ν₀, ν₁, …⟩ with ν₁ = 1 and (2) are isomorphic in Cat to
   Set^{W₀}, every component of both natural isomorphisms the identity. *)
Definition W0Sys_EM_iso@{c +} :
  @Isomorphism Cat@{c so so so o} W0Sys W0Alg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} W0Sys W0Alg
       W0Sys_to_EM EM_to_W0Sys _ _).
  - exists (fun x => W0Sys_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun A => W0Sys_EM_unit_iso A).
    intros A B f a. reflexivity.
Defined.

(* Mac Lane's Exercise 1 as a category: the systems are the monoids. *)
Definition Mon_W0Sys_iso@{c +} :
  @Isomorphism Cat@{c so so so o} MonOS W0Sys :=
  iso_compose (iso_sym W0Sys_EM_iso) Mon_EM_iso.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

Example W0Sys_EM_iso_to@{+} : to W0Sys_EM_iso = W0Sys_to_EM := eq_refl.

Example W0Sys_EM_iso_from@{+} : from W0Sys_EM_iso = EM_to_W0Sys
  := eq_refl.

(* A system's structure map is the copairing of its family, and an
   algebra's νₙ is its structure map on Sⁿ. *)
Example W0Sys_to_EM_alg@{+} (A : W0Sys) (l : list (ws0_set A)) :
  t_alg[projT2 (fobj[W0Sys_to_EM] A)] l = nu0_list (ws0_nu A) l := eq_refl.

Example EM_to_W0Sys_zero@{+} (x : W0Alg) :
  nu_zero (ws0_nu (fobj[EM_to_W0Sys] x)) = t_alg[projT2 x] word0 := eq_refl.

Example EM_to_W0Sys_nu@{+} (x : W0Alg) (n : nat) (t : Tup@{o} (projT1 x) n) :
  nu (nu_pos (ws0_nu (fobj[EM_to_W0Sys] x))) n t
    = t_alg[projT2 x] (tup_to_list n t) := eq_refl.

(* The system round trip keeps the set, ν₀ and the maps on the nose. *)
Example W0Sys_rt_set@{+} (A : W0Sys) :
  ws0_set (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A) = ws0_set A := eq_refl.

Example W0Sys_rt_zero@{+} (A : W0Sys) :
  nu_zero (ws0_nu (fobj[EM_to_W0Sys ◯ W0Sys_to_EM] A)) = nu_zero (ws0_nu A)
  := eq_refl.

Example W0Sys_rt_hom@{+} {A B : W0Sys} (f : A ~{W0Sys}~> B) :
  `1 (fmap[EM_to_W0Sys ◯ W0Sys_to_EM] f) = `1 f := eq_refl.

Example EM_W0Sys_rt_carrier@{+} (x : W0Alg) :
  projT1 (fobj[W0Sys_to_EM ◯ EM_to_W0Sys] x) = projT1 x := eq_refl.

Example EM_W0Sys_rt_alg_hom@{+} {x y : W0Alg} (f : x ~{W0Alg}~> y) :
  t_alg_hom[fmap[W0Sys_to_EM ◯ EM_to_W0Sys] f] = t_alg_hom[f] := eq_refl.

Example W0Sys_EM_iso_to_from_component@{+} (x : W0Alg) :
  (t_alg_hom[to (projT1 (iso_to_from W0Sys_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from W0Sys_EM_iso) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example W0Sys_EM_iso_from_to_component@{+} (A : W0Sys) :
  (`1 (to (projT1 (iso_from_to W0Sys_EM_iso) A)),
   `1 (from (projT1 (iso_from_to W0Sys_EM_iso) A)))
    = (@setoid_morphism_id@{o o o} (ws0_set A),
       @setoid_morphism_id@{o o o} (ws0_set A)) := eq_refl.

(* The system of a monoid M: ν₀ is the unit of M, ν₂(x, y) = x · (y · 1),
   and νₙ is the n-fold product. *)
Example Mon_system_zero@{+} (M : MonOS) :
  nu_zero (ws0_nu (fobj[EM_to_W0Sys ◯ Mon_K] M)) = mon_one M := eq_refl.

Example Mon_system_pair@{+} (M : MonOS) (x y : mon_ob M) :
  nu (nu_pos (ws0_nu (fobj[EM_to_W0Sys ◯ Mon_K] M))) 1 (x, y)
    = mon_mul M x (mon_mul M y (mon_one M)) := eq_refl.

Lemma Mon_system_nu@{+} (M : MonOS) (n : nat) (t : Tup0@{o} (mon_ob M) n) :
  nu0 (ws0_nu (fobj[EM_to_W0Sys ◯ Mon_K] M)) n t
    ≈ free_mon_extend (L := M) (fun s => s) (tup0_to_list n t).
Proof. destruct n as [|n]; reflexivity. Qed.

End W0Systems.
