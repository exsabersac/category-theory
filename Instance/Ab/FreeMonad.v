Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.

Generalizable All Variables.

(** * The free abelian group monad ℤ[−] on Set, and Ab ≅ Set^{ℤ[−]} *)

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 nLab: https://ncatlab.org/nlab/show/free+abelian+group
 nLab: https://ncatlab.org/nlab/show/monadic+functor

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeAbMonad.

Universes c so.

(* ℤ[−] = U ◯ F, with F Instance/Ab/Free.v's [FreeAb]. *)
Definition FreeAbF@{+} : Sets@{c so} ⟶ Sets@{c so} := Ab_Forget ◯ FreeAb.

(* ℤ[−], the monad of the hom-set form of the free-forgetful
   adjunction. *)
Definition FreeAbMonad@{+} : @Monad Sets@{c so} FreeAbF :=
  Adjunction_Induced_Monad free_ab_adjunction_hom.

(* The relabelling of a formal sum along u: the fold of insert ∘ u. *)
Definition fa_relabel@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : FATerm X) : FATerm Y :=
  fa_eval (A := FreeAbObject Y) (free_ab_insert Y ∘ u) t.

(* A formal sum of formal sums, flattened: the fold of the identity. *)
Definition fa_flatten@{+} {X : Sets@{c so}}
  (k : FATerm (Ab_Forget (FreeAbObject X))) : FATerm X :=
  fa_eval (A := FreeAbObject X)
    (@id Sets@{c so} (Ab_Forget (FreeAbObject X))) k.

(* ℤ[X] is the free group's setoid, whose carrier is the formal sums. *)
Example ZM_obj@{+} (X : Sets@{c so}) :
  fobj[FreeAbF] X = Ab_Forget (FreeAbObject X) := eq_refl.

Example ZM_carrier@{+} (X : Sets@{c so}) :
  carrier (fobj[FreeAbF] X) = FATerm X := eq_refl.

(* η_X is the insertion of generators, as a setoid map, and x ↦ ⟨x⟩. *)
Example ZM_ret@{+} (X : Sets@{c so}) :
  @ret _ _ FreeAbMonad X = free_ab_insert X := eq_refl.

Example ZM_ret_fun@{+} (X : Sets@{c so}) (x : carrier X) :
  @ret _ _ FreeAbMonad X x = fa_gen x := eq_refl.

(* μ = U ε F, which flattens. *)
Example ZM_join_counit@{+} (X : Sets@{c so}) :
  @join _ _ FreeAbMonad X
    = fmap[Ab_Forget] (@counit _ _ _ _ free_ab_adjunction_hom (FreeAb X))
  := eq_refl.

Example ZM_join_gen@{+} (X : Sets@{c so}) (t : FATerm X) :
  @join _ _ FreeAbMonad X (@fa_gen (Ab_Forget (FreeAbObject X)) t) = t
  := eq_refl.

Example ZM_join_fun@{+} (X : Sets@{c so})
  (k : FATerm (Ab_Forget (FreeAbObject X))) :
  @join _ _ FreeAbMonad X k = fa_flatten k := eq_refl.

Example ZM_join_zero@{+} (X : Sets@{c so}) :
  @join _ _ FreeAbMonad X fa_zero = fa_zero := eq_refl.

(* ℤ[u] relabels, up to ≈: Riehl's n1 s1 + ⋯ + nk sk ↦ n1 f(s1) + ⋯ +
   nk f(sk). *)
Lemma ZM_map_equiv@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : FATerm X) : fmap[FreeAbF] u t ≈ fa_relabel u t.
Proof.
  apply (free_ab_extend_unique (FreeAbObject Y) (free_ab_insert Y ∘ u)
           (fmap[FreeAb] u)).
  intro x. exact (free_ab_fmap_generators u x).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The comparison functor Ab → Set^{ℤ[−]} *)

Definition ZMAlg@{+} : Category@{so c c} :=
  @EilenbergMoore@{so so so c} Sets@{c so} FreeAbF FreeAbMonad.

Definition Ab_K@{+} : Ab ⟶ ZMAlg := EM_Comparison free_ab_adjunction_hom.

(* Riehl's "commutes with the left and right adjoints": Monad/
   Comparison.v's two triangles, at this adjunction. *)
Theorem Ab_K_Forget@{+} :
  @EM_Forget Sets@{c so} FreeAbF FreeAbMonad ◯ Ab_K ≈ Ab_Forget.
Proof. exact (EM_Comparison_Forget free_ab_adjunction_hom). Qed.

Theorem Ab_K_Free@{+} :
  Ab_K ◯ FreeAb ≈ @EM_Free Sets@{c so} FreeAbF FreeAbMonad.
Proof. exact (EM_Comparison_Free free_ab_adjunction_hom). Qed.

Section Algebra.

Context {A : Sets@{c so}}.
Context (α : @TAlgebra Sets@{c so} FreeAbF FreeAbMonad A).

(* The group operations of an algebra (A, ev): 0 = ev⟨⟩,
   a + b = ev(⟨a⟩ + ⟨b⟩) and −a = ev(−⟨a⟩). *)
Definition zm_alg_zero@{+} : carrier A := t_alg[α] (@fa_zero A).

Definition zm_alg_plus@{+} (x y : carrier A) : carrier A :=
  t_alg[α] (@fa_plus A (fa_gen x) (fa_gen y)).

Definition zm_alg_neg@{+} (x : carrier A) : carrier A :=
  t_alg[α] (@fa_neg A (fa_gen x)).

(* The sum the formal sum names, through the operations just defined. *)
Fixpoint zm_alg_eval@{+} (t : FATerm A) : carrier A :=
  match t with
  | fa_gen x    => x
  | fa_zero     => zm_alg_zero
  | fa_plus s u => zm_alg_plus (zm_alg_eval s) (zm_alg_eval u)
  | fa_neg s    => zm_alg_neg (zm_alg_eval s)
  end.

(* Riehl's "sanity check": ev sends a singleton sum a to a. *)
Lemma zm_alg_unit@{+} (x : carrier A) : t_alg[α] (@fa_gen A x) ≈ x.
Proof. exact (@t_id _ _ _ _ α x). Qed.

(* ev ∘ μ ≈ ev ∘ ℤ[ev], read through the relabelling. *)
Lemma zm_alg_step@{+} (K : FATerm (fobj[FreeAbF] A)) :
  t_alg[α] (@join _ _ FreeAbMonad A K) ≈ t_alg[α] (fa_relabel t_alg[α] K).
Proof.
  symmetry.
  refine (transitivity _ (@t_action _ _ _ _ α K)).
  apply (proper_morphism t_alg[α]).
  symmetry. exact (ZM_map_equiv t_alg[α] K).
Qed.

Lemma zm_alg_plus_respects@{+} :
  Proper (equiv ==> equiv ==> equiv) zm_alg_plus.
Proof.
  intros x x' Hx y y' Hy.
  exact (proper_morphism t_alg[α] _ _ (fae_plus (fae_gen Hx) (fae_gen Hy))).
Qed.

Lemma zm_alg_neg_respects@{+} : Proper (equiv ==> equiv) zm_alg_neg.
Proof.
  intros x x' Hx.
  exact (proper_morphism t_alg[α] _ _ (fae_neg (fae_gen Hx))).
Qed.

(* The evaluation IS the sum in the derived group. *)
Lemma zm_alg_fold@{+} (t : FATerm A) : t_alg[α] t ≈ zm_alg_eval t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs ]; simpl.
  - exact (zm_alg_unit x).
  - reflexivity.
  - refine (transitivity
              (zm_alg_step
                 (@fa_plus (fobj[FreeAbF] A)
                    (@fa_gen (fobj[FreeAbF] A) s)
                    (@fa_gen (fobj[FreeAbF] A) u))) _).
    exact (zm_alg_plus_respects _ _ IHs _ _ IHu).
  - refine (transitivity
              (zm_alg_step
                 (@fa_neg (fobj[FreeAbF] A) (@fa_gen (fobj[FreeAbF] A) s))) _).
    exact (zm_alg_neg_respects _ _ IHs).
Qed.

Lemma zm_alg_eval_respects@{+} (s t : FATerm A) :
  fa_eq s t → zm_alg_eval s ≈ zm_alg_eval t.
Proof.
  intro H.
  refine (transitivity (symmetry (zm_alg_fold s)) _).
  refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
  exact (zm_alg_fold t).
Qed.

(* Every algebra's carrier is propositional, with no hypothesis: x ≈ y
   iff ⟨x⟩ ≈ ⟨y⟩ in ℤ[A], a [Prop]. *)
Definition zm_alg_prop@{+} : PropEquiv (is_setoid A).
Proof using A α.
  unshelve refine
    (@Build_PropEquiv _ (is_setoid A)
       (fun x y => @fa_eq A (fa_gen x) (fa_gen y)) _ _).
  - intros x y H.
    refine (transitivity (symmetry (zm_alg_unit x)) _).
    refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
    exact (zm_alg_unit y).
  - intros x y H. exact (fae_gen H).
Defined.

(* The abelian group of the algebra: each law is one instance of
   [zm_alg_eval_respects] at a constructor of [fa_eq], so that "the
   values assigned to the sums of sums (a1 + a2) + (a3) and (a1) +
   (a2 + a3) are equal" is associativity. *)
Definition zm_alg_ab@{+} : AbObject := {|
  ab_cmon := {|
    cmon_setoid := A;
    cmon_zero := zm_alg_zero;
    cmon_plus := zm_alg_plus;
    cmon_plus_respects := zm_alg_plus_respects;
    cmon_plus_assoc := fun x y z =>
      zm_alg_eval_respects _ _ (fae_assoc (fa_gen x) (fa_gen y) (fa_gen z));
    cmon_plus_comm := fun x y =>
      zm_alg_eval_respects _ _ (fae_comm (fa_gen x) (fa_gen y));
    cmon_plus_zero_l := fun x =>
      zm_alg_eval_respects _ _ (fae_zero_l (fa_gen x));
    cmon_prop := zm_alg_prop
  |};
  ab_neg := zm_alg_neg;
  ab_neg_respects := zm_alg_neg_respects;
  ab_neg_left := fun x => zm_alg_eval_respects _ _ (fae_neg_l (fa_gen x))
|}.

End Algebra.

(* An algebra map is additive: Riehl's "a function f : A → B that
   preserves the evaluation of formal sums, i.e., a group homomorphism". *)
Lemma zm_alg_hom_step@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y)
  (t : FATerm (projT1 x)) :
  t_alg_hom[f] (t_alg[projT2 x] t)
    ≈ t_alg[projT2 y] (fa_relabel t_alg_hom[f] t).
Proof.
  refine (transitivity (@t_alg_hom_commutes _ _ _ _ _ _ _ f t) _).
  apply (proper_morphism t_alg[projT2 y]).
  exact (ZM_map_equiv t_alg_hom[f] t).
Qed.

Definition zm_alg_hom_ab@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  zm_alg_ab (projT2 x) ~{Ab}~> zm_alg_ab (projT2 y).
Proof.
  refine (@Build_CMonHom (zm_alg_ab (projT2 x)) (zm_alg_ab (projT2 y))
            t_alg_hom[f] _ _).
  - exact (zm_alg_hom_step f fa_zero).
  - intros a b. exact (zm_alg_hom_step f (fa_plus (fa_gen a) (fa_gen b))).
Defined.

(* The functor Set^{ℤ[−]} → Ab. *)
Definition EM_to_AbS@{+} : ZMAlg ⟶ Ab.
Proof.
  unshelve refine
    (@Build_Functor ZMAlg Ab (fun x => zm_alg_ab (projT2 x))
       (fun x y f => zm_alg_hom_ab f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The fold of the identity in the derived group IS [zm_alg_eval]
   (Leibniz, by induction). *)
Lemma zm_fold_is_alg_eval@{+} {A : Sets@{c so}}
  (α : @TAlgebra Sets@{c so} FreeAbF FreeAbMonad A) (t : FATerm A) :
  fa_eval (A := zm_alg_ab α) (@id Sets@{c so} (Ab_Forget (zm_alg_ab α))) t
  = zm_alg_eval α t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs ]; simpl;
    try rewrite IHs; try rewrite IHu; reflexivity.
Qed.

(* The algebra round trip, with the identity as its component. *)
Definition Ab_EM_counit_iso@{+} (x : ZMAlg) :
  @Isomorphism ZMAlg (fobj[Ab_K ◯ EM_to_AbS] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism ZMAlg (fobj[Ab_K ◯ EM_to_AbS] x) x
       (@Build_TAlgebraHom Sets@{c so} FreeAbF FreeAbMonad
          (projT1 x) (projT1 x)
          (projT2 (fobj[Ab_K ◯ EM_to_AbS] x)) (projT2 x)
          (@id Sets@{c so} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{c so} FreeAbF FreeAbMonad
          (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Ab_K ◯ EM_to_AbS] x))
          (@id Sets@{c so} (projT1 x)) _) _ _).
  - intro t.
    change (fa_eval (A := zm_alg_ab (projT2 x))
              (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x)))) t
            ≈ t_alg[projT2 x] (fmap[FreeAbF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (zm_fold_is_alg_eval (projT2 x) t).
    refine (transitivity (symmetry (zm_alg_fold (projT2 x) t)) _).
    apply (proper_morphism t_alg[projT2 x]).
    symmetry. exact (@fmap_id _ _ FreeAbF (projT1 x) t).
  - intro t.
    change (t_alg[projT2 x] t
            ≈ fa_eval (A := zm_alg_ab (projT2 x))
                (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x))))
                (fmap[FreeAbF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (zm_fold_is_alg_eval (projT2 x)).
    refine (transitivity (zm_alg_fold (projT2 x) t) _).
    apply zm_alg_eval_respects.
    exact (fae_sym (@fmap_id _ _ FreeAbF (projT1 x) t)).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The group round trip, with the identity as its component: on a group
   the derived operations ARE its own. *)
Definition Ab_EM_unit_iso@{+} (G : Ab) :
  @Isomorphism Ab (fobj[EM_to_AbS ◯ Ab_K] G) G.
Proof.
  unshelve refine
    (@Build_Isomorphism Ab (fobj[EM_to_AbS ◯ Ab_K] G) G
       (@Build_CMonHom (fobj[EM_to_AbS ◯ Ab_K] G) G
          (@id Sets@{c so} (Ab_Forget G)) _ _)
       (@Build_CMonHom G (fobj[EM_to_AbS ◯ Ab_K] G)
          (@id Sets@{c so} (Ab_Forget G)) _ _) _ _).
  all: simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. *)
Definition Ab_EM_equivalence@{+} :
  @EquivalenceOfCategories Ab ZMAlg Ab_K.
Proof.
  unshelve refine (@Build_EquivalenceOfCategories _ _ Ab_K EM_to_AbS _ _).
  - exists (fun x => Ab_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun G => iso_sym (Ab_EM_unit_iso G)). intros G H f a. reflexivity.
Defined.

(* Abelian groups are monadic over Set. *)
Definition Ab_Forget_Monadic@{+} : Monadic Ab_Forget.
Proof.
  exists FreeAb. exists free_ab_adjunction_hom. exact Ab_EM_equivalence.
Defined.

(* Ab ≅ Set^{ℤ[−]} in Cat, from the two component isomorphisms. *)
Definition Ab_EM_iso@{k +} : @Isomorphism Cat@{k so so so c} Ab ZMAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{k so so so c} Ab ZMAlg Ab_K EM_to_AbS _ _).
  - exists (fun x => Ab_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun G => Ab_EM_unit_iso G). intros G H f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* K G is ⟨G, U ε_G⟩: the evaluation of a formal sum to its actual sum. *)
Example Ab_K_carrier@{+} (G : Ab) : projT1 (fobj[Ab_K] G) = Ab_Forget G
  := eq_refl.

Example Ab_K_map@{+} {G H : Ab} (f : G ~{Ab}~> H) :
  t_alg_hom[fmap[Ab_K] f] = fmap[Ab_Forget] f := eq_refl.

Example Ab_K_alg@{+} (G : Ab) :
  t_alg[projT2 (fobj[Ab_K] G)]
    = fmap[Ab_Forget] (@counit _ _ _ _ free_ab_adjunction_hom G) := eq_refl.

Example Ab_K_alg_fun@{+} (G : Ab) (t : FATerm (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] t = fa_eval (@id Sets@{c so} (Ab_Forget G)) t
  := eq_refl.

Example Ab_K_alg_gen@{+} (G : Ab) (x : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_gen x) = x := eq_refl.

Example Ab_K_alg_zero@{+} (G : Ab) :
  t_alg[projT2 (fobj[Ab_K] G)] fa_zero = cmon_zero G := eq_refl.

Example Ab_K_alg_plus@{+} (G : Ab) (x y : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_plus (fa_gen x) (fa_gen y))
    = cmon_plus G x y := eq_refl.

Example Ab_K_alg_neg@{+} (G : Ab) (x : carrier (Ab_Forget G)) :
  t_alg[projT2 (fobj[Ab_K] G)] (fa_neg (fa_gen x)) = ab_neg G x := eq_refl.

(* The legs of the isomorphism in Cat. *)
Example Ab_EM_iso_to@{+} : to Ab_EM_iso = Ab_K := eq_refl.

Example Ab_EM_iso_from@{+} : from Ab_EM_iso = EM_to_AbS := eq_refl.

(* The group of an algebra: its carrier, its [Prop] equality and its
   operations. *)
Example EM_to_AbS_prop@{+} (x : ZMAlg) (a b : carrier (projT1 x)) :
  @pequiv _ _ (cmon_prop (fobj[EM_to_AbS] x)) a b
    = @fa_eq (projT1 x) (fa_gen a) (fa_gen b) := eq_refl.

Example EM_to_AbS_carrier@{+} (x : ZMAlg) :
  cmon_setoid (fobj[EM_to_AbS] x) = projT1 x := eq_refl.

Example EM_to_AbS_zero@{+} (x : ZMAlg) :
  cmon_zero (fobj[EM_to_AbS] x) = t_alg[projT2 x] fa_zero := eq_refl.

Example EM_to_AbS_plus@{+} (x : ZMAlg) (a b : carrier (projT1 x)) :
  cmon_plus (fobj[EM_to_AbS] x) a b
    = t_alg[projT2 x] (fa_plus (fa_gen a) (fa_gen b)) := eq_refl.

Example EM_to_AbS_neg@{+} (x : ZMAlg) (a : carrier (projT1 x)) :
  ab_neg (fobj[EM_to_AbS] x) a = t_alg[projT2 x] (fa_neg (fa_gen a))
  := eq_refl.

Example EM_to_AbS_map@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  cmon_map (fmap[EM_to_AbS] f) = t_alg_hom[f] := eq_refl.

(* The round trips keep every operation on the nose ... *)
Example Ab_rt_carrier@{+} (G : Ab) :
  cmon_setoid (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_setoid G := eq_refl.

Example Ab_rt_zero@{+} (G : Ab) :
  cmon_zero (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_zero G := eq_refl.

Example Ab_rt_plus@{+} (G : Ab) :
  cmon_plus (fobj[EM_to_AbS ◯ Ab_K] G) = cmon_plus G := eq_refl.

Example Ab_rt_neg@{+} (G : Ab) :
  ab_neg (fobj[EM_to_AbS ◯ Ab_K] G) = ab_neg G := eq_refl.

Example Ab_rt_hom@{+} {G H : Ab} (f : G ~{Ab}~> H) :
  cmon_map (fmap[EM_to_AbS ◯ Ab_K] f) = cmon_map f := eq_refl.

(* ... and so do the carrier and the maps of the algebra round trip. *)
Example ZMAlg_rt_carrier@{+} (x : ZMAlg) :
  projT1 (fobj[Ab_K ◯ EM_to_AbS] x) = projT1 x := eq_refl.

Example ZMAlg_rt_alg_fun@{+} (x : ZMAlg) (t : FATerm (projT1 x)) :
  t_alg[projT2 (fobj[Ab_K ◯ EM_to_AbS] x)] t
    = fa_eval (A := zm_alg_ab (projT2 x))
        (@id Sets@{c so} (Ab_Forget (zm_alg_ab (projT2 x)))) t
  := eq_refl.

Example ZMAlg_rt_alg_hom@{+} {x y : ZMAlg} (f : x ~{ZMAlg}~> y) :
  t_alg_hom[fmap[Ab_K ◯ EM_to_AbS] f] = t_alg_hom[f] := eq_refl.

(* Every component of the two natural isomorphisms is the identity. *)
Example Ab_EM_iso_to_from_component@{+} (x : ZMAlg) :
  (t_alg_hom[to (projT1 (iso_to_from Ab_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Ab_EM_iso) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example Ab_EM_iso_from_to_component@{+} (G : Ab) :
  (cmon_map (to (projT1 (iso_from_to Ab_EM_iso) G)),
   cmon_map (from (projT1 (iso_from_to Ab_EM_iso) G)))
    = (@id Sets@{c so} (Ab_Forget G), @id Sets@{c so} (Ab_Forget G))
  := eq_refl.

(* ...and so is every component of the equivalence's counit and unit. *)
Example Ab_EM_counit_component@{+} (x : ZMAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Ab_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _ Ab_EM_equivalence) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example Ab_EM_unit_component@{+} (G : Ab) :
  (cmon_map (to (projT1 (@equivalence_unit _ _ _ Ab_EM_equivalence) G)),
   cmon_map (from (projT1 (@equivalence_unit _ _ _ Ab_EM_equivalence) G)))
    = (@id Sets@{c so} (Ab_Forget G), @id Sets@{c so} (Ab_Forget G))
  := eq_refl.

End FreeAbMonad.
