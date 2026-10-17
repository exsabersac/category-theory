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
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.Free.

Generalizable All Variables.

(** * The free R-module monad T_R on Set and its algebras, the R-modules *)

(*
 Book: Riehl, "Category Theory in Context", Example 5.1.4(iii),
 nLab: https://ncatlab.org/nlab/show/free+module
 nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
 nLab: https://ncatlab.org/nlab/show/monadic+functor

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** T_R, the monad of the adjunction Set ⇀ R-Mod *)

Section FreeModMonad.

Universes a c p so.
Context (R : RingObject@{a c p}).

Local Notation scalar := (carrier (rig_setoid (ring_rig R))).

(* T_R = U ◯ F, with F Instance/Mod/Free.v's [FreeMod]. *)
Definition FreeModF@{+} : Sets@{c so} ⟶ Sets@{c so} :=
  RMod_Forget R ◯ FreeMod R.

(* T_R, the monad of the hom-set form of the free-forgetful adjunction. *)
Definition FreeModMonad@{+} : @Monad Sets@{c so} FreeModF :=
  Adjunction_Induced_Monad (free_module_adjunction_hom R).

(* The relabelling of a combination along u: the fold of insert ∘ u. *)
Definition fv_relabel@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : @FVTerm R Y :=
  fv_eval (W := FreeModObject Y) (fv_insert Y ∘ u) t.

(* A combination of combinations, flattened: the fold of the identity. *)
Definition fv_flatten@{+} {X : Sets@{c so}}
  (k : @FVTerm R (RMod_Forget R (FreeModObject X))) : @FVTerm R X :=
  fv_eval (W := FreeModObject X)
    (@id Sets@{c so} (RMod_Forget R (FreeModObject X))) k.

(* T_R X is the free module's setoid, whose carrier is the formal
   combinations. *)
Example TR_obj@{+} (X : Sets@{c so}) :
  fobj[FreeModF] X = RMod_Forget R (FreeModObject X) := eq_refl.

Example TR_carrier@{+} (X : Sets@{c so}) :
  carrier (fobj[FreeModF] X) = @FVTerm R X := eq_refl.

(* η_X is the insertion of the basis, as a setoid map, and x ↦ ⟨x⟩. *)
Example TR_ret@{+} (X : Sets@{c so}) :
  @ret _ _ FreeModMonad X = fv_insert X := eq_refl.

Example TR_ret_fun@{+} (X : Sets@{c so}) (x : carrier X) :
  @ret _ _ FreeModMonad X x = fv_gen x := eq_refl.

(* μ = U ε F. *)
Example TR_join_counit@{+} (X : Sets@{c so}) :
  @join _ _ FreeModMonad X
    = fmap[RMod_Forget R]
        (@counit _ _ _ _ (free_module_adjunction_hom R) (FreeMod R X))
  := eq_refl.

(* μ flattens: ⟨t⟩ ↦ t, and in general the fold of the identity. *)
Example TR_join_gen@{+} (X : Sets@{c so}) (t : @FVTerm R X) :
  @join _ _ FreeModMonad X (@fv_gen R (RMod_Forget R (FreeModObject X)) t)
    = t := eq_refl.

Example TR_join_fun@{+} (X : Sets@{c so})
  (k : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  @join _ _ FreeModMonad X k = fv_flatten k := eq_refl.

Example TR_join_zero@{+} (X : Sets@{c so}) :
  @join _ _ FreeModMonad X fv_zero = fv_zero := eq_refl.

(* μ scales and flattens: r·⟨t⟩ + s·⟨t'⟩ ↦ r·t + s·t'. *)
Example TR_join_lc@{+} (X : Sets@{c so}) (r s : scalar)
  (t t' : @FVTerm R X) :
  @join _ _ FreeModMonad X
    (fv_plus (fv_smul r (@fv_gen R (RMod_Forget R (FreeModObject X)) t))
             (fv_smul s (@fv_gen R (RMod_Forget R (FreeModObject X)) t')))
    = fv_plus (fv_smul r t) (fv_smul s t') := eq_refl.

(* T_R u relabels, up to ≈: the free functor's action on arrows is read
   through the universal arrows. *)
Lemma TR_map_equiv@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : fmap[FreeModF] u t ≈ fv_relabel u t.
Proof.
  apply (fv_extend_unique (FreeModObject Y) (fv_insert Y ∘ u)
           (fmap[FreeMod R] u)).
  intro x. exact (free_module_fmap_generators u x).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Part (a), first reading: formal linear combinations *)

(* Evaluating a relabelled combination (Leibniz, by induction). *)
Lemma fv_eval_relabel@{+} {X Y : Sets@{c so}} {W : RMod R}
  (h : Y ~{Sets@{c so}}~> RMod_Forget R W) (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : fv_eval h (fv_relabel u t) = fv_eval (h ∘ u) t.
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* Evaluating a flattened combination of combinations (Leibniz). *)
Lemma fv_eval_flatten@{+} {X : Sets@{c so}} {W : RMod R}
  (h : X ~{Sets@{c so}}~> RMod_Forget R W)
  (k : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  fv_eval h (fv_flatten k) = fv_eval (fmap[RMod_Forget R] (fv_extend h)) k.
Proof.
  induction k as [ t | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* A list of coefficient/generator pairs, relabelled pairwise. *)
Fixpoint fv_lc_map@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (l : list (fv_pair R X)) : list (fv_pair R Y) :=
  match l with
  | nil => nil
  | cons q l' => cons (fst q, u (snd q)) (fv_lc_map u l')
  end.

(* A list of scaled lists, each inner list scaled and all concatenated. *)
Fixpoint fv_lc_flat@{+} {X : Sets@{c so}}
  (L : list (scalar * list (fv_pair R X))) : list (fv_pair R X) :=
  match L with
  | nil => nil
  | cons q L' => fv_app R X (fv_scale R X (fst q) (snd q)) (fv_lc_flat L')
  end.

(* The same list of scaled lists, read as a combination of combinations. *)
Fixpoint fv_lc_inner@{+} {X : Sets@{c so}}
  (L : list (scalar * list (fv_pair R X)))
  : list (fv_pair R (RMod_Forget R (FreeModObject X))) :=
  match L with
  | nil => nil
  | cons q L' => cons (fst q, fv_lc (snd q)) (fv_lc_inner L')
  end.

(* The relabelling of a combination relabels each pair (Leibniz). *)
Lemma fv_relabel_lc@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (l : list (fv_pair R X)) :
  fv_relabel u (fv_lc l) = fv_lc (fv_lc_map u l).
Proof.
  induction l as [|q l IH]; [ reflexivity | ].
  simpl. f_equal. exact IH.
Qed.

(* T_R u relabels each pair. *)
Lemma TR_map_lc@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (l : list (fv_pair R X)) :
  fv_eq (fmap[FreeModF] u (fv_lc l)) (fv_lc (fv_lc_map u l)).
Proof.
  refine (fe_trans (TR_map_equiv u (fv_lc l)) _).
  rewrite fv_relabel_lc. apply fv_refl.
Qed.

(* η_X x is the one-pair combination 1·x. *)
Lemma TR_ret_lc@{+} {X : Sets@{c so}} (x : carrier X) :
  fv_eq (@ret _ _ FreeModMonad X x)
        (fv_lc (cons (rig_one (ring_rig R), x) nil)).
Proof.
  simpl.
  refine (fe_trans (fe_sym (fe_zero_l _)) _).
  refine (fe_trans (fe_comm _ _) _).
  exact (fe_plus (fe_sym (fe_smul_one _)) (fv_refl _)).
Qed.

(* μ_X scales each inner combination by its coefficient and
   concatenates. *)
Lemma TR_join_lc_flat@{+} {X : Sets@{c so}}
  (L : list (scalar * list (fv_pair R X))) :
  fv_eq (@join _ _ FreeModMonad X (fv_lc (fv_lc_inner L)))
        (fv_lc (fv_lc_flat L)).
Proof.
  induction L as [|q L IH]; simpl.
  - apply fv_refl.
  - refine (fe_trans _ (fe_sym (fv_lc_app R X _ _))).
    refine (fe_plus _ IH).
    refine (fe_trans _ (fe_sym (fv_lc_scale R X _ _))).
    exact (fe_smul (reflexivity _) (fv_refl _)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Part (b): the monad laws verified directly *)

(* A Leibniz equality of combinations is an [fv_eq]. *)
Lemma fv_eq_of_eq@{+} {X : Sets@{c so}} (s t : @FVTerm R X) :
  s = t → fv_eq s t.
Proof. intros ->. apply fv_refl. Qed.

Lemma fv_relabel_id@{+} {X : Sets@{c so}} (t : @FVTerm R X) :
  fv_relabel (@id Sets@{c so} X) t = t.
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

Lemma fv_relabel_comp@{+} {X Y Z : Sets@{c so}} (g : Y ~{Sets@{c so}}~> Z)
  (f : X ~{Sets@{c so}}~> Y) (t : @FVTerm R X) :
  fv_relabel (g ∘ f) t = fv_relabel g (fv_relabel f t).
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

Lemma fv_relabel_respects@{+} {X Y : Sets@{c so}}
  (u u' : X ~{Sets@{c so}}~> Y) (H : u ≈ u') (t : @FVTerm R X) :
  fv_eq (fv_relabel u t) (fv_relabel u' t).
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ]; simpl.
  - exact (fe_gen (H x)).
  - apply fv_refl.
  - exact (fe_plus IHs IHv).
  - exact (fe_neg IHs).
  - exact (fe_smul (reflexivity r) IHs).
Qed.

(* μ ∘ T μ = μ ∘ μ T, on a combination of combinations of combinations. *)
Lemma fv_flatten_assoc@{+} {X : Sets@{c so}}
  (K3 : @FVTerm R (RMod_Forget R (FreeModObject
                     (RMod_Forget R (FreeModObject X))))) :
  fv_flatten (fv_relabel (fmap[RMod_Forget R]
                (fv_extend (@id Sets@{c so}
                              (RMod_Forget R (FreeModObject X))))) K3)
  = fv_flatten (fv_flatten K3).
Proof.
  induction K3 as [ k | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* μ ∘ T η = 1. *)
Lemma fv_flatten_relabel_insert@{+} {X : Sets@{c so}} (t : @FVTerm R X) :
  fv_flatten (fv_relabel (fv_insert X) t) = t.
Proof.
  induction t as [ x | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* μ is natural. *)
Lemma fv_flatten_natural@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (K : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  fv_flatten (fv_relabel (fmap[RMod_Forget R]
                            (fv_extend (fv_insert Y ∘ u))) K)
  = fv_relabel u (fv_flatten K).
Proof.
  induction K as [ k | | s IHs v IHv | s IHs | r s IHs ];
    (reflexivity || (simpl; f_equal; assumption)).
Qed.

(* The endofunctor of Mac Lane's description: T_R t relabels each
   generator. *)
Definition FreeModF_direct@{+} : Sets@{c so} ⟶ Sets@{c so}.
Proof using R.
  unshelve refine
    (@Build_Functor Sets@{c so} Sets@{c so}
       (fun X => RMod_Forget R (FreeModObject X))
       (fun X Y u => fmap[RMod_Forget R] (fv_extend (fv_insert Y ∘ u)))
       _ _ _).
  - intros X Y u u' H t. exact (fv_relabel_respects u u' H t).
  - intros X t. exact (fv_eq_of_eq _ _ (fv_relabel_id t)).
  - intros X Y Z g f t. exact (fv_eq_of_eq _ _ (fv_relabel_comp g f t)).
Defined.

(* The monad laws, each by the Leibniz lemmas above; no adjunction is
   cited. *)
Definition FreeModMonad_direct@{+} : @Monad Sets@{c so} FreeModF_direct.
Proof.
  unshelve refine
    (@Build_Monad Sets@{c so} FreeModF_direct
       (fun X => fv_insert X)
       (fun X => fmap[RMod_Forget R]
                   (fv_extend (@id Sets@{c so}
                                 (RMod_Forget R (FreeModObject X)))))
       _ _ _ _ _).
  - (* η natural *) intros X Y u x. reflexivity.
  - (* μ ∘ T μ ≈ μ ∘ μ T *)
    intros X K3. exact (fv_eq_of_eq _ _ (fv_flatten_assoc K3)).
  - (* μ ∘ T η ≈ 1 *)
    intros X t. exact (fv_eq_of_eq _ _ (fv_flatten_relabel_insert t)).
  - (* μ ∘ η T ≈ 1 *) intros X t. apply fv_refl.
  - (* μ natural *)
    intros X Y u K. exact (fv_eq_of_eq _ _ (fv_flatten_natural u K)).
Defined.

(* Its unit and multiplication ARE T_R's, and its action on arrows is the
   relabelling. *)
Example TR_direct_ret@{+} (X : Sets@{c so}) :
  @ret _ _ FreeModMonad_direct X = @ret _ _ FreeModMonad X := eq_refl.

Example TR_direct_join@{+} (X : Sets@{c so}) :
  @join _ _ FreeModMonad_direct X = @join _ _ FreeModMonad X := eq_refl.

Example TR_direct_obj@{+} (X : Sets@{c so}) :
  fobj[FreeModF_direct] X = fobj[FreeModF] X := eq_refl.

Example TR_direct_map@{+} {X Y : Sets@{c so}} (u : X ~{Sets@{c so}}~> Y)
  (t : @FVTerm R X) : fmap[FreeModF_direct] u t = fv_relabel u t
  := eq_refl.

Example TR_direct_map_gen@{+} {X Y : Sets@{c so}}
  (u : X ~{Sets@{c so}}~> Y) (x : carrier X) :
  fmap[FreeModF_direct] u (fv_gen x) = fv_gen (u x) := eq_refl.

(* The two endofunctors agree, with identity components. *)
Definition FreeModF_direct_iso@{+} : FreeModF_direct ≈ FreeModF.
Proof.
  exists (fun X => @iso_id Sets@{c so} (fobj[FreeModF] X)).
  intros X Y u t.
  exact (fe_sym (TR_map_equiv u t)).
Defined.

Example TR_direct_iso_component@{+} (X : Sets@{c so}) :
  (to (projT1 FreeModF_direct_iso X), from (projT1 FreeModF_direct_iso X))
    = (@id Sets@{c so} (fobj[FreeModF] X), @id Sets@{c so} (fobj[FreeModF] X))
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Part (c): the algebras of T_R are the R-modules *)

Definition TRAlg@{+} : Category@{so c c} :=
  @EilenbergMoore@{so so so c} Sets@{c so} FreeModF FreeModMonad.

(* The comparison functor K : R-Mod → Set^{T_R}. *)
Definition RMod_K@{+} : RMod R ⟶ TRAlg :=
  EM_Comparison (free_module_adjunction_hom R).

(* K commutes with the right adjoints and with the left ones: Monad/
   Comparison.v's two triangles, at this adjunction. *)
Theorem RMod_K_Forget@{+} :
  @EM_Forget Sets@{c so} FreeModF FreeModMonad ◯ RMod_K ≈ RMod_Forget R.
Proof. exact (EM_Comparison_Forget (free_module_adjunction_hom R)). Qed.

Theorem RMod_K_Free@{+} :
  RMod_K ◯ FreeMod R ≈ @EM_Free Sets@{c so} FreeModF FreeModMonad.
Proof. exact (EM_Comparison_Free (free_module_adjunction_hom R)). Qed.

Section Algebra.

Context {A : Sets@{c so}}.
Context (α : @TAlgebra Sets@{c so} FreeModF FreeModMonad A).

(* The module operations of an algebra (A, h): 0 = h⟨⟩, a + b =
   h(⟨a⟩ + ⟨b⟩), −a = h(−⟨a⟩) and r·a = h(r·⟨a⟩). *)
Definition tr_alg_zero@{+} : carrier A := t_alg[α] (@fv_zero R A).

Definition tr_alg_plus@{+} (x y : carrier A) : carrier A :=
  t_alg[α] (@fv_plus R A (fv_gen x) (fv_gen y)).

Definition tr_alg_neg@{+} (x : carrier A) : carrier A :=
  t_alg[α] (@fv_neg R A (fv_gen x)).

Definition tr_alg_smul@{+} (r : scalar) (x : carrier A) : carrier A :=
  t_alg[α] (@fv_smul R A r (fv_gen x)).

(* The linear combination with the coefficients of the term, through the
   operations just defined. *)
Fixpoint tr_alg_eval@{+} (t : @FVTerm R A) : carrier A :=
  match t with
  | fv_gen x    => x
  | fv_zero     => tr_alg_zero
  | fv_plus s u => tr_alg_plus (tr_alg_eval s) (tr_alg_eval u)
  | fv_neg s    => tr_alg_neg (tr_alg_eval s)
  | fv_smul r s => tr_alg_smul r (tr_alg_eval s)
  end.

Lemma tr_alg_unit@{+} (x : carrier A) : t_alg[α] (@fv_gen R A x) ≈ x.
Proof. exact (@t_id _ _ _ _ α x). Qed.

(* h ∘ μ ≈ h ∘ T h, read through the relabelling. *)
Lemma tr_alg_step@{+} (K : @FVTerm R (fobj[FreeModF] A)) :
  t_alg[α] (@join _ _ FreeModMonad A K) ≈ t_alg[α] (fv_relabel t_alg[α] K).
Proof.
  symmetry.
  refine (transitivity _ (@t_action _ _ _ _ α K)).
  apply (proper_morphism t_alg[α]).
  symmetry. exact (TR_map_equiv t_alg[α] K).
Qed.

Lemma tr_alg_plus_respects@{+} :
  Proper (equiv ==> equiv ==> equiv) tr_alg_plus.
Proof.
  intros x x' Hx y y' Hy.
  exact (proper_morphism t_alg[α] _ _ (fe_plus (fe_gen Hx) (fe_gen Hy))).
Qed.

Lemma tr_alg_neg_respects@{+} : Proper (equiv ==> equiv) tr_alg_neg.
Proof.
  intros x x' Hx. exact (proper_morphism t_alg[α] _ _ (fe_neg (fe_gen Hx))).
Qed.

Lemma tr_alg_smul_respects@{+} :
  Proper (equiv ==> equiv ==> equiv) tr_alg_smul.
Proof.
  intros r r' Hr x x' Hx.
  exact (proper_morphism t_alg[α] _ _ (fe_smul Hr (fe_gen Hx))).
Qed.

(* The structure map IS linear combination in the derived module. *)
Lemma tr_alg_fold@{+} (t : @FVTerm R A) : t_alg[α] t ≈ tr_alg_eval t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs | r s IHs ]; simpl.
  - exact (tr_alg_unit x).
  - reflexivity.
  - refine (transitivity
              (tr_alg_step
                 (@fv_plus R (fobj[FreeModF] A)
                    (@fv_gen R (fobj[FreeModF] A) s)
                    (@fv_gen R (fobj[FreeModF] A) u))) _).
    exact (tr_alg_plus_respects _ _ IHs _ _ IHu).
  - refine (transitivity
              (tr_alg_step
                 (@fv_neg R (fobj[FreeModF] A)
                    (@fv_gen R (fobj[FreeModF] A) s))) _).
    exact (tr_alg_neg_respects _ _ IHs).
  - refine (transitivity
              (tr_alg_step
                 (@fv_smul R (fobj[FreeModF] A) r
                    (@fv_gen R (fobj[FreeModF] A) s))) _).
    exact (tr_alg_smul_respects _ _ (reflexivity r) _ _ IHs).
Qed.

Lemma tr_alg_eval_respects@{+} (s t : @FVTerm R A) :
  fv_eq s t → tr_alg_eval s ≈ tr_alg_eval t.
Proof.
  intro H.
  refine (transitivity (symmetry (tr_alg_fold s)) _).
  refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
  exact (tr_alg_fold t).
Qed.

(* Every algebra's carrier is propositional, with no hypothesis: x ≈ y
   iff ⟨x⟩ ≈ ⟨y⟩ in T_R A, a [Prop]. *)
Definition tr_alg_prop@{+} : PropEquiv (is_setoid A).
Proof using R A α.
  unshelve refine
    (@Build_PropEquiv _ (is_setoid A)
       (fun x y => @fv_eq R A (fv_gen x) (fv_gen y)) _ _).
  - intros x y H.
    refine (transitivity (symmetry (tr_alg_unit x)) _).
    refine (transitivity (proper_morphism t_alg[α] _ _ H) _).
    exact (tr_alg_unit y).
  - intros x y H. exact (fe_gen H).
Defined.

(* The R-module of the algebra: each law is one instance of
   [tr_alg_eval_respects] at a constructor of [fv_eq]. *)
Definition tr_alg_rmod@{+} : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := A;
      cmon_zero := tr_alg_zero;
      cmon_plus := tr_alg_plus;
      cmon_plus_respects := tr_alg_plus_respects;
      cmon_plus_assoc := fun x y z =>
        tr_alg_eval_respects _ _ (fe_assoc (fv_gen x) (fv_gen y) (fv_gen z));
      cmon_plus_comm := fun x y =>
        tr_alg_eval_respects _ _ (fe_comm (fv_gen x) (fv_gen y));
      cmon_plus_zero_l := fun x =>
        tr_alg_eval_respects _ _ (fe_zero_l (fv_gen x));
      cmon_prop := tr_alg_prop
    |};
    ab_neg := tr_alg_neg;
    ab_neg_respects := tr_alg_neg_respects;
    ab_neg_left := fun x => tr_alg_eval_respects _ _ (fe_neg_l (fv_gen x))
  |};
  rm_smul := tr_alg_smul;
  rm_smul_respects := tr_alg_smul_respects;
  rm_smul_distr_l := fun r x y =>
    tr_alg_eval_respects _ _ (fe_smul_distr_l r (fv_gen x) (fv_gen y));
  rm_smul_distr_r := fun r s x =>
    tr_alg_eval_respects _ _ (fe_smul_distr_r r s (fv_gen x));
  rm_smul_assoc := fun r s x =>
    tr_alg_eval_respects _ _ (fe_smul_assoc r s (fv_gen x));
  rm_smul_one := fun x => tr_alg_eval_respects _ _ (fe_smul_one (fv_gen x))
|}.

End Algebra.

(* An algebra map is linear. *)
Lemma tr_alg_hom_step@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y)
  (t : @FVTerm R (projT1 x)) :
  t_alg_hom[f] (t_alg[projT2 x] t)
    ≈ t_alg[projT2 y] (fv_relabel t_alg_hom[f] t).
Proof.
  refine (transitivity (@t_alg_hom_commutes _ _ _ _ _ _ _ f t) _).
  apply (proper_morphism t_alg[projT2 y]).
  exact (TR_map_equiv t_alg_hom[f] t).
Qed.

Definition tr_alg_hom_rmod@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y) :
  tr_alg_rmod (projT2 x) ~{RMod R}~> tr_alg_rmod (projT2 y).
Proof.
  unshelve refine
    (@Build_RModHom R (tr_alg_rmod (projT2 x)) (tr_alg_rmod (projT2 y))
       (@Build_CMonHom (tr_alg_rmod (projT2 x)) (tr_alg_rmod (projT2 y))
          t_alg_hom[f] _ _) _).
  - exact (tr_alg_hom_step f fv_zero).
  - intros a b. exact (tr_alg_hom_step f (fv_plus (fv_gen a) (fv_gen b))).
  - intros r a. exact (tr_alg_hom_step f (fv_smul r (fv_gen a))).
Defined.

(* The functor Set^{T_R} → R-Mod. *)
Definition EM_to_RModS@{+} : TRAlg ⟶ RMod R.
Proof.
  unshelve refine
    (@Build_Functor TRAlg (RMod R) (fun x => tr_alg_rmod (projT2 x))
       (fun x y f => tr_alg_hom_rmod f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The fold of the identity in the derived module IS [tr_alg_eval]
   (Leibniz, by induction). *)
Lemma tr_fold_is_alg_eval@{+} {A : Sets@{c so}}
  (α : @TAlgebra Sets@{c so} FreeModF FreeModMonad A) (t : @FVTerm R A) :
  fv_eval (W := tr_alg_rmod α)
    (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod α))) t
  = tr_alg_eval α t.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs | r s IHs ]; simpl;
    try rewrite IHs; try rewrite IHu; reflexivity.
Qed.

(* The algebra round trip, with the identity as its component. *)
Definition RMod_EM_counit_iso@{+} (x : TRAlg) :
  @Isomorphism TRAlg (fobj[RMod_K ◯ EM_to_RModS] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism TRAlg (fobj[RMod_K ◯ EM_to_RModS] x) x
       (@Build_TAlgebraHom Sets@{c so} FreeModF FreeModMonad
          (projT1 x) (projT1 x)
          (projT2 (fobj[RMod_K ◯ EM_to_RModS] x)) (projT2 x)
          (@id Sets@{c so} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{c so} FreeModF FreeModMonad
          (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[RMod_K ◯ EM_to_RModS] x))
          (@id Sets@{c so} (projT1 x)) _) _ _).
  - intro t.
    change (fv_eval (W := tr_alg_rmod (projT2 x))
              (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod (projT2 x)))) t
            ≈ t_alg[projT2 x] (fmap[FreeModF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (tr_fold_is_alg_eval (projT2 x) t).
    refine (transitivity (symmetry (tr_alg_fold (projT2 x) t)) _).
    apply (proper_morphism t_alg[projT2 x]).
    symmetry. exact (@fmap_id _ _ FreeModF (projT1 x) t).
  - intro t.
    change (t_alg[projT2 x] t
            ≈ fv_eval (W := tr_alg_rmod (projT2 x))
                (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod (projT2 x))))
                (fmap[FreeModF] (@id Sets@{c so} (projT1 x)) t)).
    rewrite (tr_fold_is_alg_eval (projT2 x)).
    refine (transitivity (tr_alg_fold (projT2 x) t) _).
    apply tr_alg_eval_respects.
    exact (fe_sym (@fmap_id _ _ FreeModF (projT1 x) t)).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The module round trip, with the identity as its component: on a module
   M the derived operations ARE M's. *)
Definition RMod_EM_unit_iso@{+} (M : RMod R) :
  @Isomorphism (RMod R) (fobj[EM_to_RModS ◯ RMod_K] M) M.
Proof.
  unshelve refine
    (@Build_Isomorphism (RMod R) (fobj[EM_to_RModS ◯ RMod_K] M) M
       (@Build_RModHom R (fobj[EM_to_RModS ◯ RMod_K] M) M
          (@Build_CMonHom (fobj[EM_to_RModS ◯ RMod_K] M) M
             (@id Sets@{c so} (RMod_Forget R M)) _ _) _)
       (@Build_RModHom R M (fobj[EM_to_RModS ◯ RMod_K] M)
          (@Build_CMonHom M (fobj[EM_to_RModS ◯ RMod_K] M)
             (@id Sets@{c so} (RMod_Forget R M)) _ _) _) _ _).
  all: simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. *)
Definition RMod_EM_equivalence@{+} :
  @EquivalenceOfCategories (RMod R) TRAlg RMod_K.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ RMod_K EM_to_RModS _ _).
  - exists (fun x => RMod_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun M => iso_sym (RMod_EM_unit_iso M)).
    intros M N f a. reflexivity.
Defined.

(* R-modules are monadic over Set. *)
Definition RMod_Forget_Monadic@{+} : Monadic (RMod_Forget R).
Proof.
  exists (FreeMod R). exists (free_module_adjunction_hom R).
  exact RMod_EM_equivalence.
Defined.

(* R-Mod ≅ Set^{T_R} in Cat, from the two component isomorphisms. *)
Definition RMod_EM_iso@{k +} :
  @Isomorphism Cat@{k so so so c} (RMod R) TRAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{k so so so c} (RMod R) TRAlg
       RMod_K EM_to_RModS _ _).
  - exists (fun x => RMod_EM_counit_iso x). intros x y f a. reflexivity.
  - exists (fun M => RMod_EM_unit_iso M). intros M N f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* K M is ⟨M, U ε_M⟩: the structure map is the fold of the identity,
   the linear combination in M. *)
Example RMod_K_carrier@{+} (M : RMod R) :
  projT1 (fobj[RMod_K] M) = RMod_Forget R M := eq_refl.

Example RMod_K_map@{+} {M N : RMod R} (f : M ~{RMod R}~> N) :
  t_alg_hom[fmap[RMod_K] f] = fmap[RMod_Forget R] f := eq_refl.

Example RMod_K_alg@{+} (M : RMod R) :
  t_alg[projT2 (fobj[RMod_K] M)]
    = fmap[RMod_Forget R] (@counit _ _ _ _ (free_module_adjunction_hom R) M)
  := eq_refl.

Example RMod_K_alg_fun@{+} (M : RMod R)
  (t : @FVTerm R (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] t
    = fv_eval (@id Sets@{c so} (RMod_Forget R M)) t := eq_refl.

Example RMod_K_alg_gen@{+} (M : RMod R) (x : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_gen x) = x := eq_refl.

Example RMod_K_alg_zero@{+} (M : RMod R) :
  t_alg[projT2 (fobj[RMod_K] M)] fv_zero = cmon_zero M := eq_refl.

Example RMod_K_alg_plus@{+} (M : RMod R) (x y : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_plus (fv_gen x) (fv_gen y))
    = cmon_plus M x y := eq_refl.

Example RMod_K_alg_neg@{+} (M : RMod R) (x : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_neg (fv_gen x)) = ab_neg M x
  := eq_refl.

Example RMod_K_alg_smul@{+} (M : RMod R) (r : scalar)
  (x : carrier (RMod_Forget R M)) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_smul r (fv_gen x)) = rm_smul M r x
  := eq_refl.

(* h at Σ rᵢ·⟨xᵢ⟩ is the fold of the identity there, [RMod_K_alg_fun] at
   a combination; for a given list it unfolds to the linear combination
   r₁·x₁ + (r₂·x₂ + (… + 0)) in M. *)
Example RMod_K_alg_lc@{+} (M : RMod R)
  (l : list (fv_pair R (RMod_Forget R M))) :
  t_alg[projT2 (fobj[RMod_K] M)] (fv_lc l)
    = fv_eval (@id Sets@{c so} (RMod_Forget R M)) (fv_lc l) := eq_refl.

(* The legs of the isomorphism in Cat. *)
Example RMod_EM_iso_to@{+} : to RMod_EM_iso = RMod_K := eq_refl.

Example RMod_EM_iso_from@{+} : from RMod_EM_iso = EM_to_RModS
  := eq_refl.

(* The module of an algebra: its carrier, its [Prop] equality and its
   operations. *)
Example EM_to_RModS_prop@{+} (x : TRAlg) (a b : carrier (projT1 x)) :
  @pequiv _ _ (cmon_prop (fobj[EM_to_RModS] x)) a b
    = @fv_eq R (projT1 x) (fv_gen a) (fv_gen b) := eq_refl.

Example EM_to_RModS_carrier@{+} (x : TRAlg) :
  cmon_setoid (fobj[EM_to_RModS] x) = projT1 x := eq_refl.

Example EM_to_RModS_zero@{+} (x : TRAlg) :
  cmon_zero (fobj[EM_to_RModS] x) = t_alg[projT2 x] fv_zero := eq_refl.

Example EM_to_RModS_plus@{+} (x : TRAlg) (a b : carrier (projT1 x)) :
  cmon_plus (fobj[EM_to_RModS] x) a b
    = t_alg[projT2 x] (fv_plus (fv_gen a) (fv_gen b)) := eq_refl.

Example EM_to_RModS_neg@{+} (x : TRAlg) (a : carrier (projT1 x)) :
  ab_neg (fobj[EM_to_RModS] x) a = t_alg[projT2 x] (fv_neg (fv_gen a))
  := eq_refl.

Example EM_to_RModS_smul@{+} (x : TRAlg) (r : scalar)
  (a : carrier (projT1 x)) :
  rm_smul (fobj[EM_to_RModS] x) r a
    = t_alg[projT2 x] (fv_smul r (fv_gen a)) := eq_refl.

Example EM_to_RModS_map@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y) :
  cmon_map (rm_hom (fmap[EM_to_RModS] f)) = t_alg_hom[f] := eq_refl.

(* The round trips keep every operation on the nose... *)
Example RMod_rt_carrier@{+} (M : RMod R) :
  cmon_setoid (fobj[EM_to_RModS ◯ RMod_K] M) = cmon_setoid M := eq_refl.

Example RMod_rt_zero@{+} (M : RMod R) :
  cmon_zero (fobj[EM_to_RModS ◯ RMod_K] M) = cmon_zero M := eq_refl.

Example RMod_rt_plus@{+} (M : RMod R) :
  cmon_plus (fobj[EM_to_RModS ◯ RMod_K] M) = cmon_plus M := eq_refl.

Example RMod_rt_neg@{+} (M : RMod R) :
  ab_neg (fobj[EM_to_RModS ◯ RMod_K] M) = ab_neg M := eq_refl.

Example RMod_rt_smul@{+} (M : RMod R) :
  rm_smul (fobj[EM_to_RModS ◯ RMod_K] M) = rm_smul M := eq_refl.

Example RMod_rt_hom@{+} {M N : RMod R} (f : M ~{RMod R}~> N) :
  cmon_map (rm_hom (fmap[EM_to_RModS ◯ RMod_K] f)) = cmon_map (rm_hom f)
  := eq_refl.

(* ...and so do the carrier and the maps of the algebra round trip. *)
Example TRAlg_rt_carrier@{+} (x : TRAlg) :
  projT1 (fobj[RMod_K ◯ EM_to_RModS] x) = projT1 x := eq_refl.

Example TRAlg_rt_alg_fun@{+} (x : TRAlg) (t : @FVTerm R (projT1 x)) :
  t_alg[projT2 (fobj[RMod_K ◯ EM_to_RModS] x)] t
    = fv_eval (W := tr_alg_rmod (projT2 x))
        (@id Sets@{c so} (RMod_Forget R (tr_alg_rmod (projT2 x)))) t
  := eq_refl.

Example TRAlg_rt_alg_hom@{+} {x y : TRAlg} (f : x ~{TRAlg}~> y) :
  t_alg_hom[fmap[RMod_K ◯ EM_to_RModS] f] = t_alg_hom[f] := eq_refl.

(* Every component of the two natural isomorphisms is the identity, at a
   variable object, to and from. *)
Example RMod_EM_iso_to_from_component@{+} (x : TRAlg) :
  (t_alg_hom[to (projT1 (iso_to_from RMod_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from RMod_EM_iso) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example RMod_EM_iso_from_to_component@{+} (M : RMod R) :
  (cmon_map (rm_hom (to (projT1 (iso_from_to RMod_EM_iso) M))),
   cmon_map (rm_hom (from (projT1 (iso_from_to RMod_EM_iso) M))))
    = (@id Sets@{c so} (RMod_Forget R M), @id Sets@{c so} (RMod_Forget R M))
  := eq_refl.

(* ...and so is every component of the equivalence's counit and unit. *)
Example RMod_EM_counit_component@{+} (x : TRAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ RMod_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             RMod_EM_equivalence) x)])
    = (@id Sets@{c so} (projT1 x), @id Sets@{c so} (projT1 x)) := eq_refl.

Example RMod_EM_unit_component@{+} (M : RMod R) :
  (cmon_map (rm_hom (to (projT1 (@equivalence_unit _ _ _
                                   RMod_EM_equivalence) M))),
   cmon_map (rm_hom (from (projT1 (@equivalence_unit _ _ _
                                     RMod_EM_equivalence) M))))
    = (@id Sets@{c so} (RMod_Forget R M), @id Sets@{c so} (RMod_Forget R M))
  := eq_refl.

End FreeModMonad.

(* ------------------------------------------------------------------------ *)
(*
   本节说明 FreeMonad 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Coefficients.

Universes c so.
Context (R : RingObject@{c c c}).

Local Notation scalar := (carrier (rig_setoid (ring_rig R))).
Local Notation rzero := (rig_zero (ring_rig R)).
Local Notation rone := (rig_one (ring_rig R)).
Local Notation radd := (rig_add (ring_rig R)).
Local Notation rmul := (rig_mul (ring_rig R)).
Local Notation decider_on X :=
  (∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).

(* f ↦ f_y, the coefficient of y, as a setoid map T_R X → R. *)
Definition fv_coef@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (y : carrier X) :
  RMod_Forget R (FreeModObject X) ~{Sets@{c so}}~> RMod_Forget R (Ring_RMod R)
  := fmap[RMod_Forget R] (fv_extend (fv_probe_at R X Xdec y)).

(* (η_X x)_x = 1 ... (Leibniz, as Mac Lane writes it) *)
Lemma fv_coef_ret_same@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) : fv_coef Xdec x (@ret _ _ (FreeModMonad R) X x) = rone.
Proof.
  simpl. destruct (Xdec x x) as [_|n]; [ reflexivity | ].
  destruct (n (reflexivity x)).
Qed.

(* ... and (η_X x)_{x'} = 0 for x' ≉ x (Leibniz). *)
Lemma fv_coef_ret_other@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x x' : carrier X) :
  (x' ≈ x → False) → fv_coef Xdec x' (@ret _ _ (FreeModMonad R) X x) = rzero.
Proof.
  intro n. simpl. destruct (Xdec x' x) as [e|_]; [ destruct (n e) | ].
  reflexivity.
Qed.

(* [(T_R t) f]_y is the linear functional "f evaluated on the indicator
   of the fibre t⁻¹(y)" ... *)
Lemma fv_coef_map@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (f : @FVTerm R X) (y : carrier Y) :
  fv_coef Ydec y (fmap[FreeModF R] t f)
    ≈ fv_eval (fv_probe_at R Y Ydec y ∘ t) f.
Proof.
  refine (transitivity
            (proper_morphism (fv_coef Ydec y) _ _ (TR_map_equiv R t f)) _).
  change (fv_eval (fv_probe_at R Y Ydec y) (fv_relabel R t f)
          ≈ fv_eval (fv_probe_at R Y Ydec y ∘ t) f).
  rewrite (fv_eval_relabel R (fv_probe_at R Y Ydec y) t f).
  reflexivity.
Qed.

(* ... which on a combination is the literal sum Σ' f_x over the pairs
   (f_x, x) of f with t x ≈ y. *)
Fixpoint fv_fibre_sum@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (y : carrier Y) (l : list (fv_pair R X))
  : scalar :=
  match l with
  | nil => rzero
  | cons q l' =>
      match Ydec y (t (snd q)) with
      | inl _ => radd (fst q) (fv_fibre_sum Ydec t y l')
      | inr _ => fv_fibre_sum Ydec t y l'
      end
  end.

(* The indicator of the fibre over y, evaluated at Σ rᵢ·⟨xᵢ⟩: the one
   induction that [fv_coef_map_lc] and FinSupp.v's [fv_coef_lc] share. *)
Lemma fv_eval_fibre_lc@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (l : list (fv_pair R X)) (y : carrier Y) :
  fv_eval (fv_probe_at R Y Ydec y ∘ t) (fv_lc l) ≈ fv_fibre_sum Ydec t y l.
Proof.
  induction l as [|[r x] l IH]; simpl; [ reflexivity | ].
  destruct (Ydec y (t x)) as [e|n].
  - rewrite (rig_mul_one_r (ring_rig R) r).
    apply (rig_add_respects (ring_rig R)); [ reflexivity | exact IH ].
  - rewrite (rig_mul_zero_r (ring_rig R) r).
    rewrite (rig_add_zero_l (ring_rig R)). exact IH.
Qed.

Lemma fv_coef_map_lc@{+} {X Y : Sets@{c so}} (Ydec : decider_on Y)
  (t : X ~{Sets@{c so}}~> Y) (l : list (fv_pair R X)) (y : carrier Y) :
  fv_coef Ydec y (fmap[FreeModF R] t (fv_lc l)) ≈ fv_fibre_sum Ydec t y l.
Proof.
  exact (transitivity (fv_coef_map Ydec t (fv_lc l) y)
           (fv_eval_fibre_lc Ydec t l y)).
Qed.

(* (μ_X k)_x = Σ_f k_f f_x: the coefficient of x in μ k is the linear
   extension of f ↦ f_x, evaluated at k, on the nose ... *)
Lemma fv_coef_join@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) (k : @FVTerm R (RMod_Forget R (FreeModObject X))) :
  fv_coef Xdec x (@join _ _ (FreeModMonad R) X k)
    = fv_eval (W := Ring_RMod R) (fv_coef Xdec x) k.
Proof. exact (fv_eval_flatten R (fv_probe_at R X Xdec x) k). Qed.

(* ... which at k = Σ rᵢ·⟨fᵢ⟩ is Σ rᵢ·(fᵢ)_x. *)
Fixpoint fv_lc_weighted@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) (L : list (fv_pair R (RMod_Forget R (FreeModObject X))))
  : scalar :=
  match L with
  | nil => rzero
  | cons q L' =>
      radd (rmul (fst q) (fv_coef Xdec x (snd q))) (fv_lc_weighted Xdec x L')
  end.

Lemma fv_coef_join_lc@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (x : carrier X) (L : list (fv_pair R (RMod_Forget R (FreeModObject X)))) :
  fv_coef Xdec x (@join _ _ (FreeModMonad R) X (fv_lc L))
    = fv_lc_weighted Xdec x L.
Proof.
  rewrite fv_coef_join.
  induction L as [|q L IH]; [ reflexivity | ].
  simpl. f_equal. exact IH.
Qed.

(* The coefficient respects ≈ in its point, Leibniz, by induction ... *)
Lemma fv_coef_respects_point@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (y y' : carrier X) (H : y ≈ y') (t : @FVTerm R X) :
  fv_coef Xdec y t = fv_coef Xdec y' t.
Proof.
  induction t as [ z | | s IHs v IHv | s IHs | r s IHs ]; simpl in *.
  - destruct (Xdec y z) as [e|n], (Xdec y' z) as [e'|n'].
    + reflexivity.
    + destruct (n' (transitivity (symmetry H) e)).
    + destruct (n (transitivity H e')).
    + reflexivity.
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

(* ... and vanishes at every point that no pair of a combination
   names: T_R X's elements are finitely supported. *)
Fixpoint fv_avoids@{+} {X : Sets@{c so}} (y : carrier X)
  (l : list (fv_pair R X)) : Type@{c} :=
  match l with
  | nil => poly_unit@{c}
  | cons q l' => ((y ≈ snd q → False) * fv_avoids y l')%type
  end.

Lemma fv_coef_support@{+} {X : Sets@{c so}} (Xdec : decider_on X)
  (y : carrier X) (l : list (fv_pair R X)) :
  fv_avoids y l → fv_coef Xdec y (fv_lc l) ≈ rzero.
Proof.
  induction l as [|[r x] l IH]; simpl; intro Ha; [ reflexivity | ].
  destruct Ha as [n Ha].
  destruct (Xdec y x) as [e|_]; [ destruct (n e) | ].
  rewrite (rig_mul_zero_r (ring_rig R) r), (rig_add_zero_l (ring_rig R)).
  exact (IH Ha).
Qed.

End Coefficients.
