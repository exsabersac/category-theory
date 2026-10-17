Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Lie.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    nLab:      https://ncatlab.org/nlab/show/universal+enveloping+algebra
    nLab:      https://ncatlab.org/nlab/show/Poincare-Birkhoff-Witt+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Universal_enveloping_algebra

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UEnveloping.

Context (K : CRng).
Context (L : LieObject K).

(** ** Formal expressions *)

Inductive UEnvTerm : Type :=
  | uen_scal : carrier (rig_setoid (`1 K)) → UEnvTerm
  | uen_gen  : carrier (cmon_setoid (lie_mod L)) → UEnvTerm
  | uen_add  : UEnvTerm → UEnvTerm → UEnvTerm
  | uen_neg  : UEnvTerm → UEnvTerm
  | uen_mul  : UEnvTerm → UEnvTerm → UEnvTerm.

(** ** The congruence *)

(* AN EARLIER REVISION of this inductive landed in [Type].  Since the PR
   "algebraic carriers are sets" (2026-09-17) it lands in [Prop], because
   [RigObject] carries a [rig_prop : PropEquiv (is_setoid rig_setoid)] field
   and the `≈` of [UEnvRing] IS [uenv_eq]: the relation must BE a [Prop] for
   that field to be the identity pair of implications.  The cost is one
   elimination — [uenv_eval_respects] below goes through [pequiv_to] at the
   target algebra — and the non-degeneracy results are untouched, their
   conclusions being [False].  Test/ProbeTermModelPropRng.v pins the refusal
   of the old script. *)
Inductive uenv_eq : UEnvTerm → UEnvTerm → Prop :=
  | uq_scal {a b} : a ≈ b → uenv_eq (uen_scal a) (uen_scal b)
  | uq_gen {v w} : v ≈ w → uenv_eq (uen_gen v) (uen_gen w)
  | uq_add {s s' t t'} :
      uenv_eq s s' → uenv_eq t t' → uenv_eq (uen_add s t) (uen_add s' t')
  | uq_neg {s s'} : uenv_eq s s' → uenv_eq (uen_neg s) (uen_neg s')
  | uq_mul {s s' t t'} :
      uenv_eq s s' → uenv_eq t t' → uenv_eq (uen_mul s t) (uen_mul s' t')

  | uq_add_assoc s t u :
      uenv_eq (uen_add (uen_add s t) u) (uen_add s (uen_add t u))
  | uq_add_comm s t : uenv_eq (uen_add s t) (uen_add t s)
  | uq_add_zero_l s : uenv_eq (uen_add (uen_scal (rig_zero (`1 K))) s) s
  | uq_add_neg_l s :
      uenv_eq (uen_add (uen_neg s) s) (uen_scal (rig_zero (`1 K)))

  | uq_mul_assoc s t u :
      uenv_eq (uen_mul (uen_mul s t) u) (uen_mul s (uen_mul t u))
  | uq_mul_one_l s : uenv_eq (uen_mul (uen_scal (rig_one (`1 K))) s) s
  | uq_mul_one_r s : uenv_eq (uen_mul s (uen_scal (rig_one (`1 K)))) s

  | uq_distr_l s t u :
      uenv_eq (uen_mul s (uen_add t u))
              (uen_add (uen_mul s t) (uen_mul s u))
  | uq_distr_r s t u :
      uenv_eq (uen_mul (uen_add s t) u)
              (uen_add (uen_mul s u) (uen_mul t u))

  | uq_scal_add a b :
      uenv_eq (uen_scal (rig_add (`1 K) a b))
              (uen_add (uen_scal a) (uen_scal b))
  | uq_scal_mul a b :
      uenv_eq (uen_scal (rig_mul (`1 K) a b))
              (uen_mul (uen_scal a) (uen_scal b))

  | uq_gen_add v w :
      uenv_eq (uen_gen (cmon_plus (lie_mod L) v w))
              (uen_add (uen_gen v) (uen_gen w))
  | uq_gen_smul_l r v :
      uenv_eq (uen_gen (rm_smul (lie_mod L) r v))
              (uen_mul (uen_scal r) (uen_gen v))
  | uq_gen_smul_r r v :
      uenv_eq (uen_gen (rm_smul (lie_mod L) r v))
              (uen_mul (uen_gen v) (uen_scal r))

  (* THE ENVELOPING RELATION. *)
  | uq_bracket x y :
      uenv_eq (uen_gen (lie_br L x y))
              (uen_add (uen_mul (uen_gen x) (uen_gen y))
                       (uen_neg (uen_mul (uen_gen y) (uen_gen x))))

  | uq_sym {s t} : uenv_eq s t → uenv_eq t s
  | uq_trans {s t u} : uenv_eq s t → uenv_eq t u → uenv_eq s u.

Lemma uenv_refl (s : UEnvTerm) : uenv_eq s s.
Proof.
  induction s.
  - exact (uq_scal (reflexivity _)).
  - exact (uq_gen (reflexivity _)).
  - exact (uq_add IHs1 IHs2).
  - exact (uq_neg IHs).
  - exact (uq_mul IHs1 IHs2).
Qed.

Lemma uenv_eq_Equivalence : Equivalence uenv_eq.
Proof.
  constructor.
  - exact uenv_refl.
  - exact (fun s t => uq_sym).
  - exact (fun s t u => uq_trans).
Qed.

Definition uenv_Setoid : Setoid UEnvTerm := {|
  equiv        := uenv_eq;
  setoid_equiv := uenv_eq_Equivalence
|}.

(** ** Derived laws *)

Let UZ : UEnvTerm := uen_scal (rig_zero (`1 K)).
Let UO : UEnvTerm := uen_scal (rig_one (`1 K)).

Lemma uq_add_zero_r (s : UEnvTerm) : uenv_eq (uen_add s UZ) s.
Proof. exact (uq_trans (uq_add_comm s UZ) (uq_add_zero_l s)). Qed.

Lemma uq_add_neg_r (s : UEnvTerm) : uenv_eq (uen_add s (uen_neg s)) UZ.
Proof. exact (uq_trans (uq_add_comm s (uen_neg s)) (uq_add_neg_l s)). Qed.

Lemma uq_add_cancel_l (s t u : UEnvTerm) :
  uenv_eq (uen_add s t) (uen_add s u) → uenv_eq t u.
Proof.
  intro H.
  refine (uq_trans (uq_sym (uq_add_zero_l t)) _).
  refine (uq_trans (uq_add (uq_sym (uq_add_neg_l s)) (uenv_refl t)) _).
  refine (uq_trans (uq_add_assoc (uen_neg s) s t) _).
  refine (uq_trans (uq_add (uenv_refl (uen_neg s)) H) _).
  refine (uq_trans (uq_sym (uq_add_assoc (uen_neg s) s u)) _).
  refine (uq_trans (uq_add (uq_add_neg_l s) (uenv_refl u)) _).
  exact (uq_add_zero_l u).
Qed.

Lemma uq_mul_zero_l (s : UEnvTerm) : uenv_eq (uen_mul UZ s) UZ.
Proof.
  apply (uq_add_cancel_l (uen_mul UZ s)).
  refine (uq_trans (uq_sym (uq_distr_r UZ UZ s)) _).
  refine (uq_trans (uq_mul _ (uenv_refl s))
            (uq_sym (uq_add_zero_r (uen_mul UZ s)))).
  refine (uq_trans (uq_sym (uq_scal_add (rig_zero (`1 K))
                              (rig_zero (`1 K)))) _).
  exact (uq_scal (rig_add_zero_l (`1 K) (rig_zero (`1 K)))).
Qed.

Lemma uq_mul_zero_r (s : UEnvTerm) : uenv_eq (uen_mul s UZ) UZ.
Proof.
  apply (uq_add_cancel_l (uen_mul s UZ)).
  refine (uq_trans (uq_sym (uq_distr_l s UZ UZ)) _).
  refine (uq_trans (uq_mul (uenv_refl s) _)
            (uq_sym (uq_add_zero_r (uen_mul s UZ)))).
  refine (uq_trans (uq_sym (uq_scal_add (rig_zero (`1 K))
                              (rig_zero (`1 K)))) _).
  exact (uq_scal (rig_add_zero_l (`1 K) (rig_zero (`1 K)))).
Qed.

Lemma uq_gen_zero : uenv_eq (uen_gen (cmon_zero (lie_mod L))) UZ.
Proof.
  apply (uq_add_cancel_l (uen_gen (cmon_zero (lie_mod L)))).
  refine (uq_trans _
            (uq_sym (uq_add_zero_r (uen_gen (cmon_zero (lie_mod L)))))).
  refine (uq_trans (uq_sym (uq_gen_add (cmon_zero (lie_mod L))
                              (cmon_zero (lie_mod L)))) _).
  exact (uq_gen (cmon_plus_zero_l (lie_mod L) (cmon_zero (lie_mod L)))).
Qed.

(** ** The ring U(L) *)

Definition UEnvRig : RigObject := {|
  rig_setoid := {| carrier := UEnvTerm; is_setoid := uenv_Setoid |};
  rig_zero := UZ;
  rig_add := uen_add;
  rig_one := UO;
  rig_mul := uen_mul;
  rig_add_respects := fun _ _ Hs _ _ Ht => uq_add Hs Ht;
  rig_mul_respects := fun _ _ Hs _ _ Ht => uq_mul Hs Ht;
  rig_add_assoc := uq_add_assoc;
  rig_add_comm := uq_add_comm;
  rig_add_zero_l := uq_add_zero_l;
  rig_mul_assoc := uq_mul_assoc;
  rig_mul_one_l := uq_mul_one_l;
  rig_mul_one_r := uq_mul_one_r;
  rig_distr_l := uq_distr_l;
  rig_distr_r := uq_distr_r;
  rig_mul_zero_l := uq_mul_zero_l;
  rig_mul_zero_r := uq_mul_zero_r;
  (* [uenv_eq] IS a [Prop]-valued relation, so it is its own [Prop] mirror
     and both implications are the identity. *)
  rig_prop := @PropEquiv_of_relation _ uenv_Setoid uenv_eq
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition UEnvRing : RingObject := {|
  ring_rig := UEnvRig;
  ring_neg := uen_neg;
  ring_neg_respects := fun _ _ Hs => uq_neg Hs;
  ring_neg_l := uq_add_neg_l
|}.

(** ** The scalar inclusion, and centrality of its image *)

Program Definition uenv_scal : `1 K ~{Rng}~> UEnvRing := {|
  rig_map := {| morphism := uen_scal |}
|}.
Next Obligation. intros a b H; exact (uq_scal H). Qed.
Next Obligation. simpl; exact (uenv_refl UZ). Qed.
Next Obligation. intros a b; exact (uq_scal_add a b). Qed.
Next Obligation. simpl; exact (uenv_refl UO). Qed.
Next Obligation. intros a b; exact (uq_scal_mul a b). Qed.

Lemma uenv_scal_central (r : carrier (rig_setoid (`1 K))) (t : UEnvTerm) :
  uenv_eq (uen_mul (uen_scal r) t) (uen_mul t (uen_scal r)).
Proof.
  induction t as [ a | v | s IHs u IHu | s IHs | s IHs u IHu ].
  - refine (uq_trans (uq_sym (uq_scal_mul r a)) _).
    refine (uq_trans (uq_scal (`2 K r a)) _).
    exact (uq_scal_mul a r).
  - exact (uq_trans (uq_sym (uq_gen_smul_l r v)) (uq_gen_smul_r r v)).
  - refine (uq_trans (uq_distr_l (uen_scal r) s u) _).
    refine (uq_trans (uq_add IHs IHu) _).
    exact (uq_sym (uq_distr_r s u (uen_scal r))).
  - refine (uq_trans (lie_mul_neg_r UEnvRing (uen_scal r) s) _).
    refine (uq_trans (uq_neg IHs) _).
    exact (uq_sym (lie_mul_neg_l UEnvRing s (uen_scal r))).
  - refine (uq_trans (uq_sym (uq_mul_assoc (uen_scal r) s u)) _).
    refine (uq_trans (uq_mul IHs (uenv_refl u)) _).
    refine (uq_trans (uq_mul_assoc s (uen_scal r) u) _).
    refine (uq_trans (uq_mul (uenv_refl s) IHu) _).
    exact (uq_sym (uq_mul_assoc s u (uen_scal r))).
Qed.

Definition UEnvAlg : AAlgObject K :=
  Build_AAlgObject K UEnvRing uenv_scal uenv_scal_central.

(** ** The insertion of the Lie algebra *)

Program Definition uenv_insert_mod
  : RModHom (lie_mod L) (AAlg_RMod UEnvAlg) := {|
  rm_hom := {| cmon_map := {| morphism := uen_gen ;
                              proper_morphism := fun v w H => uq_gen H |} ;
               cmon_map_zero := uq_gen_zero ;
               cmon_map_plus := uq_gen_add |}
|}.
Next Obligation. intros r v; exact (uq_gen_smul_l r v). Qed.

Lemma uenv_insert_br (x y : carrier (cmon_setoid (lie_mod L))) :
  cmon_map (rm_hom uenv_insert_mod) (lie_br L x y)
    ≈ lie_br (lie_of_aalg UEnvAlg)
        (cmon_map (rm_hom uenv_insert_mod) x)
        (cmon_map (rm_hom uenv_insert_mod) y).
Proof. exact (uq_bracket x y). Qed.

Definition uenv_insert : LieHom L (lie_of_aalg UEnvAlg) :=
  @Build_LieHom K L (lie_of_aalg UEnvAlg) uenv_insert_mod uenv_insert_br.

(** * Evaluation *)

Section UEnvEvaluation.

Context (A : AAlgObject K).
Context (f : LieHom L (lie_of_aalg A)).

Fixpoint uenv_eval (t : UEnvTerm) : carrier (rig_setoid (aalg_ring A)) :=
  match t with
  | uen_scal a  => rig_map (aalg_unit A) a
  | uen_gen v   => cmon_map (rm_hom (lie_hom f)) v
  | uen_add s t => rig_add (aalg_ring A) (uenv_eval s) (uenv_eval t)
  | uen_neg s   => ring_neg (aalg_ring A) (uenv_eval s)
  | uen_mul s t => rig_mul (aalg_ring A) (uenv_eval s) (uenv_eval t)
  end.

(* AN EARLIER REVISION of this proof inducted on [uenv_eq] straight into the
   [Type]-valued goal `≈`.  Since the PR "algebraic carriers are sets"
   (2026-09-17) [uenv_eq] is a [Prop] inductive, so the script opens with
   [apply pequiv_to] at the TARGET algebra's own [rig_prop] and each branch
   returns to `≈` with [pequiv_from].  The twenty-two cases and the argument
   in each are unchanged; the induction hypotheses are now [pequiv]-valued,
   so the branches that consume one spend [pequiv_to] on it.  No hypothesis
   is added. *)
Lemma uenv_eval_respects (s t : UEnvTerm) :
  uenv_eq s t → uenv_eval s ≈ uenv_eval t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ a b Hab
    | v w Hvw
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' t t' _ IHs _ IHt
    | s t w | s t | s | s
    | s t w | s | s
    | s t w | s t w
    | a b | a b
    | v w | r v | r v
    | x y
    | s t _ IHst
    | s t w _ IHst _ IHtw ]; simpl.
  - apply pequiv_from;
      exact (proper_morphism (rig_map (aalg_unit A)) _ _ Hab).
  - apply pequiv_from;
      exact (proper_morphism (cmon_map (rm_hom (lie_hom f))) _ _ Hvw).
  - apply pequiv_from.
    exact (rig_add_respects (aalg_ring A) _ _ (pequiv_to _ _ IHs)
                                          _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ring_neg_respects (aalg_ring A) _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from.
    exact (rig_mul_respects (aalg_ring A) _ _ (pequiv_to _ _ IHs)
                                          _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from; exact (rig_add_assoc (aalg_ring A) _ _ _).
  - apply pequiv_from; exact (rig_add_comm (aalg_ring A) _ _).
  - apply pequiv_from;
      rewrite (rig_map_zero (aalg_unit A)); apply rig_add_zero_l.
  - apply pequiv_from;
      rewrite (rig_map_zero (aalg_unit A));
      apply (ring_neg_l (aalg_ring A)).
  - apply pequiv_from; exact (rig_mul_assoc (aalg_ring A) _ _ _).
  - apply pequiv_from;
      rewrite (rig_map_one (aalg_unit A)); apply rig_mul_one_l.
  - apply pequiv_from;
      rewrite (rig_map_one (aalg_unit A)); apply rig_mul_one_r.
  - apply pequiv_from; exact (rig_distr_l (aalg_ring A) _ _ _).
  - apply pequiv_from; exact (rig_distr_r (aalg_ring A) _ _ _).
  - apply pequiv_from; exact (rig_map_add (aalg_unit A) a b).
  - apply pequiv_from; exact (rig_map_mul (aalg_unit A) a b).
  - apply pequiv_from; exact (cmon_map_plus (rm_hom (lie_hom f)) v w).
  - apply pequiv_from; exact (rm_map_smul (lie_hom f) r v).
  - apply pequiv_from;
      rewrite (rm_map_smul (lie_hom f) r v); apply aalg_central.
  - apply pequiv_from; exact (lie_map_br f x y).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtw).
Qed.

Program Definition uenv_extend_ring : UEnvRing ~{Rng}~> aalg_ring A := {|
  rig_map := {| morphism := uenv_eval |}
|}.
Next Obligation. intros s t He; exact (uenv_eval_respects s t He). Qed.
Next Obligation. simpl; exact (rig_map_zero (aalg_unit A)). Qed.
Next Obligation. intros s t; simpl; reflexivity. Qed.
Next Obligation. simpl; exact (rig_map_one (aalg_unit A)). Qed.
Next Obligation. intros s t; simpl; reflexivity. Qed.

Lemma uenv_extend_triangle :
  aalg_unit A ≈ uenv_extend_ring ∘ aalg_unit UEnvAlg.
Proof. intro a; simpl; reflexivity. Qed.

Definition uenv_extend : UEnvAlg ~{AAlg K}~> A :=
  (uenv_extend_ring; uenv_extend_triangle).

Example uenv_extend_gen (v : carrier (cmon_setoid (lie_mod L))) :
  rig_map (`1 uenv_extend) (uen_gen v)
    = cmon_map (rm_hom (lie_hom f)) v := eq_refl.

Example uenv_extend_scal (a : carrier (rig_setoid (`1 K))) :
  rig_map (`1 uenv_extend) (uen_scal a) = rig_map (aalg_unit A) a := eq_refl.

Lemma uenv_extend_unique (g : UEnvRing ~{Rng}~> aalg_ring A)
  (Hscal : ∀ a, rig_map g (uen_scal a) ≈ rig_map (aalg_unit A) a)
  (Hgen : ∀ v, rig_map g (uen_gen v) ≈ cmon_map (rm_hom (lie_hom f)) v)
  (t : UEnvTerm) : rig_map g t ≈ uenv_eval t.
Proof.
  induction t as [ a | v | s IHs t IHt | s IHs | s IHs t IHt ]; simpl.
  - exact (Hscal a).
  - exact (Hgen v).
  - rewrite (rig_map_add g s t).
    exact (rig_add_respects (aalg_ring A) _ _ IHs _ _ IHt).
  - rewrite (RigHom_neg UEnvRing (aalg_ring A) g s).
    exact (ring_neg_respects (aalg_ring A) _ _ IHs).
  - rewrite (rig_map_mul g s t).
    exact (rig_mul_respects (aalg_ring A) _ _ IHs _ _ IHt).
Qed.

End UEnvEvaluation.

Lemma uenv_alg_hom_scal (A : AAlgObject K) (g : UEnvAlg ~{AAlg K}~> A)
  (a : carrier (rig_setoid (`1 K))) :
  rig_map (`1 g) (uen_scal a) ≈ rig_map (aalg_unit A) a.
Proof. symmetry; exact (`2 g a). Qed.

End UEnveloping.

Arguments UEnvTerm {K} L.
Arguments uen_scal {K L} a.
Arguments uen_gen {K L} v.
Arguments uen_add {K L} s t.
Arguments uen_neg {K L} s.
Arguments uen_mul {K L} s t.
Arguments uenv_eq {K L} s t.
Arguments uq_scal {K L a b} _.
Arguments uq_gen {K L v w} _.
Arguments uq_add {K L s s' t t'} _ _.
Arguments uq_neg {K L s s'} _.
Arguments uq_mul {K L s s' t t'} _ _.
Arguments uq_bracket {K L} x y.
Arguments uq_sym {K L s t} _.
Arguments uq_trans {K L s t u} _ _.
Arguments uenv_refl {K L} s.
Arguments uq_gen_zero {K} L.
Arguments UEnvRing {K} L.
Arguments UEnvAlg {K} L.
Arguments uenv_scal {K} L.
Arguments uenv_insert {K} L.
Arguments uenv_eval {K L} A f t.
Arguments uenv_extend {K L} A f.
Arguments uenv_extend_unique {K L} A f g Hscal Hgen t.
Arguments uenv_alg_hom_scal {K L} A g a.

(** * The universal property, and Mac Lane's E *)

Section EnvelopingUniversal.

Context (K : CRng).

(** The universal mapping property in the shape [universal_arrow_from_UMP]
    consumes. *)
Lemma uenv_universal (L : Lie K) (A : AAlg K)
  (h : L ~{Lie K}~> fobj[CommutatorFunctor K] A) :
  ∃! g : UEnvAlg L ~{AAlg K}~> A,
    h ≈ fmap[CommutatorFunctor K] g ∘ uenv_insert L.
Proof.
  unshelve eexists.
  - exact (uenv_extend A h).
  - intro v; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry.
    apply (uenv_extend_unique A h (`1 g)).
    + intro a; exact (uenv_alg_hom_scal A g a).
    + intro v; symmetry; exact (Hg v).
Defined.

(* The mediator the universal property produces IS the fixpoint
   extension, on the nose -- which is why [uenv_universal] is [Defined].
   Nothing else in the file reads through it. *)
Example uenv_universal_med (L : Lie K) (A : AAlg K)
  (h : L ~{Lie K}~> fobj[CommutatorFunctor K] A) :
  unique_obj (uenv_universal L A h) = uenv_extend A h := eq_refl.

Definition uenv_universal_arrow (L : Lie K)
  : UniversalArrow L (CommutatorFunctor K) :=
  universal_arrow_from_UMP L (CommutatorFunctor K) (UEnvAlg L)
    (uenv_insert L) (uenv_universal L).

(* The same content in the direct encoding, where the universal object is
   named rather than projected out of a comma category. *)
Program Definition uenv_auniversal_arrow (L : Lie K)
  : AUniversalArrow L (CommutatorFunctor K) (UEnvAlg L) := {|
  universal_arrow := uenv_insert L
|}.
Next Obligation.
  intros L A h.
  unshelve eexists.
  - exact (uenv_extend A h).
  - intro v; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry.
    apply (uenv_extend_unique A h (`1 g)).
    + intro a; exact (uenv_alg_hom_scal A g a).
    + intro v; exact (Hg v).
Qed.

(** ** The enveloping functor and THE ADJUNCTION *)

Definition EnvelopingFunctor : Lie K ⟶ AAlg K :=
  LeftAdjointFunctorFromUniversalArrows (CommutatorFunctor K)
    uenv_universal_arrow.

Definition enveloping_adjunction
  : EnvelopingFunctor ⊣ CommutatorFunctor K :=
  AdjunctionFromUniversalArrows (CommutatorFunctor K) uenv_universal_arrow.

Example EnvelopingFunctor_obj (L : Lie K) :
  fobj[EnvelopingFunctor] L = UEnvAlg L := eq_refl.

Example uenv_arrow_is_insert (L : Lie K) :
  @arrow _ _ L (CommutatorFunctor K) (uenv_universal_arrow L)
    = uenv_insert L := eq_refl.

(** ** The unit *)

Definition uenv_unit (L : Lie K)
  : L ~{Lie K}~> fobj[CommutatorFunctor K] (fobj[EnvelopingFunctor] L) :=
  @Category.Theory.Adjunction.unit _ _ _ _ enveloping_adjunction L.

Example uenv_unit_is_gen (L : Lie K)
  (v : carrier (cmon_setoid (lie_mod L))) :
  cmon_map (rm_hom (lie_hom (uenv_unit L))) v = uen_gen v := eq_refl.

(* The unit and the insertion agree POINTWISE on the nose, by the
   [eq_refl] above; the two underlying module homomorphisms are
   nevertheless not the same record, and the probe section pins that. *)
Theorem uenv_unit_is_insert (L : Lie K) :
  uenv_unit L ≈ uenv_insert L.
Proof. intro v; reflexivity. Qed.

(** ** The counit *)

Definition uenv_counit (A : AAlg K)
  : fobj[EnvelopingFunctor] (fobj[CommutatorFunctor K] A) ~{AAlg K}~> A :=
  @Category.Theory.Adjunction.counit _ _ _ _ enveloping_adjunction A.

(* The counit evaluates a generator to the element it names. *)
Lemma uenv_counit_gen (A : AAlg K)
  (v : carrier (cmon_setoid (lie_mod (fobj[CommutatorFunctor K] A)))) :
  rig_map (`1 (uenv_counit A)) (uen_gen v) ≈ v.
Proof.
  exact (@fmap_counit_unit _ _ _ _ enveloping_adjunction A v).
Qed.

(* ...hence it IS the extension of the identity Lie map, up to [≈]. *)
Theorem uenv_counit_is_extend (A : AAlg K) :
  uenv_counit A
    ≈ uenv_extend A (@id (Lie K) (fobj[CommutatorFunctor K] A)).
Proof.
  intro t.
  apply (uenv_extend_unique A (@id (Lie K) (fobj[CommutatorFunctor K] A))
           (`1 (uenv_counit A))).
  - intro a; exact (uenv_alg_hom_scal A (uenv_counit A) a).
  - intro v; exact (uenv_counit_gen A v).
Qed.

End EnvelopingUniversal.

Arguments uenv_universal {K} L A h.
Arguments uenv_universal_arrow {K} L.
Arguments uenv_unit {K} L.
Arguments uenv_counit {K} A.
Arguments uenv_unit_is_insert {K} L.
Arguments uenv_counit_gen {K} A v.
Arguments uenv_counit_is_extend {K} A.

(** * Non-degeneracy

    Nothing below is obtained by induction on [uenv_eq]: an induction on
    a quotienting relation cannot produce a negative statement.  Every
    separation is obtained by mapping OUT of U(L) into a concrete
    algebra where the two candidates have visibly different values --
    the route Instance/Vect/TensorAlgebra.v, Instance/Rng/Polynomial.v
    and Instance/Mod/Tensor.v all take for their own negatives. *)

(** ** A ring fact the positive half needs *)

Lemma uenv_sub_zero (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_add R a (ring_neg R b) ≈ rig_zero R → a ≈ b.
Proof.
  intro H.
  apply (ab_cancel_l (ring_ab R) (ring_neg R b)); simpl.
  rewrite (rig_add_comm R (ring_neg R b) a).
  rewrite H.
  rewrite (ring_neg_l R b).
  reflexivity.
Qed.

(** ** The relation constrains: over an ABELIAN Lie algebra the
       generators commute

    This is the positive half, and it is proved from the generating
    equation alone: [uq_bracket] at v and w says the commutator of the
    two generators IS the generator of [v,w], which the abelian bracket
    makes the generator of zero, which [uq_gen_zero] makes the scalar
    zero. *)
Theorem uenv_abelian_gens_commute (K : CRng) (M : RModObject (`1 K))
  (v w : carrier (cmon_setoid M)) :
  uenv_eq
    (uen_mul (@uen_gen K (lie_abelian M) v) (@uen_gen K (lie_abelian M) w))
    (uen_mul (@uen_gen K (lie_abelian M) w) (@uen_gen K (lie_abelian M) v)).
Proof.
  apply (uenv_sub_zero (UEnvRing (lie_abelian M))).
  refine (uq_trans (uq_sym (@uq_bracket K (lie_abelian M) v w)) _).
  exact (uq_gen_zero (lie_abelian M)).
Qed.

(** ** ...and it does not collapse: over [Lie_UT2] they do not

    The witness algebra is Instance/Rng/Algebras/Associative.v's
    upper-triangular 2x2 integer matrices, whose hom-setoid is Leibniz
    equality on Z-triples, so every image below REDUCES and each
    negative closes by [discriminate].  The map out is the extension of
    the IDENTITY Lie map of [Lie_UT2], which exists because
    [Lie_UT2] IS [lie_of_aalg UT2_AAlg]. *)

Definition uenv_ut2 : UEnvAlg Lie_UT2 ~{AAlg Int_CRng}~> UT2_AAlg :=
  uenv_extend UT2_AAlg (@id (Lie Int_CRng) Lie_UT2).

Definition uenv_ut2_g (x : ut2) : UEnvTerm Lie_UT2 :=
  @uen_gen Int_CRng Lie_UT2 x.

(* The map out evaluates a generator to the matrix it names, on the
   nose: the fixpoint's generator clause is the identity map. *)
Example uenv_ut2_gen (x : ut2) :
  rig_map (`1 uenv_ut2) (uenv_ut2_g x) = x := eq_refl.

Example uenv_ut2_one :
  rig_map (`1 uenv_ut2) (rig_one (UEnvRing Lie_UT2)) = rig_one UT2 := eq_refl.

Example uenv_ut2_zero :
  rig_map (`1 uenv_ut2) (rig_zero (UEnvRing Lie_UT2)) = rig_zero UT2
  := eq_refl.

(* Distinct generators stay distinct: the insertion does not collapse
   the Lie algebra. *)
Theorem uenv_ut2_gens_distinct :
  uenv_eq (uenv_ut2_g ut2_e11) (uenv_ut2_g ut2_e12) → False.
Proof.
  intro H.
  pose proof (proper_morphism (rig_map (`1 uenv_ut2)) _ _ H) as HH.
  unfold ut2_eqT in HH; simpl in HH; discriminate.
Qed.

(* A generator is not a scalar. *)
Theorem uenv_ut2_gen_not_scalar :
  uenv_eq (uenv_ut2_g ut2_e11) (uen_scal (rig_zero (`1 Int_CRng))) → False.
Proof.
  intro H.
  pose proof (proper_morphism (rig_map (`1 uenv_ut2)) _ _ H) as HH.
  unfold ut2_eqT in HH; simpl in HH; discriminate.
Qed.

(* U(L) is not the trivial algebra. *)
Theorem uenv_ut2_one_not_zero :
  rig_one (UEnvRing Lie_UT2) ≈ rig_zero (UEnvRing Lie_UT2) → False.
Proof.
  intro H.
  pose proof (proper_morphism (rig_map (`1 uenv_ut2)) _ _ H) as HH.
  unfold ut2_eqT in HH; simpl in HH; discriminate.
Qed.

(* THE SHARP ONE: U(L) is genuinely non-commutative, so the abelian
   theorem above is not a theorem about every Lie algebra, and the
   enveloping algebra is not a polynomial algebra in disguise. *)
Theorem uenv_ut2_gens_do_not_commute :
  uenv_eq (uen_mul (uenv_ut2_g ut2_e11) (uenv_ut2_g ut2_e12))
          (uen_mul (uenv_ut2_g ut2_e12) (uenv_ut2_g ut2_e11)) → False.
Proof.
  intro H.
  pose proof (proper_morphism (rig_map (`1 uenv_ut2)) _ _ H) as HH.
  unfold ut2_eqT in HH; simpl in HH; discriminate.
Qed.

Theorem uenv_not_all_commutative :
  (∀ (K : CRng) (L : LieObject K) (s t : UEnvTerm L),
     uenv_eq (uen_mul s t) (uen_mul t s)) → False.
Proof.
  intro H.
  exact (uenv_ut2_gens_do_not_commute
           (H Int_CRng Lie_UT2 (uenv_ut2_g ut2_e11) (uenv_ut2_g ut2_e12))).
Qed.

(* And the enveloping relation is exercised at a NON-ZERO bracket: the
   commutator of the two generators is the generator of [E11,E12],
   which is E12 and not zero. *)
Example uenv_ut2_bracket_computes :
  lie_br Lie_UT2 ut2_e11 ut2_e12 = ut2_e12 := eq_refl.

Theorem uenv_ut2_bracket_relation :
  uenv_eq (uenv_ut2_g ut2_e12)
          (uen_add (uen_mul (uenv_ut2_g ut2_e11) (uenv_ut2_g ut2_e12))
                   (uen_neg (uen_mul (uenv_ut2_g ut2_e12)
                                     (uenv_ut2_g ut2_e11)))).
Proof. exact (@uq_bracket Int_CRng Lie_UT2 ut2_e11 ut2_e12). Qed.

(** * Probes

    Each negative is stated beside an APPLIED positive control.  Each
    was stripped ONE AT A TIME -- the others left as [Fail], since a
    [Fail] spans several lines and commenting out only its first line
    yields a syntax error and so a FALSE pass -- compiled alone, and its
    kind read off the WHOLE error message rather than its tail.  Each
    was confirmed to fire at ITS OWN command, by reading the reported
    line back against the source.

    FIVE NEGATIVES OF THREE KINDS, kept lexically apart: three
    CONVERSION (1-3, each reporting "cannot unify" between two terms of
    one type), one TYPING (4, a plain mismatch with NO "cannot unify"
    and no universe clause -- it reports that [h] has type [RModHom ...]
    while a [LieHom] is expected), and one RESOLUTION (5, which reports
    "Cannot infer the implicit parameter Setoid of equiv ... (no type
    class instance found)" and is the only one whose failure is an
    instance search rather than a type error), plus a scope-free
    instrument check.  NO FORMABILITY (universe) negative is delivered,
    and that is not an oversight: this file declares no universe binder
    and inspects no constraint block, so there is nothing here whose
    universes could be measured. *)

(* Negative 1 -- CONVERSION.  The unit of the adjunction and the
   insertion agree POINTWISE on the nose ([uenv_unit_is_gen] above, and
   the control below), but the two underlying module homomorphisms are
   not the same record: the unit is [⌊id⌋], which composes
   [fmap[CommutatorFunctor K] id] with the insertion, and
   [rmod_hom_compose] rebuilds the [rm_map_smul] field. *)
Fail Example uenv_probe_unit_strict (K : CRng) (L : Lie K) :
  lie_hom (uenv_unit L) = lie_hom (uenv_insert L) := eq_refl.

Example uenv_probe_unit_ctrl (K : CRng) (L : Lie K)
  (v : carrier (cmon_setoid (lie_mod L))) :
  cmon_map (rm_hom (lie_hom (uenv_unit L))) v = uen_gen v := eq_refl.

Example uenv_probe_unit_equiv_ctrl (K : CRng) (L : Lie K) :
  uenv_unit L ≈ uenv_insert L := uenv_unit_is_insert L.

(* Negative 2 -- CONVERSION.  The counit is the extension of the
   identity Lie map only up to [≈]: it is [⌈id⌉], produced by
   [ump_universal_arrows], which Theory/Universal/Arrow.v closes with
   [Qed], so nothing about it reduces. *)
Fail Example uenv_probe_counit_strict (K : CRng) (A : AAlg K) :
  uenv_counit A = uenv_extend A (@id (Lie K) (fobj[CommutatorFunctor K] A))
  := eq_refl.

Example uenv_probe_counit_ctrl (K : CRng) (A : AAlg K) :
  uenv_counit A
    ≈ uenv_extend A (@id (Lie K) (fobj[CommutatorFunctor K] A))
  := uenv_counit_is_extend A.

(* Negative 3 -- CONVERSION.  The enveloping relation is a GENERATING
   EQUATION, not a computation rule: [uenv_eq] is an inductive relation
   and the two sides are distinct constructors of [UEnvTerm], so the
   identification fails even at closed [UT2] arguments where the bracket
   itself computes ([uenv_ut2_bracket_computes] above).  The controls
   are the [≈] form and an [eq_refl] that DOES hold in the same
   vocabulary, so the failure is located at the relation and not at the
   arguments. *)
Fail Example uenv_probe_bracket_strict :
  uenv_ut2_g ut2_e12
    = uen_add (uen_mul (uenv_ut2_g ut2_e11) (uenv_ut2_g ut2_e12))
              (uen_neg (uen_mul (uenv_ut2_g ut2_e12) (uenv_ut2_g ut2_e11)))
  := eq_refl.

Example uenv_probe_bracket_ctrl :
  uenv_eq (uenv_ut2_g ut2_e12)
          (uen_add (uen_mul (uenv_ut2_g ut2_e11) (uenv_ut2_g ut2_e12))
                   (uen_neg (uen_mul (uenv_ut2_g ut2_e12)
                                     (uenv_ut2_g ut2_e11))))
  := uenv_ut2_bracket_relation.

Example uenv_probe_gen_ctrl (x : ut2) :
  rig_map (`1 uenv_ut2) (uenv_ut2_g x) = x := eq_refl.

(* Negative 4 -- TYPING.  A bare module homomorphism does not extend:
   the evaluation's respectfulness proof consumes the bracket clause at
   the [uq_bracket] case and NOWHERE else, so preservation of the
   bracket is genuine data the extension needs, not a property
   recoverable from the module map.  The control supplies the clause and
   the same extension goes through. *)
Fail Definition uenv_probe_needs_bracket
  (K : CRng) (L : LieObject K) (A : AAlgObject K)
  (h : RModHom (lie_mod L) (AAlg_RMod A)) : UEnvAlg L ~{AAlg K}~> A :=
  uenv_extend A h.

Definition uenv_probe_bracket_hom_ctrl
  (K : CRng) (L : LieObject K) (A : AAlgObject K)
  (h : RModHom (lie_mod L) (AAlg_RMod A))
  (Hb : ∀ x y, cmon_map (rm_hom h) (lie_br L x y)
                 ≈ lie_br (lie_of_aalg A) (cmon_map (rm_hom h) x)
                                          (cmon_map (rm_hom h) y))
  : UEnvAlg L ~{AAlg K}~> A :=
  uenv_extend A (@Build_LieHom K L (lie_of_aalg A) h Hb).

(* Negative 5 -- RESOLUTION.  [uenv_Setoid] is deliberately NOT
   registered as an instance -- the convention Instance/Ab/Tensor.v,
   Instance/Rng/Polynomial.v and Instance/Vect/TensorAlgebra.v all
   follow, so that the [≈] of [UEnvRing] IS [uenv_eq] definitionally and
   Theory/Algebra/Rig.v's lemmas apply to it unchanged.  The price is
   that [≈] between two BARE terms does not resolve; read through the
   ring it does, and the control is that same statement.  This is the
   one negative here whose report is an INSTANCE failure rather than a
   type error. *)
Fail Definition uenv_probe_setoid_unregistered
  (K : CRng) (L : LieObject K) (s t : UEnvTerm L) : Type := s ≈ t.

Definition uenv_probe_setoid_ctrl (K : CRng) (L : LieObject K)
  (s t : carrier (rig_setoid (UEnvRing L))) : Type := s ≈ t.

(* Instrument check: a name that exists nowhere, so the [Fail]
   mechanism itself is exercised without reference to any constant
   declared here. *)
Fail Check uenv_probe_instrument_absent.
