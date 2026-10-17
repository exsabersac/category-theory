(** * The bimodule tensor-hom adjunction, and its parameter *)

(*
 Book:      Mac Lane, ibid., §IV.7 Theorem 3, printed pp. 101–102 —
 Book:      Mac Lane, ibid., §IV.1, printed pp. 79–80 — adjunctions in
 Book:      Riehl, "Category Theory in Context", Dover 2016, §4.4
 Book:      Riehl, ibid., §4.6 Corollary 4.6.10, printed p. 169 — for
 nLab:      https://ncatlab.org/nlab/show/tensor-hom+adjunction
 nLab:      https://ncatlab.org/nlab/show/bimodule
 Wikipedia: https://en.wikipedia.org/wiki/Tensor-hom_adjunction

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Parameter.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(** ** A. The balanced tensor of a right module and a left module *)

Section BalancedTensor.

Context {X : RingObject}.

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Local Notation XC := (carrier (rig_setoid (ring_rig X))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).
Local Notation MC := (carrier (cmon_setoid (rm_ab M))).

Example bal_scalars_agree :
  carrier (rig_setoid (ring_rig (Ring_op X)))
    = carrier (rig_setoid (ring_rig X)) := eq_refl.

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive bsum : Type :=
  | bs_gen  : NC → MC → bsum
  | bs_zero : bsum
  | bs_plus : bsum → bsum → bsum
  | bs_neg  : bsum → bsum.

(* The quotienting relation: Instance/Ab/Tensor.v's eleven constructors
   plus ONE balance rule, (n · x) ⊗ m ≈ n ⊗ (x · m).  Reflexivity is
   derived. *)
Inductive bs_eq : bsum → bsum → Prop :=
  | be_gen {n n' : NC} {m m' : MC} :
      n ≈ n' → m ≈ m' → bs_eq (bs_gen n m) (bs_gen n' m')
  | be_plus {s s' t t'} :
      bs_eq s s' → bs_eq t t' → bs_eq (bs_plus s t) (bs_plus s' t')
  | be_neg {s s'} : bs_eq s s' → bs_eq (bs_neg s) (bs_neg s')
  | be_assoc (s t u : bsum) :
      bs_eq (bs_plus (bs_plus s t) u) (bs_plus s (bs_plus t u))
  | be_comm (s t : bsum) : bs_eq (bs_plus s t) (bs_plus t s)
  | be_zero_l (s : bsum) : bs_eq (bs_plus bs_zero s) s
  | be_neg_l (s : bsum) : bs_eq (bs_plus (bs_neg s) s) bs_zero
  | be_add_l (n n' : NC) (m : MC) :
      bs_eq (bs_gen (cmon_plus (rm_ab N) n n') m)
            (bs_plus (bs_gen n m) (bs_gen n' m))
  | be_add_r (n : NC) (m m' : MC) :
      bs_eq (bs_gen n (cmon_plus (rm_ab M) m m'))
            (bs_plus (bs_gen n m) (bs_gen n m'))
  | be_balance (x : XC) (n : NC) (m : MC) :
      bs_eq (bs_gen (rm_smul N x n) m) (bs_gen n (rm_smul M x m))
  | be_sym {s t} : bs_eq s t → bs_eq t s
  | be_trans {s t u} : bs_eq s t → bs_eq t u → bs_eq s u.

Lemma bs_refl (s : bsum) : bs_eq s s.
Proof.
  induction s.
  - exact (be_gen (reflexivity _) (reflexivity _)).
  - exact (be_trans (be_sym (be_zero_l bs_zero)) (be_zero_l bs_zero)).
  - exact (be_plus IHs1 IHs2).
  - exact (be_neg IHs).
Qed.

Lemma bs_eq_Equivalence : Equivalence bs_eq.
Proof.
  constructor.
  - exact bs_refl.
  - exact (fun s t => be_sym).
  - exact (fun s t u => be_trans).
Qed.

Definition bs_Setoid : Setoid bsum := {|
  equiv        := bs_eq;
  setoid_equiv := bs_eq_Equivalence
|}.

(* The balanced tensor as an abelian group: every group law is a
   constructor of the relation. *)
Definition BalTensor : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := bsum; is_setoid := bs_Setoid |};
    cmon_zero := bs_zero;
    cmon_plus := bs_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => be_plus Hs Ht;
    cmon_plus_assoc := be_assoc;
    cmon_plus_comm := be_comm;
    cmon_plus_zero_l := be_zero_l;
    (* [bs_eq] IS a [Prop] relation, so it is its own [Prop] mirror. *)
    cmon_prop := @PropEquiv_of_relation _ bs_Setoid bs_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := bs_neg;
  ab_neg_respects := fun _ _ Hs => be_neg Hs;
  ab_neg_left := be_neg_l
|}.

(** ** Balanced biadditive maps and the universal property *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record BalBiadditive (A : AbObject) := {
  bal_map : NC → MC → carrier (cmon_setoid A);
  bal_respects : Proper (equiv ==> equiv ==> equiv) bal_map;
  bal_add_l (n n' : NC) (m : MC) :
    bal_map (cmon_plus (rm_ab N) n n') m
      ≈ cmon_plus A (bal_map n m) (bal_map n' m);
  bal_add_r (n : NC) (m m' : MC) :
    bal_map n (cmon_plus (rm_ab M) m m')
      ≈ cmon_plus A (bal_map n m) (bal_map n m');
  bal_balance (x : XC) (n : NC) (m : MC) :
    bal_map (rm_smul N x n) m ≈ bal_map n (rm_smul M x m)
}.

Arguments bal_map {A} _ _ _.
Arguments bal_respects {A} _.
Arguments bal_add_l {A} _ _ _ _.
Arguments bal_add_r {A} _ _ _ _.
Arguments bal_balance {A} _ _ _ _.

(* The universal balanced map: the generator former itself. *)
Definition bal_gen : BalBiadditive BalTensor :=
  @Build_BalBiadditive BalTensor bs_gen
    (fun _ _ Hn _ _ Hm => be_gen Hn Hm)
    be_add_l be_add_r be_balance.

(* The mediator: fold a formal sum through the target's operations.  It
   computes on constructors. *)
Fixpoint bal_med_fun {A : AbObject} (β : BalBiadditive A) (s : bsum) :
  carrier (cmon_setoid A) :=
  match s with
  | bs_gen n m  => bal_map β n m
  | bs_zero     => cmon_zero A
  | bs_plus s t => cmon_plus A (bal_med_fun β s) (bal_med_fun β t)
  | bs_neg s    => ab_neg A (bal_med_fun β s)
  end.

Lemma bal_med_respects {A : AbObject} (β : BalBiadditive A) (s t : bsum) :
  bs_eq s t → bal_med_fun β s ≈ bal_med_fun β t.
Proof.
  intro He.
  (*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  apply pequiv_to.
  induction He as
    [ n n' m m' Hn Hm
    | s s' t t' _ IH1 _ IH2
    | s s' _ IH
    | s t u | s t | s | s
    | n n' m | n m m' | x n m
    | s t _ IH
    | s t u _ IH1 _ IH2 ]; simpl.
  - apply pequiv_from; exact (bal_respects β _ _ Hn _ _ Hm).
  - apply pequiv_from.
    exact (cmon_plus_respects A _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from.
    exact (ab_neg_respects A _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from; exact (cmon_plus_assoc A _ _ _).
  - apply pequiv_from; exact (cmon_plus_comm A _ _).
  - apply pequiv_from; exact (cmon_plus_zero_l A _).
  - apply pequiv_from; exact (ab_neg_left A _).
  - apply pequiv_from; exact (bal_add_l β _ _ _).
  - apply pequiv_from; exact (bal_add_r β _ _ _).
  - apply pequiv_from; exact (bal_balance β _ _ _).
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

Program Definition bal_med {A : AbObject} (β : BalBiadditive A) :
  AbHom BalTensor A := {|
  cmon_map := {| morphism := bal_med_fun β |}
|}.
Next Obligation.
  intros A β s t He; exact (bal_med_respects β s t He).
Qed.
Next Obligation. intros A β; simpl; reflexivity. Qed.
Next Obligation. intros A β s t; simpl; reflexivity. Qed.

Example bal_med_gen {A : AbObject} (β : BalBiadditive A)
  (n : NC) (m : MC) :
  cmon_map (bal_med β) (bs_gen n m) = bal_map β n m := eq_refl.

(* Uniqueness in its consumable form: homomorphisms out of the balanced
   tensor that agree on generators agree everywhere.  The [bs_neg] case
   is Instance/Ab.v's [ab_map_neg]. *)
Lemma bal_hom_ext {A : AbObject} (f g : AbHom BalTensor A) :
  (∀ (n : NC) (m : MC),
      cmon_map f (bs_gen n m) ≈ cmon_map g (bs_gen n m)) →
  ∀ s : bsum, cmon_map f s ≈ cmon_map g s.
Proof.
  intros Hgen s; induction s as [n m| |s1 IHs1 s2 IHs2|s IHs].
  - exact (Hgen n m).
  - exact (transitivity (cmon_map_zero f)
             (symmetry (cmon_map_zero g))).
  - refine (transitivity (cmon_map_plus f s1 s2) _).
    refine (transitivity _ (symmetry (cmon_map_plus g s1 s2))).
    exact (cmon_plus_respects A _ _ IHs1 _ _ IHs2).
  - refine (transitivity (ab_map_neg f s) _).
    refine (transitivity _ (symmetry (ab_map_neg g s))).
    exact (ab_neg_respects A _ _ IHs).
Qed.

Lemma bal_med_unique {A : AbObject} (β : BalBiadditive A)
  (f : AbHom BalTensor A) :
  (∀ (n : NC) (m : MC),
      cmon_map f (bs_gen n m) ≈ bal_map β n m) →
  f ≈ bal_med β.
Proof.
  intros Hgen s.
  refine (bal_hom_ext f (bal_med β) _ s).
  intros n m; exact (Hgen n m).
Qed.

(* A generator with a zero coordinate is the zero of the tensor.  Both
   halves are needed downstream: the transposes of the adjunction are
   additive because of them. *)
Lemma bal_gen_zero_l (m : MC) :
  (bs_gen (cmon_zero (rm_ab N)) m : carrier (cmon_setoid BalTensor))
    ≈ cmon_zero BalTensor.
Proof.
  apply (ab_cancel_l BalTensor (bs_gen (cmon_zero (rm_ab N)) m)).
  exact (be_trans
           (be_trans
              (be_sym (be_add_l (cmon_zero (rm_ab N))
                                (cmon_zero (rm_ab N)) m))
              (be_gen (cmon_plus_zero_l (rm_ab N) (cmon_zero (rm_ab N)))
                      (reflexivity m)))
           (be_sym (cmon_plus_zero_r BalTensor
                      (bs_gen (cmon_zero (rm_ab N)) m)))).
Qed.

Lemma bal_gen_zero_r (n : NC) :
  (bs_gen n (cmon_zero (rm_ab M)) : carrier (cmon_setoid BalTensor))
    ≈ cmon_zero BalTensor.
Proof.
  apply (ab_cancel_l BalTensor (bs_gen n (cmon_zero (rm_ab M)))).
  exact (be_trans
           (be_trans
              (be_sym (be_add_r n (cmon_zero (rm_ab M))
                                  (cmon_zero (rm_ab M))))
              (be_gen (reflexivity n)
                      (cmon_plus_zero_l (rm_ab M) (cmon_zero (rm_ab M)))))
           (be_sym (cmon_plus_zero_r BalTensor
                      (bs_gen n (cmon_zero (rm_ab M)))))).
Qed.

End BalancedTensor.

Arguments bsum {X} N M.
Arguments bs_gen {X N M} n m.
Arguments bs_zero {X N M}.
Arguments bs_plus {X N M} s t.
Arguments bs_neg {X N M} s.
Arguments bs_eq {X N M} s t.
Arguments bs_refl {X N M} s.
Arguments be_gen {X N M n n' m m'} _ _.
Arguments be_plus {X N M s s' t t'} _ _.
Arguments be_neg {X N M s s'} _.
Arguments be_assoc {X N M} s t u.
Arguments be_comm {X N M} s t.
Arguments be_zero_l {X N M} s.
Arguments be_neg_l {X N M} s.
Arguments be_add_l {X N M} n n' m.
Arguments be_add_r {X N M} n m m'.
Arguments be_balance {X N M} x n m.
Arguments be_sym {X N M s t} _.
Arguments be_trans {X N M s t u} _ _.

#[export] Existing Instance bs_eq_Equivalence.
Arguments BalTensor {X} N M.
Arguments BalBiadditive {X} N M A.
Arguments bal_map {X N M A} _ _ _.
Arguments bal_respects {X N M A} _.
Arguments bal_add_l {X N M A} _ _ _ _.
Arguments bal_add_r {X N M A} _ _ _ _.
Arguments bal_balance {X N M A} _ _ _ _.
Arguments bal_gen {X N M}.
Arguments bal_med_fun {X N M A} β s.
Arguments bal_med {X N M A} β.
Arguments bal_med_gen {X N M A} β n m.
Arguments bal_hom_ext {X N M A} f g _ s.
Arguments bal_med_unique {X N M A} β f _.
Arguments bal_gen_zero_l {X} N M m.
Arguments bal_gen_zero_r {X} N M n.

(** ** B. Mac Lane part (a): − ⊗_R E and hom_S(E, −) *)

(** *** The Ab-enrichment of a module category *)

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rmod_hom_negate {R : RingObject} {M N : RModObject R}
        (f : RModHom M N) : RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros R M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition RMod_AbEnriched (R : RingObject) :
  AbEnriched (RMod R) := {|
  abenriched_preadditive := RMod_Preadditive R;
  abneg := fun M N => @rmod_hom_negate R M N
|}.
Next Obligation.
  intros R M N f g Hfg a; simpl.
  exact (ab_neg_respects N _ _ (Hfg a)).
Qed.
Next Obligation.
  intros R M N f a; simpl.
  exact (ab_neg_right N (cmon_map (rm_hom f) a)).
Qed.

Section BimoduleTensorHom.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

(** *** The right S-action on N ⊗_R E *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rt_bilin_act (N : RModObject (Ring_op R)) (s : SC) :
  BalBiadditive N (bm_left E) (BalTensor N (bm_left E)) := {|
  bal_map := fun n e => bs_gen n (bm_rsmul E e s)
|}.
Next Obligation.
  intros N s n n' Hn e e' He.
  exact (be_gen Hn (bm_rsmul_respects E e e' He s s (reflexivity s))).
Qed.
Next Obligation.
  intros N s n n' e; exact (be_add_l n n' (bm_rsmul E e s)).
Qed.
Next Obligation.
  intros N s n e e'.
  exact (be_trans
           (be_gen (reflexivity n) (bm_rsmul_distr_l E e e' s))
           (be_add_r n (bm_rsmul E e s) (bm_rsmul E e' s))).
Qed.
Next Obligation.
  intros N s r n e.
  exact (be_trans
           (be_balance r n (bm_rsmul E e s))
           (be_sym (be_gen (reflexivity n) (bm_compat E r e s)))).
Qed.

Definition rt_smul (N : RModObject (Ring_op R)) (s : SC) :
  AbHom (BalTensor N (bm_left E)) (BalTensor N (bm_left E)) :=
  bal_med (rt_bilin_act N s).

Definition rt_act (N : RModObject (Ring_op R)) (s : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  carrier (cmon_setoid (BalTensor N (bm_left E))) :=
  cmon_map (rt_smul N s) x.

Example rt_act_gen (N : RModObject (Ring_op R)) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  rt_act N s (bs_gen n e) = bs_gen n (bm_rsmul E e s) := eq_refl.

(** *** The four module laws, each by agreement on generators *)

Lemma rt_act_scalar (N : RModObject (Ring_op R)) (s s' : SC) :
  s ≈ s' → ∀ x, rt_act N s x ≈ rt_act N s' x.
Proof.
  intros Hs x.
  refine (bal_hom_ext (rt_smul N s) (rt_smul N s') _ x).
  intros n e.
  exact (be_gen (reflexivity n)
           (bm_rsmul_respects E e e (reflexivity e) s s' Hs)).
Qed.

Lemma rt_act_respects (N : RModObject (Ring_op R)) :
  Proper (equiv ==> equiv ==> equiv) (rt_act N).
Proof.
  intros s s' Hs x y Hxy.
  transitivity (rt_act N s y).
  - exact (proper_morphism (cmon_map (rt_smul N s)) x y Hxy).
  - exact (rt_act_scalar N s s' Hs y).
Qed.

Lemma rt_act_distr_r (N : RModObject (Ring_op R)) (s s' : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_add (ring_rig S) s s') x
    ≈ cmon_plus (BalTensor N (bm_left E)) (rt_act N s x) (rt_act N s' x).
Proof.
  refine (bal_hom_ext (rt_smul N (rig_add (ring_rig S) s s'))
            (ab_hom_add (rt_smul N s) (rt_smul N s')) _ x).
  intros n e.
  exact (be_trans
           (be_gen (reflexivity n) (bm_rsmul_distr_r E e s s'))
           (be_add_r n (bm_rsmul E e s) (bm_rsmul E e s'))).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rt_act_assoc (N : RModObject (Ring_op R)) (s s' : SC)
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_mul (ring_rig (Ring_op S)) s s') x
    ≈ rt_act N s (rt_act N s' x).
Proof.
  refine (bal_hom_ext (rt_smul N (rig_mul (ring_rig (Ring_op S)) s s'))
            (cmon_hom_compose (rt_smul N s) (rt_smul N s')) _ x).
  intros n e.
  exact (be_gen (reflexivity n) (bm_rsmul_assoc E e s' s)).
Qed.

Lemma rt_act_one (N : RModObject (Ring_op R))
  (x : carrier (cmon_setoid (BalTensor N (bm_left E)))) :
  rt_act N (rig_one (ring_rig S)) x ≈ x.
Proof.
  refine (bal_hom_ext (rt_smul N (rig_one (ring_rig S)))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e.
  exact (be_gen (reflexivity n) (bm_rsmul_one E e)).
Qed.

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RTensor (N : RModObject (Ring_op R)) :
  RModObject (Ring_op S) :=
  @Build_RModObject (Ring_op S)
    (BalTensor N (bm_left E))
    (rt_act N)
    (rt_act_respects N)
    (fun s x y => cmon_map_plus (rt_smul N s) x y)
    (rt_act_distr_r N)
    (rt_act_assoc N)
    (rt_act_one N).

Example rt_carrier (N : RModObject (Ring_op R)) :
  rm_ab (RTensor N) = BalTensor N (bm_left E) := eq_refl.

Example rt_zero (N : RModObject (Ring_op R)) :
  cmon_zero (rm_ab (RTensor N)) = bs_zero := eq_refl.

Example rt_plus (N : RModObject (Ring_op R))
  (x y : carrier (cmon_setoid (rm_ab (RTensor N)))) :
  cmon_plus (rm_ab (RTensor N)) x y = bs_plus x y := eq_refl.

Example rt_smul_gen (N : RModObject (Ring_op R)) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  rm_smul (RTensor N) s (bs_gen n e) = bs_gen n (bm_rsmul E e s)
  := eq_refl.

(** *** The arrow action, and the functor − ⊗_R E *)

Program Definition rt_map_bal {N N' : RModObject (Ring_op R)}
  (f : RModHom N N') :
  BalBiadditive N (bm_left E) (BalTensor N' (bm_left E)) := {|
  bal_map := fun n e => bs_gen (cmon_map (rm_hom f) n) e
|}.
Next Obligation.
  intros N N' f n n' Hn e e' He.
  exact (be_gen (proper_morphism (cmon_map (rm_hom f)) n n' Hn) He).
Qed.
Next Obligation.
  intros N N' f n n' e.
  exact (be_trans
           (be_gen (cmon_map_plus (rm_hom f) n n') (reflexivity e))
           (be_add_l (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom f) n') e)).
Qed.
Next Obligation.
  intros N N' f n e e'.
  exact (be_add_r (cmon_map (rm_hom f) n) e e').
Qed.
Next Obligation.
  intros N N' f r n e.
  exact (be_trans
           (be_gen (rm_map_smul f r n) (reflexivity e))
           (be_balance r (cmon_map (rm_hom f) n) e)).
Qed.

Definition rt_map_ab {N N' : RModObject (Ring_op R)} (f : RModHom N N') :
  AbHom (BalTensor N (bm_left E)) (BalTensor N' (bm_left E)) :=
  bal_med (rt_map_bal f).

Program Definition RTensorMap {N N' : RModObject (Ring_op R)}
  (f : N ~{ModR R}~> N') : RTensor N ~{ModR S}~> RTensor N' := {|
  rm_hom := rt_map_ab f
|}.
Next Obligation.
  intros N N' f s x.
  refine (bal_hom_ext (cmon_hom_compose (rt_map_ab f) (rt_smul N s))
            (cmon_hom_compose (rt_smul N' s) (rt_map_ab f)) _ x).
  intros n e; reflexivity.
Qed.

Program Definition TensorWith : ModR R ⟶ ModR S := {|
  fobj := RTensor;
  fmap := @RTensorMap
|}.
Next Obligation.
  intros N N' f g Hfg x.
  refine (bal_hom_ext (rt_map_ab f) (rt_map_ab g) _ x).
  intros n e.
  exact (be_gen (Hfg n) (reflexivity e)).
Qed.
Next Obligation.
  intros N x.
  refine (bal_hom_ext (rt_map_ab (@id (ModR R) N))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e; reflexivity.
Qed.
Next Obligation.
  intros N N' N'' f g x.
  refine (bal_hom_ext (rt_map_ab (f ∘ g))
            (cmon_hom_compose (rt_map_ab f) (rt_map_ab g)) _ x).
  intros n e; reflexivity.
Qed.

Example tw_fobj (N : RModObject (Ring_op R)) :
  fobj[TensorWith] N = RTensor N := eq_refl.

Example tw_fmap_gen {N N' : RModObject (Ring_op R)}
  (f : N ~{ModR R}~> N') (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (fmap[TensorWith] f)) (bs_gen n e)
    = bs_gen (cmon_map (rm_hom f) n) e := eq_refl.

(** *** hom_S(E, M) and its right R-action *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hs_group (M : RModObject (Ring_op S)) : AbObject :=
  hom_ab (RMod_AbEnriched (Ring_op S)) EE M.

Example hs_group_carrier (M : RModObject (Ring_op S)) :
  carrier (cmon_setoid (hs_group M)) = (EE ~{ModR S}~> M) := eq_refl.

Example hs_group_plus (M : RModObject (Ring_op S)) :
  cmon_plus (hs_group M) = @rmod_hom_add (Ring_op S) EE M := eq_refl.

Example hs_group_zero (M : RModObject (Ring_op S)) :
  cmon_zero (hs_group M) = @rmod_hom_zero (Ring_op S) EE M := eq_refl.

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition hs_act (M : RModObject (Ring_op S)) (r : RC)
  (f : EE ~{ModR S}~> M) : EE ~{ModR S}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom f) (rm_smul (bm_left E) r e) |} |}
|}.
Next Obligation.
  intros M r f e e' He.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_respects (bm_left E) r r (reflexivity r) e e' He)).
Qed.
Next Obligation.
  intros M r f; simpl.
  transitivity (cmon_map (rm_hom f) (cmon_zero (rm_ab (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_zero_r (bm_left E) r)).
  - exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros M r f e e'; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (rm_smul (bm_left E) r e)
                     (rm_smul (bm_left E) r e'))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_distr_l (bm_left E) r e e')).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.
Next Obligation.
  (* [rm_map_smul] for the translated map: the ONLY use of [bm_compat]
     in this block, followed by [f]'s own linearity. *)
  intros M r f s e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (bm_rsmul E (rm_smul (bm_left E) r e) s)).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (symmetry (bm_compat E r e s))).
  - exact (rm_map_smul f s (rm_smul (bm_left E) r e)).
Qed.

Example hs_act_at (M : RModObject (Ring_op S)) (r : RC)
  (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (hs_act M r f)) e
    = cmon_map (rm_hom f) (rm_smul (bm_left E) r e) := eq_refl.

Lemma hs_act_respects (M : RModObject (Ring_op S)) :
  Proper (equiv ==> equiv ==> equiv) (hs_act M).
Proof.
  intros r r' Hr f g Hfg e; simpl.
  transitivity (cmon_map (rm_hom f) (rm_smul (bm_left E) r' e)).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_respects (bm_left E) r r' Hr e e (reflexivity e))).
  - exact (Hfg _).
Qed.

Lemma hs_act_distr_l (M : RModObject (Ring_op S)) (r : RC)
  (f g : EE ~{ModR S}~> M) :
  hs_act M r (cmon_plus (hs_group M) f g)
    ≈ cmon_plus (hs_group M) (hs_act M r f) (hs_act M r g).
Proof. intro e; reflexivity. Qed.

Lemma hs_act_distr_r (M : RModObject (Ring_op S)) (r r' : RC)
  (f : EE ~{ModR S}~> M) :
  hs_act M (rig_add (ring_rig R) r r') f
    ≈ cmon_plus (hs_group M) (hs_act M r f) (hs_act M r' f).
Proof.
  intro e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (rm_smul (bm_left E) r e)
                     (rm_smul (bm_left E) r' e))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_distr_r (bm_left E) r r' e)).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.

(* Associativity ONLY: at e the two sides are f ((r' r) · e) and
   f (r' · (r · e)), and [rm_smul_assoc] of E's LEFT module is all that
   is consumed. *)
Lemma hs_act_assoc (M : RModObject (Ring_op S)) (r r' : RC)
  (f : EE ~{ModR S}~> M) :
  hs_act M (rig_mul (ring_rig (Ring_op R)) r r') f
    ≈ hs_act M r (hs_act M r' f).
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_assoc (bm_left E) r' r e)).
Qed.

Lemma hs_act_one (M : RModObject (Ring_op S)) (f : EE ~{ModR S}~> M) :
  hs_act M (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (rm_smul_one (bm_left E) e)).
Qed.

Definition HomSObj (M : RModObject (Ring_op S)) :
  RModObject (Ring_op R) :=
  @Build_RModObject (Ring_op R)
    (hs_group M)
    (hs_act M)
    (hs_act_respects M)
    (hs_act_distr_l M)
    (hs_act_distr_r M)
    (hs_act_assoc M)
    (hs_act_one M).

(** *** The arrow action, and the functor hom_S(E, −) *)

Program Definition hs_map_ab {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') : AbHom (hs_group M) (hs_group M') := {|
  cmon_map := {| morphism := fun f =>
    (rmod_hom_compose g f : EE ~{ModR S}~> M') |}
|}.
Next Obligation.
  intros M M' g f f' Hf e; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf e)).
Qed.
Next Obligation.
  intros M M' g e; simpl.
  exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' e; simpl.
  exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition HomSMap {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') : HomSObj M ~{ModR R}~> HomSObj M' := {|
  rm_hom := hs_map_ab g
|}.
Next Obligation. intros M M' g r f e; reflexivity. Qed.

Program Definition HomS : ModR S ⟶ ModR R := {|
  fobj := HomSObj;
  fmap := @HomSMap
|}.
Next Obligation.
  intros M M' g g' Hg f e; simpl.
  exact (Hg _).
Qed.
Next Obligation. intros M f e; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f e; reflexivity. Qed.

Example hs_fobj (M : RModObject (Ring_op S)) :
  fobj[HomS] M = HomSObj M := eq_refl.

Example hs_fmap_at {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (fmap[HomS] g)) f)) e
    = cmon_map (rm_hom g) (cmon_map (rm_hom f) e) := eq_refl.

(** *** The two transposes and the adjunction *)

Program Definition bth_to_inner {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) : EE ~{ModR S}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom g) (bs_gen n e) |} |}
|}.
Next Obligation.
  intros N M g n e e' He.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (be_gen (reflexivity n) He)).
Qed.
Next Obligation.
  intros N M g n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r N (bm_left E) n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n e e'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (bs_gen n e) (bs_gen n e'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (be_add_r n e e')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* n ⊗ (e ⊲ s) IS s ·[RTensor N] (n ⊗ e) on the nose, so this is
     [g]'s own linearity with no rewriting. *)
  intros N M g n s e.
  exact (rm_map_smul g s (bs_gen n e)).
Qed.

Program Definition bth_to_ab {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M) :
  AbHom (rm_ab N) (hs_group M) := {|
  cmon_map := {| morphism := fun n => bth_to_inner g n |}
|}.
Next Obligation.
  intros N M g n n' Hn e; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (be_gen Hn (reflexivity e))).
Qed.
Next Obligation.
  intros N M g e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l N (bm_left E) e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n n' e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (bs_gen n e) (bs_gen n' e))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (be_add_l n n' e)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

(* The forward transpose is R-linear BECAUSE of the balance rule: at e
   the two sides are g ((r · n) ⊗ e) and g (n ⊗ (r · e)). *)
Program Definition bth_to {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M) :
  N ~{ModR R}~> HomSObj M := {|
  rm_hom := bth_to_ab g
|}.
Next Obligation.
  intros N M g r n e; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (@be_balance R N (bm_left E) r n e)).
Qed.

Program Definition bth_from_bal {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M) :
  BalBiadditive N (bm_left E) (rm_ab M) := {|
  bal_map := fun n e =>
    cmon_map (rm_hom (cmon_map (rm_hom h) n)) e
|}.
Next Obligation.
  intros N M h n n' Hn e e' He.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom h) n)) e').
  - exact (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom h) n)))
             e e' He).
  - exact (proper_morphism (cmon_map (rm_hom h)) n n' Hn e').
Qed.
Next Obligation.
  intros N M h n n' e.
  exact (cmon_map_plus (rm_hom h) n n' e).
Qed.
Next Obligation.
  intros N M h n e e'.
  exact (cmon_map_plus (rm_hom (cmon_map (rm_hom h) n)) e e').
Qed.
Next Obligation.
  (* Balance is [h]'s own R-linearity, read at e: the action on
     hom_S(E, M) is translation, so (r · h n) e IS (h n) (r · e). *)
  intros N M h r n e.
  exact (rm_map_smul h r n e).
Qed.

(* Multiplication by a scalar, as a homomorphism of the underlying
   group; the Instance/Mod/BaseChange.v idiom. *)
Program Definition bth_lmul (M : RModObject (Ring_op S)) (s : SC) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M s m |}
|}.
Next Obligation.
  intros M s m m' Hm.
  exact (rm_smul_respects M s s (reflexivity s) m m' Hm).
Qed.
Next Obligation. intros M s; simpl; exact (rm_smul_zero_r M s). Qed.
Next Obligation.
  intros M s m m'; simpl; exact (rm_smul_distr_l M s m m').
Qed.

Program Definition bth_from {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M) :
  RTensor N ~{ModR S}~> M := {|
  rm_hom := bal_med (bth_from_bal h)
|}.
Next Obligation.
  intros N M h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (bth_from_bal h)) (rt_smul N s))
            (cmon_hom_compose (bth_lmul M s)
                              (bal_med (bth_from_bal h))) _ x).
  intros n e.
  exact (rm_map_smul (cmon_map (rm_hom h) n) s e).
Qed.

Example bth_to_at {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (g : RTensor N ~{ModR S}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (bth_to g)) n)) e
    = cmon_map (rm_hom g) (bs_gen n e) := eq_refl.

Example bth_from_at {N : RModObject (Ring_op R)}
  {M : RModObject (Ring_op S)} (h : N ~{ModR R}~> HomSObj M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (bth_from h)) (bs_gen n e)
    = cmon_map (rm_hom (cmon_map (rm_hom h) n)) e := eq_refl.

Program Definition bth_adj_to (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  {| carrier := RTensor N ~{ModR S}~> M;
     is_setoid := @homset (ModR S) (RTensor N) M |}
    ~{Sets}~>
  {| carrier := N ~{ModR R}~> HomSObj M;
     is_setoid := @homset (ModR R) N (HomSObj M) |} := {|
  morphism := fun g => bth_to g
|}.
Next Obligation. intros N M g g' Hg n e; exact (Hg _). Qed.

Program Definition bth_adj_from (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  {| carrier := N ~{ModR R}~> HomSObj M;
     is_setoid := @homset (ModR R) N (HomSObj M) |}
    ~{Sets}~>
  {| carrier := RTensor N ~{ModR S}~> M;
     is_setoid := @homset (ModR S) (RTensor N) M |} := {|
  morphism := fun h => bth_from h
|}.
Next Obligation.
  intros N M h h' Hh x.
  refine (bal_hom_ext (bal_med (bth_from_bal h))
                      (bal_med (bth_from_bal h')) _ x).
  intros n e; exact (Hh n e).
Qed.

(* Both round trips close by [reflexivity]: the forward transpose reads
   a generator and the backward one writes one, so nothing residual is
   left behind on either side. *)
Program Definition bth_adj (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) :
  @Isomorphism Sets
    {| carrier := RTensor N ~{ModR S}~> M;
       is_setoid := @homset (ModR S) (RTensor N) M |}
    {| carrier := N ~{ModR R}~> HomSObj M;
       is_setoid := @homset (ModR R) N (HomSObj M) |} := {|
  to   := bth_adj_to N M;
  from := bth_adj_from N M
|}.
Next Obligation. intros N M h n e; reflexivity. Qed.
Next Obligation.
  intros N M g x.
  refine (bal_hom_ext (bal_med (bth_from_bal (bth_to g)))
                      (rm_hom g) _ x).
  intros n e; reflexivity.
Qed.

(* Mac Lane part (a).  Both remaining naturality obligations close by
   [reflexivity]. *)
Definition bimodule_tensor_hom_adjunction : TensorWith ⊣ HomS.
Proof.
  unshelve eapply (@Build_Adjunction' (ModR S) (ModR R) TensorWith
                     HomS bth_adj).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

(** *** Unit and counit *)

Definition bth_unit (N : RModObject (Ring_op R)) :
  N ~{ModR R}~> HomSObj (RTensor N) :=
  @unit (ModR S) (ModR R) TensorWith HomS
    bimodule_tensor_hom_adjunction N.

Definition bth_counit (M : RModObject (Ring_op S)) :
  RTensor (HomSObj M) ~{ModR S}~> M :=
  @counit (ModR S) (ModR R) TensorWith HomS
    bimodule_tensor_hom_adjunction M.

(* THE REVIEWER CHECK.  The unit IS n ↦ (e ↦ n ⊗ e) and the counit IS
   f ⊗ e ↦ f e, both on the nose. *)
Example bth_unit_is_gen (N : RModObject (Ring_op R))
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (bth_unit N)) n)) e
    = bs_gen n e := eq_refl.

Example bth_counit_is_eval (M : RModObject (Ring_op S))
  (f : EE ~{ModR S}~> M) (e : EC) :
  cmon_map (rm_hom (bth_counit M))
      (@bs_gen R (HomSObj M) (bm_left E) f e)
    = cmon_map (rm_hom f) e := eq_refl.

Example bth_adj_to_is_bth_to (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) (g : RTensor N ~{ModR S}~> M) :
  to (@adj (ModR S) (ModR R) TensorWith HomS
        bimodule_tensor_hom_adjunction N M) g = bth_to g := eq_refl.

Example bth_adj_from_is_bth_from (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op S)) (h : N ~{ModR R}~> HomSObj M) :
  from (@adj (ModR S) (ModR R) TensorWith HomS
          bimodule_tensor_hom_adjunction N M) h = bth_from h := eq_refl.

End BimoduleTensorHom.

(** ** C. The category of bimodules, the bifunctor, and Theorem 3 *)

Section BimoduleCategory.

Context {R S : RingObject}.

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record BimodHom (E E' : Bimodule R S) := {
  bh_hom :> RModHom (bm_left E) (bm_left E');

  bh_right : ∀ m s,
    cmon_map (rm_hom bh_hom) (bm_rsmul E m s)
      ≈ bm_rsmul E' (cmon_map (rm_hom bh_hom) m) s
}.

Arguments bh_hom {E E'} _.
Arguments bh_right {E E'} _ _ _.

(* The hom-setoid: two bimodule maps agree when their underlying maps
   agree pointwise, which is Instance/Mod.v's [RModHom_Setoid] one
   field further in.  Neither action plays a part. *)
#[export]
Program Instance BimodHom_Setoid {E E' : Bimodule R S} :
  Setoid (BimodHom E E') := {|
  equiv := fun f g => ∀ e,
    cmon_map (rm_hom (bh_hom f)) e ≈ cmon_map (rm_hom (bh_hom g)) e
|}.
Next Obligation.
  intros E E'.
  constructor.
  - intros f e; reflexivity.
  - intros f g Hfg e; symmetry; apply Hfg.
  - intros f g h Hfg Hgh e.
    transitivity (cmon_map (rm_hom (bh_hom g)) e).
    + apply Hfg.
    + apply Hgh.
Qed.

Program Definition bimod_hom_id {E : Bimodule R S} : BimodHom E E := {|
  bh_hom := @rmod_hom_id R (bm_left E)
|}.
Next Obligation. intros E m s; simpl; reflexivity. Qed.

Program Definition bimod_hom_compose {E E' E'' : Bimodule R S}
        (f : BimodHom E' E'') (g : BimodHom E E') : BimodHom E E'' := {|
  bh_hom := rmod_hom_compose (bh_hom f) (bh_hom g)
|}.
Next Obligation.
  intros E E' E'' f g m s; simpl.
  unfold Basics.compose.
  transitivity (cmon_map (rm_hom (bh_hom f))
                  (bm_rsmul E' (cmon_map (rm_hom (bh_hom g)) m) s)).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom f))) _ _
             (bh_right g m s)).
  - exact (bh_right f (cmon_map (rm_hom (bh_hom g)) m) s).
Qed.

Lemma bimod_hom_compose_respects {E E' E'' : Bimodule R S} :
  Proper (equiv ==> equiv ==> equiv) (@bimod_hom_compose E E' E'').
Proof.
  intros f f' Hf g g' Hg e; simpl.
  unfold Basics.compose.
  transitivity (cmon_map (rm_hom (bh_hom f))
                  (cmon_map (rm_hom (bh_hom g')) e)).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom f))) _ _ (Hg e)).
  - exact (Hf _).
Qed.

Program Definition BimodCat : Category := {|
  obj     := Bimodule R S;
  hom     := BimodHom;
  homset  := fun E E' => @BimodHom_Setoid E E';
  id      := fun E => @bimod_hom_id E;
  compose := fun E E' E'' f g => @bimod_hom_compose E E' E'' f g;

  compose_respects := fun E E' E'' => @bimod_hom_compose_respects E E' E''
|}.
Next Obligation. intros E E' f e; simpl; reflexivity. Qed.
Next Obligation. intros E E' f e; simpl; reflexivity. Qed.
Next Obligation. intros E E' E'' E''' f g h e; simpl; reflexivity. Qed.
Next Obligation. intros E E' E'' E''' f g h e; simpl; reflexivity. Qed.

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition bimod_hom_right {E E' : Bimodule R S}
  (h : BimodHom E E') :
  bimodule_right_RMod E ~{ModR S}~> bimodule_right_RMod E' := {|
  rm_hom := rm_hom (bh_hom h)
|}.
Next Obligation. intros E E' h s m; exact (bh_right h m s). Qed.

Example bimodcat_hom (E E' : Bimodule R S) :
  (E ~{BimodCat}~> E') = BimodHom E E' := eq_refl.

Example bimodcat_id_map (E : Bimodule R S)
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  cmon_map (rm_hom (bh_hom (@id BimodCat E))) e = e := eq_refl.

(** *** The tensor as a bifunctor of both variables *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition bt_map_bal {N N' : RModObject (Ring_op R)}
  {E E' : Bimodule R S} (f : N ~{ModR R}~> N') (h : E ~{BimodCat}~> E') :
  BalBiadditive N (bm_left E) (BalTensor N' (bm_left E')) := {|
  bal_map := fun n e =>
    bs_gen (cmon_map (rm_hom f) n) (cmon_map (rm_hom (bh_hom h)) e)
|}.
Next Obligation.
  intros N N' E E' f h n n' Hn e e' He.
  exact (be_gen (proper_morphism (cmon_map (rm_hom f)) n n' Hn)
                (proper_morphism (cmon_map (rm_hom (bh_hom h))) e e' He)).
Qed.
Next Obligation.
  intros N N' E E' f h n n' e.
  exact (be_trans
           (be_gen (cmon_map_plus (rm_hom f) n n') (reflexivity _))
           (be_add_l (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom f) n')
                     (cmon_map (rm_hom (bh_hom h)) e))).
Qed.
Next Obligation.
  intros N N' E E' f h n e e'.
  exact (be_trans
           (be_gen (reflexivity _)
                   (cmon_map_plus (rm_hom (bh_hom h)) e e'))
           (be_add_r (cmon_map (rm_hom f) n)
                     (cmon_map (rm_hom (bh_hom h)) e)
                     (cmon_map (rm_hom (bh_hom h)) e'))).
Qed.
Next Obligation.
  (* The balance clause spends [f]'s linearity and then [h]'s. *)
  intros N N' E E' f h r n e.
  exact (be_trans
           (be_trans
              (be_gen (rm_map_smul f r n) (reflexivity _))
              (@be_balance R N' (bm_left E') r
                 (cmon_map (rm_hom f) n)
                 (cmon_map (rm_hom (bh_hom h)) e)))
           (be_gen (reflexivity _)
                   (symmetry (rm_map_smul (bh_hom h) r e)))).
Qed.

Program Definition BimodTensorMap {N N' : RModObject (Ring_op R)}
  {E E' : Bimodule R S} (f : N ~{ModR R}~> N') (h : E ~{BimodCat}~> E') :
  RTensor E N ~{ModR S}~> RTensor E' N' := {|
  rm_hom := bal_med (bt_map_bal f h)
|}.
Next Obligation.
  intros N N' E E' f h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (bt_map_bal f h)) (rt_smul E N s))
            (cmon_hom_compose (rt_smul E' N' s)
                              (bal_med (bt_map_bal f h))) _ x).
  intros n e; simpl.
  exact (be_gen (reflexivity _) (bh_right h e s)).
Qed.

Program Definition BimodTensor : ModR R ∏ BimodCat ⟶ ModR S := {|
  fobj := fun p => RTensor (snd p) (fst p);
  fmap := fun p q fh => BimodTensorMap (fst fh) (snd fh)
|}.
Next Obligation.
  intros [N E] [N' E'] [f h] [f' h'] [Hf Hh] x; simpl in *.
  refine (bal_hom_ext (bal_med (bt_map_bal f h))
                      (bal_med (bt_map_bal f' h')) _ x).
  intros n e.
  exact (be_gen (Hf n) (Hh e)).
Qed.
Next Obligation.
  intros [N E] x; simpl.
  refine (bal_hom_ext
            (bal_med (bt_map_bal (@id (ModR R) N) (@id BimodCat E)))
            (@cmon_hom_id (BalTensor N (bm_left E))) _ x).
  intros n e; reflexivity.
Qed.
Next Obligation.
  intros [N E] [N' E'] [N'' E''] [f h] [f' h'] x; simpl in *.
  refine (bal_hom_ext
            (bal_med (bt_map_bal
                        (rmod_hom_compose f f') (bimod_hom_compose h h')))
            (cmon_hom_compose (bal_med (bt_map_bal f h))
                              (bal_med (bt_map_bal f' h'))) _ x).
  intros n e; reflexivity.
Qed.

Example bimod_tensor_obj (N : RModObject (Ring_op R))
  (E : Bimodule R S) :
  fobj[BimodTensor] (N, E) = RTensor E N := eq_refl.

Example bimod_tensor_partial_obj (E : Bimodule R S)
  (N : RModObject (Ring_op R)) :
  fobj[Partial_l BimodTensor E] N = RTensor E N := eq_refl.

Example bimod_tensor_partial_gen (E : Bimodule R S)
  {N N' : RModObject (Ring_op R)} (f : N ~{ModR R}~> N')
  (n : carrier (cmon_setoid (rm_ab N)))
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  cmon_map (rm_hom (fmap[Partial_l BimodTensor E] f)) (bs_gen n e)
    = bs_gen (cmon_map (rm_hom f) n) e := eq_refl.

(** *** Mac Lane part (b): the adjunction with a parameter *)

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition bt_partial_adj (E : Bimodule R S) :
  Partial_l BimodTensor E ⊣ HomS E.
Proof.
  unshelve eapply (@Build_Adjunction' (ModR S) (ModR R)
                     (Partial_l BimodTensor E) (HomS E) (bth_adj E)).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

Definition bimodule_parametrized_adjunction :
  ParametrizedAdjunction BimodTensor :=
  @Build_ParametrizedAdjunction (ModR R) BimodCat (ModR S)
    BimodTensor (@HomS R S) bt_partial_adj.

Example bimod_pa_right (E : Bimodule R S) :
  pa_right bimodule_parametrized_adjunction E = HomS E := eq_refl.

Example bimod_pa_adj (E : Bimodule R S) :
  pa_adj bimodule_parametrized_adjunction E = bt_partial_adj E := eq_refl.

(* Mac Lane's G : P^op × A → X.  Its arrow action in the BIMODULE
   variable is #396's [pa_param_mate] and is therefore FORCED by
   Theorem 3; nothing here re-proves functoriality in E. *)
Definition bimodule_hom_bifunctor :
  (BimodCat)^op ∏ ModR S ⟶ ModR R :=
  parametrized_right_adjoint_bifunctor bimodule_parametrized_adjunction.

Example bimod_hom_bifunctor_obj (E : Bimodule R S)
  (M : RModObject (Ring_op S)) :
  fobj[bimodule_hom_bifunctor] (E, M) = HomSObj E M := eq_refl.

End BimoduleCategory.

Arguments BimodHom {R S} E E'.

(** ** D. Part (c): the tensor of two bimodules, and the composite *)

(* Two readings of the generator former as a homomorphism of ONE of its
   two variables.  They belong beside §A and are declared here only
   because §D is their first consumer. *)

Section BalancedGenerators.

Context {X : RingObject}.
Context (N : RModObject (Ring_op X)).
Context (M : RModObject X).

Program Definition bal_gen_right
  (n : carrier (cmon_setoid (rm_ab N))) :
  AbHom (rm_ab M) (BalTensor N M) := {|
  cmon_map := {| morphism := fun m => bs_gen n m |}
|}.
Next Obligation.
  intros n m m' Hm; exact (be_gen (reflexivity n) Hm).
Qed.
Next Obligation. intros n; exact (bal_gen_zero_r N M n). Qed.
Next Obligation. intros n m m'; exact (be_add_r n m m'). Qed.

Program Definition bal_gen_left
  (m : carrier (cmon_setoid (rm_ab M))) :
  AbHom (rm_ab N) (BalTensor N M) := {|
  cmon_map := {| morphism := fun n => bs_gen n m |}
|}.
Next Obligation.
  intros m n n' Hn; exact (be_gen Hn (reflexivity m)).
Qed.
Next Obligation. intros m; exact (bal_gen_zero_l N M m). Qed.
Next Obligation. intros m n n'; exact (be_add_l n n' m). Qed.

End BalancedGenerators.

Arguments bal_gen_right {X} N M n.
Arguments bal_gen_left {X} N M m.

(** *** The left R-action on a balanced tensor over S *)

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BimoduleLeftTensor.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

Program Definition lt_bilin_act (N : RModObject S) (r : RC) :
  BalBiadditive EE N (BalTensor EE N) := {|
  bal_map := fun e n => bs_gen (rm_smul (bm_left E) r e) n
|}.
Next Obligation.
  intros N r e e' He n n' Hn.
  refine (be_gen _ Hn).
  exact (rm_smul_respects (bm_left E) r r (reflexivity r) e e' He).
Qed.
Next Obligation.
  intros N r e e' n.
  refine (be_trans _ (@be_add_l S (bimodule_right_RMod E) N
                        (rm_smul (bm_left E) r e)
                        (rm_smul (bm_left E) r e') n)).
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_distr_l (bm_left E) r e e').
Qed.
Next Obligation.
  intros N r e n n'.
  exact (@be_add_r S (bimodule_right_RMod E) N
           (rm_smul (bm_left E) r e) n n').
Qed.
Next Obligation.
  intros N r x e n.
  refine (be_trans _ (@be_balance S (bimodule_right_RMod E) N x
                        (rm_smul (bm_left E) r e) n)).
  refine (be_gen _ (reflexivity n)).
  exact (symmetry (bm_compat E r e x)).
Qed.

Definition lt_smul (N : RModObject S) (r : RC) :
  AbHom (BalTensor EE N) (BalTensor EE N) :=
  bal_med (lt_bilin_act N r).

Definition lt_act (N : RModObject S) (r : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  carrier (cmon_setoid (BalTensor EE N)) :=
  cmon_map (lt_smul N r) x.

Example lt_act_gen (N : RModObject S) (r : RC) (e : EC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  lt_act N r (@bs_gen S (bimodule_right_RMod E) N e n)
    = @bs_gen S (bimodule_right_RMod E) N
        (rm_smul (bm_left E) r e) n := eq_refl.

Lemma lt_act_scalar (N : RModObject S) (r r' : RC) :
  r ≈ r' → ∀ x, lt_act N r x ≈ lt_act N r' x.
Proof.
  intros Hr x.
  refine (bal_hom_ext (lt_smul N r) (lt_smul N r') _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_respects (bm_left E) r r' Hr e e (reflexivity e)).
Qed.

Lemma lt_act_respects (N : RModObject S) :
  Proper (equiv ==> equiv ==> equiv) (lt_act N).
Proof.
  intros r r' Hr x y Hxy.
  transitivity (lt_act N r y).
  - exact (proper_morphism (cmon_map (lt_smul N r)) x y Hxy).
  - exact (lt_act_scalar N r r' Hr y).
Qed.

Lemma lt_act_distr_r (N : RModObject S) (r r' : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_add (ring_rig R) r r') x
    ≈ cmon_plus (BalTensor EE N) (lt_act N r x) (lt_act N r' x).
Proof.
  refine (bal_hom_ext (lt_smul N (rig_add (ring_rig R) r r'))
            (ab_hom_add (lt_smul N r) (lt_smul N r')) _ x).
  intros e n.
  refine (be_trans _ (@be_add_l S (bimodule_right_RMod E) N
                        (rm_smul (bm_left E) r e)
                        (rm_smul (bm_left E) r' e) n)).
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_distr_r (bm_left E) r r' e).
Qed.

Lemma lt_act_assoc (N : RModObject S) (r r' : RC)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_mul (ring_rig R) r r') x ≈ lt_act N r (lt_act N r' x).
Proof.
  refine (bal_hom_ext (lt_smul N (rig_mul (ring_rig R) r r'))
            (cmon_hom_compose (lt_smul N r) (lt_smul N r')) _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_assoc (bm_left E) r r' e).
Qed.

Lemma lt_act_one (N : RModObject S)
  (x : carrier (cmon_setoid (BalTensor EE N))) :
  lt_act N (rig_one (ring_rig R)) x ≈ x.
Proof.
  refine (bal_hom_ext (lt_smul N (rig_one (ring_rig R)))
            (@cmon_hom_id (BalTensor EE N)) _ x).
  intros e n.
  refine (be_gen _ (reflexivity n)).
  exact (rm_smul_one (bm_left E) e).
Qed.

(* E ⊗_S N as a LEFT R-module. *)
Definition LTensor (N : RModObject S) : RModObject R :=
  @Build_RModObject R
    (BalTensor EE N)
    (lt_act N)
    (lt_act_respects N)
    (fun r x y => cmon_map_plus (lt_smul N r) x y)
    (lt_act_distr_r N)
    (lt_act_assoc N)
    (lt_act_one N).

Example lt_carrier (N : RModObject S) :
  rm_ab (LTensor N) = BalTensor EE N := eq_refl.

Example lt_smul_gen (N : RModObject S) (r : RC) (e : EC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  rm_smul (LTensor N) r (@bs_gen S (bimodule_right_RMod E) N e n)
    = @bs_gen S (bimodule_right_RMod E) N
        (rm_smul (bm_left E) r e) n := eq_refl.

End BimoduleLeftTensor.

Arguments lt_bilin_act {R S} E N r.
Arguments lt_smul {R S} E N r.
Arguments lt_act {R S} E N r x.
Arguments LTensor {R S} E N.

(** *** The tensor of two bimodules *)

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BimoduleTensorBimodule.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation TC := (carrier (rig_setoid (ring_rig T))).
Local Notation EE := (bimodule_right_RMod E).
Local Notation BTC := (BalTensor EE (bm_left E1)).

Definition btb_left : RModObject R := LTensor E (bm_left E1).
Definition btb_right : RModObject (Ring_op T) := RTensor E1 EE.

Example btb_carriers_agree : rm_ab btb_left = rm_ab btb_right := eq_refl.

Lemma btb_rsmul_respects :
  Proper (equiv ==> equiv ==> equiv)
    (fun (x : carrier (cmon_setoid BTC)) (t : TC) =>
       rm_smul btb_right t x).
Proof.
  intros x y Hxy t t' Ht.
  exact (rm_smul_respects btb_right t t' Ht x y Hxy).
Qed.

(* The ONE clause with content, and it has none: [bal_hom_ext] reduces it
   to a reflexivity on generators. *)
Lemma btb_compat (r : RC) (x : carrier (cmon_setoid BTC)) (t : TC) :
  rm_smul btb_right t (rm_smul btb_left r x)
    ≈ rm_smul btb_left r (rm_smul btb_right t x).
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (rt_smul E1 EE t)
                              (lt_smul E (bm_left E1) r))
            (cmon_hom_compose (lt_smul E (bm_left E1) r)
                              (rt_smul E1 EE t)) _ x).
  intros e e1; reflexivity.
Qed.

Definition BimodTensorBimod : Bimodule R T :=
  @Build_Bimodule R T btb_left
    (fun x t => rm_smul btb_right t x)
    btb_rsmul_respects
    (fun x y t => rm_smul_distr_l btb_right t x y)
    (fun x t t' => rm_smul_distr_r btb_right t t' x)
    (fun x t t' => rm_smul_assoc btb_right t' t x)
    (fun x => rm_smul_one btb_right x)
    btb_compat.

Example btb_bm_left : bm_left BimodTensorBimod = btb_left := eq_refl.

Example btb_carrier :
  rm_ab (bm_left BimodTensorBimod) = BalTensor EE (bm_left E1) := eq_refl.

Example btb_left_gen (r : RC)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  rm_smul (bm_left BimodTensorBimod) r
    (@bs_gen S EE (bm_left E1) e e1)
    = @bs_gen S EE (bm_left E1) (rm_smul (bm_left E) r e) e1 := eq_refl.

Example btb_right_gen (t : TC)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  bm_rsmul BimodTensorBimod (@bs_gen S EE (bm_left E1) e e1) t
    = @bs_gen S EE (bm_left E1) e (bm_rsmul E1 e1 t) := eq_refl.

End BimoduleTensorBimodule.

Arguments btb_left {R S T} E E1.
Arguments btb_right {R S T} E E1.
Arguments BimodTensorBimod {R S T} E E1.

(** *** Mac Lane part (c): the composite adjunction *)

Section BimoduleAdjunctionComposite.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation EE := (bimodule_right_RMod E).

(* Adjunction/Compose.v, applied.  Nothing is re-proved: the composite
   of two hom-setoid bijections is one, and all four naturality fields are
   that file's. *)
Definition bimodule_adjunction_composite :
  (TensorWith E1 ◯ TensorWith E) ⊣ (HomS E ◯ HomS E1) :=
  Adjunction_Compose (bimodule_tensor_hom_adjunction E)
                     (bimodule_tensor_hom_adjunction E1).

Definition bac_unit (N : RModObject (Ring_op R)) :
  N ~{ModR R}~> HomSObj E (HomSObj E1 (RTensor E1 (RTensor E N))) :=
  @unit (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
    (HomS E ◯ HomS E1) bimodule_adjunction_composite N.

Definition bac_counit (M : RModObject (Ring_op T)) :
  RTensor E1 (RTensor E (HomSObj E (HomSObj E1 M))) ~{ModR T}~> M :=
  @counit (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
    (HomS E ◯ HomS E1) bimodule_adjunction_composite M.

(* The composite's unit is the DOUBLE generator and its counit DOUBLE
   evaluation, both on the nose. *)
Example bac_unit_is_gen (N : RModObject (Ring_op R))
  (n : carrier (cmon_setoid (rm_ab N)))
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  cmon_map (rm_hom (cmon_map (rm_hom
     (cmon_map (rm_hom (bac_unit N)) n)) e)) e1
    = @bs_gen S (RTensor E N) (bm_left E1)
        (@bs_gen R N (bm_left E) n e) e1 := eq_refl.

Example bac_counit_is_eval (M : RModObject (Ring_op T))
  (f : EE ~{ModR S}~> HomSObj E1 M)
  (e : carrier (cmon_setoid (rm_ab (bm_left E))))
  (e1 : carrier (cmon_setoid (rm_ab (bm_left E1)))) :
  cmon_map (rm_hom (bac_counit M))
      (@bs_gen S (RTensor E (HomSObj E (HomSObj E1 M))) (bm_left E1)
         (@bs_gen R (HomSObj E (HomSObj E1 M)) (bm_left E) f e) e1)
    = cmon_map (rm_hom (cmon_map (rm_hom f) e)) e1 := eq_refl.

(* Mac Lane's own description of the composite's unit and counit, read
   off Adjunction/Compose.v's own two lemmas. *)
Lemma bac_unit_whiskered (N : RModObject (Ring_op R)) :
  bac_unit N
    ≈ fmap[HomS E]
        (@unit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E1) (RTensor E N))
      ∘ @unit (ModR S) (ModR R) (TensorWith E) (HomS E)
          (bimodule_tensor_hom_adjunction E) N.
Proof.
  exact (@Adjunction_Compose_unit (ModR S) (ModR R) (ModR T)
           (TensorWith E) (HomS E) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E)
           (bimodule_tensor_hom_adjunction E1) N).
Qed.

Lemma bac_counit_whiskered (M : RModObject (Ring_op T)) :
  bac_counit M
    ≈ @counit (ModR T) (ModR S) (TensorWith E1) (HomS E1)
        (bimodule_tensor_hom_adjunction E1) M
      ∘ fmap[TensorWith E1]
          (@counit (ModR S) (ModR R) (TensorWith E) (HomS E)
             (bimodule_tensor_hom_adjunction E) (HomSObj E1 M)).
Proof.
  exact (@Adjunction_Compose_counit (ModR S) (ModR R) (ModR T)
           (TensorWith E) (HomS E) (TensorWith E1) (HomS E1)
           (bimodule_tensor_hom_adjunction E)
           (bimodule_tensor_hom_adjunction E1) M).
Qed.

End BimoduleAdjunctionComposite.

Arguments bimodule_adjunction_composite {R S T} E E1.

(** *** The associativity comparison, and part (c)'s conclusion *)

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TensorAssocAt.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).
Context (N : RModObject (Ring_op R)).

Local Notation EE := (bimodule_right_RMod E).
Local Notation BTB := (BimodTensorBimod E E1).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation E1C := (carrier (cmon_setoid (rm_ab (bm_left E1)))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).
Local Notation TGT := (BalTensor N (bm_left BTB)).
Local Notation SRC := (BalTensor (RTensor E N) (bm_left E1)).

(** **** Left to right *)

Program Definition ta_inner (e1 : E1C) :
  BalBiadditive N (bm_left E) TGT := {|
  bal_map := fun n e =>
    @bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1)
|}.
Next Obligation.
  intros e1 n n' Hn e e' He.
  refine (be_gen Hn _).
  exact (@be_gen S EE (bm_left E1) e e' e1 e1 He (reflexivity e1)).
Qed.
Next Obligation.
  intros e1 n n' e.
  exact (@be_add_l R N (bm_left BTB) n n'
           (@bs_gen S EE (bm_left E1) e e1)).
Qed.
Next Obligation.
  intros e1 n e e'.
  refine (be_trans _ (@be_add_r R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1)
                        (@bs_gen S EE (bm_left E1) e' e1))).
  refine (be_gen (reflexivity n) _).
  exact (@be_add_l S EE (bm_left E1) e e' e1).
Qed.
Next Obligation.
  intros e1 r n e.
  exact (@be_balance R N (bm_left BTB) r n
           (@bs_gen S EE (bm_left E1) e e1)).
Qed.

Program Definition ta_outer :
  BalBiadditive (RTensor E N) (bm_left E1) TGT := {|
  bal_map := fun x e1 => cmon_map (bal_med (ta_inner e1)) x
|}.
Next Obligation.
  intros x x' Hx e1 e1' He1.
  transitivity (cmon_map (bal_med (ta_inner e1)) x').
  - exact (proper_morphism (cmon_map (bal_med (ta_inner e1))) x x' Hx).
  - refine (bal_hom_ext (bal_med (ta_inner e1))
              (bal_med (ta_inner e1')) _ x').
    intros n e.
    refine (be_gen (reflexivity n) _).
    exact (@be_gen S EE (bm_left E1) e e e1 e1' (reflexivity e) He1).
Qed.
Next Obligation.
  intros x x' e1.
  exact (cmon_map_plus (bal_med (ta_inner e1)) x x').
Qed.
Next Obligation.
  intros x e1 e1'.
  refine (bal_hom_ext (bal_med (ta_inner
             (cmon_plus (rm_ab (bm_left E1)) e1 e1')))
            (ab_hom_add (bal_med (ta_inner e1))
                        (bal_med (ta_inner e1'))) _ x).
  intros n e.
  refine (be_trans _ (@be_add_r R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1)
                        (@bs_gen S EE (bm_left E1) e e1'))).
  refine (be_gen (reflexivity n) _).
  exact (@be_add_r S EE (bm_left E1) e e1 e1').
Qed.
Next Obligation.
  intros s x e1.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (ta_inner e1)) (rt_smul E N s))
            (bal_med (ta_inner (rm_smul (bm_left E1) s e1))) _ x).
  intros n e.
  refine (be_gen (reflexivity n) _).
  exact (@be_balance S EE (bm_left E1) s e e1).
Qed.

Program Definition ta_to : RTensor E1 (RTensor E N) ~{ModR T}~> RTensor BTB N
  := {| rm_hom := bal_med ta_outer |}.
Next Obligation.
  intros t x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer)
                              (rt_smul E1 (RTensor E N) t))
            (cmon_hom_compose (rt_smul BTB N t) (bal_med ta_outer))
            _ x).
  intros x0 e1; simpl.
  refine (bal_hom_ext (bal_med (ta_inner (bm_rsmul E1 e1 t)))
            (cmon_hom_compose (rt_smul BTB N t)
                              (bal_med (ta_inner e1))) _ x0).
  intros n e; reflexivity.
Qed.

(** **** Right to left *)

Program Definition ta_binner (n : NC) :
  BalBiadditive EE (bm_left E1) SRC := {|
  bal_map := fun e e1 =>
    @bs_gen S (RTensor E N) (bm_left E1) (@bs_gen R N (bm_left E) n e) e1
|}.
Next Obligation.
  intros n e e' He e1 e1' He1.
  refine (be_gen _ He1).
  exact (@be_gen R N (bm_left E) n n e e' (reflexivity n) He).
Qed.
Next Obligation.
  intros n e e' e1.
  refine (be_trans _ (@be_add_l S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e)
                        (@bs_gen R N (bm_left E) n e') e1)).
  refine (be_gen _ (reflexivity e1)).
  exact (@be_add_r R N (bm_left E) n e e').
Qed.
Next Obligation.
  intros n e e1 e1'.
  exact (@be_add_r S (RTensor E N) (bm_left E1)
           (@bs_gen R N (bm_left E) n e) e1 e1').
Qed.
Next Obligation.
  intros n s e e1.
  exact (@be_balance S (RTensor E N) (bm_left E1) s
           (@bs_gen R N (bm_left E) n e) e1).
Qed.

Program Definition ta_bouter :
  BalBiadditive N (bm_left BTB) SRC := {|
  bal_map := fun n y => cmon_map (bal_med (ta_binner n)) y
|}.
Next Obligation.
  intros n n' Hn y y' Hy.
  transitivity (cmon_map (bal_med (ta_binner n)) y').
  - exact (proper_morphism (cmon_map (bal_med (ta_binner n))) y y' Hy).
  - refine (bal_hom_ext (bal_med (ta_binner n))
              (bal_med (ta_binner n')) _ y').
    intros e e1.
    refine (be_gen _ (reflexivity e1)).
    exact (@be_gen R N (bm_left E) n n' e e Hn (reflexivity e)).
Qed.
Next Obligation.
  intros n n' y.
  refine (bal_hom_ext (bal_med (ta_binner (cmon_plus (rm_ab N) n n')))
            (ab_hom_add (bal_med (ta_binner n))
                        (bal_med (ta_binner n'))) _ y).
  intros e e1.
  refine (be_trans _ (@be_add_l S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e)
                        (@bs_gen R N (bm_left E) n' e) e1)).
  refine (be_gen _ (reflexivity e1)).
  exact (@be_add_l R N (bm_left E) n n' e).
Qed.
Next Obligation.
  intros n y y'.
  exact (cmon_map_plus (bal_med (ta_binner n)) y y').
Qed.
Next Obligation.
  intros r n y.
  refine (bal_hom_ext (bal_med (ta_binner (rm_smul N r n)))
            (cmon_hom_compose (bal_med (ta_binner n))
                              (lt_smul E (bm_left E1) r)) _ y).
  intros e e1.
  refine (be_gen _ (reflexivity e1)).
  exact (@be_balance R N (bm_left E) r n e).
Qed.

Program Definition ta_from : RTensor BTB N ~{ModR T}~> RTensor E1 (RTensor E N)
  := {| rm_hom := bal_med ta_bouter |}.
Next Obligation.
  intros t y.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter) (rt_smul BTB N t))
            (cmon_hom_compose (rt_smul E1 (RTensor E N) t)
                              (bal_med ta_bouter)) _ y).
  intros n y0; simpl.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (ta_binner n))
                              (rt_smul E1 EE t))
            (cmon_hom_compose (rt_smul E1 (RTensor E N) t)
                              (bal_med (ta_binner n))) _ y0).
  intros e e1; reflexivity.
Qed.

(** **** The two round trips *)

Lemma ta_to_from (y : carrier (cmon_setoid TGT)) :
  cmon_map (rm_hom ta_to) (cmon_map (rm_hom ta_from) y) ≈ y.
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer) (bal_med ta_bouter))
            (@cmon_hom_id TGT) _ y).
  intros n y0.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_outer)
                              (bal_med (ta_binner n)))
            (bal_gen_right N (bm_left BTB) n) _ y0).
  intros e e1; reflexivity.
Qed.

Lemma ta_from_to (x : carrier (cmon_setoid SRC)) :
  cmon_map (rm_hom ta_from) (cmon_map (rm_hom ta_to) x) ≈ x.
Proof.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter) (bal_med ta_outer))
            (@cmon_hom_id SRC) _ x).
  intros x0 e1.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med ta_bouter)
                              (bal_med (ta_inner e1)))
            (bal_gen_left (RTensor E N) (bm_left E1) e1) _ x0).
  intros n e; reflexivity.
Qed.

Program Definition ta_iso :
  @Isomorphism (ModR T) (RTensor E1 (RTensor E N)) (RTensor BTB N) := {|
  to   := ta_to;
  from := ta_from
|}.
Next Obligation. intros y; exact (ta_to_from y). Qed.
Next Obligation. intros x; exact (ta_from_to x). Qed.

Example ta_to_gen (n : NC) (e : EC) (e1 : E1C) :
  cmon_map (rm_hom ta_to)
      (@bs_gen S (RTensor E N) (bm_left E1)
         (@bs_gen R N (bm_left E) n e) e1)
    = @bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1)
  := eq_refl.

Example ta_from_gen (n : NC) (e : EC) (e1 : E1C) :
  cmon_map (rm_hom ta_from)
      (@bs_gen R N (bm_left BTB) n (@bs_gen S EE (bm_left E1) e e1))
    = @bs_gen S (RTensor E N) (bm_left E1)
        (@bs_gen R N (bm_left E) n e) e1 := eq_refl.

End TensorAssocAt.

(** *** Extensionality at the double tensor, and the natural comparison *)

Section TensorAssocNatural.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

Local Notation EE := (bimodule_right_RMod E).
Local Notation BTB := (BimodTensorBimod E E1).

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ta_double_ext (N : RModObject (Ring_op R)) (A : AbObject)
  (u v : AbHom (BalTensor (RTensor E N) (bm_left E1)) A) :
  (∀ n e e1,
      cmon_map u (@bs_gen S (RTensor E N) (bm_left E1)
                    (@bs_gen R N (bm_left E) n e) e1)
        ≈ cmon_map v (@bs_gen S (RTensor E N) (bm_left E1)
                        (@bs_gen R N (bm_left E) n e) e1)) →
  ∀ x, cmon_map u x ≈ cmon_map v x.
Proof.
  intros H x.
  refine (bal_hom_ext u v _ x).
  intros x0 e1.
  refine (bal_hom_ext
            (cmon_hom_compose u
               (bal_gen_left (RTensor E N) (bm_left E1) e1))
            (cmon_hom_compose v
               (bal_gen_left (RTensor E N) (bm_left E1) e1)) _ x0).
  intros n e; exact (H n e e1).
Qed.

Lemma ta_double_ext_r (N : RModObject (Ring_op R)) (A : AbObject)
  (u v : AbHom (BalTensor N (bm_left BTB)) A) :
  (∀ n e e1,
      cmon_map u (@bs_gen R N (bm_left BTB) n
                    (@bs_gen S EE (bm_left E1) e e1))
        ≈ cmon_map v (@bs_gen R N (bm_left BTB) n
                        (@bs_gen S EE (bm_left E1) e e1))) →
  ∀ y, cmon_map u y ≈ cmon_map v y.
Proof.
  intros H y.
  refine (bal_hom_ext u v _ y).
  intros n y0.
  refine (bal_hom_ext
            (cmon_hom_compose u (bal_gen_right N (bm_left BTB) n))
            (cmon_hom_compose v (bal_gen_right N (bm_left BTB) n))
            _ y0).
  intros e e1; exact (H n e e1).
Qed.

(* THE COMPARISON.  [≈] at a functor category is Theory/Functor.v's
   [Functor_Setoid]: a family of isomorphisms together with the coherence
   square, and both halves are supplied here. *)
Definition tensor_assoc_iso :
  (TensorWith E1 ◯ TensorWith E : ModR R ⟶ ModR T)
    ≈ TensorWith (BimodTensorBimod E E1).
Proof.
  exists (fun N => ta_iso E E1 N).
  intros N N' f x.
  refine (ta_double_ext N _
            (rm_hom (fmap[TensorWith E1 ◯ TensorWith E] f))
            (rm_hom (from (ta_iso E E1 N')
                     ∘ fmap[TensorWith BTB] f
                     ∘ to (ta_iso E E1 N))) _ x).
  intros n e e1; reflexivity.
Defined.

End TensorAssocNatural.

Arguments tensor_assoc_iso {R S T} E E1.

(** *** Transporting an adjunction along an isomorphism of left adjoints *)

(*
   本节说明伴随、函子、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** *** Mac Lane's "describe the composite" *)

Section BimoduleCompositeConclusion.

Context {R S T : RingObject}.
Context (E : Bimodule R S).
Context (E1 : Bimodule S T).

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition bimodule_tensor_bimod_adjunction :
  TensorWith (BimodTensorBimod E E1) ⊣ (HomS E ◯ HomS E1) :=
  adjunction_along_left_iso
    (symmetry (tensor_assoc_iso E E1))
    (bimodule_adjunction_composite E E1).

Definition bimodule_hom_composite_iso :
  (HomS E ◯ HomS E1 : ModR T ⟶ ModR R)
    ≈ HomS (BimodTensorBimod E E1) :=
  right_adjoint_iso (TensorWith (BimodTensorBimod E E1))
    (HomS E ◯ HomS E1) (HomS (BimodTensorBimod E E1))
    bimodule_tensor_bimod_adjunction
    (bimodule_tensor_hom_adjunction (BimodTensorBimod E E1)).

(* The transported transpose is the composite's own, precomposed with
   the comparison; on a generator the comparison is [ta_from]. *)
Example btba_to_is_transposed (N : RModObject (Ring_op R))
  (M : RModObject (Ring_op T))
  (g : RTensor (BimodTensorBimod E E1) N ~{ModR T}~> M) :
  to (@adj (ModR T) (ModR R) (TensorWith (BimodTensorBimod E E1))
        (HomS E ◯ HomS E1) bimodule_tensor_bimod_adjunction N M) g
    = to (@adj (ModR T) (ModR R) (TensorWith E1 ◯ TensorWith E)
            (HomS E ◯ HomS E1) (bimodule_adjunction_composite E E1) N M)
        (g ∘ from (aali_cell (symmetry (tensor_assoc_iso E E1)) N))
  := eq_refl.

End BimoduleCompositeConclusion.

Arguments bimodule_tensor_bimod_adjunction {R S T} E E1.
Arguments bimodule_hom_composite_iso {R S T} E E1.

(** ** E. The left-module mirror, and Riehl's Corollary 4.6.10 *)

(*
   本节说明阿贝尔范畴、伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Multiplication by a scalar as an endomorphism of the underlying
   group, over an ARBITRARY ring.  [bth_lmul] of §B is its instance at
   an opposite ring, and is left as it stands. *)
Program Definition rmod_lmul {X : RingObject} (M : RModObject X)
  (x : carrier (rig_setoid (ring_rig X))) :
  AbHom (rm_ab M) (rm_ab M) := {|
  cmon_map := {| morphism := fun m => rm_smul M x m |}
|}.
Next Obligation.
  intros X M x m m' Hm.
  exact (rm_smul_respects M x x (reflexivity x) m m' Hm).
Qed.
Next Obligation. intros X M x; simpl; exact (rm_smul_zero_r M x). Qed.
Next Obligation.
  intros X M x m m'; simpl; exact (rm_smul_distr_l M x m m').
Qed.

Section BimoduleLeftTensorHom.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

(** *** The functor E ⊗_S − *)

Program Definition lt_map_bal {N N' : RModObject S} (f : RModHom N N') :
  BalBiadditive EE N (BalTensor EE N') := {|
  bal_map := fun e n => bs_gen e (cmon_map (rm_hom f) n)
|}.
Next Obligation.
  intros N N' f e e' He n n' Hn.
  refine (be_gen He _).
  exact (proper_morphism (cmon_map (rm_hom f)) n n' Hn).
Qed.
Next Obligation.
  intros N N' f e e' n.
  exact (@be_add_l S EE N' e e' (cmon_map (rm_hom f) n)).
Qed.
Next Obligation.
  intros N N' f e n n'.
  refine (be_trans _ (@be_add_r S EE N' e
                        (cmon_map (rm_hom f) n)
                        (cmon_map (rm_hom f) n'))).
  refine (be_gen (reflexivity e) _).
  exact (cmon_map_plus (rm_hom f) n n').
Qed.
Next Obligation.
  intros N N' f x e n.
  refine (be_trans (@be_balance S EE N' x e (cmon_map (rm_hom f) n)) _).
  refine (be_gen (reflexivity e) _).
  exact (symmetry (rm_map_smul f x n)).
Qed.

Definition lt_map_ab {N N' : RModObject S} (f : RModHom N N') :
  AbHom (BalTensor EE N) (BalTensor EE N') :=
  bal_med (lt_map_bal f).

Program Definition LTensorMap {N N' : RModObject S}
  (f : N ~{RMod S}~> N') : LTensor E N ~{RMod R}~> LTensor E N' := {|
  rm_hom := lt_map_ab f
|}.
Next Obligation.
  intros N N' f r x.
  refine (bal_hom_ext
            (cmon_hom_compose (lt_map_ab f) (lt_smul E N r))
            (cmon_hom_compose (lt_smul E N' r) (lt_map_ab f)) _ x).
  intros e n; reflexivity.
Qed.

Program Definition LTensorWith : RMod S ⟶ RMod R := {|
  fobj := LTensor E;
  fmap := @LTensorMap
|}.
Next Obligation.
  intros N N' f g Hfg x.
  refine (bal_hom_ext (lt_map_ab f) (lt_map_ab g) _ x).
  intros e n.
  refine (be_gen (reflexivity e) _).
  exact (Hfg n).
Qed.
Next Obligation.
  intros N x.
  refine (bal_hom_ext (lt_map_ab (@id (RMod S) N))
            (@cmon_hom_id (BalTensor EE N)) _ x).
  intros e n; reflexivity.
Qed.
Next Obligation.
  intros N N' N'' f g x.
  refine (bal_hom_ext (lt_map_ab (f ∘ g))
            (cmon_hom_compose (lt_map_ab f) (lt_map_ab g)) _ x).
  intros e n; reflexivity.
Qed.

Example ltw_fobj (N : RModObject S) : fobj[LTensorWith] N = LTensor E N
  := eq_refl.

Example ltw_fmap_gen {N N' : RModObject S} (f : N ~{RMod S}~> N')
  (e : EC) (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (rm_hom (fmap[LTensorWith] f))
      (@bs_gen S EE N e n)
    = @bs_gen S EE N' e (cmon_map (rm_hom f) n) := eq_refl.

(** *** hom_R(E, M) and its left S-action *)

Definition lhs_group (M : RModObject R) : AbObject :=
  hom_ab (RMod_AbEnriched R) (bm_left E) M.

Example lhs_group_carrier (M : RModObject R) :
  carrier (cmon_setoid (lhs_group M)) = (bm_left E ~{RMod R}~> M)
  := eq_refl.

(* (s · f)(e) = f (e ⊲ s): translation through the RIGHT action, the
   mirror of §B's (f ⊲ r)(e) = f (r · e). *)
Program Definition lhs_act (M : RModObject R) (s : SC)
  (f : bm_left E ~{RMod R}~> M) : bm_left E ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom f) (bm_rsmul E e s) |} |}
|}.
Next Obligation.
  intros M s f e e' He.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (bm_rsmul_respects E e e' He s s (reflexivity s))).
Qed.
Next Obligation.
  intros M s f; simpl.
  transitivity (cmon_map (rm_hom f) (cmon_zero (rm_ab (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (rm_smul_zero_r (bimodule_right_RMod E) s)).
  - exact (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros M s f e e'; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (bm_rsmul E e s) (bm_rsmul E e' s))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_distr_l E e e' s)).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.
Next Obligation.
  (* the ONLY use of [bm_compat] in this block *)
  intros M s f r e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (rm_smul (bm_left E) r (bm_rsmul E e s))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_compat E r e s)).
  - exact (rm_map_smul f r (bm_rsmul E e s)).
Qed.

Example lhs_act_at (M : RModObject R) (s : SC)
  (f : bm_left E ~{RMod R}~> M) (e : EC) :
  cmon_map (rm_hom (lhs_act M s f)) e
    = cmon_map (rm_hom f) (bm_rsmul E e s) := eq_refl.

Lemma lhs_act_respects (M : RModObject R) :
  Proper (equiv ==> equiv ==> equiv) (lhs_act M).
Proof.
  intros s s' Hs f g Hfg e; simpl.
  transitivity (cmon_map (rm_hom f) (bm_rsmul E e s')).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_respects E e e (reflexivity e) s s' Hs)).
  - exact (Hfg _).
Qed.

Lemma lhs_act_distr_l (M : RModObject R) (s : SC)
  (f g : bm_left E ~{RMod R}~> M) :
  lhs_act M s (cmon_plus (lhs_group M) f g)
    ≈ cmon_plus (lhs_group M) (lhs_act M s f) (lhs_act M s g).
Proof. intro e; reflexivity. Qed.

Lemma lhs_act_distr_r (M : RModObject R) (s s' : SC)
  (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_add (ring_rig S) s s') f
    ≈ cmon_plus (lhs_group M) (lhs_act M s f) (lhs_act M s' f).
Proof.
  intro e; simpl.
  transitivity (cmon_map (rm_hom f)
                  (cmon_plus (rm_ab (bm_left E))
                     (bm_rsmul E e s) (bm_rsmul E e s'))).
  - exact (proper_morphism (cmon_map (rm_hom f)) _ _
             (bm_rsmul_distr_r E e s s')).
  - exact (cmon_map_plus (rm_hom f) _ _).
Qed.

Lemma lhs_act_assoc (M : RModObject R) (s s' : SC)
  (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_mul (ring_rig S) s s') f
    ≈ lhs_act M s (lhs_act M s' f).
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _
           (bm_rsmul_assoc E e s s')).
Qed.

Lemma lhs_act_one (M : RModObject R) (f : bm_left E ~{RMod R}~> M) :
  lhs_act M (rig_one (ring_rig S)) f ≈ f.
Proof.
  intro e; simpl.
  exact (proper_morphism (cmon_map (rm_hom f)) _ _ (bm_rsmul_one E e)).
Qed.

Definition LHomSObj (M : RModObject R) : RModObject S :=
  @Build_RModObject S
    (lhs_group M)
    (lhs_act M)
    (lhs_act_respects M)
    (lhs_act_distr_l M)
    (lhs_act_distr_r M)
    (lhs_act_assoc M)
    (lhs_act_one M).

Program Definition lhs_map_ab {M M' : RModObject R}
  (g : M ~{RMod R}~> M') : AbHom (lhs_group M) (lhs_group M') := {|
  cmon_map := {| morphism := fun f =>
    (rmod_hom_compose g f : bm_left E ~{RMod R}~> M') |}
|}.
Next Obligation.
  intros M M' g f f' Hf e; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf e)).
Qed.
Next Obligation.
  intros M M' g e; simpl; exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' e; simpl; exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition LHomSMap {M M' : RModObject R}
  (g : M ~{RMod R}~> M') : LHomSObj M ~{RMod S}~> LHomSObj M' := {|
  rm_hom := lhs_map_ab g
|}.
Next Obligation. intros M M' g s f e; reflexivity. Qed.

Program Definition LHomS : RMod R ⟶ RMod S := {|
  fobj := LHomSObj;
  fmap := @LHomSMap
|}.
Next Obligation. intros M M' g g' Hg f e; simpl; exact (Hg _). Qed.
Next Obligation. intros M f e; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f e; reflexivity. Qed.

End BimoduleLeftTensorHom.

(** *** The left-module tensor-hom adjunction *)

Section BimoduleLeftAdjunction.

Context {R S : RingObject}.
Context (E : Bimodule R S).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation EC := (carrier (cmon_setoid (rm_ab (bm_left E)))).
Local Notation EE := (bimodule_right_RMod E).

Program Definition blt_to_inner {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) :
  bm_left E ~{RMod R}~> M := {|
  rm_hom := {| cmon_map := {| morphism := fun e =>
    cmon_map (rm_hom g) (@bs_gen S EE N e n) |} |}
|}.
Next Obligation.
  intros N M g n e e' He.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen S EE N e e' n n He (reflexivity n)).
Qed.
Next Obligation.
  intros N M g n; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (BalTensor EE N))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l EE N n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n e e'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor EE N)
                     (@bs_gen S EE N e n) (@bs_gen S EE N e' n))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_l S EE N e e' n)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* (r · e) ⊗ n IS r ·[LTensor] (e ⊗ n) on the nose. *)
  intros N M g n r e.
  exact (rm_map_smul g r (@bs_gen S EE N e n)).
Qed.

Program Definition blt_to_ab {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M) :
  AbHom (rm_ab N) (lhs_group E M) := {|
  cmon_map := {| morphism := fun n => blt_to_inner g n |}
|}.
Next Obligation.
  intros N M g n n' Hn e; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen S EE N e e n n' (reflexivity e) Hn).
Qed.
Next Obligation.
  intros N M g e; simpl.
  transitivity (cmon_map (rm_hom g) (cmon_zero (BalTensor EE N))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r EE N e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros N M g n n' e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor EE N)
                     (@bs_gen S EE N e n) (@bs_gen S EE N e n'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_r S EE N e n n')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

(* The forward transpose is S-linear BECAUSE of the balance rule. *)
Program Definition blt_to {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M) : N ~{RMod S}~> LHomSObj E M := {|
  rm_hom := blt_to_ab g
|}.
Next Obligation.
  intros N M g s n e; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (symmetry (@be_balance S EE N s e n)).
Qed.

Program Definition blt_from_bal {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M) :
  BalBiadditive EE N (rm_ab M) := {|
  bal_map := fun e n => cmon_map (rm_hom (cmon_map (rm_hom h) n)) e
|}.
Next Obligation.
  intros N M h e e' He n n' Hn.
  transitivity (cmon_map (rm_hom (cmon_map (rm_hom h) n)) e').
  - exact (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom h) n)))
             e e' He).
  - exact (proper_morphism (cmon_map (rm_hom h)) n n' Hn e').
Qed.
Next Obligation.
  intros N M h e e' n.
  exact (cmon_map_plus (rm_hom (cmon_map (rm_hom h) n)) e e').
Qed.
Next Obligation.
  intros N M h e n n'.
  exact (cmon_map_plus (rm_hom h) n n' e).
Qed.
Next Obligation.
  (* Balance is [h]'s own S-linearity read at e. *)
  intros N M h s e n.
  exact (symmetry (rm_map_smul h s n e)).
Qed.

Program Definition blt_from {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M) : LTensor E N ~{RMod R}~> M := {|
  rm_hom := bal_med (blt_from_bal h)
|}.
Next Obligation.
  intros N M h r x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (blt_from_bal h))
                              (lt_smul E N r))
            (cmon_hom_compose (rmod_lmul M r)
                              (bal_med (blt_from_bal h))) _ x).
  intros e n.
  exact (rm_map_smul (cmon_map (rm_hom h) n) r e).
Qed.

Example blt_to_at {N : RModObject S} {M : RModObject R}
  (g : LTensor E N ~{RMod R}~> M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (blt_to g)) n)) e
    = cmon_map (rm_hom g) (@bs_gen S EE N e n) := eq_refl.

Example blt_from_at {N : RModObject S} {M : RModObject R}
  (h : N ~{RMod S}~> LHomSObj E M)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (blt_from h)) (@bs_gen S EE N e n)
    = cmon_map (rm_hom (cmon_map (rm_hom h) n)) e := eq_refl.

Program Definition blt_adj (N : RModObject S) (M : RModObject R) :
  @Isomorphism Sets
    {| carrier := LTensor E N ~{RMod R}~> M;
       is_setoid := @homset (RMod R) (LTensor E N) M |}
    {| carrier := N ~{RMod S}~> LHomSObj E M;
       is_setoid := @homset (RMod S) N (LHomSObj E M) |} := {|
  to   := {| morphism := fun g => blt_to g |};
  from := {| morphism := fun h => blt_from h |}
|}.
Next Obligation. intros N M g g' Hg n e; exact (Hg _). Qed.
Next Obligation.
  intros N M h h' Hh x.
  refine (bal_hom_ext (bal_med (blt_from_bal h))
                      (bal_med (blt_from_bal h')) _ x).
  intros e n; exact (Hh n e).
Qed.
Next Obligation. intros N M h n e; reflexivity. Qed.
Next Obligation.
  intros N M g x.
  refine (bal_hom_ext (bal_med (blt_from_bal (blt_to g)))
                      (rm_hom g) _ x).
  intros e n; reflexivity.
Qed.

Definition bimodule_left_tensor_hom_adjunction :
  LTensorWith E ⊣ LHomS E.
Proof using E R S.
  unshelve eapply (@Build_Adjunction' (RMod R) (RMod S)
                     (LTensorWith E) (LHomS E) blt_adj).
  - intros N N' M f g n e; reflexivity.
  - intros N M M' f g n e; reflexivity.
Defined.

Definition blt_unit (N : RModObject S) :
  N ~{RMod S}~> LHomSObj E (LTensor E N) :=
  @unit (RMod R) (RMod S) (LTensorWith E) (LHomS E)
    bimodule_left_tensor_hom_adjunction N.

Definition blt_counit (M : RModObject R) :
  LTensor E (LHomSObj E M) ~{RMod R}~> M :=
  @counit (RMod R) (RMod S) (LTensorWith E) (LHomS E)
    bimodule_left_tensor_hom_adjunction M.

Example blt_unit_is_gen (N : RModObject S)
  (n : carrier (cmon_setoid (rm_ab N))) (e : EC) :
  cmon_map (rm_hom (cmon_map (rm_hom (blt_unit N)) n)) e
    = @bs_gen S EE N e n := eq_refl.

Example blt_counit_is_eval (M : RModObject R)
  (f : bm_left E ~{RMod R}~> M) (e : EC) :
  cmon_map (rm_hom (blt_counit M))
      (@bs_gen S EE (LHomSObj E M) e f)
    = cmon_map (rm_hom f) e := eq_refl.

End BimoduleLeftAdjunction.

(** *** Riehl 4.6.10, at the strength the tree can state *)

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition bimodule_left_tensor_preserves_colimits
  {R S : RingObject} (E : Bimodule R S) :
  PreservesAllColimits (LTensorWith E) :=
  left_adjoint_preserves_colimits (bimodule_left_tensor_hom_adjunction E).

Definition bimodule_tensor_preserves_colimits
  {R S : RingObject} (E : Bimodule R S) :
  PreservesAllColimits (TensorWith E) :=
  left_adjoint_preserves_colimits (bimodule_tensor_hom_adjunction E).

(* The composite of part (c) is a left adjoint too, so it preserves all
   colimits by the same one-line reading. *)
Definition bimodule_tensor_bimod_preserves_colimits
  {R S T : RingObject} (E : Bimodule R S) (E1 : Bimodule S T) :
  PreservesAllColimits (TensorWith (BimodTensorBimod E E1)) :=
  left_adjoint_preserves_colimits (bimodule_tensor_bimod_adjunction E E1).

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Arguments bh_hom {R S E E'} b.
Arguments bh_right {R S E E'} b m s.

(** ** F. The second closure, and the two-variable adjunction *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section HomAbBimodule.

Context {R S : RingObject}.

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).

Context (N : RModObject (Ring_op R)).
Context (M : RModObject (Ring_op S)).

Definition hab_group : AbObject :=
  hom_ab Ab_AbEnriched (rm_ab N) (rm_ab M).

Example hab_group_carrier :
  carrier (cmon_setoid hab_group) = (rm_ab N ~{Ab}~> rm_ab M) := eq_refl.

Program Definition hab_lact (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n => cmon_map f (rm_smul N r n) |}
|}.
Next Obligation.
  intros r f n n' Hn.
  exact (proper_morphism (cmon_map f) _ _
           (rm_smul_respects N r r (reflexivity r) n n' Hn)).
Qed.
Next Obligation.
  intros r f; simpl.
  transitivity (cmon_map f (cmon_zero (rm_ab N))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_zero_r N r)).
  - exact (cmon_map_zero f).
Qed.
Next Obligation.
  intros r f n n'; simpl.
  transitivity (cmon_map f
                  (cmon_plus (rm_ab N) (rm_smul N r n) (rm_smul N r n'))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_l N r n n')).
  - exact (cmon_map_plus f _ _).
Qed.

Program Definition hab_ract (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n => rm_smul M s (cmon_map f n) |}
|}.
Next Obligation.
  intros f s n n' Hn.
  exact (rm_smul_respects M s s (reflexivity s) _ _
           (proper_morphism (cmon_map f) n n' Hn)).
Qed.
Next Obligation.
  intros f s; simpl.
  transitivity (rm_smul M s (cmon_zero (rm_ab M))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_zero f)).
  - exact (rm_smul_zero_r M s).
Qed.
Next Obligation.
  intros f s n n'; simpl.
  transitivity (rm_smul M s
                  (cmon_plus (rm_ab M) (cmon_map f n) (cmon_map f n'))).
  - exact (rm_smul_respects M s s (reflexivity s) _ _
             (cmon_map_plus f n n')).
  - exact (rm_smul_distr_l M s _ _).
Qed.

Lemma hab_lact_respects : Proper (equiv ==> equiv ==> equiv) hab_lact.
Proof.
  intros r r' Hr f g Hfg n; simpl.
  transitivity (cmon_map f (rm_smul N r' n)).
  - exact (proper_morphism (cmon_map f) _ _
             (rm_smul_respects N r r' Hr n n (reflexivity n))).
  - exact (Hfg _).
Qed.

Lemma hab_lact_distr_l (r : RC) (f g : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact r (cmon_plus hab_group f g)
    ≈ cmon_plus hab_group (hab_lact r f) (hab_lact r g).
Proof. intro n; reflexivity. Qed.

Lemma hab_lact_distr_r (r r' : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_add (ring_rig R) r r') f
    ≈ cmon_plus hab_group (hab_lact r f) (hab_lact r' f).
Proof.
  intro n; simpl.
  transitivity (cmon_map f
                  (cmon_plus (rm_ab N) (rm_smul N r n) (rm_smul N r' n))).
  - exact (proper_morphism (cmon_map f) _ _ (rm_smul_distr_r N r r' n)).
  - exact (cmon_map_plus f _ _).
Qed.

Lemma hab_lact_assoc (r r' : RC) (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_mul (ring_rig R) r r') f ≈ hab_lact r (hab_lact r' f).
Proof.
  intro n; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_assoc N r' r n)).
Qed.

Lemma hab_lact_one (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_lact (rig_one (ring_rig R)) f ≈ f.
Proof.
  intro n; simpl.
  exact (proper_morphism (cmon_map f) _ _ (rm_smul_one N n)).
Qed.

Definition hab_left : RModObject R :=
  @Build_RModObject R hab_group hab_lact hab_lact_respects
    hab_lact_distr_l hab_lact_distr_r hab_lact_assoc hab_lact_one.

Lemma hab_ract_respects : Proper (equiv ==> equiv ==> equiv) hab_ract.
Proof.
  intros f g Hfg s s' Hs n; simpl.
  exact (rm_smul_respects M s s' Hs _ _ (Hfg n)).
Qed.

Lemma hab_ract_distr_l (f g : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  hab_ract (cmon_plus hab_group f g) s
    ≈ cmon_plus hab_group (hab_ract f s) (hab_ract g s).
Proof. intro n; simpl; exact (rm_smul_distr_l M s _ _). Qed.

Lemma hab_ract_distr_r (f : rm_ab N ~{Ab}~> rm_ab M) (s s' : SC) :
  hab_ract f (rig_add (ring_rig S) s s')
    ≈ cmon_plus hab_group (hab_ract f s) (hab_ract f s').
Proof. intro n; simpl; exact (rm_smul_distr_r M s s' _). Qed.

Lemma hab_ract_assoc (f : rm_ab N ~{Ab}~> rm_ab M) (s s' : SC) :
  hab_ract f (rig_mul (ring_rig S) s s')
    ≈ hab_ract (hab_ract f s) s'.
Proof. intro n; simpl; exact (rm_smul_assoc M s' s _). Qed.

Lemma hab_ract_one (f : rm_ab N ~{Ab}~> rm_ab M) :
  hab_ract f (rig_one (ring_rig S)) ≈ f.
Proof. intro n; simpl; exact (rm_smul_one M _). Qed.

(* The compatibility law holds POINTWISE, with no law of either module
   consumed: both sides send n to (f (n ⊲ r)) ⊲ s. *)
Lemma hab_compat (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC) :
  hab_ract (hab_lact r f) s ≈ hab_lact r (hab_ract f s).
Proof. intro n; reflexivity. Qed.

Definition HomAbBimod : Bimodule R S :=
  @Build_Bimodule R S hab_left hab_ract hab_ract_respects
    hab_ract_distr_l hab_ract_distr_r hab_ract_assoc hab_ract_one
    hab_compat.

Example hab_bimod_left_at (r : RC) (f : rm_ab N ~{Ab}~> rm_ab M)
  (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (rm_smul (bm_left HomAbBimod) r f) n
    = cmon_map f (rm_smul N r n) := eq_refl.

Example hab_bimod_right_at (f : rm_ab N ~{Ab}~> rm_ab M) (s : SC)
  (n : carrier (cmon_setoid (rm_ab N))) :
  cmon_map (bm_rsmul HomAbBimod f s) n
    = rm_smul M s (cmon_map f n) := eq_refl.

End HomAbBimodule.

Arguments hab_group {R S} N M.
Arguments hab_left {R S} N M.
Arguments HomAbBimod {R S} N M.

(** *** The second closure as a functor, and the mirror adjunction *)

Section HomAbFunctorSection.

Context {R S : RingObject}.
Context (N : RModObject (Ring_op R)).

Local Notation RC := (carrier (rig_setoid (ring_rig R))).
Local Notation SC := (carrier (rig_setoid (ring_rig S))).
Local Notation NC := (carrier (cmon_setoid (rm_ab N))).

Program Definition hab_map_ab {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') :
  RModHom (hab_left N M) (hab_left N M') := {|
  rm_hom := {| cmon_map := {| morphism := fun f =>
    (cmon_hom_compose (rm_hom g) f : rm_ab N ~{Ab}~> rm_ab M') |} |}
|}.
Next Obligation.
  intros M M' g f f' Hf n; simpl.
  unfold Basics.compose.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _ (Hf n)).
Qed.
Next Obligation.
  intros M M' g n; simpl; exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros M M' g f f' n; simpl; exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation. intros M M' g r f n; reflexivity. Qed.

Program Definition HomAbMap {M M' : RModObject (Ring_op S)}
  (g : M ~{ModR S}~> M') :
  HomAbBimod N M ~{@BimodCat R S}~> HomAbBimod N M' := {|
  bh_hom := hab_map_ab g
|}.
Next Obligation.
  intros M M' g f s n; simpl.
  exact (rm_map_smul g s (cmon_map f n)).
Qed.

Program Definition HomAbFunctor : ModR S ⟶ @BimodCat R S := {|
  fobj := HomAbBimod N;
  fmap := @HomAbMap
|}.
Next Obligation.
  intros M M' g g' Hg f n; simpl; exact (Hg _).
Qed.
Next Obligation. intros M f n; reflexivity. Qed.
Next Obligation. intros M M' M'' g g' f n; reflexivity. Qed.

Example hab_functor_obj (M : RModObject (Ring_op S)) :
  fobj[HomAbFunctor] M = HomAbBimod N M := eq_refl.

(** *** The bijection: bimodule maps into hom_Ab(N, M) *)

Program Definition hbt_to_inner {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M)
  (e : carrier (cmon_setoid (rm_ab (bm_left E)))) :
  rm_ab N ~{Ab}~> rm_ab M := {|
  cmon_map := {| morphism := fun n =>
    cmon_map (rm_hom g) (@bs_gen R N (bm_left E) n e) |}
|}.
Next Obligation.
  intros E M g e n n' Hn.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen R N (bm_left E) n n' e e Hn (reflexivity e)).
Qed.
Next Obligation.
  intros E M g e; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_l N (bm_left E) e)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros E M g e n n'; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (@bs_gen R N (bm_left E) n e)
                     (@bs_gen R N (bm_left E) n' e))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_l R N (bm_left E) n n' e)).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.

Program Definition hbt_to_hom {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M) :
  RModHom (bm_left E) (hab_left N M) := {|
  rm_hom := {| cmon_map := {| morphism := fun e => hbt_to_inner g e |} |}
|}.
Next Obligation.
  intros E M g e e' He n; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (@be_gen R N (bm_left E) n n e e' (reflexivity n) He).
Qed.
Next Obligation.
  intros E M g n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_zero (BalTensor N (bm_left E)))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (bal_gen_zero_r N (bm_left E) n)).
  - exact (cmon_map_zero (rm_hom g)).
Qed.
Next Obligation.
  intros E M g e e' n; simpl.
  transitivity (cmon_map (rm_hom g)
                  (cmon_plus (BalTensor N (bm_left E))
                     (@bs_gen R N (bm_left E) n e)
                     (@bs_gen R N (bm_left E) n e'))).
  - exact (proper_morphism (cmon_map (rm_hom g)) _ _
             (@be_add_r R N (bm_left E) n e e')).
  - exact (cmon_map_plus (rm_hom g) _ _).
Qed.
Next Obligation.
  (* R-linearity of the transpose IS the balance rule, again. *)
  intros E M g r e n; simpl.
  refine (proper_morphism (cmon_map (rm_hom g)) _ _ _).
  exact (symmetry (@be_balance R N (bm_left E) r n e)).
Qed.

Program Definition hbt_to {E : Bimodule R S}
  {M : RModObject (Ring_op S)} (g : RTensor E N ~{ModR S}~> M) :
  E ~{@BimodCat R S}~> HomAbBimod N M := {|
  bh_hom := hbt_to_hom g
|}.
Next Obligation.
  intros E M g e s n; simpl.
  exact (rm_map_smul g s (@bs_gen R N (bm_left E) n e)).
Qed.

Program Definition hbt_from_bal {E : Bimodule R S}
  {M : RModObject (Ring_op S)}
  (h : E ~{@BimodCat R S}~> HomAbBimod N M) :
  BalBiadditive N (bm_left E) (rm_ab M) := {|
  bal_map := fun n e =>
    cmon_map (cmon_map (rm_hom (bh_hom h)) e) n
|}.
Next Obligation.
  intros E M h n n' Hn e e' He.
  transitivity (cmon_map (cmon_map (rm_hom (bh_hom h)) e) n').
  - exact (proper_morphism (cmon_map (cmon_map (rm_hom (bh_hom h)) e))
             n n' Hn).
  - exact (proper_morphism (cmon_map (rm_hom (bh_hom h))) e e' He n').
Qed.
Next Obligation.
  intros E M h n n' e.
  exact (cmon_map_plus (cmon_map (rm_hom (bh_hom h)) e) n n').
Qed.
Next Obligation.
  intros E M h n e e'.
  exact (cmon_map_plus (rm_hom (bh_hom h)) e e' n).
Qed.
Next Obligation.
  intros E M h r n e.
  exact (symmetry (rm_map_smul (bh_hom h) r e n)).
Qed.

Program Definition hbt_from {E : Bimodule R S}
  {M : RModObject (Ring_op S)}
  (h : E ~{@BimodCat R S}~> HomAbBimod N M) :
  RTensor E N ~{ModR S}~> M := {|
  rm_hom := bal_med (hbt_from_bal h)
|}.
Next Obligation.
  intros E M h s x.
  refine (bal_hom_ext
            (cmon_hom_compose (bal_med (hbt_from_bal h)) (rt_smul E N s))
            (cmon_hom_compose (rmod_lmul M s)
                              (bal_med (hbt_from_bal h))) _ x).
  intros n e.
  exact (bh_right h e s n).
Qed.

Program Definition hab_adj (E : Bimodule R S)
  (M : RModObject (Ring_op S)) :
  @Isomorphism Sets
    {| carrier := RTensor E N ~{ModR S}~> M;
       is_setoid := @homset (ModR S) (RTensor E N) M |}
    {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
       is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |} := {|
  to   := {| morphism := fun g => hbt_to g |};
  from := {| morphism := fun h => hbt_from h |}
|}.
Next Obligation. intros E M g g' Hg e n; exact (Hg _). Qed.
Next Obligation.
  intros E M h h' Hh x.
  refine (bal_hom_ext (bal_med (hbt_from_bal h))
                      (bal_med (hbt_from_bal h')) _ x).
  intros n e; exact (Hh e n).
Qed.
Next Obligation. intros E M h e n; reflexivity. Qed.
Next Obligation.
  intros E M g x.
  refine (bal_hom_ext (bal_med (hbt_from_bal (hbt_to g)))
                      (rm_hom g) _ x).
  intros n e; reflexivity.
Qed.

Definition hab_partial_adj :
  Partial_r (@BimodTensor R S) N ⊣ HomAbFunctor.
Proof using N R S.
  unshelve eapply (@Build_Adjunction' (ModR S) (@BimodCat R S)
                     (Partial_r (@BimodTensor R S) N) HomAbFunctor
                     hab_adj).
  - intros E E' M f g e n; reflexivity.
  - intros E M M' f g e n; reflexivity.
Defined.

End HomAbFunctorSection.

Arguments HomAbFunctor {R S} N.

(** *** All three legs of Riehl's Definition 4.4.7 *)

(*
   本节说明伴随、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BimoduleTwoVariable.

Context {R S : RingObject}.

Definition bimodule_mirror_family :
  ParametrizedAdjunction
    ((@BimodTensor R S) ◯ @Swap (@BimodCat R S) (ModR R)) :=
  mirror_family (@BimodTensor R S) (fun N => HomAbFunctor N)
    (fun N => hab_partial_adj N).

Definition bimodule_two_variable_adjunction
  (M : RModObject (Ring_op S)) :
  AdjointOnTheRight
    (mr_left (@bimodule_parametrized_adjunction R S) M)
    (mr_right bimodule_mirror_family M) :=
  mutually_right_adjoint (@bimodule_parametrized_adjunction R S)
    bimodule_mirror_family M.

Example btv_left_obj (M : RModObject (Ring_op S)) (E : Bimodule R S) :
  mr_left (@bimodule_parametrized_adjunction R S) M E = HomSObj E M
  := eq_refl.

Example btv_right_obj (M : RModObject (Ring_op S))
  (N : RModObject (Ring_op R)) :
  mr_right bimodule_mirror_family M N = HomAbBimod N M := eq_refl.

End BimoduleTwoVariable.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition bimodule_third_leg {R S : RingObject}
  (M : RModObject (Ring_op S)) (E : Bimodule R S)
  (N : RModObject (Ring_op R)) :
  @Isomorphism Sets
    {| carrier := E ~{@BimodCat R S}~> HomAbBimod N M;
       is_setoid := @homset (@BimodCat R S) E (HomAbBimod N M) |}
    {| carrier := N ~{ModR R}~> HomSObj E M;
       is_setoid := @homset (ModR R) N (HomSObj E M) |} :=
  @aor (@BimodCat R S) (ModR R)
    (mr_left (@bimodule_parametrized_adjunction R S) M)
    (mr_right (@bimodule_mirror_family R S) M)
    (bimodule_two_variable_adjunction M) E N.

(** ** G. A concrete witness at a named pair of rings *)

(*
   本节说明 Bimodule 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section IntegerWitness.

Local Notation ZC := (carrier (rig_setoid (ring_rig Int_Ring))).

(* ℤ read as a RIGHT ℤ-module, i.e. as an object of [ModR Int_Ring]. *)
Definition ZRight : RModObject (Ring_op Int_Ring) :=
  bimodule_right_RMod Int_Bimodule.

Local Notation ZG := (@bs_gen Int_Ring ZRight (bm_left Int_Bimodule)).

Example z_tensor_smul_gen (a b s : ZC) :
  rm_smul (RTensor Int_Bimodule ZRight) s (ZG a b)
    = ZG a (rig_mul (ring_rig Int_Ring) b s) := eq_refl.

Example z_tensor_smul_computes :
  rm_smul (RTensor Int_Bimodule ZRight) 5%Z (ZG 2%Z 3%Z) = ZG 2%Z 15%Z
  := eq_refl.

Example z_tensor_unit_computes :
  cmon_map (rm_hom (cmon_map (rm_hom
      (bth_unit Int_Bimodule ZRight)) 2%Z)) 3%Z = ZG 2%Z 3%Z := eq_refl.

Example z_tensor_counit_computes :
  cmon_map (rm_hom (bth_counit Int_Bimodule ZRight))
      (@bs_gen Int_Ring (HomSObj Int_Bimodule ZRight)
         (bm_left Int_Bimodule) (@id (ModR Int_Ring) ZRight) 7%Z)
    = 7%Z := eq_refl.

(* Multiplication is balanced and biadditive, so it descends; it is what
   SEPARATES two generators, since no induction over the quotienting
   relation could produce a negative. *)
(* Every field is a rig law of ℤ applied, so the record literal raises no
   obligation at all: multiplication is biadditive by distributivity and
   balanced by associativity. *)
Definition int_mult_bal :
  BalBiadditive ZRight (bm_left Int_Bimodule) (ring_ab Int_Ring) :=
  @Build_BalBiadditive Int_Ring ZRight (bm_left Int_Bimodule)
    (ring_ab Int_Ring)
    (rig_mul (ring_rig Int_Ring))
    (rig_mul_respects (ring_rig Int_Ring))
    (fun a a' b => rig_distr_r (ring_rig Int_Ring) a a' b)
    (fun a b b' => rig_distr_l (ring_rig Int_Ring) a b b')
    (fun x a b => rig_mul_assoc (ring_rig Int_Ring) a x b).

Example int_mult_gen (a b : ZC) :
  cmon_map (bal_med int_mult_bal) (ZG a b)
    = rig_mul (ring_rig Int_Ring) a b := eq_refl.

Lemma int_tensor_separates :
  (ZG 1%Z 1%Z
     : carrier (cmon_setoid (rm_ab (RTensor Int_Bimodule ZRight))))
    ≈ ZG 1%Z 2%Z → False.
Proof.
  intro H.
  pose proof (bal_med_respects ZRight (bm_left Int_Bimodule)
                int_mult_bal _ _ H) as Hm.
  simpl in Hm; discriminate Hm.
Qed.

(** *** The tensor of two bimodules, and the comparison, at ℤ *)

Local Notation ZZ := (BimodTensorBimod Int_Bimodule Int_Bimodule).
Local Notation ZGG :=
  (@bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
     (bm_left Int_Bimodule)).

Example z_btb_left_computes :
  rm_smul (bm_left ZZ) 2%Z (ZGG 3%Z 5%Z) = ZGG 6%Z 5%Z := eq_refl.

Example z_btb_right_computes :
  bm_rsmul ZZ (ZGG 3%Z 5%Z) 2%Z = ZGG 3%Z 10%Z := eq_refl.

Example z_assoc_to_computes (a b c : ZC) :
  cmon_map (rm_hom (ta_to Int_Bimodule Int_Bimodule ZRight))
      (@bs_gen Int_Ring (RTensor Int_Bimodule ZRight)
         (bm_left Int_Bimodule) (ZG a b) c)
    = @bs_gen Int_Ring ZRight (bm_left ZZ) a (ZGG b c) := eq_refl.

Example z_assoc_from_computes (a b c : ZC) :
  cmon_map (rm_hom (ta_from Int_Bimodule Int_Bimodule ZRight))
      (@bs_gen Int_Ring ZRight (bm_left ZZ) a (ZGG b c))
    = @bs_gen Int_Ring (RTensor Int_Bimodule ZRight)
        (bm_left Int_Bimodule) (ZG a b) c := eq_refl.

(** *** The left-module mirror, and the second closure, at ℤ *)

Example z_ltensor_smul_gen (a b r : ZC) :
  rm_smul (LTensor Int_Bimodule (Ring_RMod Int_Ring)) r
      (@bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
         (Ring_RMod Int_Ring) a b)
    = @bs_gen Int_Ring (bimodule_right_RMod Int_Bimodule)
        (Ring_RMod Int_Ring) (rig_mul (ring_rig Int_Ring) r a) b
  := eq_refl.

Example z_hab_left_computes (f : rm_ab ZRight ~{Ab}~> rm_ab ZRight)
  (r n : ZC) :
  cmon_map (rm_smul (bm_left (HomAbBimod ZRight ZRight)) r f) n
    = cmon_map f (rig_mul (ring_rig Int_Ring) n r) := eq_refl.

Example z_hab_right_computes (f : rm_ab ZRight ~{Ab}~> rm_ab ZRight)
  (s n : ZC) :
  cmon_map (bm_rsmul (HomAbBimod ZRight ZRight) f s) n
    = rig_mul (ring_rig Int_Ring) (cmon_map f n) s := eq_refl.

End IntegerWitness.
