Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.FreeMonoidal.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Normal.

Context {B : Category}.
Context `{MB : @Monoidal B}.
Context (b : B).

(** ** The right-normalised tensor and the join *)

(* [nf n X] is b ⨂ (b ⨂ (… ⨂ X)), n copies of b with tail X. *)
Fixpoint nf (n : nat) (X : B) : B :=
  match n with
  | O   => X
  | S m => b ⨂ nf m X
  end.

(* The join: appending under the tail parameter.  See the header design note
   for why the codomain is [nf (m + n) X]. *)
Fixpoint J (m n : nat) (X : B) : (nf m I ⨂ nf n X) ≅ nf (m + n) X :=
  match m with
  | O   => unit_left
  | S k => tensor_iso iso_id (J k n X) ⊙ tensor_assoc
  end.

(* Mac Lane's "substitute b into all blanks" — (e0)_b = e, (-)_b = b,
   (v □ w)_b = v_b ⨂ w_b.  Strict on the nose, by construction. *)
Fixpoint subst (w : Word) : B :=
  match w with
  | WE     => I
  | WI     => b
  | WT v u => subst v ⨂ subst u
  end.

(* The normalisation isomorphism.  The [WT] branch IS the multiplicativity of
   the normaliser, definitionally — there is no separate lemma to prove. *)
Fixpoint can (w : Word) : subst w ≅ nf (wlen w) I :=
  match w with
  | WE     => iso_id
  | WI     => iso_sym unit_right
  | WT v u => J (wlen v) (wlen u) I ⊙ tensor_iso (can v) (can u)
  end.

(*
   本节说明 Normal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma nf_cast_irr {m n : nat} {X : B} (e e' : m = n) :
  id_cast (f_equal (fun i => nf i X) e)
    ≈ id_cast (f_equal (fun i => nf i X) e').
Proof. now rewrite (UIP_dec Nat.eq_dec e e'). Qed.

Lemma nf_cast_loop {m : nat} {X : B} (e : m = m) :
  id_cast (f_equal (fun i => nf i X) e) ≈ id.
Proof. rewrite (UIP_dec Nat.eq_dec e eq_refl); reflexivity. Qed.

Lemma nf_cast_trans {m n k : nat} {X : B} (e1 : m = n) (e2 : n = k) :
  id_cast (f_equal (fun i => nf i X) e2)
    ∘ id_cast (f_equal (fun i => nf i X) e1)
    ≈ id_cast (f_equal (fun i => nf i X) (eq_trans e1 e2)).
Proof.
  destruct e1, e2.
  change (id[nf m X] ∘ id[nf m X] ≈ id[nf m X]).
  now rewrite id_left.
Qed.

Lemma nf_cast_succ {m n : nat} {X : B} (e : m = n) :
  id_cast (f_equal (fun i => nf i X) (f_equal S e))
    ≈ bimap id[b] (id_cast (f_equal (fun i => nf i X) e)).
Proof.
  destruct e.
  change (id[(b ⨂ nf m X)%object] ≈ bimap id[b] id[nf m X]).
  symmetry; apply bimap_id_id.
Qed.

(* Casting commutes with the join. *)
Lemma J_cast {m m' n n' : nat} {X : B} (p : m = m') (q : n = n') :
  id_cast (f_equal (fun i => nf i X) (f_equal2 Nat.add p q)) ∘ to (J m n X)
    ≈ to (J m' n' X)
        ∘ bimap (id_cast (f_equal (fun i => nf i I) p))
                (id_cast (f_equal (fun i => nf i X) q)).
Proof.
  (* [f_equal2] is opaque (Qed) in the stdlib, so after [destruct] its result
     does not reduce to [eq_refl] — but it is still a LOOP equality, which
     [nf_cast_loop] handles through nat-UIP. *)
  destruct p, q.
  rewrite nf_cast_loop, id_left.
  change (to (J m n X) ≈ to (J m n X) ∘ bimap id[nf m I] id[nf n X]).
  now rewrite bimap_id_id, id_right.
Qed.

(** ** Where the coherence of B is spent *)

(* Associativity of the join: joining (m + m') then n agrees with joining m
   then (m' + n), up to the nat-level reassociation cast.  Induction on [m];
   the inductive step is the PENTAGON. *)
Theorem J_assoc (m m' n : nat) (X : B) :
  to (J (m + m') n X) ∘ bimap (to (J m m' I)) id[nf n X]
    ≈ id_cast (f_equal (fun i => nf i X) (Nat.add_assoc m m' n))
        ∘ to (J m (m' + n) X)
        ∘ bimap id[nf m I] (to (J m' n X))
        ∘ to (@tensor_assoc B _ (nf m I) (nf m' I) (nf n X)).
Proof.
  induction m; simpl.
  - (* Both outer joins are the left unitor and the cast is a loop; the
       residue is λ-naturality against J m' n X plus the left triangle. *)
    rewrite nf_cast_loop, id_left.
    rewrite <- (to_unit_left_natural (to (J m' n X))).
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    apply triangle_identity_left.
  - (*
   本节说明 Normal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    rewrite (UIP_dec Nat.eq_dec (Nat.add_assoc (S m) m' n)
               (f_equal S (Nat.add_assoc m m' n))).
    rewrite (@nf_cast_succ (m + (m' + n)) (m + m' + n) X
               (Nat.add_assoc m m' n)).
    normal.
    (* Right side: peel the associator across the (id ⨂ J m' n) factor. *)
    pose proof (to_tensor_assoc_natural
                  (id[b]) (id[nf m I]) (to (J m' n X))) as N1.
    rewrite bimap_id_id in N1.
    rewrite <- (comp_assoc _ (to tensor_assoc)
                  (bimap id (to (J m' n X)))).
    rewrite <- N1.
    (* Left side: split the bimap-of-composite, then peel its associator. *)
    rewrite (bimap_comp_id_right (bimap id[b] (to (J m m' I)))
                                 (to tensor_assoc)).
    rewrite (comp_assoc _ (bimap (bimap id[b] (to (J m m' I))) id)
                          (bimap (to tensor_assoc) id)).
    rewrite <- (comp_assoc _ (to tensor_assoc)
                  (bimap (bimap id[b] (to (J m m' I))) id)).
    pose proof (to_tensor_assoc_natural
                  (id[b]) (to (J m m' I)) (id[nf n X])) as N2.
    rewrite <- N2.
    normal.
    rewrite IHm.
    rewrite (bimap_comp_id_left _ (to tensor_assoc)).
    rewrite <- !comp_assoc.
    apply compose_respects; [ reflexivity |].
    rewrite !comp_assoc.
    apply pentagon_identity.
Qed.

(* The join with an empty tail is the right unitor.  Induction on [n]; the
   base is Kelly's λ_I ≈ ρ_I, the step is the (right) triangle. *)
Theorem J_right_unit (n : nat) :
  id_cast (f_equal (fun i => nf i I) (Nat.add_0_r n)) ∘ to (J n 0 I)
    ≈ to (@unit_right B _ (nf n I)).
Proof.
  induction n; simpl.
  - (*
   本节说明 Normal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
    rewrite (UIP_dec Nat.eq_dec (Nat.add_0_r 0) eq_refl).
    simpl.
    rewrite id_left.
    apply unit_identity.
  - (* Same implicit-index obstruction in the successor case; route the cast
       step through [apply] (full conversion) instead of [rewrite]. *)
    etransitivity.
    { apply compose_respects.
      - rewrite (UIP_dec Nat.eq_dec (Nat.add_0_r (S n))
                   (f_equal S (Nat.add_0_r n))).
        apply nf_cast_succ.
      - reflexivity. }
    normal.
    rewrite IHn.
    symmetry; apply bimap_triangle_right.
Qed.

(** ** Acceptance tests *)

(* Substitution is definitional. *)
Example subst_mix : subst (WT (WT WI WE) WI) = ((b ⨂ I) ⨂ b)%object := eq_refl.

(* The normal form of length 3, and its agreement with the normalised word. *)
Example nf_3 : nf 3 I = (b ⨂ (b ⨂ (b ⨂ I)))%object := eq_refl.
Example subst_nfword_3 : subst (nfword 3) = nf 3 I := eq_refl.

End Normal.
