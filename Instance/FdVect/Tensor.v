(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.QArith.QArith.
Require Import Coq.Vectors.Fin.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FdVect.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

Section Tensor.

Context (F : FieldObject).

(* 相关说明。 （已译） *)
Notation FR := (field_ring F).

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* A sum over Fin.t (a + b) splits 进入 two blocks cut out by
 [Fin.L] [Fin.R]. Both index shifts reduce judgmentally, so the
 induction needs no transport. （已译） *)
Lemma fin_sum_split (a b : nat)
  (h : Fin.t (a + b) → carrier (rig_setoid F)) :
  fin_sum FR h
    ≈ rig_add F (fin_sum FR (fun i : Fin.t a => h (Fin.L b i)))
                (fin_sum FR (fun j : Fin.t b => h (Fin.R a j))).
Proof.
  revert h.
  induction a as [| a' IH]; intro h; simpl.
  - now rewrite rig_add_zero_l.
  - rewrite (IH (fun x : Fin.t (a' + b) => h (Fin.FS x))).
    now rewrite rig_add_assoc.
Qed.

(* 相关说明。 （已译） *)
Lemma fin_sum_pair (m n : nat)
  (h : Fin.t (m * n) → carrier (rig_setoid F)) :
  fin_sum FR h
    ≈ fin_sum FR (fun i : Fin.t m =>
        fin_sum FR (fun j : Fin.t n => h (fin_pair i j))).
Proof.
  revert h.
  induction m as [| m' IH]; intro h; simpl.
  - reflexivity.
  - rewrite (fin_sum_split n (m' * n) h).
    apply rig_add_respects; [ reflexivity |].
    apply (IH (fun q : Fin.t (m' * n) => h (Fin.R n q))).
Qed.

(* The codec is injective, by its own round trip. *)
Lemma fin_pair_inj {m n : nat} (i k : Fin.t m) (j l : Fin.t n) :
  fin_pair i j = fin_pair k l → (i = k) * (j = l).
Proof.
  intro H.
  pose proof (f_equal (@fin_unpair m n) H) as Hp.
  rewrite !fin_unpair_pair in Hp.
  exact (f_equal fst Hp, f_equal snd Hp).
Qed.

(* 相关说明。 （已译） *)
Lemma delta_pair {m n : nat} (i k : Fin.t m) (j l : Fin.t n) :
  delta FR (fin_pair i j) (fin_pair k l)
    ≈ rig_mul F (delta FR i k) (delta FR j l).
Proof.
  destruct (Fin.eq_dec i k) as [Hik | Hik];
  destruct (Fin.eq_dec j l) as [Hjl | Hjl].
  - subst.
    rewrite !delta_refl.
    now rewrite rig_mul_one_l.
  - rewrite (delta_neq FR j l Hjl).
    rewrite rig_mul_zero_r.
    apply delta_neq.
    intro Hc.
    exact (Hjl (snd (fin_pair_inj i k j l Hc))).
  - rewrite (delta_neq FR i k Hik).
    rewrite rig_mul_zero_l.
    apply delta_neq.
    intro Hc.
    exact (Hik (fst (fin_pair_inj i k j l Hc))).
  - rewrite (delta_neq FR i k Hik).
    rewrite rig_mul_zero_l.
    apply delta_neq.
    intro Hc.
    exact (Hik (fst (fin_pair_inj i k j l Hc))).
Qed.

(* 相关说明。 （已译） *)
Lemma delta_unpair {m n : nat} (a b : Fin.t (m * n)) :
  rig_mul F (delta FR (fst (fin_unpair a)) (fst (fin_unpair b)))
            (delta FR (snd (fin_unpair a)) (snd (fin_unpair b)))
    ≈ delta FR a b.
Proof.
  transitivity (delta FR
    (fin_pair (fst (fin_unpair a)) (snd (fin_unpair a)))
    (fin_pair (fst (fin_unpair b)) (snd (fin_unpair b)))).
  - symmetry; apply delta_pair.
  - now rewrite !fin_pair_unpair.
Qed.

(* 相关说明。 （已译） *)
Lemma fin_sum_pair_mul (m n : nat)
  (h1 : Fin.t m → carrier (rig_setoid F))
  (h2 : Fin.t n → carrier (rig_setoid F)) :
  fin_sum FR (fun p => rig_mul F (h1 (fst (fin_unpair p)))
                                 (h2 (snd (fin_unpair p))))
    ≈ rig_mul F (fin_sum FR h1) (fin_sum FR h2).
Proof.
  rewrite (fin_sum_pair m n
    (fun p => rig_mul F (h1 (fst (fin_unpair p)))
                        (h2 (snd (fin_unpair p))))).
  rewrite (fin_sum_mul_r FR (fin_sum FR h2) h1).
  apply fin_sum_respects; intro i.
  rewrite (fin_sum_mul_l FR (h1 i) h2).
  apply fin_sum_respects; intro j.
  now rewrite fin_unpair_pair.
Qed.

(* 相关说明。 （已译） *)

Lemma mul_shuffle4 (a b c d : carrier (rig_setoid F)) :
  rig_mul F (rig_mul F a b) (rig_mul F c d)
    ≈ rig_mul F (rig_mul F a c) (rig_mul F b d).
Proof.
  rewrite (rig_mul_assoc F a b (rig_mul F c d)).
  rewrite <- (rig_mul_assoc F b c d).
  rewrite (field_comm F b c).
  rewrite (rig_mul_assoc F c b d).
  rewrite <- (rig_mul_assoc F a c (rig_mul F b d)).
  reflexivity.
Qed.

Lemma mul_swap_left (a b c : carrier (rig_setoid F)) :
  rig_mul F a (rig_mul F b c) ≈ rig_mul F b (rig_mul F a c).
Proof.
  rewrite <- (rig_mul_assoc F a b c).
  rewrite (field_comm F a b).
  apply rig_mul_assoc.
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The i-th basis vector V: expansion i-th standard
 tuple. A based 对象 exactly one makes sense. （已译） *)
Definition bvec (V : FdVectObject F) (i : Fin.t (fdv_dim V)) :
  carrier (cmon_setoid (fdv_mod V)) :=
  fdv_expand V (std_basis F (fdv_dim V) i).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coord_msum (V : FdVectObject F) {p : nat}
  (g : Fin.t p → carrier (cmon_setoid (fdv_mod V)))
  (k : Fin.t (fdv_dim V)) :
  fdv_coord V (msum (fdv_mod V) g) k
    ≈ fin_sum FR (fun t => fdv_coord V (g t) k).
Proof.
  revert g.
  induction p as [| p' IH]; intros g; simpl.
  - apply fdv_coord_zero.
  - rewrite (fdv_coord_plus V (g Fin.F1)
      (msum (fdv_mod V) (fun i => g (Fin.FS i))) k).
    apply rig_add_respects; [ reflexivity |].
    apply (IH (fun i => g (Fin.FS i))).
Qed.

(* Coordinates jointly injective — they ARE 同构 onto
 F^n — so agreeing at every index agreeing. （已译） *)
Lemma coord_ext (V : FdVectObject F)
  (v w : carrier (cmon_setoid (fdv_mod V))) :
  (∀ k, fdv_coord V v k ≈ fdv_coord V w k) → v ≈ w.
Proof.
  intro H.
  transitivity (fdv_expand V (fdv_coord V v)).
  - symmetry; apply fdv_expand_coord.
  - transitivity (fdv_expand V (fdv_coord V w)).
    + apply fdv_expand_respects; exact H.
    + apply fdv_expand_coord.
Qed.

(* 相关说明。 （已译） *)
Lemma vec_expansion (V : FdVectObject F)
  (v : carrier (cmon_setoid (fdv_mod V))) :
  v ≈ msum (fdv_mod V)
        (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)).
Proof.
  apply coord_ext; intro k.
  rewrite (coord_msum V
    (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)) k).
  transitivity (fin_sum FR
    (fun i => rig_mul F (fdv_coord V v i) (delta FR i k))).
  - symmetry; apply (fin_sum_delta_r FR k (fdv_coord V v)).
  - apply fin_sum_respects; intro i.
    symmetry.
    rewrite (fdv_coord_smul V (fdv_coord V v i) (bvec V i) k).
    apply rig_mul_respects; [ reflexivity |].
    unfold bvec, std_basis.
    rewrite (fdv_coord_expand V (std_basis F (fdv_dim V) i) k).
    apply delta_sym.
Qed.

(* 相关说明。 （已译） *)
Definition fentry {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (i : Fin.t (fdv_dim V)) (k : Fin.t (fdv_dim W)) :
  carrier (rig_setoid F) :=
  fdv_coord W (cmon_map (rm_hom f) (bvec V i)) k.

Lemma fentry_respects {V W : FdVectObject F}
  (f g : V ~{FdVect F}~> W) (H : f ≈ g)
  (i : Fin.t (fdv_dim V)) (k : Fin.t (fdv_dim W)) :
  fentry f i k ≈ fentry g i k.
Proof.
  exact (fdv_coord_respects W _ _ (H (bvec V i)) k).
Qed.

(* The 恒等's table Kronecker delta — arguments in
 order, what pins orientation down. （已译） *)
Lemma fentry_id (V : FdVectObject F) (i k : Fin.t (fdv_dim V)) :
  fentry (@id (FdVect F) V) i k ≈ delta FR k i.
Proof.
  unfold fentry, bvec.
  apply (fdv_coord_expand V (std_basis F (fdv_dim V) i) k).
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_coords {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (v : carrier (cmon_setoid (fdv_mod V))) (k : Fin.t (fdv_dim W)) :
  fdv_coord W (cmon_map (rm_hom f) v) k
    ≈ fin_sum FR (fun i => rig_mul F (fdv_coord V v i) (fentry f i k)).
Proof.
  transitivity (fdv_coord W (cmon_map (rm_hom f)
    (msum (fdv_mod V)
       (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)))) k).
  { exact (fdv_coord_respects W _ _
      (proper_morphism (cmon_map (rm_hom f)) _ _ (vec_expansion V v)) k). }
  transitivity (fdv_coord W (msum (fdv_mod W)
    (fun i => cmon_map (rm_hom f)
       (rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i)))) k).
  { exact (fdv_coord_respects W _ _
      (msum_hom (rm_hom f)
         (fun i => rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i))) k). }
  rewrite (coord_msum W
    (fun i => cmon_map (rm_hom f)
       (rm_smul (fdv_mod V) (fdv_coord V v i) (bvec V i))) k).
  apply fin_sum_respects; intro i.
  transitivity (fdv_coord W (rm_smul (fdv_mod W) (fdv_coord V v i)
    (cmon_map (rm_hom f) (bvec V i))) k).
  { exact (fdv_coord_respects W _ _
      (rm_map_smul f (fdv_coord V v i) (bvec V i)) k). }
  apply (fdv_coord_smul W (fdv_coord V v i)
    (cmon_map (rm_hom f) (bvec V i)) k).
Qed.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fentry_comp {V W X : FdVectObject F}
  (f : V ~{FdVect F}~> W) (g : W ~{FdVect F}~> X)
  (i : Fin.t (fdv_dim V)) (k : Fin.t (fdv_dim X)) :
  fentry (g ∘ f) i k
    ≈ fin_sum FR (fun j => rig_mul F (fentry f i j) (fentry g j k)).
Proof.
  exact (hom_coords g (cmon_map (rm_hom f) (bvec V i)) k).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition TensorSq_obj (V : FdVectObject F) : FdVectObject F :=
  StdVect F (fdv_dim V * fdv_dim V).

(* 相关说明。 （已译） *)
Definition tsq_ker {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (p : Fin.t (fdv_dim V * fdv_dim V))
  (q : Fin.t (fdv_dim W * fdv_dim W)) : carrier (rig_setoid F) :=
  rig_mul F (fentry f (fst (fin_unpair p)) (fst (fin_unpair q)))
            (fentry f (snd (fin_unpair p)) (snd (fin_unpair q))).

Definition tsq_map {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim W * fdv_dim W)) : carrier (rig_setoid F) :=
  fin_sum FR (fun p => rig_mul F (t p) (tsq_ker f p q)).

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma tsq_map_respects {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (t u : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (H : ∀ p, t p ≈ u p) (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f t q ≈ tsq_map f u q.
Proof.
  apply fin_sum_respects; intro p.
  apply rig_mul_respects; [ exact (H p) | reflexivity ].
Qed.

Lemma tsq_map_zero {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f (fun _ => rig_zero F) q ≈ rig_zero F.
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR
    (fun _ : Fin.t (fdv_dim V * fdv_dim V) => rig_zero F)).
  - apply fin_sum_respects; intro p.
    apply rig_mul_zero_l.
  - apply fin_sum_zero.
Qed.

Lemma tsq_map_plus {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (t u : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f (fun p => rig_add F (t p) (u p)) q
    ≈ rig_add F (tsq_map f t q) (tsq_map f u q).
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR (fun p =>
    rig_add F (rig_mul F (t p) (tsq_ker f p q))
              (rig_mul F (u p) (tsq_ker f p q)))).
  - apply fin_sum_respects; intro p.
    apply rig_distr_r.
  - apply fin_sum_add.
Qed.

Lemma tsq_map_smul {V W : FdVectObject F} (f : V ~{FdVect F}~> W)
  (r : carrier (rig_setoid F))
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim W * fdv_dim W)) :
  tsq_map f (fun p => rig_mul F r (t p)) q
    ≈ rig_mul F r (tsq_map f t q).
Proof.
  unfold tsq_map.
  rewrite (fin_sum_mul_l FR r
    (fun p => rig_mul F (t p) (tsq_ker f p q))).
  apply fin_sum_respects; intro p.
  apply rig_mul_assoc.
Qed.

(* * *** The two 函子 laws have content （已译） *)

(* The 恒等's Kronecker square 恒等: two deltas fuse
 one [delta_unpair], sum then collapses. （已译） *)
Lemma tsq_map_id (V : FdVectObject F)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  tsq_map (@id (FdVect F) V) t q ≈ t q.
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR (fun p => rig_mul F (t p) (delta FR p q))).
  - apply fin_sum_respects; intro p.
    apply rig_mul_respects; [ reflexivity |].
    unfold tsq_ker.
    transitivity (rig_mul F
      (delta FR (fst (fin_unpair q)) (fst (fin_unpair p)))
      (delta FR (snd (fin_unpair q)) (snd (fin_unpair p)))).
    + apply rig_mul_respects; apply fentry_id.
    + transitivity (delta FR q p).
      * apply delta_unpair.
      * apply delta_sym.
  - apply (fin_sum_delta_r FR q t).
Qed.

(* 相关说明。 （已译） *)
Lemma tsq_map_comp {V W X : FdVectObject F}
  (f : V ~{FdVect F}~> W) (g : W ~{FdVect F}~> X)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim X * fdv_dim X)) :
  tsq_map (g ∘ f) t q ≈ tsq_map g (tsq_map f t) q.
Proof.
  unfold tsq_map.
  symmetry.
  transitivity (fin_sum FR (fun s => fin_sum FR (fun p =>
    rig_mul F (rig_mul F (t p) (tsq_ker f p s)) (tsq_ker g s q)))).
  { apply fin_sum_respects; intro s.
    apply (fin_sum_mul_r FR (tsq_ker g s q)
      (fun p => rig_mul F (t p) (tsq_ker f p s))). }
  transitivity (fin_sum FR (fun p => fin_sum FR (fun s =>
    rig_mul F (rig_mul F (t p) (tsq_ker f p s)) (tsq_ker g s q)))).
  { apply fin_sum_swap. }
  apply fin_sum_respects; intro p.
  transitivity (fin_sum FR (fun s => rig_mul F (t p) (rig_mul F
    (rig_mul F (fentry f (fst (fin_unpair p)) (fst (fin_unpair s)))
               (fentry g (fst (fin_unpair s)) (fst (fin_unpair q))))
    (rig_mul F (fentry f (snd (fin_unpair p)) (snd (fin_unpair s)))
               (fentry g (snd (fin_unpair s)) (snd (fin_unpair q))))))).
  { apply fin_sum_respects; intro s.
    unfold tsq_ker.
    etransitivity; [ apply rig_mul_assoc |].
    apply rig_mul_respects; [ reflexivity |].
    apply mul_shuffle4. }
  transitivity (rig_mul F (t p) (fin_sum FR (fun s => rig_mul F
    (rig_mul F (fentry f (fst (fin_unpair p)) (fst (fin_unpair s)))
               (fentry g (fst (fin_unpair s)) (fst (fin_unpair q))))
    (rig_mul F (fentry f (snd (fin_unpair p)) (snd (fin_unpair s)))
               (fentry g (snd (fin_unpair s)) (snd (fin_unpair q))))))).
  { symmetry; apply fin_sum_mul_l. }
  apply rig_mul_respects; [ reflexivity |].
  etransitivity.
  { apply (fin_sum_pair_mul (fdv_dim W) (fdv_dim W)
      (fun j => rig_mul F (fentry f (fst (fin_unpair p)) j)
                          (fentry g j (fst (fin_unpair q))))
      (fun j => rig_mul F (fentry f (snd (fin_unpair p)) j)
                          (fentry g j (snd (fin_unpair q))))). }
  unfold tsq_ker.
  apply rig_mul_respects; symmetry; apply fentry_comp.
Qed.

(* * *** The packaged 态射 函子 （已译） *)

Definition tsq_hom {V W : FdVectObject F} (f : V ~{FdVect F}~> W) :
  TensorSq_obj V ~{FdVect F}~> TensorSq_obj W.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F)
       (std_mod F (fdv_dim V * fdv_dim V))
       (std_mod F (fdv_dim W * fdv_dim W))
       (@Build_CMonHom (std_cmon F (fdv_dim V * fdv_dim V))
                       (std_cmon F (fdv_dim W * fdv_dim W))
          (@Build_SetoidMorphism _ _ _ _ (tsq_map f) _) _ _) _).
  - intros t u H q; exact (tsq_map_respects f t u H q).
  - intro q; exact (tsq_map_zero f q).
  - intros t u q; exact (tsq_map_plus f t u q).
  - intros r t q; exact (tsq_map_smul f r t q).
Defined.

Program Definition TensorSq : FdVect F ⟶ FdVect F := {|
  fobj := TensorSq_obj;
  fmap := fun V W f => tsq_hom f
|}.
Next Obligation.
  intros V W f g H t q.
  apply fin_sum_respects; intro p.
  apply rig_mul_respects; [ reflexivity |].
  apply rig_mul_respects; apply fentry_respects; exact H.
Qed.
Next Obligation.
  intros V t q.
  apply tsq_map_id.
Qed.
Next Obligation.
  intros V W X f g t q.
  apply tsq_map_comp.
Qed.

(* 相关说明。 （已译） *)

(* Multiplication by a scalar.  It is a map of F-modules only because F
   is COMMUTATIVE: [rm_map_smul] wants c·(r·v) ≈ r·(c·v), which is
   [rm_smul_assoc] twice around one [field_comm]. *)
Definition scale (c : carrier (rig_setoid F)) (V : FdVectObject F) :
  V ~{FdVect F}~> V.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (fdv_mod V) (fdv_mod V)
       (@Build_CMonHom (fdv_mod V) (fdv_mod V)
          (@Build_SetoidMorphism _ _ _ _
             (rm_smul (fdv_mod V) c) _) _ _) _).
  - intros v w Hvw; now rewrite Hvw.
  - apply rm_smul_zero_r.
  - intros v w; apply rm_smul_distr_l.
  - intros r v.
    transitivity (rm_smul (fdv_mod V) (rig_mul F c r) v).
    + symmetry; apply rm_smul_assoc.
    + transitivity (rm_smul (fdv_mod V) (rig_mul F r c) v).
      * apply rm_smul_respects; [ apply field_comm | reflexivity ].
      * apply rm_smul_assoc.
Defined.

(* The scalar the argument runs at. *)
Definition two : carrier (rig_setoid F) := rig_add F (rig_one F) (rig_one F).

Lemma two_mul (x : carrier (rig_setoid F)) :
  rig_mul F two x ≈ rig_add F x x.
Proof.
  unfold two.
  transitivity (rig_add F (rig_mul F (rig_one F) x)
                          (rig_mul F (rig_one F) x)).
  - apply rig_distr_r.
  - apply rig_add_respects; apply rig_mul_one_l.
Qed.

(* 相关说明。 （已译） *)
Lemma add_idem_zero (b : carrier (rig_setoid F)) :
  rig_add F b b ≈ b → b ≈ rig_zero F.
Proof.
  intro H.
  transitivity (rig_add F (ring_neg F b) (rig_add F b b)).
  - transitivity (rig_add F (rig_add F (ring_neg F b) b) b).
    + transitivity (rig_add F (rig_zero F) b).
      * symmetry; apply rig_add_zero_l.
      * apply rig_add_respects; [| reflexivity ].
        symmetry; apply ring_neg_l.
    + apply rig_add_assoc.
  - transitivity (rig_add F (ring_neg F b) b).
    + apply rig_add_respects; [ reflexivity | exact H ].
    + apply ring_neg_l.
Qed.

(* Cancelling 2. THIS where [finv]/[finv_l] become load-bearing
 — see header — it place file where the
 characteristic 假设 consumed. （已译） *)
Lemma double_zero (two_nz : two ≈ rig_zero F → False)
  (x : carrier (rig_setoid F)) :
  rig_mul F two x ≈ rig_zero F → x ≈ rig_zero F.
Proof.
  intro H.
  transitivity (rig_mul F (rig_one F) x).
  - symmetry; apply rig_mul_one_l.
  - transitivity (rig_mul F (rig_mul F (finv F two) two) x).
    + apply rig_mul_respects; [| reflexivity ].
      symmetry; exact (finv_l F two two_nz).
    + transitivity (rig_mul F (finv F two) (rig_mul F two x)).
      * apply rig_mul_assoc.
      * transitivity (rig_mul F (finv F two) (rig_zero F)).
        -- apply rig_mul_respects; [ reflexivity | exact H ].
        -- apply rig_mul_zero_r.
Qed.

(* The whole scaling argument, as arithmetic: 4a ≈ 2a forces a ≈ 0. *)
Lemma square_fixes_zero (two_nz : two ≈ rig_zero F → False)
  (a : carrier (rig_setoid F)) :
  rig_mul F (rig_mul F two two) a ≈ rig_mul F two a → a ≈ rig_zero F.
Proof.
  intro H.
  apply (double_zero two_nz).
  apply add_idem_zero.
  transitivity (rig_mul F two (rig_mul F two a)).
  - symmetry; apply two_mul.
  - transitivity (rig_mul F (rig_mul F two two) a).
    + symmetry; apply rig_mul_assoc.
    + exact H.
Qed.

(* 相关说明。 （已译） *)

Lemma fentry_scale (c : carrier (rig_setoid F)) (V : FdVectObject F)
  (i k : Fin.t (fdv_dim V)) :
  fentry (scale c V) i k ≈ rig_mul F c (delta FR k i).
Proof.
  unfold fentry.
  transitivity (rig_mul F c (fdv_coord V (bvec V i) k)).
  - apply (fdv_coord_smul V c (bvec V i) k).
  - apply rig_mul_respects; [ reflexivity |].
    unfold bvec.
    apply (fdv_coord_expand V (std_basis F (fdv_dim V) i) k).
Qed.

Lemma tsq_ker_scale (c : carrier (rig_setoid F)) (V : FdVectObject F)
  (p q : Fin.t (fdv_dim V * fdv_dim V)) :
  tsq_ker (scale c V) p q ≈ rig_mul F (rig_mul F c c) (delta FR q p).
Proof.
  unfold tsq_ker.
  transitivity (rig_mul F
    (rig_mul F c (delta FR (fst (fin_unpair q)) (fst (fin_unpair p))))
    (rig_mul F c (delta FR (snd (fin_unpair q)) (snd (fin_unpair p))))).
  - apply rig_mul_respects; apply fentry_scale.
  - etransitivity; [ apply mul_shuffle4 |].
    apply rig_mul_respects; [ reflexivity |].
    apply delta_unpair.
Qed.

(* 相关说明。 （已译） *)
Lemma tsq_map_scale (c : carrier (rig_setoid F)) (V : FdVectObject F)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid F))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  tsq_map (scale c V) t q ≈ rig_mul F (rig_mul F c c) (t q).
Proof.
  unfold tsq_map.
  transitivity (fin_sum FR (fun p => rig_mul F (rig_mul F c c)
    (rig_mul F (t p) (delta FR p q)))).
  - apply fin_sum_respects; intro p.
    transitivity (rig_mul F (t p)
      (rig_mul F (rig_mul F c c) (delta FR p q))).
    + apply rig_mul_respects; [ reflexivity |].
      transitivity (rig_mul F (rig_mul F c c) (delta FR q p)).
      * apply tsq_ker_scale.
      * apply rig_mul_respects; [ reflexivity | apply delta_sym ].
    + apply mul_swap_left.
  - transitivity (rig_mul F (rig_mul F c c)
      (fin_sum FR (fun p => rig_mul F (t p) (delta FR p q)))).
    + symmetry; apply fin_sum_mul_l.
    + apply rig_mul_respects; [ reflexivity |].
      apply (fin_sum_delta_r FR q t).
Qed.

(* 相关说明。 （已译） *)

(* The zero 态射 V → V ⊗ V, written out so 定理 below
 can say "the component IS this" rather than "every value zero". （已译） *)
Definition tsq_zero (V : FdVectObject F) :
  V ~{FdVect F}~> TensorSq_obj V.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (fdv_mod V)
       (std_mod F (fdv_dim V * fdv_dim V))
       (@Build_CMonHom (fdv_mod V)
                       (std_cmon F (fdv_dim V * fdv_dim V))
          (@Build_SetoidMorphism _ _ _ _
             (fun _ (_ : Fin.t (fdv_dim V * fdv_dim V)) =>
                rig_zero F) _) _ _) _).
  - intros v w Hvw q; reflexivity.
  - intro q; reflexivity.
  - intros v w q; symmetry; apply rig_add_zero_l.
  - intros r v q; symmetry; apply rig_mul_zero_r.
Defined.

(* The zero family IS natural, so 定理 below classifies a
 NONEMPTY collection: it says zero transformation only
 one, not there none. （已译） *)
Program Definition tsq_zero_transform : Id[FdVect F] ⟹ TensorSq := {|
  transform := fun V => tsq_zero V
|}.
Next Obligation.
  intros V W f v q.
  apply tsq_map_zero.
Qed.
Next Obligation.
  intros V W f v q.
  symmetry; apply tsq_map_zero.
Qed.

(*
   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem diag_transform_zero (two_nz : two ≈ rig_zero F → False)
  (alpha : Id[FdVect F] ⟹ TensorSq) (V : FdVectObject F) :
  transform alpha V ≈ tsq_zero V.
Proof.
  intros v q.
  apply (square_fixes_zero two_nz).
  transitivity (tsq_map (scale two V)
    (cmon_map (rm_hom (transform alpha V)) v) q).
  - symmetry; apply tsq_map_scale.
  - transitivity (cmon_map (rm_hom (transform alpha V))
      (rm_smul (fdv_mod V) two v) q).
    + exact (naturality alpha V V (scale two V) v q).
    + exact (rm_map_smul (transform alpha V) two v q).
Qed.

(* The same statement read coordinatewise. *)
Corollary diag_transform_zero_coord
  (two_nz : two ≈ rig_zero F → False)
  (alpha : Id[FdVect F] ⟹ TensorSq) (V : FdVectObject F)
  (v : carrier (cmon_setoid (fdv_mod V)))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  cmon_map (rm_hom (transform alpha V)) v q ≈ rig_zero F.
Proof.
  exact (diag_transform_zero two_nz alpha V v q).
Qed.

End Tensor.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Q_two_nz : two Q_Field ≈ rig_zero Q_Field → False.
Proof.
  unfold two; simpl; unfold Qeq; simpl; discriminate.
Qed.

(** Riehl's example over ℚ: no nonzero 自然变换 the
 恒等 函子 finite-dimensional ℚ-vector spaces the
 diagonal square 函子. （已译） *)
Corollary diag_transform_zero_Q
  (alpha : Id[FdVect Q_Field] ⟹ TensorSq Q_Field)
  (V : FdVectObject Q_Field) :
  transform alpha V ≈ tsq_zero Q_Field V.
Proof.
  exact (diag_transform_zero Q_Field Q_two_nz alpha V).
Qed.

(** ** Acceptance tests *)

(* The 对象 realization: square two-dimensional space is
 four-dimensional, nose. （已译） *)
Example tensor_dim_two :
  fdv_dim (TensorSq_obj Q_Field (StdVect Q_Field 2)) = 4%nat := eq_refl.

(* 相关说明。 （已译） *)
Example fin_pair_anchor :
  @fin_pair 2 2 (Fin.FS Fin.F1) Fin.F1 = Fin.FS (Fin.FS (@Fin.F1 1))
  := eq_refl.

Example fin_unpair_anchor :
  @fin_unpair 2 2 (Fin.FS (Fin.FS (@Fin.F1 1))) = (Fin.FS Fin.F1, Fin.F1)
  := eq_refl.

(* The 函子 fixes every vector square at 恒等. （已译） *)
Example tsq_id_fixes (V : FdVectObject Q_Field)
  (t : Fin.t (fdv_dim V * fdv_dim V) → carrier (rig_setoid Q_Field))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  cmon_map (rm_hom (fmap[TensorSq Q_Field] (@id (FdVect Q_Field) V))) t q
    ≈ t q.
Proof. apply tsq_map_id. Qed.

(* The zero morphism really is zero, at open arguments. *)
Example tsq_zero_value (V : FdVectObject Q_Field)
  (v : carrier (cmon_setoid (fdv_mod V)))
  (q : Fin.t (fdv_dim V * fdv_dim V)) :
  cmon_map (rm_hom (tsq_zero Q_Field V)) v q = rig_zero Q_Field := eq_refl.

(* 相关说明。 （已译） *)
Example fentry_swap_01 :
  fentry Q_Field (std_reindex Q_Field fin2_swap) Fin.F1 (Fin.FS Fin.F1)
    = 1%Q := eq_refl.

Example fentry_swap_00 :
  fentry Q_Field (std_reindex Q_Field fin2_swap) Fin.F1 Fin.F1
    = 0%Q := eq_refl.

(*
   本节说明 Tensor 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition qt4 : Fin.t (2 * 2) → carrier (rig_setoid Q_Field) :=
  fun p => fin2 (fin2 (5 # 1)%Q (6 # 1)%Q)
                (fin2 (7 # 1)%Q (8 # 1)%Q)
             (fst (fin_unpair p)) (snd (fin_unpair p)).

(* Position 0 is (0, 0); its image pulls back from (1, 1), entry 8. *)
Example tsq_swap_00 :
  tsq_map Q_Field (std_reindex Q_Field fin2_swap) qt4 Fin.F1
    = (8 # 1)%Q := eq_refl.

(* Position 1 is (0, 1); its image pulls back from (1, 0), entry 7. *)
Example tsq_swap_01 :
  tsq_map Q_Field (std_reindex Q_Field fin2_swap) qt4 (Fin.FS Fin.F1)
    = (7 # 1)%Q := eq_refl.
