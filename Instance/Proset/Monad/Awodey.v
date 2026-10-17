Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * Awodey's 伴随 closure operator （已译） *)

(*
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,

   本文件给出单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition ClosedElt@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) : Type@{u} :=
  { x : A | R (cl_fun c x) x }.

Definition closed_le@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) : relation (ClosedElt c) :=
  fun a b => R (proj1_sig a) (proj1_sig b).

Definition closed_PreOrder@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) : PreOrder (closed_le c) :=
  {| PreOrder_Reflexive  := fun a => @PreOrder_Reflexive A R P (proj1_sig a)
   ; PreOrder_Transitive := fun a b d (H1 : closed_le c a b)
                                (H2 : closed_le c b d) =>
       @PreOrder_Transitive A R P _ _ _ H1 H2 |}.

(** ** Awodey's t and i *)

(* t : P → K, the factorisation of cl through K. *)
Definition closed_t@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (x : A) : ClosedElt c :=
  exist _ (cl_fun c x) (cl_mult c x).

(* i : K → P, the inclusion. *)
Definition closed_i@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (k : ClosedElt c) : A :=
  proj1_sig k.

(* Awodey's two 蕴含, unit counit inequalities. （已译） *)
Definition closed_galois@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  GaloisConnection R (closed_le c) :=
  galois_of_unit_counit P (closed_PreOrder c) (closed_t c) (closed_i c)
    (fun a a' h => mono_pres (cl_fun c) a a' h)
    (fun b b' h => h)
    (fun a => cl_ext c a)
    (fun b => proj2_sig b).

(* t ⊣ i. *)
Definition closed_adj@{u h s a | h < s +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (c : ClosureOperator@{u} P) :=
  GaloisAdjunction@{u u s a h} P (closed_PreOrder c) (closed_galois c).

(* * ** T = i ∘ t, induced 单子 T （已译） *)

(* T = i ∘ t on objects, on the nose. *)
Example closed_factorisation_obj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (x : A) :
  fobj[GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
       ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)] x
    = cl_fun c x := eq_refl.

(* 相关说明。 （已译） *)
Example closed_factorisation_fmap@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (x y : A) (f : R x y) :
  fmap[GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
       ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)] f
    = fmap[closure_functor@{u h} c] f := eq_refl.

(* The induced 单子, read back closure operator, has c's monotone
 map nose. （已译） *)
Example closed_induced_is_c@{u h s a | h < s +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (c : ClosureOperator@{u} P) :
  cl_fun (closure_of_monad _
            (MM := Adjunction_Induced_Monad (closed_adj@{u h s a} c)))
    = cl_fun c := eq_refl.

(* i ◯ t closure 函子, 恒等 components. （已译） *)
Lemma closed_induced_functor@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
    ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)
    ≈ closure_functor@{u h} c.
Proof. exists (fun x => iso_id). intros; exact I. Qed.

(* 相关说明。 （已译） *)

(* t (i k) has first component cl k... *)
Example closed_tik_fst@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (k : ClosedElt c) :
  proj1_sig (closed_t c (closed_i c k)) = cl_fun c (proj1_sig k)
  := eq_refl.

(* ...and is isomorphic to k in K... *)
Definition closed_tik_iso@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (k : ClosedElt c) :
  closed_t c (closed_i c k) ≅[Proset@{u h} (closed_PreOrder c)] k :=
  @Build_Isomorphism (Proset@{u h} (closed_PreOrder c))
    (closed_t c (closed_i c k)) k (proj2_sig k) (cl_ext c (proj1_sig k)) I I.

(* ...and equal to k on first components under antisymmetry. *)
Lemma closed_tik_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (c : ClosureOperator@{u} P)
  (k : ClosedElt c) :
  proj1_sig (closed_t c (closed_i c k)) = proj1_sig k.
Proof. exact (AS _ _ (proj2_sig k) (cl_ext c (proj1_sig k))). Qed.
