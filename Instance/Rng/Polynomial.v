Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Book: Riehl, "Category Theory in Context", 2nd ed., §2.1
 Book: Riehl, ibid., §2.3 Example 2.3.4, printed p. 68 — the same in
 nLab:      https://ncatlab.org/nlab/show/polynomial+ring
 nLab:      https://ncatlab.org/nlab/show/free+functor
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Polynomial_ring

   本文件给出多项式函子相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma rng_mul_neg_r (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R a (ring_neg R b) ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_l.
  rewrite (ring_neg_l R b).
  apply rig_mul_zero_r.
Qed.

Lemma rng_mul_neg_l (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R a) b ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_r.
  rewrite (ring_neg_l R a).
  apply rig_mul_zero_l.
Qed.

Section Polynomial.

Context (K : RingObject).

(** ** Formal polynomial expressions *)

Inductive PTerm : Type :=
  | pt_const : carrier (rig_setoid K) → PTerm
  | pt_x     : PTerm
  | pt_add   : PTerm → PTerm → PTerm
  | pt_neg   : PTerm → PTerm
  | pt_mul   : PTerm → PTerm → PTerm.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive pt_eq : PTerm → PTerm → Prop :=
  (* congruence for each former, saturating under K's own [≈] *)
  | pe_const {a b} : a ≈ b → pt_eq (pt_const a) (pt_const b)
  | pe_add {s s' t t'} :
      pt_eq s s' → pt_eq t t' → pt_eq (pt_add s t) (pt_add s' t')
  | pe_neg {s s'} : pt_eq s s' → pt_eq (pt_neg s) (pt_neg s')
  | pe_mul {s s' t t'} :
      pt_eq s s' → pt_eq t t' → pt_eq (pt_mul s t) (pt_mul s' t')

  (* abelian group under addition *)
  | pe_add_assoc s t u :
      pt_eq (pt_add (pt_add s t) u) (pt_add s (pt_add t u))
  | pe_add_comm s t : pt_eq (pt_add s t) (pt_add t s)
  | pe_add_zero_l s : pt_eq (pt_add (pt_const (rig_zero K)) s) s
  | pe_add_neg_l s : pt_eq (pt_add (pt_neg s) s) (pt_const (rig_zero K))

  (* commutative monoid under multiplication *)
  | pe_mul_assoc s t u :
      pt_eq (pt_mul (pt_mul s t) u) (pt_mul s (pt_mul t u))
  | pe_mul_comm s t : pt_eq (pt_mul s t) (pt_mul t s)
  | pe_mul_one_l s : pt_eq (pt_mul (pt_const (rig_one K)) s) s

  (* 相关说明。 （已译） *)
  | pe_distr_l s t u :
      pt_eq (pt_mul s (pt_add t u)) (pt_add (pt_mul s t) (pt_mul s u))

  (* the coefficient inclusion is a homomorphism of rings *)
  | pe_const_add a b :
      pt_eq (pt_const (rig_add K a b)) (pt_add (pt_const a) (pt_const b))
  | pe_const_mul a b :
      pt_eq (pt_const (rig_mul K a b)) (pt_mul (pt_const a) (pt_const b))

  | pe_sym {s t} : pt_eq s t → pt_eq t s
  | pe_trans {s t u} : pt_eq s t → pt_eq t u → pt_eq s u.

Lemma pt_refl (s : PTerm) : pt_eq s s.
Proof.
  induction s.
  - exact (pe_const (reflexivity _)).
  - exact (pe_trans (pe_sym (pe_add_zero_l pt_x)) (pe_add_zero_l pt_x)).
  - exact (pe_add IHs1 IHs2).
  - exact (pe_neg IHs).
  - exact (pe_mul IHs1 IHs2).
Qed.

Lemma pt_eq_Equivalence : Equivalence pt_eq.
Proof.
  constructor.
  - exact pt_refl.
  - exact (fun s t => pe_sym).
  - exact (fun s t u => pe_trans).
Qed.

Definition pt_Setoid : Setoid PTerm := {|
  equiv        := pt_eq;
  setoid_equiv := pt_eq_Equivalence
|}.

(** ** Derived laws *)

Let PZ : PTerm := pt_const (rig_zero K).
Let PO : PTerm := pt_const (rig_one K).

Lemma pe_add_zero_r (s : PTerm) : pt_eq (pt_add s PZ) s.
Proof.
  exact (pe_trans (pe_add_comm s PZ) (pe_add_zero_l s)).
Qed.

Lemma pe_add_neg_r (s : PTerm) : pt_eq (pt_add s (pt_neg s)) PZ.
Proof.
  exact (pe_trans (pe_add_comm s (pt_neg s)) (pe_add_neg_l s)).
Qed.

Lemma pe_mul_one_r (s : PTerm) : pt_eq (pt_mul s PO) s.
Proof.
  exact (pe_trans (pe_mul_comm s PO) (pe_mul_one_l s)).
Qed.

Lemma pe_distr_r (s t u : PTerm) :
  pt_eq (pt_mul (pt_add s t) u) (pt_add (pt_mul s u) (pt_mul t u)).
Proof.
  refine (pe_trans (pe_mul_comm (pt_add s t) u) _).
  refine (pe_trans (pe_distr_l u s t) _).
  exact (pe_add (pe_mul_comm u s) (pe_mul_comm u t)).
Qed.

(* Cancellation: adding negative left what makes the
 annihilation law below 定理 rather than further constructor. （已译） *)
Lemma pe_add_cancel_l (s t u : PTerm) :
  pt_eq (pt_add s t) (pt_add s u) → pt_eq t u.
Proof.
  intro H.
  refine (pe_trans (pe_sym (pe_add_zero_l t)) _).
  refine (pe_trans (pe_add (pe_sym (pe_add_neg_l s)) (pt_refl t)) _).
  refine (pe_trans (pe_add_assoc (pt_neg s) s t) _).
  refine (pe_trans (pe_add (pt_refl (pt_neg s)) H) _).
  refine (pe_trans (pe_sym (pe_add_assoc (pt_neg s) s u)) _).
  refine (pe_trans (pe_add (pe_add_neg_l s) (pt_refl u)) _).
  exact (pe_add_zero_l u).
Qed.

Lemma pe_mul_zero_l (s : PTerm) : pt_eq (pt_mul PZ s) PZ.
Proof.
  (* 0·s ≈ (0+0)·s ≈ 0·s + 0·s, so 0·s ≈ 0 by cancellation. *)
  apply (pe_add_cancel_l (pt_mul PZ s)).
  refine (pe_trans (pe_sym (pe_distr_r PZ PZ s)) _).
  refine (pe_trans (pe_mul _ (pt_refl s)) (pe_sym (pe_add_zero_r (pt_mul PZ s)))).
  refine (pe_trans (pe_sym (pe_const_add (rig_zero K) (rig_zero K))) _).
  exact (pe_const (rig_add_zero_l K (rig_zero K))).
Qed.

Lemma pe_mul_zero_r (s : PTerm) : pt_eq (pt_mul s PZ) PZ.
Proof.
  exact (pe_trans (pe_mul_comm s PZ) (pe_mul_zero_l s)).
Qed.

(* The coefficient 含入 carries negation, uniqueness of
 additive inverses term ring. （已译） *)
Lemma pe_const_neg (a : carrier (rig_setoid K)) :
  pt_eq (pt_const (ring_neg K a)) (pt_neg (pt_const a)).
Proof.
  apply (pe_add_cancel_l (pt_const a)).
  refine (pe_trans _ (pe_sym (pe_add_neg_r (pt_const a)))).
  refine (pe_trans (pe_sym (pe_const_add a (ring_neg K a))) _).
  refine (pe_const _).
  refine (transitivity (rig_add_comm K a (ring_neg K a)) _).
  exact (ring_neg_l K a).
Qed.

(** ** The ring K[x] *)

Definition PolyRig : RigObject := {|
  rig_setoid := {| carrier := PTerm; is_setoid := pt_Setoid |};
  rig_zero := PZ;
  rig_add := pt_add;
  rig_one := PO;
  rig_mul := pt_mul;
  rig_add_respects := fun _ _ Hs _ _ Ht => pe_add Hs Ht;
  rig_mul_respects := fun _ _ Hs _ _ Ht => pe_mul Hs Ht;
  rig_add_assoc := pe_add_assoc;
  rig_add_comm := pe_add_comm;
  rig_add_zero_l := pe_add_zero_l;
  rig_mul_assoc := pe_mul_assoc;
  rig_mul_one_l := pe_mul_one_l;
  rig_mul_one_r := pe_mul_one_r;
  rig_distr_l := pe_distr_l;
  rig_distr_r := pe_distr_r;
  rig_mul_zero_l := pe_mul_zero_l;
  rig_mul_zero_r := pe_mul_zero_r;
  (* [pt_eq] IS [Prop]-valued 关系, so it own [Prop] 镜像 and
 both 蕴含 恒等. （已译） *)
  rig_prop := @PropEquiv_of_relation _ pt_Setoid pt_eq
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition PolyRing : RingObject := {|
  ring_rig := PolyRig;
  ring_neg := pt_neg;
  ring_neg_respects := fun _ _ Hs => pe_neg Hs;
  ring_neg_l := pe_add_neg_l
|}.

Lemma poly_comm : ∀ a b : carrier (rig_setoid PolyRing),
  rig_mul PolyRing a b ≈ rig_mul PolyRing b a.
Proof. exact pe_mul_comm. Qed.

(* * ** The coefficient 含入 indeterminate （已译） *)

Program Definition poly_const : K ~{Rng}~> PolyRing := {|
  rig_map := {| morphism := pt_const |}
|}.
Next Obligation. intros a b H; exact (pe_const H). Qed.
Next Obligation. simpl; exact (pt_refl PZ). Qed.
Next Obligation. intros a b; exact (pe_const_add a b). Qed.
Next Obligation. simpl; exact (pt_refl PO). Qed.
Next Obligation. intros a b; exact (pe_const_mul a b). Qed.

Definition poly_x : carrier (rig_setoid PolyRing) := pt_x.

End Polynomial.

Arguments PTerm {K}.
Arguments pt_const {K} a.
Arguments pt_x {K}.
Arguments pt_add {K} s t.
Arguments pt_neg {K} s.
Arguments pt_mul {K} s t.
Arguments pt_eq {K} s t.
Arguments pt_refl {K} s.
Arguments poly_x {K}.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Evaluation.

Context (K : RingObject).
Context (S : RingObject).
Context (phi : K ~{Rng}~> S).
Context (s : carrier (rig_setoid S)).

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Notation Kcomm_hyp :=
  (∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a).
Notation Hcs_hyp :=
  (∀ a : carrier (rig_setoid K),
     rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s).

Fixpoint peval (t : @PTerm K) : carrier (rig_setoid S) :=
  match t with
  | pt_const a => rig_map phi a
  | pt_x       => s
  | pt_add u v => rig_add S (peval u) (peval v)
  | pt_neg u   => ring_neg S (peval u)
  | pt_mul u v => rig_mul S (peval u) (peval v)
  end.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Lemma peval_comm_gen (a : carrier (rig_setoid S))
  (H1 : ∀ k, rig_mul S a (rig_map phi k) ≈ rig_mul S (rig_map phi k) a)
  (H2 : rig_mul S a s ≈ rig_mul S s a) (u : @PTerm K) :
  rig_mul S a (peval u) ≈ rig_mul S (peval u) a.
Proof.
  induction u as [ k | | u IHu v IHv | u IHu | u IHu v IHv ]; simpl.
  - exact (H1 k).
  - exact H2.
  - rewrite rig_distr_l, IHu, IHv; symmetry; apply rig_distr_r.
  - rewrite rng_mul_neg_r, IHu; symmetry; apply rng_mul_neg_l.
  - rewrite <- rig_mul_assoc, IHu, rig_mul_assoc, IHv.
    symmetry; apply rig_mul_assoc.
Qed.

(* The image of [phi] is commutative, because [K] is. *)
Lemma phi_image_comm (Kcomm : Kcomm_hyp) (k l : carrier (rig_setoid K)) :
  rig_mul S (rig_map phi k) (rig_map phi l)
    ≈ rig_mul S (rig_map phi l) (rig_map phi k).
Proof.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map phi)), Kcomm.
Qed.

Lemma peval_comm (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) (t u : @PTerm K) :
  rig_mul S (peval t) (peval u) ≈ rig_mul S (peval u) (peval t).
Proof.
  apply peval_comm_gen.
  - intro k.
    symmetry.
    exact (peval_comm_gen (rig_map phi k) (phi_image_comm Kcomm k)
             (symmetry (Hcs k)) t).
  - symmetry.
    exact (peval_comm_gen s Hcs (reflexivity _) t).
Qed.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma peval_respects (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) (t u : @PTerm K) :
  pt_eq t u → peval t ≈ peval u.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ a b Hab
    | t t' u u' _ IHt _ IHu
    | t t' _ IHt
    | t t' u u' _ IHt _ IHu
    | t u v | t u | t | t
    | t u v | t u | t
    | t u v
    | a b | a b
    | t u _ IHtu
    | t u v _ IHtu _ IHuv ]; simpl.
  - apply pequiv_from; exact (proper_morphism (rig_map phi) _ _ Hab).
  - apply pequiv_from.
    exact (rig_add_respects S _ _ (pequiv_to _ _ IHt)
                              _ _ (pequiv_to _ _ IHu)).
  - apply pequiv_from.
    exact (ring_neg_respects S _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (rig_mul_respects S _ _ (pequiv_to _ _ IHt)
                              _ _ (pequiv_to _ _ IHu)).
  - apply pequiv_from; exact (rig_add_assoc S _ _ _).
  - apply pequiv_from; exact (rig_add_comm S _ _).
  - apply pequiv_from; rewrite (rig_map_zero phi); apply rig_add_zero_l.
  - apply pequiv_from; rewrite (rig_map_zero phi); apply (ring_neg_l S).
  - apply pequiv_from; exact (rig_mul_assoc S _ _ _).
  - apply pequiv_from; exact (peval_comm Kcomm Hcs t u).
  - apply pequiv_from; rewrite (rig_map_one phi); apply rig_mul_one_l.
  - apply pequiv_from; exact (rig_distr_l S _ _ _).
  - apply pequiv_from; exact (rig_map_add phi a b).
  - apply pequiv_from; exact (rig_map_mul phi a b).
  - exact (symmetry IHtu).
  - exact (transitivity IHtu IHuv).
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition poly_extend (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp)
  : PolyRing K ~{Rng}~> S := {|
  rig_map := {| morphism := peval |}
|}.
Next Obligation.
  intros Kcomm Hcs t u He; exact (peval_respects Kcomm Hcs t u He).
Qed.
Next Obligation. intros Kcomm Hcs; simpl; exact (rig_map_zero phi). Qed.
Next Obligation. intros Kcomm Hcs t u; simpl; reflexivity. Qed.
Next Obligation. intros Kcomm Hcs; simpl; exact (rig_map_one phi). Qed.
Next Obligation. intros Kcomm Hcs t u; simpl; reflexivity. Qed.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example poly_extend_const (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp)
  (a : carrier (rig_setoid K)) :
  rig_map (poly_extend Kcomm Hcs) (pt_const a) = rig_map phi a := eq_refl.

Example poly_extend_x (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) :
  rig_map (poly_extend Kcomm Hcs) (@poly_x K) = s := eq_refl.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma poly_extend_unique (g : PolyRing K ~{Rng}~> S)
  (Hconst : ∀ a, rig_map g (pt_const a) ≈ rig_map phi a)
  (Hx : rig_map g (@poly_x K) ≈ s) (t : @PTerm K) :
  rig_map g t ≈ peval t.
Proof.
  induction t as [ a | | t IHt u IHu | t IHt | t IHt u IHu ]; simpl.
  - exact (Hconst a).
  - exact Hx.
  - rewrite (rig_map_add g t u); exact (rig_add_respects S _ _ IHt _ _ IHu).
  - rewrite (RigHom_neg (PolyRing K) S g t).
    exact (ring_neg_respects S _ _ IHt).
  - rewrite (rig_map_mul g t u); exact (rig_mul_respects S _ _ IHt _ _ IHu).
Qed.

End Evaluation.

Arguments peval {K S} phi s t.
Arguments poly_extend {K S} phi s Kcomm Hcs.
Arguments poly_extend_unique {K S} phi s g Hconst Hx t.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma rig_iter_central (S : RingObject) (n : nat)
  (b : carrier (rig_setoid S)) :
  rig_mul S (rig_iter S n) b ≈ rig_mul S b (rig_iter S n).
Proof.
  induction n as [ | n IH ]; simpl.
  - rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
  - rewrite rig_distr_r, rig_distr_l, IH.
    rewrite rig_mul_one_l, rig_mul_one_r; reflexivity.
Qed.

Lemma zring_central (S : RingObject) (z : Z) (b : carrier (rig_setoid S)) :
  rig_mul S (zring S z) b ≈ rig_mul S b (zring S z).
Proof.
  destruct z; simpl.
  - rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
  - apply rig_iter_central.
  - rewrite rng_mul_neg_l, rng_mul_neg_r, rig_iter_central; reflexivity.
Qed.

(* 相关说明。 （已译） *)

Section KAlgebra.

Context (K : CRng).

(** The polynomial ring, commutative K-algebra: ring is
 [PolyRing], commutativity [poly_comm], structure map is
 coefficient 含入. （已译） *)
Definition PolyAlg : KAlgObject K := {|
  kalg_ring := PolyRing (`1 K);
  kalg_comm := poly_comm (`1 K);
  kalg_unit := poly_const (`1 K)
|}.

(** The underlying-set 函子 范畴 K-algebras. （已译） *)
Program Definition KAlg_Forget : KAlg K ⟶ Sets := {|
  fobj := fun A => rig_setoid (kalg_ring A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** The K-algebra map evaluating at a chosen element of a K-algebra. *)
Definition kalg_eval (A : KAlgObject K) (a : carrier (rig_setoid (kalg_ring A)))
  : PolyAlg ~{KAlg K}~> A.
Proof.
  unshelve eexists.
  - refine (poly_extend (kalg_unit A) a (`2 K) _).
    intro c; exact (kalg_comm A a (rig_map (kalg_unit A) c)).
  - intro c; simpl; reflexivity.
Defined.

(** 本节：Mac Lane's Exercise 7, element form: pair ⟨K[x], x⟩ is
 universal among K-algebras chosen element. （已译） *)
Definition poly_universal_element : AUniversalElement KAlg_Forget PolyAlg.
Proof.
  unshelve econstructor.
  - exact (@poly_x (`1 K)).
  - intros A a.
    unshelve econstructor.
    + exact (kalg_eval A a).
    + simpl; reflexivity.
    + intros g Hg t; simpl.
      symmetry.
      apply (poly_extend_unique (kalg_unit A) a (`1 g)).
      * intro c; symmetry; exact (`2 g c).
      * exact Hg.
Defined.

(** The same content bundled form, hence representation:
 underlying-set 函子 K-algebras 已表示的 K[x]. （已译） *)
Definition poly_universal_element_bundled : UniversalElement KAlg_Forget :=
  UniversalElement_of_AUniversalElement poly_universal_element.

Definition poly_representation
  : @Curried_Hom (KAlg K) PolyAlg ≅[[KAlg K, Sets]] KAlg_Forget :=
  ue_representation KAlg_Forget PolyAlg poly_universal_element.

Definition poly_representable : Representable KAlg_Forget :=
  Representable_of_UniversalElement poly_universal_element_bundled.

(** ... 泛箭头 one-point setoid, both of
 Theory/Universal/Arrow.v's encodings. （已译） *)
Definition poly_auniversal_arrow
  : AUniversalArrow SetsOne KAlg_Forget PolyAlg :=
  AUniversalArrow_of_AUniversalElement KAlg_Forget PolyAlg
    poly_universal_element.

Definition poly_universal_arrow : UniversalArrow SetsOne KAlg_Forget.
Proof.
  unshelve eapply (universal_arrow_from_UMP SetsOne KAlg_Forget PolyAlg).
  - exact (@universal_arrow _ _ _ _ _ poly_auniversal_arrow).
  - intros A f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           poly_auniversal_arrow A f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                poly_auniversal_arrow A f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           poly_auniversal_arrow A f) v (symmetry Hv)).
Defined.

End KAlgebra.

(* 相关说明。 （已译） *)

Definition ZPoly : RingObject := PolyRing Int_Ring.

(** Evaluation at element ARBITRARY unital ring: the
 commutation 假设 discharged [zring_central], so no
 commutativity target required. （已译） *)
Definition zpoly_eval (S : RingObject) (b : carrier (rig_setoid S))
  : ZPoly ~{Rng}~> S.
Proof.
  refine (poly_extend (rng_from_Z S) b Int_Ring_commutative _).
  intro z; simpl; symmetry; apply zring_central.
Defined.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zpoly_hom_const (S : RingObject) (g : ZPoly ~{Rng}~> S) (z : Z) :
  rig_map g (@pt_const Int_Ring z) ≈ zring S z.
Proof.
  exact (rng_from_Z_unique S (rig_hom_compose g (poly_const Int_Ring)) z).
Qed.

(** Riehl §2.3 Example 2.3.4: indeterminate universal element of
 underlying-set 函子 rings. （已译） *)
Definition zpoly_universal_element : AUniversalElement Rng_Forget ZPoly.
Proof.
  unshelve econstructor.
  - exact (@poly_x Int_Ring).
  - intros S b.
    unshelve econstructor.
    + exact (zpoly_eval S b).
    + simpl; reflexivity.
    + intros g Hg t; simpl.
      symmetry.
      apply (poly_extend_unique (rng_from_Z S) b g).
      * intro z; exact (zpoly_hom_const S g z).
      * exact Hg.
Defined.

Definition zpoly_universal_element_bundled : UniversalElement Rng_Forget :=
  UniversalElement_of_AUniversalElement zpoly_universal_element.

(** Riehl §2.1 Example 2.1.5(v): forgetful 函子 Rng ⟶ Sets is
 已表示的 ℤ[x] — natural 同构 [[Rng, Sets]], not
 merely ∃! factorization property. （已译） *)
Definition zpoly_representation
  : @Curried_Hom Rng ZPoly ≅[[Rng, Sets]] Rng_Forget :=
  ue_representation Rng_Forget ZPoly zpoly_universal_element.

Definition zpoly_representable : Representable Rng_Forget :=
  Representable_of_UniversalElement zpoly_universal_element_bundled.

(** ... 泛箭头 one-point setoid. （已译） *)
Definition zpoly_auniversal_arrow
  : AUniversalArrow SetsOne Rng_Forget ZPoly :=
  AUniversalArrow_of_AUniversalElement Rng_Forget ZPoly
    zpoly_universal_element.

Definition zpoly_universal_arrow : UniversalArrow SetsOne Rng_Forget.
Proof.
  unshelve eapply (universal_arrow_from_UMP SetsOne Rng_Forget ZPoly).
  - exact (@universal_arrow _ _ _ _ _ zpoly_auniversal_arrow).
  - intros S f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           zpoly_auniversal_arrow S f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                zpoly_auniversal_arrow S f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           zpoly_auniversal_arrow S f) v (symmetry Hv)).
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem rng_monic_injective {R S : RingObject} (f : R ~{Rng}~> S) :
  Monic f → ∀ a b : carrier (rig_setoid R),
    rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intros Hm a b Hab.
  destruct Hm as [Hcancel].
  assert (Heq : f ∘ zpoly_eval R a ≈ f ∘ zpoly_eval R b).
  { intro t.
    transitivity (peval (rng_from_Z S) (rig_map f a) t).
    - apply (poly_extend_unique (rng_from_Z S) (rig_map f a)
               (f ∘ zpoly_eval R a)).
      + intro z; exact (zpoly_hom_const S (f ∘ zpoly_eval R a) z).
      + simpl; reflexivity.
    - symmetry.
      apply (poly_extend_unique (rng_from_Z S) (rig_map f a)
               (f ∘ zpoly_eval R b)).
      + intro z; exact (zpoly_hom_const S (f ∘ zpoly_eval R b) z).
      + simpl; symmetry; exact Hab. }
  exact (Hcancel ZPoly (zpoly_eval R a) (zpoly_eval R b) Heq (@poly_x Int_Ring)).
Qed.

(** Both directions, the forward one being Instance/Rng.v's. *)
Theorem rng_monic_iff_injective {R S : RingObject} (f : R ~{Rng}~> S) :
  Monic f ↔ (∀ a b : carrier (rig_setoid R),
               rig_map f a ≈ rig_map f b → a ≈ b).
Proof.
  split.
  - exact (rng_monic_injective f).
  - exact (rng_injective_monic f).
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma poly_hom_value_central (K S : RingObject)
  (g : PolyRing K ~{Rng}~> S) (c : carrier (rig_setoid K)) :
  rig_mul S (rig_map g (@poly_x K)) (rig_map g (@pt_const K c))
    ≈ rig_mul S (rig_map g (@pt_const K c)) (rig_map g (@poly_x K)).
Proof.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map g)).
  exact (pe_mul_comm K _ _).
Qed.

(** 本节：The same, read through structure map K-algebra hom restricts
 to: value at x commutes everything coming K. （已译） *)
Corollary poly_extend_commutation_necessary (K S : RingObject)
  (g : PolyRing K ~{Rng}~> S) (c : carrier (rig_setoid K)) :
  rig_mul S (rig_map g (@poly_x K))
            (rig_map (rig_hom_compose g (poly_const K)) c)
    ≈ rig_mul S (rig_map (rig_hom_compose g (poly_const K)) c)
                (rig_map g (@poly_x K)).
Proof. exact (poly_hom_value_central K S g c). Qed.

(** * Non-degeneracy *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma poly_const_injective (K : RingObject)
  (Kcomm : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (a b : carrier (rig_setoid K)) :
  pt_eq (@pt_const K a) (@pt_const K b) → a ≈ b.
Proof.
  intro H.
  refine (peval_respects K K (@rig_hom_id K) (rig_zero K) Kcomm _
            (@pt_const K a) (@pt_const K b) H).
  intro c; simpl.
  rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
Qed.

Corollary poly_const_monic (K : CRng) : Monic (kalg_unit (PolyAlg K)).
Proof.
  apply rng_injective_monic.
  exact (poly_const_injective (`1 K) (`2 K)).
Qed.

(*
   本节说明 Polynomial 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma poly_x_not_constant (K : RingObject)
  (Kcomm : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hnt : rig_one K ≈ rig_zero K → False)
  (k : carrier (rig_setoid K)) :
  pt_eq (@poly_x K) (@pt_const K k) → False.
Proof.
  intro H.
  assert (H0 : rig_zero K ≈ k).
  { refine (peval_respects K K (@rig_hom_id K) (rig_zero K) Kcomm _
              (@poly_x K) (@pt_const K k) H).
    intro c; simpl.
    rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity. }
  assert (H1 : rig_one K ≈ k).
  { refine (peval_respects K K (@rig_hom_id K) (rig_one K) Kcomm _
              (@poly_x K) (@pt_const K k) H).
    intro c; simpl.
    rewrite rig_mul_one_l, rig_mul_one_r; reflexivity. }
  apply Hnt.
  rewrite H1, <- H0; reflexivity.
Qed.

(** ** The witnesses over ℤ *)

Definition zconst (z : Z) : carrier (rig_setoid ZPoly) := @pt_const Int_Ring z.

Lemma Int_nontrivial : rig_one Int_Ring ≈ rig_zero Int_Ring → False.
Proof. simpl; unfold Z_eqT; discriminate. Qed.

Corollary zpoly_x_not_constant (k : Z) :
  pt_eq (@poly_x Int_Ring) (zconst k) → False.
Proof.
  exact (poly_x_not_constant Int_Ring Int_Ring_commutative Int_nontrivial k).
Qed.

Corollary zpoly_x_nonzero :
  pt_eq (@poly_x Int_Ring) (rig_zero ZPoly) → False.
Proof. exact (zpoly_x_not_constant 0%Z). Qed.

Corollary zpoly_x_not_one :
  pt_eq (@poly_x Int_Ring) (rig_one ZPoly) → False.
Proof. exact (zpoly_x_not_constant 1%Z). Qed.

(** Evaluation COMPUTES: polynomial x² + 2x + 1 at 3 16. This is
 convertibility exception — equation between elements ℤ, not
 between 态射. （已译） *)
Definition zpoly_sample : carrier (rig_setoid ZPoly) :=
  pt_add (pt_add (pt_mul (@poly_x Int_Ring) poly_x)
                 (pt_mul (zconst 2%Z) poly_x))
         (zconst 1%Z).

Example zpoly_eval_at_three :
  rig_map (zpoly_eval Int_Ring 3%Z) zpoly_sample = 16%Z := eq_refl.

Example zpoly_eval_at_zero :
  rig_map (zpoly_eval Int_Ring 0%Z) zpoly_sample = 1%Z := eq_refl.

Example zpoly_eval_at_neg_one :
  rig_map (zpoly_eval Int_Ring (-1)%Z) zpoly_sample = 0%Z := eq_refl.

(** 本节：The universal element indeterminate, mediating
 homomorphism sends it chosen element — both [eq_refl]. （已译） *)
Example zpoly_universal_elem_is_x :
  @aue_elem Rng Rng_Forget ZPoly zpoly_universal_element = @poly_x Int_Ring
  := eq_refl.

Example zpoly_mediator_at_x (S : RingObject) (b : carrier (rig_setoid S)) :
  rig_map (zpoly_eval S b) (@poly_x Int_Ring) = b := eq_refl.
