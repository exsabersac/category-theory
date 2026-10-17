Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Mod.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 nLab:      https://ncatlab.org/nlab/show/monoid+algebra
 nLab:      https://ncatlab.org/nlab/show/group+algebra
 Wikipedia: https://en.wikipedia.org/wiki/Group_ring

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition MonSets : Category := @Mon Sets Sets_Product_Monoidal.

Definition mcar (M : MonSets) : SetoidObject := `1 M.

Definition mop (M : MonSets) (a b : carrier (mcar M)) : carrier (mcar M) :=
  @mu Sets Sets_Product_Monoidal _ (`2 M) (a, b).

Definition mone (M : MonSets) : carrier (mcar M) :=
  @eta Sets Sets_Product_Monoidal _ (`2 M) ttt.

Lemma mop_respects (M : MonSets) : Proper (equiv ==> equiv ==> equiv) (mop M).
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism (@mu Sets Sets_Product_Monoidal _ (`2 M))
           (a, b) (a', b') (Ha, Hb)).
Qed.

Lemma mop_assoc (M : MonSets) (a b c : carrier (mcar M)) :
  mop M (mop M a b) c ≈ mop M a (mop M b c).
Proof. exact (@mu_assoc Sets Sets_Product_Monoidal _ (`2 M) ((a, b), c)). Qed.

Lemma mop_one_l (M : MonSets) (a : carrier (mcar M)) : mop M (mone M) a ≈ a.
Proof. exact (@mu_unit_left Sets Sets_Product_Monoidal _ (`2 M) (ttt, a)). Qed.

Lemma mop_one_r (M : MonSets) (a : carrier (mcar M)) : mop M a (mone M) ≈ a.
Proof. exact (@mu_unit_right Sets Sets_Product_Monoidal _ (`2 M) (a, ttt)). Qed.

Definition mmap {M N : MonSets} (f : M ~{MonSets}~> N)
  : carrier (mcar M) → carrier (mcar N) := `1 f.

Lemma mmap_op {M N : MonSets} (f : M ~{MonSets}~> N) (a b : carrier (mcar M)) :
  mmap f (mop M a b) ≈ mop N (mmap f a) (mmap f b).
Proof. exact (@hom_mu Sets Sets_Product_Monoidal _ _ _ _ _ (`2 f) (a, b)). Qed.

Lemma mmap_one {M N : MonSets} (f : M ~{MonSets}~> N) :
  mmap f (mone M) ≈ mone N.
Proof. exact (@hom_eta Sets Sets_Product_Monoidal _ _ _ _ _ (`2 f) ttt). Qed.

(* ...and back: element-level data assembles into a morphism of [MonSets]. *)
Program Definition mhom {M N : MonSets}
  (f : carrier (mcar M) → carrier (mcar N))
  (fp : Proper (equiv ==> equiv) f)
  (fo : ∀ a b, f (mop M a b) ≈ mop N (f a) (f b))
  (fu : f (mone M) ≈ mone N) : M ~{MonSets}~> N :=
  (({| morphism := f |} : mcar M ~{Sets}~> mcar N); _).
Next Obligation.
  intros M N f fp fo fu.
  unshelve econstructor.
  - intros [a b]; simpl; apply fo.
  - intros []; simpl; apply fu.
Qed.

(* * The multiplicative-monoid 遗忘 函子 RINGS, obtained by
 extending Theory/Algebra/Rig.v's [Rig_Forget_Mon] along
 [Ring_Forget_Rig]. All four element-level readings hold the
 nose.（已译） *)
Definition Rng_Forget_Mon : Rng ⟶ MonSets := Rig_Forget_Mon ◯ Ring_Forget_Rig.

Example rng_forget_mon_carrier (S : Rng) :
  mcar (Rng_Forget_Mon S) = rig_setoid S := eq_refl.
Example rng_forget_mon_op (S : Rng) (a b : carrier (rig_setoid S)) :
  mop (Rng_Forget_Mon S) a b = rig_mul S a b := eq_refl.
Example rng_forget_mon_one (S : Rng) :
  mone (Rng_Forget_Mon S) = rig_one S := eq_refl.
Example rng_forget_mon_map (S T : Rng) (f : S ~{Rng}~> T)
  (a : carrier (rig_setoid S)) :
  mmap (fmap[Rng_Forget_Mon] f) a = rig_map f a := eq_refl.

(** * The term algebra *)

Section MonoidRing.

Context (R : RingObject).
Context (M : MonSets).

Inductive MRTerm : Type :=
  | mr_scal : carrier (rig_setoid R) → MRTerm
  | mr_gen  : carrier (mcar M) → MRTerm
  | mr_add  : MRTerm → MRTerm → MRTerm
  | mr_neg  : MRTerm → MRTerm
  | mr_mul  : MRTerm → MRTerm → MRTerm.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive mr_eq : MRTerm → MRTerm → Prop :=
  (* 相关说明。 （已译） *)
  | me_scal {a b} : a ≈ b → mr_eq (mr_scal a) (mr_scal b)
  | me_gen {a b} : a ≈ b → mr_eq (mr_gen a) (mr_gen b)
  | me_add {s s' t t'} :
      mr_eq s s' → mr_eq t t' → mr_eq (mr_add s t) (mr_add s' t')
  | me_neg {s s'} : mr_eq s s' → mr_eq (mr_neg s) (mr_neg s')
  | me_mul {s s' t t'} :
      mr_eq s s' → mr_eq t t' → mr_eq (mr_mul s t) (mr_mul s' t')

  (* abelian group under addition *)
  | me_add_assoc s t u :
      mr_eq (mr_add (mr_add s t) u) (mr_add s (mr_add t u))
  | me_add_comm s t : mr_eq (mr_add s t) (mr_add t s)
  | me_add_zero_l s : mr_eq (mr_add (mr_scal (rig_zero R)) s) s
  | me_add_neg_l s : mr_eq (mr_add (mr_neg s) s) (mr_scal (rig_zero R))

  (* monoid under multiplication — commutativity is NOT among the laws *)
  | me_mul_assoc s t u :
      mr_eq (mr_mul (mr_mul s t) u) (mr_mul s (mr_mul t u))
  | me_mul_one_l s : mr_eq (mr_mul (mr_scal (rig_one R)) s) s
  | me_mul_one_r s : mr_eq (mr_mul s (mr_scal (rig_one R))) s

  (* distributivity on both sides *)
  | me_distr_l s t u :
      mr_eq (mr_mul s (mr_add t u)) (mr_add (mr_mul s t) (mr_mul s u))
  | me_distr_r s t u :
      mr_eq (mr_mul (mr_add s t) u) (mr_add (mr_mul s u) (mr_mul t u))

  (* the scalar inclusion is a homomorphism of rings *)
  | me_scal_add a b :
      mr_eq (mr_scal (rig_add R a b)) (mr_add (mr_scal a) (mr_scal b))
  | me_scal_mul a b :
      mr_eq (mr_scal (rig_mul R a b)) (mr_mul (mr_scal a) (mr_scal b))

  (* the generator insertion is a homomorphism of monoids *)
  | me_gen_op a b :
      mr_eq (mr_gen (mop M a b)) (mr_mul (mr_gen a) (mr_gen b))
  | me_gen_one : mr_eq (mr_gen (mone M)) (mr_scal (rig_one R))

  (* 相关说明。 （已译） *)
  | me_scal_gen a m :
      mr_eq (mr_mul (mr_scal a) (mr_gen m)) (mr_mul (mr_gen m) (mr_scal a))

  | me_sym {s t} : mr_eq s t → mr_eq t s
  | me_trans {s t u} : mr_eq s t → mr_eq t u → mr_eq s u.

Lemma mr_refl (s : MRTerm) : mr_eq s s.
Proof.
  induction s.
  - exact (me_scal (reflexivity _)).
  - exact (me_gen (reflexivity _)).
  - exact (me_add IHs1 IHs2).
  - exact (me_neg IHs).
  - exact (me_mul IHs1 IHs2).
Qed.

Lemma mr_eq_Equivalence : Equivalence mr_eq.
Proof.
  constructor.
  - exact mr_refl.
  - exact (fun s t => me_sym).
  - exact (fun s t u => me_trans).
Qed.

Definition mr_Setoid : Setoid MRTerm := {|
  equiv        := mr_eq;
  setoid_equiv := mr_eq_Equivalence
|}.

(** ** Derived laws *)

Let MZ : MRTerm := mr_scal (rig_zero R).
Let MO : MRTerm := mr_scal (rig_one R).

Lemma me_add_zero_r (s : MRTerm) : mr_eq (mr_add s MZ) s.
Proof. exact (me_trans (me_add_comm s MZ) (me_add_zero_l s)). Qed.

Lemma me_add_neg_r (s : MRTerm) : mr_eq (mr_add s (mr_neg s)) MZ.
Proof. exact (me_trans (me_add_comm s (mr_neg s)) (me_add_neg_l s)). Qed.

Lemma me_add_cancel_l (s t u : MRTerm) :
  mr_eq (mr_add s t) (mr_add s u) → mr_eq t u.
Proof.
  intro H.
  refine (me_trans (me_sym (me_add_zero_l t)) _).
  refine (me_trans (me_add (me_sym (me_add_neg_l s)) (mr_refl t)) _).
  refine (me_trans (me_add_assoc (mr_neg s) s t) _).
  refine (me_trans (me_add (mr_refl (mr_neg s)) H) _).
  refine (me_trans (me_sym (me_add_assoc (mr_neg s) s u)) _).
  refine (me_trans (me_add (me_add_neg_l s) (mr_refl u)) _).
  exact (me_add_zero_l u).
Qed.

Lemma me_mul_zero_l (s : MRTerm) : mr_eq (mr_mul MZ s) MZ.
Proof.
  apply (me_add_cancel_l (mr_mul MZ s)).
  refine (me_trans (me_sym (me_distr_r MZ MZ s)) _).
  refine (me_trans (me_mul _ (mr_refl s))
            (me_sym (me_add_zero_r (mr_mul MZ s)))).
  refine (me_trans (me_sym (me_scal_add (rig_zero R) (rig_zero R))) _).
  exact (me_scal (rig_add_zero_l R (rig_zero R))).
Qed.

Lemma me_mul_zero_r (s : MRTerm) : mr_eq (mr_mul s MZ) MZ.
Proof.
  apply (me_add_cancel_l (mr_mul s MZ)).
  refine (me_trans (me_sym (me_distr_l s MZ MZ)) _).
  refine (me_trans (me_mul (mr_refl s) _)
            (me_sym (me_add_zero_r (mr_mul s MZ)))).
  refine (me_trans (me_sym (me_scal_add (rig_zero R) (rig_zero R))) _).
  exact (me_scal (rig_add_zero_l R (rig_zero R))).
Qed.

(** ** The ring R[M] *)

Definition MonoidRig : RigObject := {|
  rig_setoid := {| carrier := MRTerm; is_setoid := mr_Setoid |};
  rig_zero := MZ;
  rig_add := mr_add;
  rig_one := MO;
  rig_mul := mr_mul;
  rig_add_respects := fun _ _ Hs _ _ Ht => me_add Hs Ht;
  rig_mul_respects := fun _ _ Hs _ _ Ht => me_mul Hs Ht;
  rig_add_assoc := me_add_assoc;
  rig_add_comm := me_add_comm;
  rig_add_zero_l := me_add_zero_l;
  rig_mul_assoc := me_mul_assoc;
  rig_mul_one_l := me_mul_one_l;
  rig_mul_one_r := me_mul_one_r;
  rig_distr_l := me_distr_l;
  rig_distr_r := me_distr_r;
  rig_mul_zero_l := me_mul_zero_l;
  rig_mul_zero_r := me_mul_zero_r;
  (* [mr_eq] IS [Prop]-valued 关系, so it own [Prop] 镜像 and
 both 蕴含 恒等. （已译） *)
  rig_prop := @PropEquiv_of_relation _ mr_Setoid mr_eq
                (fun _ _ h => h) (fun _ _ h => h)
|}.

Definition MonoidRing : RingObject := {|
  ring_rig := MonoidRig;
  ring_neg := mr_neg;
  ring_neg_respects := fun _ _ Hs => me_neg Hs;
  ring_neg_l := me_add_neg_l
|}.

(** ** The two insertions *)

Program Definition mring_scal : R ~{Rng}~> MonoidRing := {|
  rig_map := {| morphism := mr_scal |}
|}.
Next Obligation. intros a b H; exact (me_scal H). Qed.
Next Obligation. simpl; exact (mr_refl MZ). Qed.
Next Obligation. intros a b; exact (me_scal_add a b). Qed.
Next Obligation. simpl; exact (mr_refl MO). Qed.
Next Obligation. intros a b; exact (me_scal_mul a b). Qed.

(*
   本节说明 MonoidRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mring_scal_central
  (Rcomm : ∀ a b, rig_mul R a b ≈ rig_mul R b a)
  (r : carrier (rig_setoid R)) (t : MRTerm) :
  mr_eq (mr_mul (mr_scal r) t) (mr_mul t (mr_scal r)).
Proof.
  induction t as [ a | m | s IHs u IHu | s IHs | s IHs u IHu ].
  - refine (me_trans (me_sym (me_scal_mul r a)) _).
    refine (me_trans (me_scal (Rcomm r a)) _).
    exact (me_scal_mul a r).
  - exact (me_scal_gen r m).
  - refine (me_trans (me_distr_l (mr_scal r) s u) _).
    refine (me_trans (me_add IHs IHu) _).
    exact (me_sym (me_distr_r s u (mr_scal r))).
  - refine (me_trans (rng_mul_neg_r MonoidRing (mr_scal r) s) _).
    refine (me_trans (me_neg IHs) _).
    exact (me_sym (rng_mul_neg_l MonoidRing s (mr_scal r))).
  - refine (me_trans (me_sym (me_mul_assoc (mr_scal r) s u)) _).
    refine (me_trans (me_mul IHs (mr_refl u)) _).
    refine (me_trans (me_mul_assoc s (mr_scal r) u) _).
    refine (me_trans (me_mul (mr_refl s) IHu) _).
    exact (me_sym (me_mul_assoc s u (mr_scal r))).
Qed.

End MonoidRing.

Arguments mr_scal {R M} a.
Arguments mr_gen {R M} m.
Arguments mr_add {R M} s t.
Arguments mr_neg {R M} s.
Arguments mr_mul {R M} s t.
Arguments mr_eq {R M} s t.
Arguments mr_refl {R M} s.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mring_gen (R : RingObject) (M : MonSets)
  : M ~{MonSets}~> Rng_Forget_Mon (MonoidRing R M) :=
  @mhom M (Rng_Forget_Mon (MonoidRing R M)) (@mr_gen R M)
    (fun a b H => me_gen R M H) (me_gen_op R M) (me_gen_one R M).

Example mring_gen_computes (R : RingObject) (M : MonSets)
  (m : carrier (mcar M)) : mmap (mring_gen R M) m = mr_gen m := eq_refl.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition MRComm {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S) : Type :=
  ∀ (a : carrier (rig_setoid R)) (m : carrier (mcar M)),
    rig_mul S (rig_map phi a) (mmap psi m)
      ≈ rig_mul S (mmap psi m) (rig_map phi a).

Fixpoint mreval {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
  (t : MRTerm R M) : carrier (rig_setoid S) :=
  match t with
  | mr_scal a  => rig_map phi a
  | mr_gen m   => mmap psi m
  | mr_add s t => rig_add S (mreval phi psi s) (mreval phi psi t)
  | mr_neg s   => ring_neg S (mreval phi psi s)
  | mr_mul s t => rig_mul S (mreval phi psi s) (mreval phi psi t)
  end.

(*
   本节说明 MonoidRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mreval_respects {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
  (Hcomm : MRComm phi psi) (s t : MRTerm R M) :
  mr_eq s t → mreval phi psi s ≈ mreval phi psi t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as
    [ a b Hab
    | a b Hab
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' t t' _ IHs _ IHt
    | s t u | s t | s | s
    | s t u | s | s
    | s t u | s t u
    | a b | a b
    | a b |
    | a m
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - apply pequiv_from; exact (proper_morphism (rig_map phi) _ _ Hab).
  - apply pequiv_from;
      exact (proper_morphism (mmap psi : SetoidMorphism _ _) _ _ Hab).
  - apply pequiv_from.
    exact (rig_add_respects S _ _ (pequiv_to _ _ IHs)
                              _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from.
    exact (ring_neg_respects S _ _ (pequiv_to _ _ IHs)).
  - apply pequiv_from.
    exact (rig_mul_respects S _ _ (pequiv_to _ _ IHs)
                              _ _ (pequiv_to _ _ IHt)).
  - apply pequiv_from; exact (rig_add_assoc S _ _ _).
  - apply pequiv_from; exact (rig_add_comm S _ _).
  - apply pequiv_from; rewrite (rig_map_zero phi); apply rig_add_zero_l.
  - apply pequiv_from; rewrite (rig_map_zero phi); apply (ring_neg_l S).
  - apply pequiv_from; exact (rig_mul_assoc S _ _ _).
  - apply pequiv_from; rewrite (rig_map_one phi); apply rig_mul_one_l.
  - apply pequiv_from; rewrite (rig_map_one phi); apply rig_mul_one_r.
  - apply pequiv_from; exact (rig_distr_l S _ _ _).
  - apply pequiv_from; exact (rig_distr_r S _ _ _).
  - apply pequiv_from; exact (rig_map_add phi a b).
  - apply pequiv_from; exact (rig_map_mul phi a b).
  - apply pequiv_from; exact (mmap_op psi a b).
  - apply pequiv_from;
      rewrite (mmap_one psi); symmetry; apply (rig_map_one phi).
  - apply pequiv_from; exact (Hcomm a m).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

Program Definition mring_extend {R : RingObject} {M : MonSets}
  {S : RingObject} (phi : R ~{Rng}~> S)
  (psi : M ~{MonSets}~> Rng_Forget_Mon S) (Hcomm : MRComm phi psi)
  : MonoidRing R M ~{Rng}~> S := {|
  rig_map := {| morphism := mreval phi psi |}
|}.
Next Obligation.
  intros R M S phi psi Hcomm s t He; exact (mreval_respects phi psi Hcomm s t He).
Qed.
Next Obligation.
  intros R M S phi psi Hcomm; simpl; exact (rig_map_zero phi).
Qed.
Next Obligation. intros R M S phi psi Hcomm s t; simpl; reflexivity. Qed.
Next Obligation.
  intros R M S phi psi Hcomm; simpl; exact (rig_map_one phi).
Qed.
Next Obligation. intros R M S phi psi Hcomm s t; simpl; reflexivity. Qed.

(*
   本节说明 MonoidRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example mring_extend_scal {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
  (Hcomm : MRComm phi psi) (a : carrier (rig_setoid R)) :
  rig_map (mring_extend phi psi Hcomm) (mr_scal a) = rig_map phi a := eq_refl.

Example mring_extend_gen {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
  (Hcomm : MRComm phi psi) (m : carrier (mcar M)) :
  rig_map (mring_extend phi psi Hcomm) (mr_gen m) = mmap psi m := eq_refl.

(*
   本节说明 MonoidRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma mring_extend_unique {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
  (g : MonoidRing R M ~{Rng}~> S)
  (Hscal : ∀ a, rig_map g (mr_scal a) ≈ rig_map phi a)
  (Hgen : ∀ m, rig_map g (mr_gen m) ≈ mmap psi m) (t : MRTerm R M) :
  rig_map g t ≈ mreval phi psi t.
Proof.
  induction t as [ a | m | s IHs t IHt | s IHs | s IHs t IHt ]; simpl.
  - exact (Hscal a).
  - exact (Hgen m).
  - rewrite (rig_map_add g s t); exact (rig_add_respects S _ _ IHs _ _ IHt).
  - rewrite (RigHom_neg (MonoidRing R M) S g s).
    exact (ring_neg_respects S _ _ IHs).
  - rewrite (rig_map_mul g s t); exact (rig_mul_respects S _ _ IHs _ _ IHt).
Qed.

(*
   本节说明 MonoidRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma mring_comm_self (R : RingObject) (M : MonSets)
  : MRComm (mring_scal R M) (mring_gen R M).
Proof. intros a m; exact (me_scal_gen R M a m). Qed.

Lemma mring_extend_self (R : RingObject) (M : MonSets) (t : MRTerm R M) :
  rig_map (mring_extend (mring_scal R M) (mring_gen R M)
             (mring_comm_self R M)) t ≈ t.
Proof.
  symmetry.
  apply (mring_extend_unique (mring_scal R M) (mring_gen R M)
           (@id Rng (MonoidRing R M))).
  - intro a; exact (mr_refl _).
  - intro m; exact (mr_refl _).
Qed.

(*
   本节说明 MonoidRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition mring_AAlg (R : CRng) (M : MonSets) : AAlgObject R :=
  Build_AAlgObject R (MonoidRing (`1 R) M) (mring_scal (`1 R) M)
    (mring_scal_central (`1 R) M (`2 R)).

(*
   本节说明 MonoidRing 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ZMonRing (M : MonSets) : RingObject := MonoidRing Int_Ring M.

Definition zmring_insert (M : MonSets)
  : M ~{MonSets}~> Rng_Forget_Mon (ZMonRing M) :=
  mring_gen Int_Ring M.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zmring_hom_scal (M : MonSets) (S : Rng) (g : ZMonRing M ~{Rng}~> S)
  (z : Z) : rig_map g (@mr_scal Int_Ring M z) ≈ zring S z.
Proof.
  exact (rng_from_Z_unique S (rig_hom_compose g (mring_scal Int_Ring M)) z).
Qed.

Definition zmring_eval (M : MonSets) (S : Rng)
  (h : M ~{MonSets}~> Rng_Forget_Mon S) : ZMonRing M ~{Rng}~> S.
Proof.
  refine (mring_extend (rng_from_Z S) h _).
  intros z m; simpl.
  apply zring_central.
Defined.

Lemma zmring_universal (M : MonSets) (S : Rng)
  (h : M ~{MonSets}~> Rng_Forget_Mon S) :
  ∃! g : ZMonRing M ~{Rng}~> S,
    h ≈ fmap[Rng_Forget_Mon] g ∘ zmring_insert M.
Proof.
  unshelve eexists.
  - exact (zmring_eval M S h).
  - intro m; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry.
    apply (mring_extend_unique (rng_from_Z S) h g).
    + intro z; exact (zmring_hom_scal M S g z).
    + intro m; symmetry; exact (Hg m).
Qed.

Definition zmring_universal_arrow (M : MonSets)
  : UniversalArrow M Rng_Forget_Mon :=
  universal_arrow_from_UMP M Rng_Forget_Mon (ZMonRing M) (zmring_insert M)
    (zmring_universal M).

Program Definition zmring_auniversal_arrow (M : MonSets)
  : AUniversalArrow M Rng_Forget_Mon (ZMonRing M) := {|
  universal_arrow := zmring_insert M
|}.
Next Obligation.
  intros M S h.
  unshelve eexists.
  - exact (zmring_eval M S h).
  - intro m; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry.
    apply (mring_extend_unique (rng_from_Z S) h g).
    + intro z; exact (zmring_hom_scal M S g z).
    + intro m; exact (Hg m).
Qed.

(** The left-adjoint reading: ℤ[−] 左伴随 the
 multiplicative-幺半群 函子. Both come out generic machinery
 no further 证明. （已译） *)
Definition MonoidRingFunctor : MonSets ⟶ Rng :=
  LeftAdjointFunctorFromUniversalArrows Rng_Forget_Mon zmring_universal_arrow.

Definition zmring_adjunction : MonoidRingFunctor ⊣ Rng_Forget_Mon :=
  AdjunctionFromUniversalArrows Rng_Forget_Mon zmring_universal_arrow.

Example MonoidRingFunctor_obj (M : MonSets) :
  fobj[MonoidRingFunctor] M = ZMonRing M := eq_refl.

Example zmring_arrow_is_insert (M : MonSets) :
  @arrow _ _ M Rng_Forget_Mon (zmring_universal_arrow M) = zmring_insert M
  := eq_refl.

Definition zmring_unit (M : MonSets)
  : M ~{MonSets}~> Rng_Forget_Mon (fobj[MonoidRingFunctor] M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ zmring_adjunction M.

Example zmring_unit_is_gen (M : MonSets) (m : carrier (mcar M)) :
  mmap (zmring_unit M) m = @mr_gen Int_Ring M m := eq_refl.

(* * * Non-degeneracy

 Nothing below obtained induction [mr_eq]: induction a
 quotienting 关系 cannot produce negative statement. Every
 separation obtained 映射 OUT concrete ring — here the
 upper-triangular 2×2 integer matrices of
 Instance/Rng/Algebras/Associative.v, whose multiplicative 幺半群 a
 NON-COMMUTATIVE 幺半群 available no new construction, so the
 witness 幺半群 costs nothing. （已译） *)

Definition UT2_Mon : MonSets := Rng_Forget_Mon UT2.

(* The 恒等 UT2's carrier IS 幺半群 homomorphism that
 multiplicative 幺半群 itself, since [Rng_Forget_Mon]'s operation and
 unit UT2's own. （已译） *)
Definition ut2_mon_id : UT2_Mon ~{MonSets}~> Rng_Forget_Mon UT2 :=
  @id MonSets UT2_Mon.

Definition zmring_to_UT2 : ZMonRing UT2_Mon ~{Rng}~> UT2 :=
  zmring_eval UT2_Mon UT2 ut2_mon_id.

Example zmring_to_UT2_gen (x : ut2) :
  rig_map zmring_to_UT2 (@mr_gen Int_Ring UT2_Mon x) = x := eq_refl.

Example zmring_to_UT2_e11_e12 :
  rig_map zmring_to_UT2
    (mr_mul (@mr_gen Int_Ring UT2_Mon ut2_e11)
            (@mr_gen Int_Ring UT2_Mon ut2_e12)) = ut2_e12 := eq_refl.

Example zmring_to_UT2_e12_e11 :
  rig_map zmring_to_UT2
    (mr_mul (@mr_gen Int_Ring UT2_Mon ut2_e12)
            (@mr_gen Int_Ring UT2_Mon ut2_e11)) = ut2_zero := eq_refl.

(* ℤ[M] is non-commutative when M is. *)
Theorem zmring_not_commutative :
  mr_eq (mr_mul (@mr_gen Int_Ring UT2_Mon ut2_e11)
                (@mr_gen Int_Ring UT2_Mon ut2_e12))
        (mr_mul (@mr_gen Int_Ring UT2_Mon ut2_e12)
                (@mr_gen Int_Ring UT2_Mon ut2_e11)) → False.
Proof.
  intro H.
  apply UT2_not_commutative.
  exact (proper_morphism (rig_map zmring_to_UT2) _ _ H).
Qed.

(* A generator is not a scalar. *)
Theorem zmring_gen_not_scalar (r : Z) :
  mr_eq (@mr_gen Int_Ring UT2_Mon ut2_e12) (@mr_scal Int_Ring UT2_Mon r)
    → False.
Proof.
  intro H.
  (* 相关说明。 （已译） *)
  pose proof (proper_morphism (rig_map zmring_to_UT2) _ _ H) as H2.
  pose proof (rng_from_Z_unique UT2 ut2_scalar r) as H3.
  assert (Hx : ((0, 1, 0)%Z : ut2) = ((r, 0, r)%Z : ut2))
    by (unfold ut2_eqT in H2, H3; exact (eq_trans H2 (eq_sym H3))).
  inversion Hx.
Qed.

(* ...and the ring is not trivial. *)
Theorem zmring_nontrivial :
  mr_eq (@mr_scal Int_Ring UT2_Mon 1%Z) (@mr_scal Int_Ring UT2_Mon 0%Z)
    → False.
Proof.
  intro H.
  pose proof (proper_morphism (rig_map zmring_to_UT2) _ _ H) as H2.
  simpl in H2; unfold ut2_eqT in H2.
  inversion H2.
Qed.

(* Two distinct elements 幺半群 stay distinct ℤ[M]: the
 嵌入 does not collapse. （已译） *)
Theorem zmring_gens_distinct :
  mr_eq (@mr_gen Int_Ring UT2_Mon ut2_e11) (@mr_gen Int_Ring UT2_Mon ut2_e12)
    → False.
Proof.
  intro H.
  pose proof (proper_morphism (rig_map zmring_to_UT2) _ _ H) as H2.
  unfold ut2_eqT, ut2_e11, ut2_e12 in H2.
  inversion H2.
Qed.
