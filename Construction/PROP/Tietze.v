Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Presentation.

From Coq Require Import Arith.

Generalizable All Variables.

Open Scope nat_scope.

(** * Tietze moves for presentations of PROPs *)

(*
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/Tietze_transformations
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出 PROP 相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition T_map {S T : Signature} (h : SubSig S T) {m n : nat}
  (t : Term S m n) : Term T m n :=
  T_subst (fun a b (s : S a b) => T_gen (h a b s)) t.

(** The instantiation is definitional, so every [T_subst]-level lemma
    specializes to [T_map] by conversion. *)
Example T_map_is_T_subst {S T : Signature} (h : SubSig S T) {m n : nat} :
  @T_map S T h m n
  = @T_subst S T (fun a b (s : S a b) => T_gen (h a b s)) m n := eq_refl.

(** [T_map] agrees with the tactic-built [T_inj] of [Term.v] on the
    nose; [T_inj] itself is left untouched. *)
Lemma T_map_T_inj {S T : Signature} (h : SubSig S T) {m n : nat}
  (t : Term S m n) :
  T_map h t = T_inj h t.
Proof.
  induction t; cbn; try reflexivity; now f_equal.
Qed.

(** Casts are fixed by every signature morphism (a Leibniz equality:
    both sides are the same [match] once [e] is destructed). *)
Lemma T_map_T_cast {S T : Signature} (h : SubSig S T) {a b : nat}
  (e : a = b) :
  T_map h (T_cast e) = T_cast e.
Proof. destruct e; reflexivity. Qed.

(** *** Soundness of relabelling

    [T_map h] carries every free equation of [TermEq S] to the
    corresponding free equation of [TermEq T] — the nineteen-case
    preservation induction [T_subst_TermEq] of
    [Construction/PROP/TermEq.v], specialized (definitionally) to the
    relabelling substitution. *)

Lemma T_map_TermEq {S T : Signature} (h : SubSig S T) {m n : nat}
  {s t : Term S m n} :
  TermEq S s t → TermEq T (T_map h s) (T_map h t).
Proof.
  exact (T_subst_TermEq (fun a b (g : S a b) => T_gen (h a b g))).
Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SignatureMorphism.

Context {S T : Signature}.
Context (h : SubSig S T).

Definition RelabelFunctor : FreeCat S ⟶ FreeCat T :=
  Build_Functor (FreeCat S) (FreeCat T)
    (fun n : nat => n)
    (fun m n (t : Term S m n) => T_map h t)
    (fun m n s t Hst => T_map_TermEq h Hst)
    (fun x => TE_refl (T_id x))
    (fun x y z f g => TE_refl (T_comp (T_map h f) (T_map h g))).

(** The tensor-then-map and map-then-tensor composites related by the
    tensor comparison of the monoidal structure. *)
Definition Relabel_ap_dom : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  FreeCat_Tensor T ◯ (RelabelFunctor ∏⟶ RelabelFunctor).

Definition Relabel_ap_cod : FreeCat S ∏ FreeCat S ⟶ FreeCat T :=
  RelabelFunctor ◯ FreeCat_Tensor S.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Relabel_ap_to : Relabel_ap_dom ⟹ Relabel_ap_cod :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Relabel_ap_dom Relabel_ap_cod
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

Definition Relabel_ap_from : Relabel_ap_cod ⟹ Relabel_ap_dom :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) (FreeCat T)
    Relabel_ap_cod Relabel_ap_dom
    (fun p => T_id (fst p + snd p))
    (fun p q f => tm_id_swap (T_tens (T_map h (fst f)) (T_map h (snd f)))).

(** The identity components are inverse up to [TermEq] (the identity
    natural transformation of a composite-with-tensor functor has
    components [T_tens (T_id _) (T_id _)]). *)
Program Definition Relabel_ap_iso :
  Relabel_ap_dom ≅[[FreeCat S ∏ FreeCat S, FreeCat T]] Relabel_ap_cod := {|
  to   := Relabel_ap_to;
  from := Relabel_ap_from;
  iso_to_from := fun p => tm_comp_id_tens (fst p) (snd p);
  iso_from_to := fun p => tm_comp_id_tens (fst p) (snd p)
|}.

(*
   本节说明 Tietze 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Relabel_unit_left_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_l x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_l x))) (T_id (0 + x)))
            (T_tens (T_id 0) (T_id x))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_l x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Relabel_unit_right_square (x : nat) :
  TermEq T (T_cast (Nat.add_0_r x))
    (T_comp (T_comp (T_map h (T_cast (Nat.add_0_r x))) (T_id (x + 0)))
            (T_tens (T_id x) (T_id 0))).
Proof.
  rewrite (T_map_T_cast h (Nat.add_0_r x)).
  apply TE_sym, tm_collapse_r.
Qed.

Lemma Relabel_assoc_square (x y z : nat) :
  TermEq T
    (T_comp (T_comp (T_map h (T_cast (eq_sym (Nat.add_assoc x y z))))
                    (T_id ((x + y) + z)))
            (T_tens (T_id (x + y)) (T_id z)))
    (T_comp (T_comp (T_id (x + (y + z)))
                    (T_tens (T_id x) (T_id (y + z))))
            (T_cast (eq_sym (Nat.add_assoc x y z)))).
Proof.
  rewrite (T_map_T_cast h (eq_sym (Nat.add_assoc x y z))).
  apply TE_trans with (T_cast (eq_sym (Nat.add_assoc x y z))).
  - apply tm_collapse_r.
  - apply TE_sym, tm_collapse_l.
Qed.

Program Definition RelabelFunctor_Monoidal :
  @MonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) RelabelFunctor := {|
  pure_iso := iso_id;
  ap_functor_iso := Relabel_ap_iso;
  pure_iso_left  := fun x => iso_id;
  pure_iso_right := fun x => iso_id;
  ap_iso_assoc := fun x y z =>
    @tensor_assoc (FreeCat T) (FreeCat_Monoidal T) x y z;
  monoidal_unit_left  := fun x => Relabel_unit_left_square x;
  monoidal_unit_right := fun x => Relabel_unit_right_square x;
  monoidal_assoc := fun x y z => Relabel_assoc_square x y z
|}.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition RelabelFunctor_Strict :
  @StrictMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Monoidal S) (FreeCat_Monoidal T) RelabelFunctor := {|
  strict_functor_is_monoidal := RelabelFunctor_Monoidal;
  strict_pure_obj := eq_refl;
  strict_ap_obj := fun x y => eq_refl
|}.
Next Obligation. exact (TE_refl _). Qed.
Next Obligation. exact (TE_refl _). Qed.

(** The braid-compatibility square: [T_map] fixes [T_braid], and both
    tensor comparisons are identities, so the square is one slide of an
    identity past the braid. *)
Lemma RelabelFunctor_braid (m n : nat) :
  fmap[RelabelFunctor] (@braid (FreeCat S) (FreeCat_Braided S) m n)
    ∘ to (@ap_iso _ _ _ _ RelabelFunctor RelabelFunctor_Monoidal m n)
  ≈[FreeCat T]
  to (@ap_iso _ _ _ _ RelabelFunctor RelabelFunctor_Monoidal n m)
    ∘ @braid (FreeCat T) (FreeCat_Braided T) m n.
Proof.
  exact (tm_id_swap (T_braid m n)).
Qed.

Program Definition RelabelFunctor_Braided :
  @BraidedMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Braided S) (FreeCat_Braided T) RelabelFunctor := {|
  braided_is_strong := RelabelFunctor_Monoidal
|}.
Next Obligation.
  exact (tm_id_swap (T_braid x y)).
Qed.

(** A braided monoidal functor between symmetric monoidal categories IS
    a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition RelabelFunctor_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat S) (FreeCat T)
    (FreeCat_Symmetric S) (FreeCat_Symmetric T) RelabelFunctor :=
  RelabelFunctor_Braided.

End SignatureMorphism.

Arguments RelabelFunctor {S T} h : assert.
Arguments RelabelFunctor_Monoidal {S T} h : assert.
Arguments RelabelFunctor_Strict {S T} h : assert.
Arguments RelabelFunctor_Braided {S T} h : assert.
Arguments RelabelFunctor_Symmetric {S T} h : assert.

(*
   本节说明 Tietze 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sig_inl {S T : Signature} : SubSig S (Sum_Sig S T) :=
  fun _ _ s => Datatypes.inl s.

Definition sig_inr {S T : Signature} : SubSig T (Sum_Sig S T) :=
  fun _ _ t => Datatypes.inr t.

Definition copair_val {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) : Valuation P (Sum_Sig S T) :=
  fun m n g =>
    match g with
    | Datatypes.inl s => v m n s
    | Datatypes.inr t => w m n t
    end.

(** No decidability or reflection hypotheses are needed here: the
    induction never leaves the [Type]-valued hom equivalence. *)
Lemma interp_copair_inl {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) {m n : nat} (t : Term S m n) :
  interp P (Sum_Sig S T) (copair_val v w) (T_map sig_inl t)
    ≈ interp P S v t.
Proof.
  induction t; cbn [T_map T_subst interp].
  - reflexivity.
  - reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - reflexivity.
Qed.

Lemma interp_copair_inr {S T : Signature} {P : PROP}
  (v : Valuation P S) (w : Valuation P T) {m n : nat} (t : Term T m n) :
  interp P (Sum_Sig S T) (copair_val v w) (T_map sig_inr t)
    ≈ interp P T w t.
Proof.
  induction t; cbn [T_map T_subst interp].
  - reflexivity.
  - reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - rewrite <- IHt1, <- IHt2; reflexivity.
  - reflexivity.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AddEquation.

Context (E : SMT).
Context {m n : nat}.
Context (s t : Term (smt_sig E) m n).

Inductive add_eqn : ∀ a b : nat,
  Term (smt_sig E) a b → Term (smt_sig E) a b → Prop :=
  | ae_base {a b} (u u' : Term (smt_sig E) a b) :
      smt_eqs E a b u u' → add_eqn a b u u'
  | ae_new : add_eqn m n s t.

Definition AddEqn : SMT := {|
  smt_sig := smt_sig E;
  smt_eqs := add_eqn
|}.

(*
   本节说明 Tietze 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem AddEqn_derivable_conservative (Hd : TermEqW E s t) :
  ∀ (a b : nat) (u u' : Term (smt_sig E) a b),
    TermEqW AddEqn u u' <-> TermEqW E u u'.
Proof.
  intros a b u u'.
  split; intros H.
  - induction H as [a1 b1 u1 u2 Hfree
                   |a1 b1 u1 u2 Hax
                   |a1 b1 u1 u2 Hw IHw
                   |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                   |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                   |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
    + apply TEW_termeq; exact Hfree.
    + destruct Hax as [a2 b2 u3 u4 Hax'|].
      * apply TEW_ax; exact Hax'.
      * exact Hd.
    + apply TEW_sym; exact IHw.
    + exact (TEW_trans _ _ _ _ IHw1 IHw2).
    + exact (TEW_comp E _ _ _ _ IHf IHg).
    + exact (TEW_tens E _ _ _ _ IHf IHg).
  - induction H as [a1 b1 u1 u2 Hfree
                   |a1 b1 u1 u2 Hax
                   |a1 b1 u1 u2 Hw IHw
                   |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                   |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                   |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
    + apply TEW_termeq; exact Hfree.
    + apply TEW_ax, ae_base; exact Hax.
    + apply TEW_sym; exact IHw.
    + exact (TEW_trans _ _ _ _ IHw1 IHw2).
    + exact (TEW_comp AddEqn _ _ _ _ IHf IHg).
    + exact (TEW_tens AddEqn _ _ _ _ IHf IHg).
Qed.

End AddEquation.

Arguments AddEqn E {m n} s t : assert.

(*
   本节说明 Tietze 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Extension.

Context (B : SMT).
Context (m n : nat).
Context (w : Term (smt_sig B) m n).

(** The extended signature: the base plus one generator. *)
Definition ext_sig : Signature := Sum_Sig (smt_sig B) (Single_Sig m n).

(*
   本节说明 Tietze 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint nat_eqb_refl (x : nat) : Nat.eqb x x = true :=
  match x return Nat.eqb x x = true with
  | O => eq_refl
  | Datatypes.S k => nat_eqb_refl k
  end.

Fixpoint nat_eqb_eq (a b : nat) {struct a} : Nat.eqb a b = true → a = b :=
  match a, b return Nat.eqb a b = true → a = b with
  | O, O => fun _ => eq_refl
  | O, Datatypes.S b' => fun H =>
      match H in _ = c return if c then O = Datatypes.S b' else True with
      | eq_refl => Logic.I
      end
  | Datatypes.S a', O => fun H =>
      match H in _ = c return if c then Datatypes.S a' = O else True with
      | eq_refl => Logic.I
      end
  | Datatypes.S a', Datatypes.S b' => fun H =>
      f_equal Datatypes.S (nat_eqb_eq a' b' H)
  end.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition single_gen : Single_Sig m n m n :=
  match eq_sym (nat_eqb_refl m) in _ = c
    return (if c then if Nat.eqb n n then unit else Empty_set
            else Empty_set)
  with
  | eq_refl =>
      match eq_sym (nat_eqb_refl n) in _ = d
        return (if d then unit else Empty_set)
      with
      | eq_refl => tt
      end
  end.

Definition single_dom {a b : nat} : Single_Sig m n a b → a = m :=
  match Nat.eqb a m as c
    return (Nat.eqb a m = c →
            (if c then if Nat.eqb b n then unit else Empty_set
             else Empty_set) → a = m)
  with
  | true  => fun Ha _ => nat_eqb_eq a m Ha
  | false => fun _ s => match s return a = m with end
  end eq_refl.

Definition single_cod {a b : nat} : Single_Sig m n a b → b = n :=
  match Nat.eqb a m as c
    return ((if c then if Nat.eqb b n then unit else Empty_set
             else Empty_set) → b = n)
  with
  | true =>
      match Nat.eqb b n as d
        return (Nat.eqb b n = d → (if d then unit else Empty_set) → b = n)
      with
      | true  => fun Hb _ => nat_eqb_eq b n Hb
      | false => fun _ s => match s return b = n with end
      end eq_refl
  | false => fun s => match s return b = n with end
  end.

(** [Single_Sig m n] is a SINGLETON: any two generators of any one
    arity are equal.  This identifies a generator of the extended
    signature with [single_gen] in the section lemma below. *)
Lemma single_sig_singleton {a b : nat} (s s' : Single_Sig m n a b) :
  s = s'.
Proof.
  revert s s'.
  unfold Single_Sig.
  destruct (Nat.eqb a m), (Nat.eqb b n); intros s s'; now destruct s, s'.
Qed.

(** The fresh generator, as a generator of the extended signature. *)
Definition new_gen : ext_sig m n := Datatypes.inr single_gen.

(** The equations of the extended theory: the base axioms (embedded
    along [sig_inl]) plus the single defining equation. *)
Inductive ext_eqs : ∀ a b : nat,
  Term ext_sig a b → Term ext_sig a b → Prop :=
  | ee_base {a b} (s t : Term (smt_sig B) a b) :
      smt_eqs B a b s t →
      ext_eqs a b (T_map sig_inl s) (T_map sig_inl t)
  | ee_def : ext_eqs m n (T_gen new_gen) (T_map sig_inl w).

Definition ext_smt : SMT := {|
  smt_sig := ext_sig;
  smt_eqs := ext_eqs
|}.

(*
   本节说明 Tietze 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ext_retract_gen {a b : nat} (g : ext_sig a b) :
  Term (smt_sig B) a b :=
  match g with
  | Datatypes.inl s => T_gen s
  | Datatypes.inr s => T_comp (T_cast (eq_sym (single_cod s)))
                              (T_comp w (T_cast (single_dom s)))
  end.

Definition ext_retract {a b : nat} (t : Term ext_sig a b) :
  Term (smt_sig B) a b :=
  T_subst (@ext_retract_gen) t.

(** The instantiation is definitional, so every [T_subst]-level lemma
    specializes to [ext_retract] by conversion. *)
Example ext_retract_is_T_subst {a b : nat} :
  @ext_retract a b
  = @T_subst ext_sig (smt_sig B) (@ext_retract_gen) a b := eq_refl.

(** [ext_retract] fixes casts, just as [T_map] does. *)
Lemma retract_T_cast {a b : nat} (e : a = b) :
  ext_retract (T_cast e) = T_cast e.
Proof. destruct e; reflexivity. Qed.

(** The retraction is a left inverse of the embedding — a Leibniz
    equality, by term induction. *)
Lemma retract_map_inl {a b : nat} (t : Term (smt_sig B) a b) :
  ext_retract (T_map sig_inl t) = t.
Proof.
  induction t;
  cbn [T_map ext_retract T_subst ext_retract_gen sig_inl];
  try reflexivity.
  - now f_equal.
  - now f_equal.
Qed.

(** The retraction carries free equations to free equations — the
    nineteen-case preservation induction [T_subst_TermEq] of
    [Construction/PROP/TermEq.v], specialized (definitionally) to the
    retraction substitution. *)
Lemma retract_TermEq {a b : nat} {s t : Term ext_sig a b} :
  TermEq ext_sig s t → TermEq (smt_sig B) (ext_retract s) (ext_retract t).
Proof.
  exact (T_subst_TermEq (@ext_retract_gen)).
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma retract_sound {a b : nat} {s t : Term ext_sig a b} :
  TermEqW ext_smt s t → TermEqW B (ext_retract s) (ext_retract t).
Proof.
  intros H.
  induction H as [a1 b1 u1 u2 Hfree
                 |a1 b1 u1 u2 Hax
                 |a1 b1 u1 u2 Hw IHw
                 |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                 |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                 |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
  - apply TEW_termeq, retract_TermEq; exact Hfree.
  - destruct Hax as [a2 b2 u3 u4 Hax'|].
    + rewrite !retract_map_inl.
      apply TEW_ax; exact Hax'.
    + rewrite retract_map_inl.
      cbn [ext_retract T_subst ext_retract_gen new_gen].
      rewrite (T_cast_id (single_dom single_gen)).
      rewrite (T_cast_id (eq_sym (single_cod single_gen))).
      apply TEW_termeq.
      apply TE_trans with (T_comp w (T_id m)).
      * apply TE_id_left.
      * apply TE_id_right.
  - apply TEW_sym; exact IHw.
  - exact (TEW_trans _ _ _ _ IHw1 IHw2).
  - cbn [ext_retract T_subst]; apply TEW_comp; assumption.
  - cbn [ext_retract T_subst]; apply TEW_tens; assumption.
Qed.

(** *** Conservativity, both directions *)

(** Base-signature terms identified in the extension were already
    identified in the base theory. *)
Theorem ext_conservative {a b : nat} (s t : Term (smt_sig B) a b) :
  TermEqW ext_smt (T_map sig_inl s) (T_map sig_inl t) →
  TermEqW B s t.
Proof.
  intros H.
  pose proof (retract_sound H) as Hr.
  rewrite !retract_map_inl in Hr.
  exact Hr.
Qed.

(** Conversely, every base identification survives the extension. *)
Theorem ext_reflects {a b : nat} {s t : Term (smt_sig B) a b} :
  TermEqW B s t →
  TermEqW ext_smt (T_map sig_inl s) (T_map sig_inl t).
Proof.
  intros H.
  induction H as [a1 b1 u1 u2 Hfree
                 |a1 b1 u1 u2 Hax
                 |a1 b1 u1 u2 Hw IHw
                 |a1 b1 u1 u2 u3 Hw1 IHw1 Hw2 IHw2
                 |a1 b1 c1 f1 f2 g1 g2 Hf IHf Hg IHg
                 |a1 b1 c1 d1 f1 f2 g1 g2 Hf IHf Hg IHg].
  - apply TEW_termeq, T_map_TermEq; exact Hfree.
  - apply TEW_ax, ee_base; exact Hax.
  - apply TEW_sym; exact IHw.
  - exact (TEW_trans _ _ _ _ IHw1 IHw2).
  - cbn [T_map T_subst]; apply TEW_comp; assumption.
  - cbn [T_map T_subst]; apply TEW_tens; assumption.
Qed.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ext_retract_section {a b : nat} (t : Term ext_sig a b) :
  TermEqW ext_smt t (T_map sig_inl (ext_retract t)).
Proof.
  induction t.
  - (* T_id *)
    apply TEW_termeq, TE_refl.
  - (* T_braid *)
    apply TEW_termeq, TE_refl.
  - (* T_comp *)
    cbn [ext_retract T_subst T_map].
    apply TEW_comp; assumption.
  - (* T_tens *)
    cbn [ext_retract T_subst T_map].
    apply TEW_tens; assumption.
  - (* T_gen *)
    destruct s as [s|s].
    + (* a base generator retracts to itself *)
      apply TEW_termeq, TE_refl.
    + (* the fresh generator: pin the arity, then [ee_def] *)
      pose proof (single_dom s) as ea.
      pose proof (single_cod s) as eb.
      subst.
      cbn [ext_retract T_subst ext_retract_gen].
      rewrite (T_cast_id (single_dom s)).
      rewrite (T_cast_id (eq_sym (single_cod s))).
      rewrite (single_sig_singleton s single_gen).
      apply TEW_trans with (t := T_map sig_inl w).
      * exact (TEW_ax ext_smt _ _ ee_def).
      * apply TEW_termeq, T_map_TermEq.
        apply TE_sym.
        apply TE_trans with (T_comp w (T_id m)).
        -- apply TE_id_left.
        -- apply TE_id_right.
Qed.

(** The defining equation itself holds in the extended theory. *)
Example ext_definition_holds :
  TermEqW ext_smt (T_gen new_gen) (T_map sig_inl w) :=
  TEW_ax ext_smt _ _ ee_def.

(** The retraction computes on embedded generators, by [eq_refl]. *)
Example retract_fixes_base_gen {a b : nat} (s : smt_sig B a b) :
  ext_retract (T_map sig_inl (T_gen s)) = T_gen s := eq_refl.

End Extension.

Arguments ext_smt B m n w : assert.
Arguments new_gen B m n : assert.

(** ** Machine-checked sanity

    [T_map] computes on the structural constructors, so the functor
    action of [RelabelFunctor] is definitional. *)

Example T_map_fixes_id {S T : Signature} (h : SubSig S T) (k : nat) :
  T_map h (T_id k) = T_id k := eq_refl.

Example T_map_fixes_braid {S T : Signature} (h : SubSig S T) (a b : nat) :
  T_map h (T_braid a b) = T_braid a b := eq_refl.

Example T_map_computes_comp {S T : Signature} (h : SubSig S T)
  {a b c : nat} (g : Term S b c) (f : Term S a b) :
  T_map h (T_comp g f) = T_comp (T_map h g) (T_map h f) := eq_refl.

Example T_map_computes_tens {S T : Signature} (h : SubSig S T)
  {a b c d : nat} (f : Term S a b) (g : Term S c d) :
  T_map h (T_tens f g) = T_tens (T_map h f) (T_map h g) := eq_refl.

Example RelabelFunctor_obj_id {S T : Signature} (h : SubSig S T) (k : nat) :
  fobj[RelabelFunctor h] k = k := eq_refl.

(*
   本节说明 Tietze 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Definition scratch_smt : SMT :=
  {| smt_sig := Empty_Sig; smt_eqs := fun _ _ _ _ => False |}.

Example ext_retract_computes_on_new_gen :
  ext_retract scratch_smt 1 1 (T_id 1) (T_gen (new_gen scratch_smt 1 1))
  = T_comp (T_id 1) (T_comp (T_id 1) (T_id 1)) := eq_refl.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
