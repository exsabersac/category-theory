Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.

From Coq Require Import Arith.
From Coq Require Import Lists.List.
From Coq Require Import Eqdep_dec.
Import ListNotations.

Generalizable All Variables.

(** * The unit-colour bridge: PROPs are one-colour coloured PROPs *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Layer 0: unit-colour utilities *)

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition unit_dec (u v : unit) : {u = v} + {u <> v} :=
  left (match u return u = v with
        | tt => match v return tt = v with
                | tt => eq_refl
                end
        end).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma unit_list_eta (l : list unit) : repeat tt (length l) = l.
Proof.
  induction l as [| u l IH]; cbn.
  - reflexivity.
  - destruct u.
    now rewrite IH.
Qed.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma braid_conj_close {C : Category} (OD : @ObjDecEq C)
  {p q t1 t2 t3 s : C}
  (k : p = t1) (a1 : t1 = t2) (b1 : t2 = p)
  (b2 : q = t3) (a2 : t3 = s) (k' : q = s)
  (f : p ~{C}~> q) :
  ((id_cast a2 ∘ ((id_cast b2 ∘ f) ∘ id_cast b1)) ∘ id_cast a1) ∘ id_cast k
    ≈ id_cast k' ∘ f.
Proof.
  destruct k, a1, b2, a2.
  rewrite (@obj_uip C OD _ _ b1 eq_refl).
  rewrite (@obj_uip C OD _ _ k' eq_refl).
  rewrite !id_cast_refl.
  now rewrite !id_left, !id_right.
Qed.

(** ** Layer 1: the class-level transports *)

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma len_app {A : Type} (xs ys : list A) :
  length (xs ++ ys) = (length xs + length ys)%nat.
Proof.
  induction xs; simpl; [reflexivity|].
  now rewrite IHxs.
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PROP_to_ColouredPROP (Q : PROP) : ColouredPROP unit :=
  Build_ColouredPROP unit
    (@prop_cat Q)
    (@prop_strict Q)
    (@prop_symmetric Q)
    (@prop_monoidal_coherence Q)
    (fun cs : list unit => @prop_of_nat Q (length cs))
    (@prop_unit_zero Q)
    (fun cs ds : list unit =>
       eq_trans (@prop_tensor_plus Q (length cs) (length ds))
                (f_equal (@prop_of_nat Q) (eq_sym (len_app cs ds)))).

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ColouredPROP_unit_to_PROP (Q : ColouredPROP unit) : PROP :=
  Build_PROP
    (@cprop_cat unit Q)
    (@cprop_strict unit Q)
    (@cprop_symmetric unit Q)
    (@cprop_monoidal_coherence unit Q)
    (fun n : nat => @cprop_of_list unit Q (repeat tt n))
    (@cprop_unit_nil unit Q)
    (fun m n : nat =>
       eq_trans (@cprop_tensor_app unit Q (repeat tt m) (repeat tt n))
                (f_equal (@cprop_of_list unit Q) (eq_sym (repeat_app tt m n)))).

(** *** Machine-checked: the transports are structure-preserving on
    the nose.  Each [Example] is [eq_refl]. *)

(** The underlying category is untouched, in both directions. *)
Example PROP_to_ColouredPROP_cat (Q : PROP) :
  @cprop_cat unit (PROP_to_ColouredPROP Q) = @prop_cat Q := eq_refl.

Example ColouredPROP_unit_to_PROP_cat (Q : ColouredPROP unit) :
  @prop_cat (ColouredPROP_unit_to_PROP Q) = @cprop_cat unit Q := eq_refl.

(** The strict and symmetric structures, and with them the coherence
    proof relating the two [Monoidal] paths, are passed through
    verbatim — no re-proving, no transport. *)
Example PROP_to_ColouredPROP_coherence (Q : PROP) :
  @cprop_monoidal_coherence unit (PROP_to_ColouredPROP Q)
  = @prop_monoidal_coherence Q := eq_refl.

Example ColouredPROP_unit_to_PROP_coherence (Q : ColouredPROP unit) :
  @prop_monoidal_coherence (ColouredPROP_unit_to_PROP Q)
  = @cprop_monoidal_coherence unit Q := eq_refl.

(** The single wire of the transported coloured PROP is the PROP's
    1-object. *)
Example PROP_to_ColouredPROP_wire (Q : PROP) :
  wire (P := PROP_to_ColouredPROP Q) tt = @prop_of_nat Q 1 := eq_refl.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roundtrip_prop_of_nat_2 (Q : PROP) :
  @prop_of_nat (ColouredPROP_unit_to_PROP (PROP_to_ColouredPROP Q)) 2
  = @prop_of_nat Q 2 := eq_refl.

Example roundtrip_cprop_of_list_pair (Q : ColouredPROP unit) (u v : unit) :
  @cprop_of_list unit (PROP_to_ColouredPROP (ColouredPROP_unit_to_PROP Q))
                 [u; v]
  = @cprop_of_list unit Q [tt; tt] := eq_refl.

(** ** Layer 2: the free-level bridge *)

Section UnitBridge.

Context (S : Signature).

(** The unit-coloured signature of a one-sorted signature: a
    generator with colour-word boundary [(cs, ds)] is a generator of
    arity [(length cs, length ds)]. *)
Definition USig : CSignature unit :=
  fun cs ds : list unit => S (length cs) (length ds).

(** Transport of a generator along arity equalities (the one-sorted
    mirror of the boundary transports of [Relabel.v]). *)
Definition nsig_cast {m m' n n' : nat} (em : m = m') (en : n = n')
  (g : S m n) : S m' n' :=
  match en in _ = b return S m' b with
  | eq_refl =>
      match em in _ = a return S a n with
      | eq_refl => g
      end
  end.

(** [nsig_cast] is proof-irrelevant, by UIP on [nat] — no axioms. *)
Lemma nsig_cast_irr {m m' n n' : nat}
  (e1 e1' : m = m') (e2 e2' : n = n') (g : S m n) :
  nsig_cast e1 e2 g = nsig_cast e1' e2' g.
Proof.
  rewrite (UIP_dec Nat.eq_dec e1 e1'), (UIP_dec Nat.eq_dec e2 e2').
  reflexivity.
Qed.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition LengthPROP : ColouredPROP unit :=
  PROP_to_ColouredPROP (FreePROP S).

(** The valuation: a [USig]-generator is by definition an [S]-
    generator at the boundary lengths, so [T_gen] applies on the
    nose. *)
Definition length_val : CValuation LengthPROP USig :=
  fun (cs ds : list unit) (g : USig cs ds) => T_gen g.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition LengthFunctor : CFreeCat USig ⟶ FreeCat S :=
  @CInterpF unit USig LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

(** Its strong/strict monoidal packagings, from [Universal.v]. *)
Definition LengthFunctor_Monoidal :
  @MonoidalFunctor (CFreeCat USig) (FreeCat S)
    (CFreeCat_Monoidal USig unit_dec) (FreeCat_Monoidal S) LengthFunctor :=
  @CInterpF_Monoidal unit USig unit_dec LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

Definition LengthFunctor_Strict :
  @StrictMonoidalFunctor (CFreeCat USig) (FreeCat S)
    (CFreeCat_Monoidal USig unit_dec) (FreeCat_Monoidal S) LengthFunctor :=
  @CInterpF_Strict unit USig unit_dec LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

Definition LengthFunctor_SymmetricStrict :
  CSymmetricStrict USig unit_dec LengthPROP
    LengthFunctor LengthFunctor_Monoidal :=
  @CInterpF_SymmetricStrict unit USig unit_dec LengthPROP
    (FreeCat_HomEqProp S) (FreeCat_ObjDecEq S) length_val.

(** Machine-checked behaviour: objects go to their lengths, and
    generators are relabelled on the nose. *)
Example LengthFunctor_fobj (cs : list unit) :
  fobj[LengthFunctor] cs = length cs := eq_refl.

Example LengthFunctor_gen (cs ds : list unit) (g : USig cs ds) :
  fmap[LengthFunctor] (CT_gen g) = T_gen g := eq_refl.

(** The strict object comparison is the [len_app]-shaped tensor
    field of the layer-1 transport, verbatim. *)
Example LengthFunctor_strict_ap_obj (x y : list unit) :
  @strict_ap_obj _ _ _ _ LengthFunctor LengthFunctor_Strict x y
  = @cprop_tensor_app unit LengthPROP x y := eq_refl.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition RepeatPROP : PROP :=
  ColouredPROP_unit_to_PROP (FreeColouredPROP USig unit_dec).

(** The valuation: an [S]-generator of arity [(m, n)] becomes a
    [USig]-generator at boundary [(repeat tt m, repeat tt n)], with
    the arities corrected by [repeat_length]. *)
Definition repeat_val : Valuation RepeatPROP S :=
  fun (m n : nat) (g : S m n) =>
    CT_gen (nsig_cast (eq_sym (repeat_length tt m))
                      (eq_sym (repeat_length tt n)) g).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RepeatFunctor : FreeCat S ⟶ CFreeCat USig :=
  @InterpF S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

Definition RepeatFunctor_Monoidal :
  @MonoidalFunctor (FreeCat S) (CFreeCat USig)
    (FreeCat_Monoidal S) (CFreeCat_Monoidal USig unit_dec) RepeatFunctor :=
  @InterpF_Monoidal S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

Definition RepeatFunctor_Strict :
  @StrictMonoidalFunctor (FreeCat S) (CFreeCat USig)
    (FreeCat_Monoidal S) (CFreeCat_Monoidal USig unit_dec) RepeatFunctor :=
  @InterpF_Strict S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

Definition RepeatFunctor_SymmetricStrict :
  SymmetricStrict S RepeatPROP RepeatFunctor RepeatFunctor_Monoidal :=
  @InterpF_SymmetricStrict S RepeatPROP
    (CFreeCat_HomEqProp USig) (CFreeCat_ObjDecEq USig unit_dec) repeat_val.

(** Machine-checked behaviour on objects. *)
Example RepeatFunctor_fobj (n : nat) :
  fobj[RepeatFunctor] n = repeat tt n := eq_refl.

(** The strict object comparison is the [repeat_app]-shaped tensor
    field of the layer-1 transport, verbatim. *)
Example RepeatFunctor_strict_ap_obj (x y : nat) :
  @strict_ap_obj _ _ _ _ RepeatFunctor RepeatFunctor_Strict x y
  = @prop_tensor_plus RepeatPROP x y := eq_refl.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example MPc_LengthPROP_shared :
  MPc LengthPROP = FreeCat_Monoidal S := eq_refl.

Example MP_RepeatPROP_shared :
  MP RepeatPROP = CFreeCat_Monoidal USig unit_dec := eq_refl.

Example strict_braid_FreePROP_eq (x y : nat) :
  strict_braid (FreePROP S) x y = T_braid x y := eq_refl.

Example cstrict_braid_LengthPROP_eq (x y : nat) :
  cstrict_braid LengthPROP x y = T_braid x y := eq_refl.

Example strict_braid_RepeatPROP_eq (x y : list unit) :
  strict_braid RepeatPROP x y = CT_braid x y := eq_refl.

Example cstrict_braid_FreeCPROP_eq (x y : list unit) :
  cstrict_braid (FreeColouredPROP USig unit_dec) x y = CT_braid x y
  := eq_refl.

(** ** Layer 3: the round-trip laws *)

(** The tautological valuations of the two free instances: each
    generator names itself. *)
Definition taut_val : Valuation (FreePROP S) S :=
  fun (m n : nat) (g : S m n) => T_gen g.

Definition ctaut_val : CValuation (FreeColouredPROP USig unit_dec) USig :=
  fun (cs ds : list unit) (g : USig cs ds) => CT_gen g.

(** *** Round trip on the one-sorted side *)

(** The composite, packaged strictly by [Compose_StrictMonoidalFunctor]
    (its object comparisons are the [eq_trans]/[f_equal] composites of
    the two legs'). *)
Definition LengthRepeat_Strict :
  @StrictMonoidalFunctor (FreeCat S) (FreeCat S)
    (FreeCat_Monoidal S) (MP (FreePROP S))
    (LengthFunctor ◯ RepeatFunctor) :=
  @Compose_StrictMonoidalFunctor (FreeCat S) (CFreeCat USig) (FreeCat S)
    (FreeCat_Monoidal S) (CFreeCat_Monoidal USig unit_dec) (MP (FreePROP S))
    LengthFunctor RepeatFunctor LengthFunctor_Strict RepeatFunctor_Strict.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma LengthRepeat_SymmetricStrict :
  SymmetricStrict S (FreePROP S)
    (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict.
Proof.
  intros m n.
  assert (Hap : forall x y : nat,
    to (@ap_iso _ _ _ _ (LengthFunctor ◯ RepeatFunctor)
          (@strict_functor_is_monoidal _ _ _ _
             (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict) x y)
      ≈ id_cast (@strict_ap_obj _ _ _ _
                   (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict x y)).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _
             (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict x y). }
  rewrite (Hap m n), (Hap n m).
  assert (Hsb : forall x y : nat,
             strict_braid (FreePROP S) x y = T_braid x y) by reflexivity.
  rewrite Hsb.
  (*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  assert (HRL : fmap[LengthFunctor ◯ RepeatFunctor] (T_braid m n)
            = (fmap[LengthFunctor]
                 (id_cast (@prop_tensor_plus RepeatPROP n m))
                 ∘ ((id_cast (@cprop_tensor_app unit LengthPROP
                                (repeat tt n) (repeat tt m))
                       ∘ T_braid (length (repeat tt m))
                                 (length (repeat tt n)))
                      ∘ id_cast (eq_sym (@cprop_tensor_app unit LengthPROP
                                           (repeat tt m) (repeat tt n)))))
                ∘ fmap[LengthFunctor]
                    (id_cast (eq_sym (@prop_tensor_plus RepeatPROP m n))))
    by reflexivity.
  rewrite HRL.
  rewrite !fmap_id_cast.
  apply (braid_conj_close (FreeCat_ObjDecEq S)).
Qed.

(** The identity competitor's braid square: its tensor comparison is
    the identity and the target braiding is the braid constructor. *)
Lemma Id_SymmetricStrict_free :
  SymmetricStrict S (FreePROP S) Id[FreeCat S]
    (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S)).
Proof.
  intros m n.
  assert (Hap : forall x y : nat,
    to (@ap_iso _ _ _ _ Id[FreeCat S]
          (@strict_functor_is_monoidal _ _ _ _ Id[FreeCat S]
             (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S)))
          x y)
      ≈ id).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _ Id[FreeCat S]
             (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S))
             x y). }
  rewrite (Hap m n), (Hap n m).
  assert (Hsb : forall x y : nat,
             strict_braid (FreePROP S) x y = T_braid x y) by reflexivity.
  rewrite Hsb.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** Generator transport against [hom_cast], in general position: with
    both arity equalities destructed the two casts are the identity. *)
Lemma T_gen_cast_agree {m a n b : nat} (em : m = a) (en : n = b)
  (g : S m n) :
  (T_gen (nsig_cast em en g) : a ~{FreeCat S}~> b)
    ≈ @hom_cast (FreeCat S) m n a b em en (T_gen g).
Proof.
  destruct em, en.
  reflexivity.
Qed.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma LengthRepeat_gen_agree (m n : nat) (g : S m n) :
  fmap[LengthFunctor ◯ RepeatFunctor] (T_gen g)
    ≈ @hom_cast (FreeCat S) _ _ _ _
        (eq_sym (repeat_length tt m)) (eq_sym (repeat_length tt n))
        (taut_val m n g).
Proof.
  exact (T_gen_cast_agree (eq_sym (repeat_length tt m))
                          (eq_sym (repeat_length tt n)) g).
Qed.

(** The identity competitor extends the tautological valuation with
    reflexivity-grade casts. *)
Lemma Id_gen_agree (m n : nat) (g : S m n) :
  fmap[Id[FreeCat S]] (T_gen g)
    ≈ @hom_cast (FreeCat S) _ _ _ _
        (eq_sym (@eq_refl _ (@prop_of_nat (FreePROP S) m)))
        (eq_sym (@eq_refl _ (@prop_of_nat (FreePROP S) n)))
        (taut_val m n g).
Proof.
  reflexivity.
Qed.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem LengthRepeat_roundtrip (m n : nat) (t : Term S m n) :
  @hom_cast (FreeCat S) _ _ _ _
    (repeat_length tt m) (repeat_length tt n)
    (fmap[LengthFunctor ◯ RepeatFunctor] t)
    ≈ (t : m ~{FreeCat S}~> n).
Proof.
  exact (@interp_unique2 S (FreePROP S) (FreeCat_ObjDecEq S) taut_val
           (LengthFunctor ◯ RepeatFunctor) LengthRepeat_Strict
           LengthRepeat_SymmetricStrict
           (fun k : nat => repeat_length tt k)
           LengthRepeat_gen_agree
           Id[FreeCat S]
           (@Id_StrictMonoidalFunctor (FreeCat S) (FreeCat_Monoidal S))
           Id_SymmetricStrict_free
           (fun k : nat => eq_refl)
           Id_gen_agree
           m n t).
Qed.

(** *** Round trip on the coloured side *)

Definition RepeatLength_Strict :
  @StrictMonoidalFunctor (CFreeCat USig) (CFreeCat USig)
    (CFreeCat_Monoidal USig unit_dec)
    (MPc (FreeColouredPROP USig unit_dec))
    (RepeatFunctor ◯ LengthFunctor) :=
  @Compose_StrictMonoidalFunctor (CFreeCat USig) (FreeCat S) (CFreeCat USig)
    (CFreeCat_Monoidal USig unit_dec) (FreeCat_Monoidal S)
    (MPc (FreeColouredPROP USig unit_dec))
    RepeatFunctor LengthFunctor RepeatFunctor_Strict LengthFunctor_Strict.

(** The mirror braid square, by the same cast calculus. *)
Lemma RepeatLength_SymmetricStrict :
  CSymmetricStrict USig unit_dec (FreeColouredPROP USig unit_dec)
    (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict.
Proof.
  intros cs ds.
  assert (Hap : forall x y : list unit,
    to (@ap_iso _ _ _ _ (RepeatFunctor ◯ LengthFunctor)
          (@strict_functor_is_monoidal _ _ _ _
             (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict) x y)
      ≈ id_cast (@strict_ap_obj _ _ _ _
                   (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict x y)).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _
             (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict x y). }
  rewrite (Hap cs ds), (Hap ds cs).
  assert (Hsb : forall x y : list unit,
             cstrict_braid (FreeColouredPROP USig unit_dec) x y
             = CT_braid x y) by reflexivity.
  rewrite Hsb.
  (*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  assert (HLR : fmap[RepeatFunctor ◯ LengthFunctor] (CT_braid cs ds)
            = (fmap[RepeatFunctor]
                 (id_cast (@cprop_tensor_app unit LengthPROP ds cs))
                 ∘ ((id_cast (@prop_tensor_plus RepeatPROP
                                (length ds) (length cs))
                       ∘ CT_braid (repeat tt (length cs))
                                  (repeat tt (length ds)))
                      ∘ id_cast (eq_sym (@prop_tensor_plus RepeatPROP
                                           (length cs) (length ds)))))
                ∘ fmap[RepeatFunctor]
                    (id_cast (eq_sym (@cprop_tensor_app unit LengthPROP
                                        cs ds))))
    by reflexivity.
  rewrite HLR.
  rewrite !fmap_id_cast.
  apply (braid_conj_close (CFreeCat_ObjDecEq USig unit_dec)).
Qed.

(** The coloured identity competitor's braid square. *)
Lemma CId_SymmetricStrict_free :
  CSymmetricStrict USig unit_dec (FreeColouredPROP USig unit_dec)
    Id[CFreeCat USig]
    (@Id_StrictMonoidalFunctor (CFreeCat USig)
       (CFreeCat_Monoidal USig unit_dec)).
Proof.
  intros cs ds.
  assert (Hap : forall x y : list unit,
    to (@ap_iso _ _ _ _ Id[CFreeCat USig]
          (@strict_functor_is_monoidal _ _ _ _ Id[CFreeCat USig]
             (@Id_StrictMonoidalFunctor (CFreeCat USig)
                (CFreeCat_Monoidal USig unit_dec))) x y)
      ≈ id).
  { intros x y.
    exact (@strict_ap_iso_id _ _ _ _ Id[CFreeCat USig]
             (@Id_StrictMonoidalFunctor (CFreeCat USig)
                (CFreeCat_Monoidal USig unit_dec)) x y). }
  rewrite (Hap cs ds), (Hap ds cs).
  assert (Hsb : forall x y : list unit,
             cstrict_braid (FreeColouredPROP USig unit_dec) x y
             = CT_braid x y) by reflexivity.
  rewrite Hsb.
  rewrite id_left, id_right.
  reflexivity.
Qed.

(** Coloured generator transport against [hom_cast]: the boundary
    equalities are between colour WORDS; their [length]-images drive
    the [nsig_cast]. *)
Lemma CT_gen_cast_agree {cs a ds b : list unit}
  (ecs : cs = a) (eds : ds = b) (g : USig cs ds) :
  (CT_gen (nsig_cast (f_equal (@length unit) ecs)
                     (f_equal (@length unit) eds) g)
     : a ~{CFreeCat USig}~> b)
    ≈ @hom_cast (CFreeCat USig) cs ds a b ecs eds (CT_gen g).
Proof.
  destruct ecs, eds.
  reflexivity.
Qed.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma RepeatLength_gen_agree (cs ds : list unit) (g : USig cs ds) :
  fmap[RepeatFunctor ◯ LengthFunctor] (CT_gen g)
    ≈ @hom_cast (CFreeCat USig) _ _ _ _
        (eq_sym (unit_list_eta cs)) (eq_sym (unit_list_eta ds))
        (ctaut_val cs ds g).
Proof.
  assert (Hg : fmap[RepeatFunctor ◯ LengthFunctor] (CT_gen g)
           = CT_gen (nsig_cast (eq_sym (repeat_length tt (length cs)))
                               (eq_sym (repeat_length tt (length ds))) g))
    by reflexivity.
  rewrite Hg.
  rewrite (nsig_cast_irr
             (eq_sym (repeat_length tt (length cs)))
             (f_equal (@length unit) (eq_sym (unit_list_eta cs)))
             (eq_sym (repeat_length tt (length ds)))
             (f_equal (@length unit) (eq_sym (unit_list_eta ds))) g).
  exact (CT_gen_cast_agree (eq_sym (unit_list_eta cs))
                           (eq_sym (unit_list_eta ds)) g).
Qed.

(** The coloured identity competitor extends the tautological
    valuation with reflexivity-grade casts. *)
Lemma CId_gen_agree (cs ds : list unit) (g : USig cs ds) :
  fmap[Id[CFreeCat USig]] (CT_gen g)
    ≈ @hom_cast (CFreeCat USig) _ _ _ _
        (eq_sym (@eq_refl _ (@cprop_of_list unit
                               (FreeColouredPROP USig unit_dec) cs)))
        (eq_sym (@eq_refl _ (@cprop_of_list unit
                               (FreeColouredPROP USig unit_dec) ds)))
        (ctaut_val cs ds g).
Proof.
  reflexivity.
Qed.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem RepeatLength_roundtrip (cs ds : list unit)
  (t : CTerm USig cs ds) :
  @hom_cast (CFreeCat USig) _ _ _ _
    (unit_list_eta cs) (unit_list_eta ds)
    (fmap[RepeatFunctor ◯ LengthFunctor] t)
    ≈ (t : cs ~{CFreeCat USig}~> ds).
Proof.
  exact (@cinterp_unique2 unit USig unit_dec
           (FreeColouredPROP USig unit_dec)
           (CFreeCat_ObjDecEq USig unit_dec) ctaut_val
           (RepeatFunctor ◯ LengthFunctor) RepeatLength_Strict
           RepeatLength_SymmetricStrict
           (fun ks : list unit => unit_list_eta ks)
           RepeatLength_gen_agree
           Id[CFreeCat USig]
           (@Id_StrictMonoidalFunctor (CFreeCat USig)
              (CFreeCat_Monoidal USig unit_dec))
           CId_SymmetricStrict_free
           (fun ks : list unit => eq_refl)
           CId_gen_agree
           cs ds t).
Qed.

(*
   本节说明 UnitBridge 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example LengthRepeat_fobj (n : nat) :
  fobj[LengthFunctor ◯ RepeatFunctor] n = length (repeat tt n) := eq_refl.

Example RepeatLength_fobj (cs : list unit) :
  fobj[RepeatFunctor ◯ LengthFunctor] cs = repeat tt (length cs) := eq_refl.

End UnitBridge.

Arguments USig S _ _ : assert.
Arguments LengthPROP S : assert.
Arguments LengthFunctor S : assert.
Arguments RepeatPROP S : assert.
Arguments RepeatFunctor S : assert.
Arguments LengthRepeat_roundtrip S m n t : assert.
Arguments RepeatLength_roundtrip S cs ds t : assert.
