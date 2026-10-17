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
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.BaseChange.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Laws of base change for coloured PROPs *)

(*
   nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Transport of generators along boundary equalities

    A signature is a family [S : list Colour → list Colour → Type];
    reindexing a generator along propositional equalities of its
    boundary words is the evident double transport.  Spelled as a
    nested [match] (the [hom_cast] shape of [Construction/Quotient.v])
    so that it computes at [eq_refl]. *)

Definition csig_transport {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a b) :
  S a' b' :=
  match e2 in _ = d return S a' d with
  | eq_refl =>
      match e1 in _ = c return S c b with
      | eq_refl => s
      end
  end.

(** At [eq_refl] on both ends, the transport is the identity. *)
Example csig_transport_refl {Colour : Type} {S : CSignature Colour}
  {a b : list Colour} (s : S a b) :
  csig_transport eq_refl eq_refl s = s := eq_refl.

(*
   本节说明 Laws 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma csig_transport_inv {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a' b') :
  csig_transport e1 e2 (csig_transport (eq_sym e1) (eq_sym e2) s) = s.
Proof. destruct e1, e2; reflexivity. Qed.

Lemma csig_transport_inv_sym {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a b) :
  csig_transport (eq_sym e1) (eq_sym e2) (csig_transport e1 e2 s) = s.
Proof. destruct e1, e2; reflexivity. Qed.

(** A [hom_cast] of a generator leaf is the generator of the
    transported datum — the bridge between the object-level cast kit
    and the signature-level transport. *)
Lemma CT_gen_hom_cast {Colour : Type} {S : CSignature Colour}
  {a a' b b' : list Colour} (e1 : a = a') (e2 : b = b') (s : S a b) :
  @hom_cast (CFreeCat S) a b a' b' e1 e2 (CT_gen s)
  = CT_gen (csig_transport e1 e2 s).
Proof. destruct e1, e2; reflexivity. Qed.

(** ** 1. Base change along the identity colour function *)

Section BaseChangeIdentity.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).

(*
   本节说明 Laws 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CSigMap_id : CSigMap (fun c : Colour => c) S S :=
  fun (cs ds : list Colour) (s : S cs ds) =>
    csig_transport (eq_sym (map_id cs)) (eq_sym (map_id ds)) s.

(** Machine-checked: the identity base change acts on objects by
    [map (fun c => c)] and sends a generator to its transport. *)
Example BaseChangeF_identity_fobj (cs : list Colour) :
  fobj[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] cs
  = map (fun c : Colour => c) cs := eq_refl.

Example BaseChangeF_identity_gen {cs ds : list Colour} (s : S cs ds) :
  fmap[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] (CT_gen s)
  = CT_gen (CSigMap_id cs ds s) := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma BaseChangeF_id_square :
  CSymmetricStrict S Cdec (basechange_target (fun c : Colour => c) Cdec S)
    Id[CFreeCat S]
    (@strict_functor_is_monoidal _ _ _ _ Id[CFreeCat S]
       (@Id_StrictMonoidalFunctor (CFreeCat S) (CFreeCat_Monoidal S Cdec))).
Proof.
  intros x y.
  etransitivity; [ apply id_right | symmetry; apply id_left ].
Qed.

(** Generator agreement of the identity competitor: unwinding the
    double [eq_sym] with [eq_sym_involutive], the conjugating cast
    exactly undoes the [CSigMap_id] transport. *)
Lemma BaseChangeF_id_gen (cs ds : list Colour) (s : S cs ds) :
  fmap[Id[CFreeCat S]] (CT_gen s)
    ≈ @hom_cast (CFreeCat S) _ _ _ _
        (eq_sym (eq_sym (map_id cs))) (eq_sym (eq_sym (map_id ds)))
        (basechange_val (fun c : Colour => c) Cdec S S CSigMap_id cs ds s).
Proof.
  rewrite (eq_sym_involutive (map_id cs)), (eq_sym_involutive (map_id ds)).
  unfold basechange_val; cbn beta.
  rewrite CT_gen_hom_cast.
  unfold CSigMap_id; cbn beta.
  rewrite csig_transport_inv.
  reflexivity.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem BaseChangeF_id {cs ds : list Colour} (t : CTerm S cs ds) :
  @hom_cast (CFreeCat S)
    (map (fun c : Colour => c) cs) (map (fun c : Colour => c) ds)
    cs ds (map_id cs) (map_id ds)
    (fmap[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] t)
  ≈ t.
Proof.
  assert (HU := @cinterp_unique Colour S Cdec
    (basechange_target (fun c : Colour => c) Cdec S)
    (CFreeCat_ObjDecEq S Cdec)
    (basechange_val (fun c : Colour => c) Cdec S S CSigMap_id)
    Id[CFreeCat S]
    (@Id_StrictMonoidalFunctor (CFreeCat S) (CFreeCat_Monoidal S Cdec))
    BaseChangeF_id_square
    (fun ks : list Colour => eq_sym (map_id ks))
    BaseChangeF_id_gen
    cs ds t).
  symmetry.
  transitivity
    (@hom_cast (CFreeCat S) _ _ _ _
       (eq_sym (eq_sym (map_id cs))) (eq_sym (eq_sym (map_id ds)))
       (fmap[BaseChangeF (fun c : Colour => c) Cdec S S CSigMap_id] t)).
  { exact HU. }
  rewrite (eq_sym_involutive (map_id cs)), (eq_sym_involutive (map_id ds)).
  reflexivity.
Qed.

End BaseChangeIdentity.

(* [CSigMap_id] keeps its auto-generated argument status ({Colour} S):
   its type unfolds to a ∀, so the boundary words and the generator
   ride along as trailing arguments (compare [basechange_val] in
   [Construction/ColouredPROP/BaseChange.v]). *)

(** ** 2. Base change along a composite colour function *)

Section BaseChangeComposite.

Context {Colour Colour' Colour'' : Type}.
Context (f : Colour -> Colour').
Context (g : Colour' -> Colour'').
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (C'dec : forall c d : Colour', {c = d} + {c <> d}).
Context (C''dec : forall c d : Colour'', {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (S' : CSignature Colour').
Context (S'' : CSignature Colour'').
Context (hf : CSigMap f S S').
Context (hg : CSigMap g S' S'').

(** The composite signature morphism over [fun c => g (f c)]: apply
    [hf] then [hg], and reindex the boundary words along [map_map]. *)
Definition CSigMap_compose : CSigMap (fun c : Colour => g (f c)) S S'' :=
  fun (cs ds : list Colour) (s : S cs ds) =>
    csig_transport (map_map f g cs) (map_map f g ds)
      (hg (map f cs) (map f ds) (hf cs ds s)).

(** Local abbreviations for the two legs, their strict structures, and
    their strict tensor comparisons (the [map_app]-shaped object
    equalities pinned by [Example]s in [BaseChange.v]). *)
Notation F1 := (BaseChangeF f C'dec S S' hf).
Notation G1 := (BaseChangeF g C''dec S' S'' hg).
Notation SF1 := (BaseChangeF_Strict f Cdec C'dec S S' hf).
Notation SG1 := (BaseChangeF_Strict g C'dec C''dec S' S'' hg).
Notation apF x y := (@strict_ap_obj _ _ _ _ F1 SF1 x y).
Notation apG x y := (@strict_ap_obj _ _ _ _ G1 SG1 x y).

(*
   本节说明 Laws 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example BaseChangeF_comp_fobj (cs : list Colour) :
  fobj[G1 ◯ F1] cs = map g (map f cs) := eq_refl.

Example BaseChangeF_comp_gen_datum {cs ds : list Colour} (s : S cs ds) :
  fmap[BaseChangeF (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose]
    (CT_gen s)
  = CT_gen (CSigMap_compose cs ds s) := eq_refl.

(** The composite functor is strict monoidal, by the generic
    composition of strict monoidal functors; its strict object
    comparisons are the [eq_trans]/[f_equal] composites of the legs'. *)
Definition BaseChangeF_comp_Strict :
  @StrictMonoidalFunctor (CFreeCat S) (CFreeCat S'')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S'' C''dec)
    (G1 ◯ F1) :=
  @Compose_StrictMonoidalFunctor (CFreeCat S) (CFreeCat S') (CFreeCat S'')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec)
    (CFreeCat_Monoidal S'' C''dec)
    G1 F1 SG1 SF1.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma hf_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ F1 (BaseChangeF_Monoidal f Cdec C'dec S S' hf) x y)
    ≈ id_cast (apF x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ F1 SF1 x y). Qed.

Lemma hg_ap_cast (x y : list Colour') :
  to (@ap_iso _ _ _ _ G1 (BaseChangeF_Monoidal g C'dec C''dec S' S'' hg) x y)
    ≈ id_cast (apG x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ G1 SG1 x y). Qed.

Lemma comp_ap_cast (x y : list Colour) :
  to (@ap_iso _ _ _ _ (G1 ◯ F1)
        (@strict_functor_is_monoidal _ _ _ _ (G1 ◯ F1)
           BaseChangeF_comp_Strict) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ (G1 ◯ F1) BaseChangeF_comp_Strict x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ (G1 ◯ F1) BaseChangeF_comp_Strict x y). Qed.

(*
   本节说明 Laws 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma hf_braid_conj (x y : list Colour) :
  fmap[F1] (CT_braid x y)
    ≈ id_cast (apF y x) ∘ CT_braid (map f x) (map f y)
        ∘ id_cast (eq_sym (apF x y)).
Proof.
  assert (HB := BaseChangeF_SymmetricStrict f Cdec C'dec S S' hf x y).
  rewrite (hf_ap_cast x y), (hf_ap_cast y x) in HB.
  exact (comp_cast_shift (apF x y) (fmap[F1] (CT_braid x y))
           (id_cast (apF y x) ∘ CT_braid (map f x) (map f y)) HB).
Qed.

Lemma hg_braid_conj (x y : list Colour') :
  fmap[G1] (CT_braid x y)
    ≈ id_cast (apG y x) ∘ CT_braid (map g x) (map g y)
        ∘ id_cast (eq_sym (apG x y)).
Proof.
  assert (HB := BaseChangeF_SymmetricStrict g C'dec C''dec S' S'' hg x y).
  rewrite (hg_ap_cast x y), (hg_ap_cast y x) in HB.
  exact (comp_cast_shift (apG x y) (fmap[G1] (CT_braid x y))
           (id_cast (apG y x) ∘ CT_braid (map g x) (map g y)) HB).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma BaseChange_comp_square :
  CSymmetricStrict S Cdec
    (basechange_target (fun c : Colour => g (f c)) C''dec S'')
    (G1 ◯ F1)
    (@strict_functor_is_monoidal _ _ _ _ (G1 ◯ F1) BaseChangeF_comp_Strict).
Proof using C''dec C'dec Cdec Colour Colour' Colour'' S S' S'' f g hf hg.
  intros x y.
  rewrite (comp_ap_cast x y), (comp_ap_cast y x).
  change (fmap[G1 ◯ F1] (CT_braid x y))
    with (fmap[G1] (fmap[F1] (CT_braid x y))).
  rewrite (hf_braid_conj x y).
  rewrite !fmap_comp.
  rewrite (fmap_id_cast G1 (apF y x)).
  rewrite (fmap_id_cast G1 (eq_sym (apF x y))).
  rewrite (hg_braid_conj (map f x) (map f y)).
  rewrite <- !comp_assoc.
  rewrite id_cast_trans.
  rewrite id_cast_trans.
  rewrite (@id_cast_loop (CFreeCat S'') (CFreeCat_ObjDecEq S'' C''dec)).
  rewrite id_right.
  rewrite comp_assoc.
  rewrite id_cast_trans.
  reflexivity.
Qed.

(** Generator agreement of the composite competitor: the conjugating
    cast along [eq_sym (map_map ...)] exactly undoes the
    [CSigMap_compose] transport. *)
Lemma BaseChangeF_comp_gen (cs ds : list Colour) (s : S cs ds) :
  fmap[G1 ◯ F1] (CT_gen s)
    ≈ @hom_cast (CFreeCat S'') _ _ _ _
        (eq_sym (map_map f g cs)) (eq_sym (map_map f g ds))
        (basechange_val (fun c : Colour => g (f c)) C''dec S S''
           CSigMap_compose cs ds s).
Proof.
  unfold basechange_val; cbn beta.
  rewrite CT_gen_hom_cast.
  unfold CSigMap_compose; cbn beta.
  rewrite csig_transport_inv_sym.
  reflexivity.
Qed.

(** Generator agreement of the one-step competitor, with [eq_refl]
    object family — definitional. *)
Lemma BaseChangeF_comp_gen2 (cs ds : list Colour) (s : S cs ds) :
  fmap[BaseChangeF (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose]
    (CT_gen s)
    ≈ @hom_cast (CFreeCat S'') _ _ _ _
        (eq_sym (@eq_refl _ (map (fun c : Colour => g (f c)) cs)))
        (eq_sym (@eq_refl _ (map (fun c : Colour => g (f c)) ds)))
        (basechange_val (fun c : Colour => g (f c)) C''dec S S''
           CSigMap_compose cs ds s).
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem BaseChangeF_comp {cs ds : list Colour} (t : CTerm S cs ds) :
  @hom_cast (CFreeCat S'')
    (map g (map f cs)) (map g (map f ds))
    (map (fun c : Colour => g (f c)) cs) (map (fun c : Colour => g (f c)) ds)
    (map_map f g cs) (map_map f g ds)
    (fmap[G1 ◯ F1] t)
  ≈ fmap[BaseChangeF (fun c : Colour => g (f c)) C''dec S S''
           CSigMap_compose] t.
Proof using C''dec C'dec Cdec Colour Colour' Colour'' S S' S'' f g hf hg.
  exact (@cinterp_unique2 Colour S Cdec
    (basechange_target (fun c : Colour => g (f c)) C''dec S'')
    (CFreeCat_ObjDecEq S'' C''dec)
    (basechange_val (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose)
    (G1 ◯ F1)
    BaseChangeF_comp_Strict
    BaseChange_comp_square
    (fun ks : list Colour => map_map f g ks)
    BaseChangeF_comp_gen
    (BaseChangeF (fun c : Colour => g (f c)) C''dec S S'' CSigMap_compose)
    (BaseChangeF_Strict (fun c : Colour => g (f c)) Cdec C''dec S S''
       CSigMap_compose)
    (BaseChangeF_SymmetricStrict (fun c : Colour => g (f c)) Cdec C''dec
       S S'' CSigMap_compose)
    (fun ks : list Colour => @eq_refl _ (map (fun c : Colour => g (f c)) ks))
    BaseChangeF_comp_gen2
    cs ds t).
Qed.

End BaseChangeComposite.

(* [CSigMap_compose] keeps its auto-generated argument status
   ({Colour Colour' Colour''} f g S S' S'' hf hg): its type unfolds to
   a ∀, so the boundary words and the generator ride along as trailing
   arguments. *)
Arguments BaseChangeF_comp_Strict {Colour Colour' Colour''} f g Cdec C'dec
  C''dec S S' S'' hf hg : assert.

(** ** 3. Subset restriction: base change along a subtype projection *)

(** The subtype of colours satisfying a predicate [Q].  Base change
    along the first projection restricts a free coloured PROP over
    [Colour] to the colours in [Q]. *)
Definition ColourSub {Colour : Type} (Q : Colour -> Prop) : Type :=
  { c : Colour | Q c }.

Section SubsetRestriction.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).
Context (Q : Colour -> Prop).
Context (Ssub : CSignature (ColourSub Q)).

(*
   本节说明 Laws 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (CdecSub : forall a b : ColourSub Q, {a = b} + {a <> b}).
Context (hsub : CSigMap (@proj1_sig Colour Q) Ssub S).

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SubColourFunctor : CFreeCat Ssub ⟶ CFreeCat S :=
  BaseChangeF (@proj1_sig Colour Q) Cdec Ssub S hsub.

Definition SubColourFunctor_Monoidal :
  @MonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Monoidal Ssub CdecSub) (CFreeCat_Monoidal S Cdec)
    SubColourFunctor :=
  BaseChangeF_Monoidal (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_Strict :
  @StrictMonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Monoidal Ssub CdecSub) (CFreeCat_Monoidal S Cdec)
    SubColourFunctor :=
  BaseChangeF_Strict (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_Braided :
  @BraidedMonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Braided Ssub CdecSub) (CFreeCat_Braided S Cdec)
    SubColourFunctor :=
  BaseChangeF_Braided (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat Ssub) (CFreeCat S)
    (CFreeCat_Symmetric Ssub CdecSub) (CFreeCat_Symmetric S Cdec)
    SubColourFunctor :=
  BaseChangeF_Symmetric (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

Definition SubColourFunctor_SymmetricStrict :
  CSymmetricStrict Ssub CdecSub
    (basechange_target (@proj1_sig Colour Q) Cdec S)
    SubColourFunctor SubColourFunctor_Monoidal :=
  BaseChangeF_SymmetricStrict (@proj1_sig Colour Q) CdecSub Cdec Ssub S hsub.

(** Machine-checked: the restriction acts on objects by erasing the
    membership proofs, and on generators through [hsub]. *)
Example SubColourFunctor_fobj (cs : list (ColourSub Q)) :
  fobj[SubColourFunctor] cs = map (@proj1_sig Colour Q) cs := eq_refl.

Example SubColourFunctor_gen {cs ds : list (ColourSub Q)}
  (s : Ssub cs ds) :
  fmap[SubColourFunctor] (CT_gen s) = CT_gen (hsub cs ds s) := eq_refl.

(** A restricted wire is the wire of the underlying colour. *)
Example SubColourFunctor_wire (c : ColourSub Q) :
  fmap[SubColourFunctor] (CT_id [c]) = CT_id [proj1_sig c] := eq_refl.

End SubsetRestriction.

Arguments SubColourFunctor {Colour} Cdec S Q Ssub hsub : assert.

(** ** 4. Descent to presented coloured PROPs *)

Section PresentedDescent.

Context {Colour Colour' : Type}.
Context (f : Colour -> Colour').
Context (C'dec : forall c d : Colour', {c = d} + {c <> d}).
Context (E : CSMT Colour).
Context (E' : CSMT Colour').
Context (hE : CSigMap f (csmt_sig E) (csmt_sig E')).

(** The base-change functor between the underlying free categories. *)
Notation BF := (BaseChangeF f C'dec (csmt_sig E) (csmt_sig E') hE).

(*
   本节说明 Laws 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition BaseChangeRespects : Type :=
  forall (cs ds : list Colour) (s t : CTerm (csmt_sig E) cs ds),
    csmt_eqs E cs ds s t ->
    CTermEqW E' (fmap[BF] s) (fmap[BF] t).

Context (HR : BaseChangeRespects).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma BaseChange_CTermEqW {cs ds : list Colour}
  {s t : CTerm (csmt_sig E) cs ds} :
  CTermEqW E s t -> CTermEqW E' (fmap[BF] s) (fmap[BF] t).
Proof using C'dec E E' HR f hE.
  intros H.
  induction H as
    [ cs0 ds0 s0 t0 Hst
    | cs0 ds0 s0 t0 Hax
    | cs0 ds0 s0 t0 Hst IH
    | cs0 ds0 s0 t0 u0 Hst IH1 Htu IH2
    | cs0 ds0 es0 f0 f0' g0 g0' Hf IHf Hg IHg
    | cs1 ds1 cs2 ds2 f0 f0' g0 g0' Hf IHf Hg IHg ].
  - (* CTEW_termeq: a free equation, through fmap_respects *)
    apply CTEW_termeq.
    exact (@fmap_respects _ _ BF cs0 ds0 s0 t0 Hst).
  - (* CTEW_ax: an axiom of E, through the respect hypothesis *)
    exact (HR cs0 ds0 s0 t0 Hax).
  - (* CTEW_sym *)
    exact (CTEW_sym E' _ _ IH).
  - (* CTEW_trans *)
    exact (CTEW_trans E' _ _ _ IH1 IH2).
  - (* CTEW_comp: fmap computes to CT_comp on both sides *)
    exact (CTEW_comp E' _ _ _ _ IHf IHg).
  - (* CTEW_tens: fmap computes to a cast-conjugated CT_tens; the
       casts agree on both sides, so two composition congruences
       around the tensor congruence close the goal *)
    exact (CTEW_comp E' _ _ _ _
             (CTEW_comp E' _ _ _ _
                (CTermEqW_refl E' _)
                (CTEW_tens E' _ _ _ _ IHf IHg))
             (CTermEqW_refl E' _)).
Qed.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PresentedBaseChange : CPresentedCat E ⟶ CPresentedCat E' :=
  @QuotientLift (CFreeCat (csmt_sig E))
    (fun cs ds : list Colour => @CTermEqW Colour E cs ds)
    (CTermEqW_Congruence E)
    (CPresentedCat E')
    (CPresentedProj E' ◯ BF)
    (fun (cs ds : list Colour) (s t : CTerm (csmt_sig E) cs ds)
         (H : CTermEqW E s t) => BaseChange_CTermEqW H).

(** Machine-checked: the descended functor acts on objects by [map f],
    on quotiented terms by [fmap[BF]], and the descent square with the
    two projections commutes definitionally. *)
Example PresentedBaseChange_fobj (cs : list Colour) :
  fobj[PresentedBaseChange] cs = map f cs := eq_refl.

Example PresentedBaseChange_fmap {cs ds : list Colour}
  (t : CTerm (csmt_sig E) cs ds) :
  fmap[PresentedBaseChange] (cquot E t) = cquot E' (fmap[BF] t) := eq_refl.

Example PresentedBaseChange_factor {cs ds : list Colour}
  (t : CTerm (csmt_sig E) cs ds) :
  fmap[PresentedBaseChange] (fmap[CPresentedProj E] t)
  = fmap[CPresentedProj E'] (fmap[BF] t) := eq_refl.

(** Every axiom of [E] holds in [CPresentedCat E'] after descent — the
    end-to-end form of [BaseChangeRespects]. *)
Example PresentedBaseChange_respects_axioms {cs ds : list Colour}
  (s t : CTerm (csmt_sig E) cs ds) (Hax : csmt_eqs E cs ds s t) :
  fmap[PresentedBaseChange] (cquot E s)
    ≈[CPresentedCat E'] fmap[PresentedBaseChange] (cquot E t) :=
  HR cs ds s t Hax.

End PresentedDescent.

Arguments BaseChangeRespects {Colour Colour'} f C'dec E E' hE : assert.
Arguments PresentedBaseChange {Colour Colour'} f C'dec E E' hE HR : assert.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
