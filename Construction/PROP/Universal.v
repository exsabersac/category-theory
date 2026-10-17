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
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Structural.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The universal property of the free PROP *)

(*
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   本文件给出泛构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition MonoidalFunctor_transport {C D : Category} {MC : @Monoidal C}
  {N1 N2 : @Monoidal D} (e : N1 = N2) {F : C ⟶ D} :
  @MonoidalFunctor C D MC N1 F → @MonoidalFunctor C D MC N2 F :=
  match e in _ = N
        return @MonoidalFunctor C D MC N1 F → @MonoidalFunctor C D MC N F
  with eq_refl => fun X => X end.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ap_iso_transport {C D : Category} {MC : @Monoidal C}
  {N1 N2 : @Monoidal D} (e : N1 = N2) {F : C ⟶ D}
  (MF : @MonoidalFunctor C D MC N1 F) (x y : C) :
  to (@ap_iso C D MC N2 F (MonoidalFunctor_transport e MF) x y)
  = match e in _ = N
          return ((F x ⨂[N] F y)%object ~{D}~> F ((x ⨂[MC] y)%object))
    with eq_refl => to (@ap_iso C D MC N1 F MF x y) end.
Proof. destruct e; reflexivity. Qed.

Section Universal.

Context (S : Signature).
Context (P : PROP).
Context {HP : HomEqProp P}.
Context {OD : @ObjDecEq P}.
Context (v : Valuation P S).

Open Scope nat_scope.

Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma InterpF_fmap_id (n : nat) :
  interp P S v (T_id n) ≈ id[⟦n⟧].
Proof. reflexivity. Qed.

Lemma InterpF_fmap_comp {m n p : nat} (f : Term S n p) (g : Term S m n) :
  interp P S v (T_comp f g) ≈ interp P S v f ∘ interp P S v g.
Proof. reflexivity. Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition InterpF : FreeCat S ⟶ P :=
  Build_Functor (FreeCat S) P
    (@prop_of_nat P)
    (fun m n t => interp P S v t)
    (fun m n s t Hst => interp_sound P S v Hst)
    InterpF_fmap_id
    (fun m n p f g => InterpF_fmap_comp f g).

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example InterpF_extends_valuation (m n : nat) (g : S m n) :
  fmap[InterpF] (T_gen g) = v m n g := eq_refl.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Naturality of the tensor-comparison cast against [interp]: the
    conjugating cast of [⊞] cancels its inverse. *)
Lemma interp_ap_natural {m n m' n'} (f : Term S m m') (g : Term S n n') :
  interp P S v (T_tens f g) ∘ id_cast (prop_tensor_plus m n)
    ≈ id_cast (prop_tensor_plus m' n')
        ∘ (interp P S v f ⨂[MP P] interp P S v g).
Proof.
  cbn [interp].
  unfold prop_tensor_hom.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(** The inverse-direction square, by flipping across the casts. *)
Lemma interp_ap_natural_from {m n m' n'} (f : Term S m m') (g : Term S n n') :
  (interp P S v f ⨂[MP P] interp P S v g)
      ∘ id_cast (eq_sym (prop_tensor_plus m n))
    ≈ id_cast (eq_sym (prop_tensor_plus m' n'))
        ∘ interp P S v (T_tens f g).
Proof.
  apply id_cast_flip.
  apply interp_ap_natural.
Qed.

(** General left-unit coherence: with every comparison an [id_cast],
    the left-unitality square collapses to the strict unitor. *)
Lemma to_unit_left_cast_general {u w s : P}
  (eu : @I P (MP P) = u) (e : (u ⨂[MP P] w)%object = s) (d : s = w) :
  to (@unit_left P (MP P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id_cast eu ⨂[MP P] id[w]).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_left_obj w)).
  rewrite !id_right.
  symmetry; apply strict_unitl_cast.
Qed.

(** General right-unit coherence. *)
Lemma to_unit_right_cast_general {u w s : P}
  (eu : @I P (MP P) = u) (e : (w ⨂[MP P] u)%object = s) (d : s = w) :
  to (@unit_right P (MP P) w)
    ≈ id_cast d ∘ id_cast e ∘ (id[w] ⨂[MP P] id_cast eu).
Proof using OD P.
  destruct eu, e.
  rewrite !id_cast_refl.
  rewrite bimap_id_id.
  rewrite (obj_uip d (strict_unit_right_obj w)).
  rewrite !id_right.
  symmetry; apply strict_unitr_cast.
Qed.

(** General associativity coherence. *)
Lemma to_assoc_cast_general {a b c ab bc u w : P}
  (eab : (a ⨂[MP P] b)%object = ab)
  (ebc : (b ⨂[MP P] c)%object = bc)
  (eu : (ab ⨂[MP P] c)%object = u)
  (ew : (a ⨂[MP P] bc)%object = w)
  (d : u = w) :
  id_cast d ∘ id_cast eu ∘ (id_cast eab ⨂[MP P] id[c])
    ≈ id_cast ew ∘ (id[a] ⨂[MP P] id_cast ebc)
        ∘ to (@tensor_assoc P (MP P) a b c).
Proof using OD P.
  destruct eab, ebc, eu, ew.
  rewrite !id_cast_refl.
  rewrite !bimap_id_id.
  rewrite (obj_uip d (strict_assoc_obj a b c)).
  rewrite !id_right, !id_left.
  apply strict_assoc_cast.
Qed.

(** The left-unitality field of [MonoidalFunctor] at [InterpF]. *)
Lemma interp_monoidal_unit_left (x : nat) :
  to (@unit_left P (MP P) ⟦x⟧)
    ≈ interp P S v (T_cast (Nat.add_0_l x))
        ∘ id_cast (prop_tensor_plus 0 x)
        ∘ (id_cast (@prop_unit_zero P) ⨂[MP P] id[⟦x⟧]).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_unit_left_cast_general.
Qed.

(** The right-unitality field of [MonoidalFunctor] at [InterpF]. *)
Lemma interp_monoidal_unit_right (x : nat) :
  to (@unit_right P (MP P) ⟦x⟧)
    ≈ interp P S v (T_cast (Nat.add_0_r x))
        ∘ id_cast (prop_tensor_plus x 0)
        ∘ (id[⟦x⟧] ⨂[MP P] id_cast (@prop_unit_zero P)).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_unit_right_cast_general.
Qed.

(** The associativity field of [MonoidalFunctor] at [InterpF]. *)
Lemma interp_monoidal_assoc (x y z : nat) :
  interp P S v (T_cast (eq_sym (Nat.add_assoc x y z)))
      ∘ id_cast (prop_tensor_plus (x + y) z)
      ∘ (id_cast (prop_tensor_plus x y) ⨂[MP P] id[⟦z⟧])
    ≈ id_cast (prop_tensor_plus x (y + z))
        ∘ (id[⟦x⟧] ⨂[MP P] id_cast (prop_tensor_plus y z))
        ∘ to (@tensor_assoc P (MP P) ⟦x⟧ ⟦y⟧ ⟦z⟧).
Proof using OD P S v.
  rewrite interp_T_cast.
  unfold hcast.
  apply to_assoc_cast_general.
Qed.

(** The braid-compatibility square of [interp] against the target's
    strict-path braiding [strict_braid]. *)
Lemma interp_braid_ap (m n : nat) :
  interp P S v (T_braid m n) ∘ id_cast (prop_tensor_plus m n)
    ≈ id_cast (prop_tensor_plus n m) ∘ strict_braid P ⟦m⟧ ⟦n⟧.
Proof.
  cbn [interp].
  unfold prop_braid.
  rewrite <- comp_assoc.
  rewrite id_cast_inv_l.
  now rewrite id_right.
Qed.

(** ** 3. The strong and strict monoidal structure on [InterpF]

    The tensor comparison is the [prop_tensor_plus] cast, packaged as
    a natural isomorphism in the functor category. *)

Definition InterpF_ap_dom : FreeCat S ∏ FreeCat S ⟶ P :=
  @tensor P (MP P) ◯ InterpF ∏⟶ InterpF.

Definition InterpF_ap_cod : FreeCat S ∏ FreeCat S ⟶ P :=
  InterpF ◯ @tensor (FreeCat S) (FreeCat_Monoidal S).

Definition InterpF_ap_to : InterpF_ap_dom ⟹ InterpF_ap_cod :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) P InterpF_ap_dom InterpF_ap_cod
    (fun mn => id_cast (prop_tensor_plus (fst mn) (snd mn)))
    (fun x y f => interp_ap_natural (fst f) (snd f)).

Definition InterpF_ap_from : InterpF_ap_cod ⟹ InterpF_ap_dom :=
  @Build_Transform' (FreeCat S ∏ FreeCat S) P InterpF_ap_cod InterpF_ap_dom
    (fun mn => id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn))))
    (fun x y f => interp_ap_natural_from (fst f) (snd f)).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma InterpF_ap_to_from (mn : FreeCat S ∏ FreeCat S) :
  id_cast (prop_tensor_plus (fst mn) (snd mn))
      ∘ id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
    ≈ interp P S v (T_tens (T_id (fst mn)) (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_r.
  symmetry.
  cbn [interp].
  apply tensor_hom_id.
Qed.

Lemma InterpF_ap_from_to (mn : FreeCat S ∏ FreeCat S) :
  id_cast (eq_sym (prop_tensor_plus (fst mn) (snd mn)))
      ∘ id_cast (prop_tensor_plus (fst mn) (snd mn))
    ≈ (interp P S v (T_id (fst mn)) ⨂[MP P] interp P S v (T_id (snd mn))).
Proof.
  rewrite id_cast_inv_l.
  symmetry.
  cbn [interp].
  apply bimap_id_id.
Qed.

Program Definition InterpF_ap_iso :
  InterpF_ap_dom ≅[[FreeCat S ∏ FreeCat S, P]] InterpF_ap_cod := {|
  to := InterpF_ap_to;
  from := InterpF_ap_from;
  iso_to_from := InterpF_ap_to_from;
  iso_from_to := InterpF_ap_from_to
|}.

(** The strong monoidal structure.  All proof fields are the named
    lemmas of section 2; the derived-iso data fields are casts. *)
Program Definition InterpF_Monoidal :
  @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) InterpF := {|
  pure_iso := id_cast_iso (@prop_unit_zero P);
  ap_functor_iso := InterpF_ap_iso;
  pure_iso_left := fun x : nat => @unit_left P (MP P) ⟦x⟧;
  pure_iso_right := fun x : nat =>
    iso_compose
      (id_cast_iso (f_equal (@prop_of_nat P) (eq_sym (Nat.add_0_r x))))
      (@unit_right P (MP P) ⟦x⟧);
  ap_iso_assoc := fun x y z : nat =>
    id_cast_iso
      (eq_trans
         (f_equal (fun u : P => (u ⨂[MP P] ⟦z⟧)%object)
                  (prop_tensor_plus x y))
         (eq_trans (prop_tensor_plus (x + y) z)
                   (f_equal (@prop_of_nat P)
                            (eq_sym (Nat.add_assoc x y z)))));
  monoidal_unit_left := interp_monoidal_unit_left;
  monoidal_unit_right := interp_monoidal_unit_right;
  monoidal_assoc := interp_monoidal_assoc
|}.

(** The comparisons ARE the PROP's strictness equalities, verbatim. *)
Lemma InterpF_strict_pure_iso_id :
  to (@pure_iso _ _ _ _ InterpF InterpF_Monoidal)
    ≈ match @prop_unit_zero P in _ = T return @I P (MP P) ~{P}~> T
      with eq_refl => id end.
Proof. reflexivity. Qed.

Lemma InterpF_strict_ap_iso_id (x y : nat) :
  to (@ap_iso _ _ _ _ InterpF InterpF_Monoidal x y)
    ≈ match @prop_tensor_plus P x y in _ = T
            return ((InterpF x ⨂[MP P] InterpF y)%object ~{P}~> T)
      with eq_refl => id end.
Proof. reflexivity. Qed.

Program Definition InterpF_Strict :
  @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) InterpF := {|
  strict_functor_is_monoidal := InterpF_Monoidal;
  strict_pure_obj := @prop_unit_zero P;               (* the PROP field *)
  strict_ap_obj := fun x y : nat => @prop_tensor_plus P x y;  (* ditto *)
  strict_pure_iso_id := InterpF_strict_pure_iso_id;
  strict_ap_iso_id := InterpF_strict_ap_iso_id
|}.

(** Machine-checked: the strict object comparisons of [InterpF_Strict]
    are the PROP class fields themselves. *)
Example InterpF_strict_pure_obj_is_prop_unit_zero :
  @strict_pure_obj _ _ _ _ InterpF InterpF_Strict = @prop_unit_zero P
  := eq_refl.

Example InterpF_strict_ap_obj_is_prop_tensor_plus (x y : nat) :
  @strict_ap_obj _ _ _ _ InterpF InterpF_Strict x y = @prop_tensor_plus P x y
  := eq_refl.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SymmetricStrict (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G) : Type :=
  ∀ m n : nat,
    fmap[G] (T_braid m n) ∘ to (@ap_iso _ _ _ _ G MG m n)
      ≈ to (@ap_iso _ _ _ _ G MG n m) ∘ strict_braid P (G m) (G n).

Lemma InterpF_SymmetricStrict : SymmetricStrict InterpF InterpF_Monoidal.
Proof.
  intros m n.
  exact (interp_braid_ap m n).
Qed.

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma SymmetricStrict_square_transport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N1 G)
  (b : braid_family N2) (x y : nat) :
  fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y) →
  fmap[G] (T_braid x y)
      ∘ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
    ≈ to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) y x)
        ∘ b (G x) (G y).
Proof.
  revert b; destruct e; intros b H.
  exact H.
Qed.

(** The converse direction: a braid square at the transported functor
    comes back to one at the original, against the transported braid. *)
Lemma SymmetricStrict_untransport
  {N1 N2 : @Monoidal P} (e : N1 = N2)
  (G : FreeCat S ⟶ P)
  (MG : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N1 G)
  (MG' : @MonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) N2 G)
  (b : braid_family N2)
  (Hap : ∀ x y : nat,
     to (@ap_iso _ _ _ _ G (MonoidalFunctor_transport e MG) x y)
       ≈ to (@ap_iso _ _ _ _ G MG' x y))
  (Hsq : ∀ x y : nat,
     fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG' x y)
       ≈ to (@ap_iso _ _ _ _ G MG' y x) ∘ b (G x) (G y)) :
  ∀ x y : nat,
    fmap[G] (T_braid x y) ∘ to (@ap_iso _ _ _ _ G MG x y)
      ≈ to (@ap_iso _ _ _ _ G MG y x) ∘ transport_braid e b (G x) (G y).
Proof.
  revert MG' b Hap Hsq; destruct e; intros MG' b Hap Hsq x y.
  simpl in Hap.
  rewrite (Hap x y), (Hap y x).
  exact (Hsq x y).
Qed.

(** [InterpF] as a [BraidedMonoidalFunctor]: the underlying
    strong structure is [InterpF_Monoidal] transported across the
    coherence, and the braid square is [InterpF_SymmetricStrict]. *)
Program Definition InterpF_Braided :
  @BraidedMonoidalFunctor (FreeCat S) P (FreeCat_Braided S)
    (@symmetric_is_braided P (@prop_symmetric P)) InterpF := {|
  braided_is_strong :=
    MonoidalFunctor_transport (@prop_monoidal_coherence P) InterpF_Monoidal
|}.
Next Obligation.
  exact (SymmetricStrict_square_transport (@prop_monoidal_coherence P)
           InterpF InterpF_Monoidal
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@prop_symmetric P)) a b)
           x y (InterpF_SymmetricStrict x y)).
Qed.

(** [SymmetricMonoidalFunctor] is a [Definition] alias in
    [Functor/Structure/Monoidal/Braided.v], so the instance is supplied
    explicitly rather than by class search. *)
Definition InterpF_Symmetric :
  @SymmetricMonoidalFunctor (FreeCat S) P (FreeCat_Symmetric S)
    (@prop_symmetric P) InterpF := InterpF_Braided.

(** Competitors arriving with a [BraidedMonoidalFunctor]
    convert to [SymmetricStrict], given that their two tensor
    comparisons agree across the coherence transport. *)
Corollary SymmetricStrict_of_Braided
  (G : FreeCat S ⟶ P)
  (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G)
  (BG : @BraidedMonoidalFunctor (FreeCat S) P (FreeCat_Braided S)
          (@symmetric_is_braided P (@prop_symmetric P)) G)
  (Hap : ∀ x y : nat,
     to (@ap_iso _ _ _ _ G
           (MonoidalFunctor_transport (@prop_monoidal_coherence P)
              (@strict_functor_is_monoidal _ _ _ _ G SG)) x y)
       ≈ to (@ap_iso _ _ _ _ G (@braided_is_strong _ _ _ _ G BG) x y)) :
  SymmetricStrict G SG.
Proof.
  exact (SymmetricStrict_untransport (@prop_monoidal_coherence P) G
           (@strict_functor_is_monoidal _ _ _ _ G SG)
           (@braided_is_strong _ _ _ _ G BG)
           (fun a b : P =>
              @braid P (@symmetric_is_braided P (@prop_symmetric P)) a b)
           Hap
           (fun x y => @braid_compat _ _ _ _ G BG x y)).
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Uniqueness.

Context (G : FreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S)
                (MP P) G).
Context (HB : SymmetricStrict G SG).
Context (Hobj : ∀ n : nat, G n = ⟦n⟧).
Context (Hgen : ∀ m n (g : S m n),
  fmap[G] (T_gen g)
    ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (v m n g)).

(** The tensor comparison of [SG], spelled as an [id_cast]. *)
Lemma G_ap_cast (x y : nat) :
  to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG) x y)
    ≈ id_cast (@strict_ap_obj _ _ _ _ G SG x y).
Proof. exact (@strict_ap_iso_id _ _ _ _ G SG x y). Qed.

(** Naturality of [SG]'s tensor comparison at a pair of terms. *)
Lemma G_ap_natural {m1 m2 n1 n2 : nat}
  (f : Term S m1 n1) (g : Term S m2 n2) :
  fmap[G] (T_tens f g)
      ∘ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
              m1 m2)
    ≈ to (@ap_iso _ _ _ _ G (@strict_functor_is_monoidal _ _ _ _ G SG)
            n1 n2)
        ∘ (fmap[G] f ⨂[MP P] fmap[G] g).
Proof.
  exact (naturality
           (to (@ap_functor_iso _ _ _ _ G
                  (@strict_functor_is_monoidal _ _ _ _ G SG)))
           (m1, m2) (n1, n2) (f, g)).
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem interp_unique : ∀ m n (t : Term S m n),
  fmap[G] t ≈ hom_cast (eq_sym (Hobj m)) (eq_sym (Hobj n)) (interp P S v t).
Proof using G HB Hgen Hobj OD P S SG v.
  intros m n t.
  induction t as [k | bm bn | cm cn cp tg IHg tf IHf
                  | m1 n1 m2 n2 tf IHf tg IHg | gm gn gs].
  - (* T_id *)
    cbn [interp].
    rewrite hom_cast_id.
    exact (@fmap_id (FreeCat S) P G k).
  - (* T_braid *)
    cbn [interp].
    unfold prop_braid.
    assert (Hb : fmap[G] (T_braid bm bn)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG bn bm)
                  ∘ strict_braid P (G bm) (G bn)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG bm bn))).
    { apply comp_cast_shift.
      rewrite <- !G_ap_cast.
      apply HB. }
    rewrite Hb.
    rewrite (strict_braid_cast P (eq_sym (Hobj bm)) (eq_sym (Hobj bn))).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* T_comp *)
    cbn [interp].
    rewrite <- (hom_cast_comp (eq_sym (Hobj cm)) (eq_sym (Hobj cn))
                  (eq_sym (Hobj cp))).
    rewrite <- IHg, <- IHf.
    exact (@fmap_comp (FreeCat S) P G cm cn cp tg tf).
  - (* T_tens *)
    cbn [interp].
    unfold prop_tensor_hom.
    assert (Ht : fmap[G] (T_tens tf tg)
              ≈ id_cast (@strict_ap_obj _ _ _ _ G SG n1 n2)
                  ∘ (fmap[G] tf ⨂[MP P] fmap[G] tg)
                  ∘ id_cast (eq_sym (@strict_ap_obj _ _ _ _ G SG m1 m2))).
    { apply comp_cast_shift.
      rewrite <- !G_ap_cast.
      apply G_ap_natural. }
    rewrite Ht.
    rewrite IHf, IHg.
    rewrite (bimap_hom_cast P).
    rewrite !hom_cast_decompose.
    rewrite !id_cast_conj_fuse.
    apply id_cast_conj_irr.
  - (* T_gen *)
    apply Hgen.
Qed.

End Uniqueness.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example InterpF_generator_agreement (m n : nat) (g : S m n) :
  fmap[InterpF] (T_gen g)
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (v m n g).
Proof. reflexivity. Qed.

Example InterpF_interp_unique_self (m n : nat) (t : Term S m n) :
  fmap[InterpF] t
    ≈ hom_cast (eq_sym (@eq_refl _ ⟦m⟧)) (eq_sym (@eq_refl _ ⟦n⟧))
               (interp P S v t).
Proof.
  exact (interp_unique InterpF InterpF_Strict InterpF_SymmetricStrict
           (fun k : nat => eq_refl) InterpF_generator_agreement m n t).
Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniquenessFromOne.

Context (G : FreeCat S ⟶ P).
Context (SG : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S)
                (MP P) G).
Context (HB : SymmetricStrict G SG).
Context (H1 : G 1 = ⟦1⟧).

Fixpoint G_obj (n : nat) : G n = ⟦n⟧ :=
  match n with
  | O => eq_trans (eq_sym (@strict_pure_obj _ _ _ _ G SG))
                  (@prop_unit_zero P)
  | Datatypes.S k =>
      eq_trans
        (eq_sym (@strict_ap_obj _ _ _ _ G SG 1 k))
        (eq_trans
           (f_equal2 (fun a b : P => (a ⨂[MP P] b)%object) H1 (G_obj k))
           (@prop_tensor_plus P 1 k))
  end.

Corollary interp_unique_from_one
  (Hgen : ∀ m n (g : S m n),
     fmap[G] (T_gen g)
       ≈ hom_cast (eq_sym (G_obj m)) (eq_sym (G_obj n)) (v m n g)) :
  ∀ m n (t : Term S m n),
    fmap[G] t ≈ hom_cast (eq_sym (G_obj m)) (eq_sym (G_obj n))
                         (interp P S v t).
Proof using G H1 HB OD P S SG v. exact (interp_unique G SG HB G_obj Hgen). Qed.

End UniquenessFromOne.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary interp_unique2
  (G1 : FreeCat S ⟶ P)
  (SG1 : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G1)
  (HB1 : SymmetricStrict G1 SG1)
  (Hobj1 : ∀ n : nat, G1 n = ⟦n⟧)
  (Hgen1 : ∀ m n (g : S m n),
     fmap[G1] (T_gen g)
       ≈ hom_cast (eq_sym (Hobj1 m)) (eq_sym (Hobj1 n)) (v m n g))
  (G2 : FreeCat S ⟶ P)
  (SG2 : @StrictMonoidalFunctor (FreeCat S) P (FreeCat_Monoidal S) (MP P) G2)
  (HB2 : SymmetricStrict G2 SG2)
  (Hobj2 : ∀ n : nat, G2 n = ⟦n⟧)
  (Hgen2 : ∀ m n (g : S m n),
     fmap[G2] (T_gen g)
       ≈ hom_cast (eq_sym (Hobj2 m)) (eq_sym (Hobj2 n)) (v m n g)) :
  ∀ m n (t : Term S m n),
    hom_cast (Hobj1 m) (Hobj1 n) (fmap[G1] t)
      ≈ hom_cast (Hobj2 m) (Hobj2 n) (fmap[G2] t).
Proof using OD P S v.
  intros m n t.
  rewrite (interp_unique G1 SG1 HB1 Hobj1 Hgen1 m n t).
  rewrite (interp_unique G2 SG2 HB2 Hobj2 Hgen2 m n t).
  now rewrite !hom_cast_roundtrip.
Qed.

End Universal.

Arguments InterpF S P {HP OD} v : assert.
Arguments SymmetricStrict S P G MG : assert.
