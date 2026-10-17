Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Functor.Strong.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Monad.Strong.

Generalizable All Variables.

(** Strong monads over a symmetric monoidal base: the full right strength. *)

(*
   nLab: https://ncatlab.org/nlab/show/commutative+monad

   本文件给出（余）强度/强（余）单子相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section StrongSymmetric.

Context {C : Category}.
Context `{SM : @SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{SMon : @StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(** ** Naturality corollaries in single-variable rewrite form.          *)
(* ------------------------------------------------------------------ *)

(* Clean the identity components out of a joint naturality square. *)
Local Ltac cleanup_nat SN :=
  repeat (rewrite ?bimap_id_id in SN; rewrite ?fmap_id in SN);
  rewrite ?id_left, ?id_right in SN.

(* Massage a joint (factored) naturality square into single-bimap form. *)
Local Ltac fuse_nat SN :=
  rewrite <- ?fmap_comp in SN;
  rewrite <- ?comp_assoc in SN;
  rewrite ?bimap_id_left_right in SN.

Lemma strength_natural_l {x y z} (g : x ~> y) :
  fmap[M] (g ⨂ id[z]) ∘ strength[M] ≈ strength[M] ∘ (g ⨂ id[M z]).
Proof.
  pose proof (@strength_natural _ _ M _ x y g z z (id[z])) as SN.
  simpl in SN.
  cleanup_nat SN.
  exact SN.
Qed.

Lemma strength_natural_r {x z w} (h : z ~> w) :
  fmap[M] (id[x] ⨂ h) ∘ strength[M] ≈ strength[M] ∘ (id[x] ⨂ fmap[M] h).
Proof.
  pose proof (@strength_natural _ _ M _ x x (id[x]) z w h) as SN.
  simpl in SN.
  cleanup_nat SN.
  exact SN.
Qed.

Lemma rstr_natural_l {x z y} (f : x ~> z) :
  fmap[M] (f ⨂ id[y]) ∘ rstr ≈ rstr ∘ (fmap[M] f ⨂ id[y]).
Proof.
  pose proof (@rstr_natural _ _ M _ x z y y f (id[y])) as RN.
  rewrite ?fmap_id in RN.
  exact RN.
Qed.

Lemma rstr_natural_r {x y w} (g : y ~> w) :
  fmap[M] (id[x] ⨂ g) ∘ rstr ≈ rstr ∘ (id[M x] ⨂ g).
Proof.
  pose proof (@rstr_natural _ _ M _ x x y w (id[x]) g) as RN.
  rewrite ?fmap_id in RN.
  exact RN.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The double-strength toolkit: unit laws and naturality.           *)
(* ------------------------------------------------------------------ *)

(* Feeding a returned value into the left factor of [dstr] leaves just the
   left strength: the rstr leg collapses by [rstr_ret] and [join_ret]. *)
Lemma dstr_ret_left {x y} :
  dstr ∘ (ret[M] ⨂ id[M y]) ≈ (strength[M] : x ⨂ M y ~> M (x ⨂ y)).
Proof.
  unfold dstr.
  rewrite <- !comp_assoc.
  rewrite rstr_ret.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(* Mirror: feeding a returned value into the right factor of [dstr'] leaves
   just the derived right strength. *)
Lemma dstr'_ret_right {x y} :
  dstr' ∘ (id[M x] ⨂ ret[M]) ≈ (rstr : M x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold dstr'.
  rewrite <- !comp_assoc.
  rewrite strength_ret.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma dstr'_ret_left {x y} :
  dstr' ∘ (ret[M] ⨂ id[M y]) ≈ (strength[M] : x ⨂ M y ~> M (x ⨂ y)).
Proof.
  unfold dstr'.
  rewrite <- !comp_assoc.
  rewrite <- strength_natural_l.
  rewrite (comp_assoc (fmap[M] rstr)).
  rewrite <- fmap_comp.
  rewrite rstr_ret.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

Lemma dstr_ret_right {x y} :
  dstr ∘ (id[M x] ⨂ ret[M]) ≈ (rstr : M x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold dstr.
  rewrite <- !comp_assoc.
  rewrite <- rstr_natural_r.
  rewrite (comp_assoc (fmap[M] strength[M])).
  rewrite <- fmap_comp.
  rewrite strength_ret.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(* Both factors pure at once: the double strength collapses to the unit.
   Shared by [kl_pure_tensor] (Monad/Kleisli/Commutative.v) and the
   thunkability development (Monad/Thunkable.v). *)
Lemma dstr_ret_ret {x y} :
  dstr ∘ (ret[M] ⨂ ret[M]) ≈ (ret[M] : x ⨂ y ~{C}~> M (x ⨂ y)).
Proof.
  transitivity (dstr ∘ ((ret[M] ⨂ id[M y]) ∘ (id[x] ⨂ ret[M]))).
  - apply compose_respects; [reflexivity|].
    rewrite <- bimap_comp.
    now rewrite id_left, id_right.
  - rewrite comp_assoc.
    rewrite dstr_ret_left.
    apply strength_ret.
Qed.

Lemma dstr_natural {x y z w} (u : x ~> z) (v : y ~> w) :
  fmap[M] (u ⨂ v) ∘ dstr ≈ dstr ∘ (fmap[M] u ⨂ fmap[M] v).
Proof.
  unfold dstr.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@strength_natural _ _ M _ x z u y w v) as SN.
  simpl in SN.
  fuse_nat SN.
  rewrite <- (@rstr_natural _ _ M _ x z (fobj[M] y) (fobj[M] w) u (fmap[M] v)).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite SN.
  reflexivity.
Qed.

Lemma dstr'_natural {x y z w} (u : x ~> z) (v : y ~> w) :
  fmap[M] (u ⨂ v) ∘ dstr' ≈ dstr' ∘ (fmap[M] u ⨂ fmap[M] v).
Proof.
  unfold dstr'.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  pose proof (@strength_natural _ _ M _ (fobj[M] x) (fobj[M] z) (fmap[M] u) y w v) as SN.
  simpl in SN.
  fuse_nat SN.
  rewrite <- SN.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite (@rstr_natural _ _ M _ x z y w u v).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Führmann's reassociation lemmas.                                 *)
(* ------------------------------------------------------------------ *)

(* Rebracketing [dstr] through an extra M-layer on the left factor: for ANY
   f, applying [fmap ret] to the left component and then collapsing with
   join ∘ fmap rstr computes [dstr] again. *)
Lemma dstr_reassoc_left {a b c d} (f : a ~> M b) (g : c ~> M d) :
  join[M] ∘ fmap[M] rstr ∘ dstr ∘ ((fmap[M] ret[M] ∘ f) ⨂ g)
    ≈ dstr ∘ (f ⨂ g).
Proof.
  assert (E : (fmap[M] ret[M] ∘ f) ⨂ g ≈ (fmap[M] ret[M] ⨂ id) ∘ (f ⨂ g)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite <- (@fmap_id _ _ M d).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr).
  rewrite <- dstr_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] rstr)).
  rewrite <- fmap_comp.
  rewrite rstr_ret.
  rewrite (comp_assoc join[M]).
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(* The same expression with a bare ret in place of fmap ret instead
   computes the sibling double strength [dstr']. *)
Lemma dstr_reassoc_left' {a b c d} (f : a ~> M b) (g : c ~> M d) :
  join[M] ∘ fmap[M] rstr ∘ dstr ∘ ((ret[M] ∘ f) ⨂ g)
    ≈ dstr' ∘ (f ⨂ g).
Proof.
  assert (E : (ret[M] ∘ f) ⨂ g ≈ (ret[M] ⨂ id[M d]) ∘ (f ⨂ g)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr).
  rewrite dstr_ret_left.
  unfold dstr'.
  reflexivity.
Qed.

(* Mirror reassociation on the right factor of [dstr']. *)
Lemma dstr'_reassoc_right {a b c d} (g : c ~> M d) (f : a ~> M b) :
  join[M] ∘ fmap[M] strength[M] ∘ dstr' ∘ (g ⨂ (fmap[M] ret[M] ∘ f))
    ≈ dstr' ∘ (g ⨂ f).
Proof.
  assert (E : g ⨂ (fmap[M] ret[M] ∘ f) ≈ (id ⨂ fmap[M] ret[M]) ∘ (g ⨂ f)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite <- (@fmap_id _ _ M d).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr').
  rewrite <- dstr'_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] strength[M])).
  rewrite <- fmap_comp.
  rewrite strength_ret.
  rewrite (comp_assoc join[M]).
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(* Mirror: the bare-ret variant computes [dstr]. *)
Lemma dstr'_reassoc_right' {a b c d} (g : c ~> M d) (f : a ~> M b) :
  join[M] ∘ fmap[M] strength[M] ∘ dstr' ∘ (g ⨂ (ret[M] ∘ f))
    ≈ dstr ∘ (g ⨂ f).
Proof.
  assert (E : g ⨂ (ret[M] ∘ f) ≈ (id[M d] ⨂ ret[M]) ∘ (g ⨂ f)).
  { rewrite <- bimap_comp.
    now rewrite id_left. }
  rewrite E; clear E.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ dstr').
  rewrite dstr'_ret_right.
  unfold dstr.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The two right-strength coherences.                               *)
(* ------------------------------------------------------------------ *)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma strength_assoc_solved {a b c} :
  strength[M] ∘ (id[a] ⨂ strength[M])
    ≈ fmap[M] (to (@tensor_assoc _ _ a b c)) ∘ strength[M]
        ∘ from (@tensor_assoc _ _ a b (M c)).
Proof.
  rewrite strength_assoc.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

(*
   本节说明 Symmetric 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma braid_swap_assoc {a b c} :
  from (@tensor_assoc _ _ a b c) ∘ (braid ∘ (braid ⨂ id[a]))
    ≈ (braid ∘ ((id[c] ⨂ braid) ∘ to (@tensor_assoc _ _ c b a))
         : (c ⨂ b) ⨂ a ~> (a ⨂ b) ⨂ c).
Proof.
  rewrite <- bimap_braid.
  rewrite hexagon_b.
  rewrite hexagon_a_solved.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* The same coherence solved against the associator: precomposing the braid
   word with to tensor_assoc on the left cancels the inverse associator. *)
Lemma braid_swap_assoc_solved {a b c} :
  to (@tensor_assoc _ _ a b c) ∘ braid ∘ (id[c] ⨂ braid)
    ∘ to (@tensor_assoc _ _ c b a)
    ≈ (braid ∘ (braid ⨂ id[a]) : (c ⨂ b) ⨂ a ~> a ⨂ (b ⨂ c)).
Proof.
  rewrite <- !comp_assoc.
  rewrite <- braid_swap_assoc.
  rewrite (cancel_to_from_cons tensor_assoc).
  reflexivity.
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rstr_id_right {x} :
  fmap[M] (to unit_right) ∘ rstr ≈ to (@unit_right _ _ (M x)).
Proof.
  unfold rstr.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite braid_unit_right.
  rewrite strength_id_left.
  apply braid_unit_left.
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rstr_assoc_to {x y z} :
  fmap[M] (to (@tensor_assoc _ _ x y z)) ∘ rstr ∘ bimap rstr id
    ≈ rstr ∘ to (@tensor_assoc _ _ (M x) y z).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ fmap[M] braid)).
  rewrite <- strength_natural_r.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ strength[M])).
  rewrite strength_assoc_solved.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  rewrite braid_swap_assoc.
  rewrite (comp_assoc braid (id[M x] ⨂ braid)).
  rewrite <- bimap_braid.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (braid ⨂ id[M x])).
  rewrite <- strength_natural_l.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  rewrite braid_swap_assoc_solved.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol.
  rewrite id_left.
  rewrite bimap_id_id.
  now rewrite id_right.
Qed.

(* The α-coherence in the [RightStrongFunctor] field orientation. *)
Lemma rstr_assoc {x y z} :
  rstr ∘ bimap rstr id ∘ from (@tensor_assoc _ _ (M x) y z)
    ≈ fmap[M] (from (@tensor_assoc _ _ x y z)) ∘ rstr.
Proof.
  apply (iso_to_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to.
  rewrite id_right.
  rewrite <- rstr_assoc_to.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite iso_from_to.
  rewrite fmap_id.
  now rewrite id_left.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The mixed associativity coherence.                               *)
(* ------------------------------------------------------------------ *)

(*
   本节说明单子、Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma strength_rstr_assoc {x y z} :
  fmap[M] (to (@tensor_assoc _ _ x y z)) ∘ rstr ∘ bimap strength[M] id
    ≈ strength[M] ∘ bimap id rstr ∘ to (@tensor_assoc _ _ x (M y) z).
Proof.
  (* Stage 1: the symmetric hexagon, solved for α⁻¹ ∘ β. *)
  assert (S1 : from (@tensor_assoc _ _ z x (M y))
                 ∘ @braid C _ (x ⨂ M y)%object z
                 ≈ (braid ⨂ id[M y])
                     ∘ (from (@tensor_assoc _ _ x z (M y))
                          ∘ ((id[x] ⨂ braid)
                               ∘ to (@tensor_assoc _ _ x (M y) z)))).
  { apply (iso_to_epic (iso_sym tensor_assoc)).
    rewrite <- !comp_assoc.
    rewrite iso_to_from.
    rewrite id_right.
    rewrite !comp_assoc.
    apply hexagon_identity_sym. }
  unfold rstr.
  rewrite <- !comp_assoc.
  (* Stage 2: normalize both sides onto the common strength-spine. *)
  rewrite <- bimap_braid.
  rewrite !bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[x] ⨂ fmap[M] braid)).
  rewrite <- strength_natural_r.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc strength[M] (id[z] ⨂ strength[M])).
  rewrite (comp_assoc strength[M] (id[x] ⨂ strength[M])).
  rewrite !strength_assoc_solved.
  rewrite <- !comp_assoc.
  rewrite S1.
  rewrite (comp_assoc strength[M] (braid ⨂ id[M y])).
  rewrite <- strength_natural_l.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply compose_respects; [|reflexivity].
  apply fmap_respects.
  (* Stage 3: the residual braid word is the first hexagon plus invol. *)
  rewrite hexagon_identity.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol.
  rewrite id_left.
  rewrite bimap_id_id.
  now rewrite id_right.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Packaging: the right strong functor and right strong monad.      *)
(* ------------------------------------------------------------------ *)

(*
   本节说明自然变换、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rstr_nat : (⨂) ◯ M ∏⟶ Id ⟹ M ◯ (⨂).
Proof using C M SM SMon.
  refine (@Build_Transform' (C ∏ C) C ((⨂) ◯ M ∏⟶ Id) (M ◯ (⨂))
            (fun p => match p with (x, y) => @rstr C SM M SMon x y end) _).
  intros [x1 x2] [y1 y2] [f g]; simpl.
  exact (@rstr_natural C SM M SMon x1 y1 x2 y2 f g).
Defined.

(* The packaging that Monad/Strong.v deferred: rstr, with the ρ- and
   α-coherences proved above, is a [RightStrongFunctor] structure on M. *)
Definition rstr_RightStrongFunctor : @RightStrongFunctor C _ M :=
  @Build_RightStrongFunctor C _ M
    rstr_nat
    (fun x => @rstr_id_right x)
    (fun x y z => @rstr_assoc x y z).

(* Sanity check: the packaged right strength is definitionally [rstr]. *)
Corollary rstrength_is_rstr {x y} :
  @rstrength C _ M rstr_RightStrongFunctor x y ≈ rstr.
Proof. reflexivity. Qed.

(* Together with the monad-compatibility laws [rstr_ret] and [rstr_join]
   from Monad/Strong.v, every strong monad over a symmetric base is a right
   strong monad. *)
Definition rstr_RightStrongMonad : @RightStrongMonad C _ M :=
  @Build_RightStrongMonad C _ M
    strongmonad_is_monad
    rstr_RightStrongFunctor
    (fun x y => @rstr_ret C SM M SMon x y)
    (fun x y => @rstr_join C SM M SMon x y).

(* ------------------------------------------------------------------ *)
(** ** The bridge to [CommutativeStrongMonad].                          *)
(* ------------------------------------------------------------------ *)

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition commutative_CommutativeStrongMonad
  (comm : @commutative_sm C SM M SMon) : @CommutativeStrongMonad C _ M :=
  @Build_CommutativeStrongMonad C _ M
    SMon
    rstr_RightStrongFunctor
    (fun x y => @rstr_ret C SM M SMon x y)
    (fun x y => @rstr_join C SM M SMon x y)
    (fun x y => comm x y).

(*
   本节说明单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CSM_commutative_sm
  (H' : @CommutativeStrongMonad C _ M)
  (E : ∀ x y, @rstrength C _ M (@comm_is_rstrong C _ M H') x y
                ≈ @rstr C SM M (@comm_is_strong C _ M H') x y) :
  @commutative_sm C SM M (@comm_is_strong C _ M H').
Proof.
  intros x y.
  unfold dstr, dstr'.
  rewrite <- !E.
  exact (@commutativity C _ M H' x y).
Qed.

(*
   本节说明单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary commutative_sm_round_trip
  (comm : @commutative_sm C SM M SMon) : @commutative_sm C SM M SMon.
Proof.
  apply (CSM_commutative_sm (commutative_CommutativeStrongMonad comm)).
  intros x y.
  reflexivity.
Qed.

End StrongSymmetric.
