Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Naturality.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Strong.
Require Import Category.Natural.Transformation.Strong.

Generalizable All Variables.

(** Strong monads (monads whose functor carries a compatible strength) *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   本文件给出（余）强度/强（余）单子相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ================================================================== *)
(** ** The strong monad class.                                         *)
(* ================================================================== *)

Section StrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

(*
   本节说明函子、单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class StrongMonad := {
  strongmonad_is_monad  :: @Monad C M;           (* the underlying monad (η, μ) *)
  strongmonad_is_strong :: @StrongFunctor C _ M; (* the underlying left strength t *)

  (*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  strength_ret {x y} :
    strength ∘ (id[x] ⨂ ret[M]) ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  (*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  strength_join {x y} :
    strength ∘ (id[x] ⨂ join[M])
      ≈ (join[M] ∘ fmap[M] strength ∘ strength
           : x ⨂ M (M y) ~> M (x ⨂ y))
}.

End StrongMonad.

Arguments StrongMonad {C} _ M.

(* ================================================================== *)
(** ** Tier 1 instance: the identity strong monad.                    *)
(* ================================================================== *)

Section IdStrongMonad.

Context `{@Monoidal C}.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Program Instance Id_Monad : @Monad C Id[C] := {
  ret  := fun _ => id;
  join := fun _ => id
}.

(*
   本节说明单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Id_StrongMonad : StrongMonad _ Id[C] := {
  strongmonad_is_monad  := Id_Monad;
  strongmonad_is_strong := Id_StrongFunctor
}.

End IdStrongMonad.

(* ================================================================== *)
(** ** Tier 2: validation — η and μ are strong natural transformations *)
(* ================================================================== *)

(*
   本节说明自然变换、单子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section StrongMonadValidation.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(*
   本节说明自然变换、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Monad_unit : Id[C] ⟹ M :=
  Build_Transform' (F:=Id[C]) (G:=M) (fun _ => ret[M])
    (fun _ _ _ => ltac:(simpl; symmetry; apply fmap_ret)).

(* μ packaged as a natural transformation M ◯ M ⟹ M.  Its naturality square is
   the multiplication naturality law [join_fmap_fmap] of the monad. *)
Definition Monad_mult : M ◯ M ⟹ M :=
  Build_Transform' (F:=M ◯ M) (G:=M) (fun _ => join[M])
    (fun _ _ _ => ltac:(simpl; symmetry; apply join_fmap_fmap)).

(*
   本节说明自然变换、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance ret_Strong_Transform :
  @Strong_Transform C _ Id[C] Id_StrongFunctor M _ Monad_unit.
Next Obligation.
  simpl.
  rewrite id_right.
  apply strength_ret.
Qed.

(*
   本节说明自然变换、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance join_Strong_Transform :
  @Strong_Transform C _ (M ◯ M) (Compose_StrongFunctor M M _ _) M _ Monad_mult.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  apply strength_join.
Qed.

End StrongMonadValidation.

(* ================================================================== *)
(** ** Tier 3: right-strong monads, the symmetric bridge,             *)
(**            commutativity, and the induced double strength.        *)
(* ================================================================== *)

(*
   nLab: https://ncatlab.org/nlab/show/strong+monad

   本节说明函子、单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RightStrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

Class RightStrongMonad := {
  rstrongmonad_is_monad   :: @Monad C M;
  rstrongmonad_is_rstrong :: @RightStrongFunctor C _ M;

  (* η-compat (right): rstrength ∘ (ret ⨂ id) ≈ ret *)
  rstrength_ret {x y} :
    rstrength ∘ (ret[M] ⨂ id[y])
      ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  (* μ-compat (right): rstrength ∘ (join ⨂ id)
                         ≈ join ∘ fmap rstrength ∘ rstrength *)
  rstrength_join {x y} :
    rstrength ∘ (join[M] ⨂ id[y])
      ≈ (join[M] ∘ fmap[M] rstrength ∘ rstrength
           : M (M x) ⨂ y ~> M (x ⨂ y))
}.

End RightStrongMonad.

Arguments RightStrongMonad {C} _ M.

(* ------------------------------------------------------------------ *)
(** ** Commutative strong monads (left and right strengths cohere).    *)
(* ------------------------------------------------------------------ *)

(*
   nLab: https://ncatlab.org/nlab/show/commutative+monad

   本节说明单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CommutativeStrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

Class CommutativeStrongMonad := {
  comm_is_strong :: @StrongMonad C _ M;

  (* the right strength over the *same* underlying monad *)
  comm_is_rstrong : @RightStrongFunctor C _ M;

  comm_rstrength_ret {x y} :
    @rstrength _ _ _ comm_is_rstrong x y ∘ (ret[M] ⨂ id[y])
      ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  comm_rstrength_join {x y} :
    @rstrength _ _ _ comm_is_rstrong x y ∘ (join[M] ⨂ id[y])
      ≈ (join[M] ∘ fmap[M] (@rstrength _ _ _ comm_is_rstrong x y)
                ∘ @rstrength _ _ _ comm_is_rstrong (M x) y
           : M (M x) ⨂ y ~> M (x ⨂ y));

  (* the two double strengths agree *)
  commutativity {x y} :
    join[M] ∘ fmap[M] strength ∘ @rstrength _ _ _ comm_is_rstrong x (M y)
      ≈ join[M] ∘ fmap[M] (@rstrength _ _ _ comm_is_rstrong x y) ∘ strength
}.

End CommutativeStrongMonad.

Arguments CommutativeStrongMonad {C} _ M.

(* ------------------------------------------------------------------ *)
(** ** The symmetric bridge: a strong monad over a symmetric base      *)
(**     carries a right strength compatible with η and μ.              *)
(* ------------------------------------------------------------------ *)

(*
   本节说明幺半结构、单子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SymmetricRightStrength.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(* The derived right strength rstr = M(braid) ∘ strength ∘ braid. *)
Definition rstr {x y} : M x ⨂ y ~> M (x ⨂ y) :=
  fmap[M] braid ∘ strength ∘ braid.

(* Joint naturality of the derived right strength:
     fmap (f ⨂ g) ∘ rstr ≈ rstr ∘ (fmap f ⨂ g). *)
Lemma rstr_natural {x z y w} (f : x ~> z) (g : y ~> w) :
  fmap[M] (bimap f g) ∘ rstr ≈ rstr ∘ bimap (fmap[M] f) g.
Proof.
  unfold rstr.
  pose proof (@strength_natural _ _ M _ y w g x z f) as SN.
  simpl in SN.
  normal.
  (* LHS: fmap((f⨂g)∘braid) ∘ strength ∘ braid;  (f⨂g)∘braid = braid∘(g⨂f) *)
  rewrite bimap_braid.
  normal.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] (g ⨂ f))).
  rewrite SN.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  reflexivity.
Qed.

(* η-compat for the derived right strength: rstr ∘ (ret ⨂ id) ≈ ret. *)
Lemma rstr_ret {x y} :
  rstr ∘ (ret[M] ⨂ id[y]) ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.            (* braid∘(ret⨂id) = (id⨂ret)∘braid *)
  rewrite (comp_assoc strength).
  rewrite strength_ret.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  rewrite <- !comp_assoc.
  rewrite braid_invol.
  rewrite id_right.
  reflexivity.
Qed.

(* μ-compat for the derived right strength:
     rstr ∘ (join ⨂ id) ≈ join ∘ fmap rstr ∘ rstr. *)
Lemma rstr_join {x y} :
  rstr ∘ (join[M] ⨂ id[y])
    ≈ (join[M] ∘ fmap[M] rstr ∘ rstr : M (M x) ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.            (* braid∘(join⨂id) = (id⨂join)∘braid *)
  rewrite (comp_assoc strength).
  rewrite strength_join.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.         (* fmap braid ∘ join = join ∘ fmap(fmap braid) *)
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite braid_invol.               (* braid ∘ braid = id collapses the RHS *)
  rewrite id_right.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* The induced double strength M x ⨂ M y ~> M (x ⨂ y) built from the left
   strength and the derived right strength, and its mirror. *)
Definition dstr {x y} : M x ⨂ M y ~> M (x ⨂ y) :=
  join[M] ∘ fmap[M] strength ∘ rstr.

Definition dstr' {x y} : M x ⨂ M y ~> M (x ⨂ y) :=
  join[M] ∘ fmap[M] rstr ∘ strength.

(*
   本节说明单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition commutative_sm : Type := ∀ x y, @dstr x y ≈ @dstr' x y.

End SymmetricRightStrength.
