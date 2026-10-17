Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* * * The environment (coreader) 余单子 COQ （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)

   本文件给出余单子相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/coreader+comonad
   Paper: Petricek, Orchard, Mycroft, "Coeffects: a calculus of

   本节说明余单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The action e × − 态射: apply f under environment. （已译） *)
Definition env_map {e x y : Type} (f : x → y) (p : e * x) : e * y :=
  match p with (e0, v) => (e0, f v) end.

Lemma env_map_respects {e x y : Type} (f g : x → y) :
  (∀ v, f v = g v) → ∀ p : e * x, env_map f p = env_map g p.
Proof.
  intros Hfg [e0 v]; simpl.
  now rewrite Hfg.
Qed.

Lemma env_map_id {e x : Type} (p : e * x) : env_map (λ v : x, v) p = p.
Proof. now destruct p. Qed.

Lemma env_map_comp {e x y z : Type} (f : y → z) (g : x → y) (p : e * x) :
  env_map (λ v, f (g v)) p = env_map f (env_map g p).
Proof. now destruct p. Qed.

(** The environment endofunctor e × − on COQ. *)
Definition EnvF (e : Type) : Coq ⟶ Coq := @Build_Functor Coq Coq
  (λ x : Type, (e * x)%type)
  (λ (x y : Type) (f : x → y), @env_map e x y f)
  (λ x y : Type, @env_map_respects e x y)
  (λ x : Type, @env_map_id e x)
  (λ (x y z : Type) (f : y → z) (g : x → y), @env_map_comp e x y z f g).

(** 本节：The counit ε: project out value. （已译） *)
Definition env_extract {e x : Type} (p : e * x) : x := snd p.

(** The comultiplication δ: copy environment 进入 payload. （已译） *)
Definition env_duplicate {e x : Type} (p : e * x) : e * (e * x) :=
  match p with (e0, v) => (e0, (e0, v)) end.

(** 本节：Naturality counit — op-read [fmap_ret]. （已译） *)
Lemma env_extract_natural {e x y : Type} (f : x → y) (p : e * x) :
  f (env_extract p) = env_extract (env_map f p).
Proof. now destruct p. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. *)
Lemma env_duplicate_coassoc {e x : Type} (p : e * x) :
  env_map env_duplicate (env_duplicate p) = env_duplicate (env_duplicate p).
Proof. now destruct p. Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. *)
Lemma env_fmap_extract_duplicate {e x : Type} (p : e * x) :
  env_map env_extract (env_duplicate p) = p.
Proof. now destruct p. Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. *)
Lemma env_extract_duplicate {e x : Type} (p : e * x) :
  env_extract (env_duplicate p) = p.
Proof. now destruct p. Qed.

(** 本节：Naturality comultiplication — op-read [join_fmap_fmap]. （已译） *)
Lemma env_duplicate_natural {e x y : Type} (f : x → y) (p : e * x) :
  env_map (env_map f) (env_duplicate p) = env_duplicate (env_map f p).
Proof. now destruct p. Qed.

(*
   本节说明单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Env_Comonad (e : Type) : @Comonad Coq (EnvF e) :=
  @Build_Monad (Coq^op) ((EnvF e)^op)
    (λ x : Type, @env_extract e x)                (* ret  = ε *)
    (λ x : Type, @env_duplicate e x)              (* join = δ *)
    (λ (x y : Type) (f : y → x), @env_extract_natural e y x f)
    (λ x : Type, @env_duplicate_coassoc e x)
    (λ x : Type, @env_fmap_extract_duplicate e x)
    (λ x : Type, @env_extract_duplicate e x)
    (λ (x y : Type) (f : y → x), @env_duplicate_natural e y x f).

(*
   本节说明余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Env_extract_spec {e x : Type} (p : e * x) :
  extract[EnvF e] p = snd p.
Proof. reflexivity. Qed.

Lemma Env_duplicate_spec {e x : Type} (e0 : e) (v : x) :
  duplicate[EnvF e] (e0, v) = (e0, (e0, v)).
Proof. reflexivity. Qed.

Lemma Env_extend_spec {e x y : Type} (f : e * x → y) (e0 : e) (v : x) :
  extend[EnvF e] f (e0, v) = (e0, f (e0, v)).
Proof. reflexivity. Qed.
