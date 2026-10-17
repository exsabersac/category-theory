Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Naturality.

Generalizable All Variables.

Section BraidedMonoidal.

Context {C : Category}.

(** Braided monoidal category. *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Braided_monoidal_category

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the braiding的来源与用途

   nLab:  https://ncatlab.org/nlab/show/Yang-Baxter+equation
   nLab:  https://ncatlab.org/nlab/show/periodic+table
   Paper: Joyal, Street, "Braided tensor categories", Advances in

   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class BraidedMonoidal := {
  braided_is_monoidal : @Monoidal C;

  (* The braiding beta : x ⊗ y ≅ y ⊗ x, natural in both arguments. *)
  braid {x y} : x ⨂ y ~> y ⨂ x;
  braid_natural : natural (@braid);

  (* First hexagon: braiding x past the tensor product y ⊗ z. *)
  hexagon_identity {x y z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (x ⨂ y) ⨂ z ~~> y ⨂ (z ⨂ x) >>
    id ⨂ braid ∘ tensor_assoc ∘ braid ⨂ id;

  (* Second hexagon: braiding the tensor product x ⊗ y past z. *)
  hexagon_identity_sym {x y z} :
    tensor_assoc⁻¹ ∘ braid ∘ tensor_assoc⁻¹
      << x ⨂ (y ⨂ z) ~~> (z ⨂ x) ⨂ y >>
    braid ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ braid;
}.
#[export] Existing Instance braided_is_monoidal.

Coercion braided_is_monoidal : BraidedMonoidal >-> Monoidal.

Context `{BraidedMonoidal}.

(* The hexagons imply the Yang-Baxter equation on a triple tensor product:
   the two ways of fully reversing a ⊗ b ⊗ c by adjacent braidings agree. *)
Theorem Yang_Baxter_equation {a b c : C} :
  braid ⨂ id[a] ∘ tensor_assoc⁻¹
    ∘ id[b] ⨂ braid ∘ tensor_assoc
    ∘ braid ⨂ id[c] ∘ tensor_assoc⁻¹
    ≈ tensor_assoc⁻¹ ∘ id[c] ⨂ braid
        ∘ tensor_assoc ∘ braid ⨂ id[b]
        ∘ tensor_assoc⁻¹ ∘ id[a] ⨂ braid.
Proof.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite iso_to_from, id_right.
  rewrite (@comp_assoc _ _ _ _ _ (id ⨂ braid)).
  rewrite (@comp_assoc _ _ _ _ _ _ (braid ⨂ id)).
  rewrite <- hexagon_identity.
  rewrite <- !comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ tensor_assoc⁻¹ tensor_assoc).
  rewrite iso_from_to, id_left.
  rewrite (@comp_assoc _ _ _ _ _ _ tensor_assoc⁻¹).
  rewrite iso_to_from, id_left.
  spose (braid_natural a _ id _ _ (@braid _ b c)) as X.
  rewrite bimap_id_id in X.
  rewrite id_right in X.
  rewrite X.
  rewrite bimap_id_id.
  rewrite id_right.
  reflexivity.
Qed.

End BraidedMonoidal.
