Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * Wide pullbacks from completeness *)

(*
   nLab:      https://ncatlab.org/nlab/show/complete+category
   nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   本文件给出完备范畴结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CompleteWide.

Context {C : Category}.
Context (comp : @Complete C).

Section AtFamily.

Context {J : Type} {A : J → C} {z : C} (f : ∀ j, A j ~> z).

(* The product of the family, and its projections. *)
Definition cwp_P_lim := comp _ (DiscreteCat_Functor A).
Definition cwp_P : C := iprod A cwp_P_lim.
Definition cwp_pi (j : J) : cwp_P ~> A j := iprod_proj A cwp_P_lim j.

(* The [J × J]-fold power of the codomain. *)
Definition cwp_Z_lim := comp _ (DiscreteCat_Functor (fun _ : J * J => z)).
Definition cwp_Z : C := iprod (fun _ : J * J => z) cwp_Z_lim.
Definition cwp_rho (k : J * J) : cwp_Z ~> z :=
  iprod_proj (fun _ : J * J => z) cwp_Z_lim k.

(* The two maps whose equalizer is the wide pullback. *)
Definition cwp_l : cwp_P ~> cwp_Z :=
  unique_obj (iprod_ump (fun _ : J * J => z) cwp_Z_lim cwp_P
                (fun k => f (fst k) ∘ cwp_pi (fst k))).
Definition cwp_r : cwp_P ~> cwp_Z :=
  unique_obj (iprod_ump (fun _ : J * J => z) cwp_Z_lim cwp_P
                (fun k => f (snd k) ∘ cwp_pi (snd k))).

(* The equalizer, from the Structure layer's finite-limit bridge. *)
Definition cwp_E :=
  @equalizer C (FinitelyComplete_HasEqualizers (Complete_FinitelyComplete comp))
    _ _ cwp_l cwp_r.
Definition cwp_Eobj : C := `1 cwp_E.
Definition cwp_e : cwp_Eobj ~> cwp_P := `1 (`2 cwp_E).
Definition cwp_isE : IsEqualizer cwp_l cwp_r cwp_Eobj cwp_e := `2 (`2 cwp_E).

Lemma cwp_rho_l (k : J * J) : cwp_rho k ∘ cwp_l ≈ f (fst k) ∘ cwp_pi (fst k).
Proof. exact (unique_property (iprod_ump _ cwp_Z_lim cwp_P _) k). Qed.

Lemma cwp_rho_r (k : J * J) : cwp_rho k ∘ cwp_r ≈ f (snd k) ∘ cwp_pi (snd k).
Proof. exact (unique_property (iprod_ump _ cwp_Z_lim cwp_P _) k). Qed.

Definition complete_wide_pullback : WidePullback f.
Proof using comp.
  unshelve refine {| WPull := cwp_Eobj;
                     wide_pullback_proj := fun j => cwp_pi j ∘ cwp_e |}.
  - intros i j.
    rewrite !comp_assoc.
    rewrite <- (cwp_rho_l (i, j)), <- (cwp_rho_r (i, j)).
    simpl.
    rewrite <- !comp_assoc.
    now rewrite (fork_eq cwp_isE).
  - intros Q q Hq.
    pose (t := iprod_ump A cwp_P_lim Q q).
    assert (Ht : cwp_l ∘ unique_obj t ≈ cwp_r ∘ unique_obj t).
    { apply (pe_iprod_ext (limit_is_indexed_product _ _)); intro k.
      rewrite !comp_assoc.
      change (iprod_proj (fun _ : J * J => z) cwp_Z_lim k) with (cwp_rho k).
      rewrite cwp_rho_l, cwp_rho_r.
      rewrite <- !comp_assoc.
      change (iprod_proj A cwp_P_lim) with cwp_pi in (type of t).
      rewrite (unique_property t (fst k)), (unique_property t (snd k)).
      exact (Hq (fst k) (snd k)). }
    pose (u := eq_desc cwp_isE (unique_obj t) Ht).
    unshelve eapply Build_Unique.
    + exact (unique_obj u).
    + intro j. rewrite <- comp_assoc.
      rewrite (unique_property u).
      exact (unique_property t j).
    + intros v Hv.
      apply (uniqueness u).
      apply (pe_iprod_ext (limit_is_indexed_product _ _)); intro j.
      rewrite comp_assoc.
      change (iprod_proj A cwp_P_lim j) with (cwp_pi j).
      rewrite (Hv j).
      symmetry; exact (unique_property t j).
Defined.

End AtFamily.

End CompleteWide.

(* The class, with its index slot at [Complete]'s shape-object universe. *)
Definition Complete_HasWidePullbacks {C : Category} (comp : @Complete C) :
  HasWidePullbacks C :=
  {| wide_pullback := fun I A z f => complete_wide_pullback comp f |}.
