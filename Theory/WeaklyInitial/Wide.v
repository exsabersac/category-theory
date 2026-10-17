Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Wide.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Freyd's initial-object construction, through the wide-equalizer API *)

(*
 nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   本文件给出 wide 相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* A weakly initial family, a product of it, and a supply of wide
   equalizers yield a genuine initial object.

   Construction.  Write [P0] for the product object [iprod (wif_obj W) P].
   For any [c], the covering arrow [wif_cover c] composed with the matching
   projection gives a map [P0 ~> c], so [P0] is weakly initial.  Take the
   wide equalizer [e : I ~> P0] of the family of ALL endomorphisms of [P0],
   indexed by the hom-type itself.  Its fork condition instantiated at an
   endomorphism [u] and at [id] says [u ∘ e ≈ id ∘ e], i.e. [e] absorbs
   every endomorphism; and [e] is monic.  This [I] is initial:

     - existence  [I ~> c]:  [wmap c ∘ e];
     - uniqueness: given [f g : I ~> c], take the wide equalizer [k : K ~> I]
       of the two-element family {f, g}; weak initiality gives [s : P0 ~> K],
       so [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e];
       monicity of [e] then makes [(k ∘ s) ∘ e ≈ id], i.e. [k] is split epi,
       and [f ∘ k ≈ g ∘ k] forces [f ≈ g]. *)
Theorem initial_from_weakly_initial_wide `(W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W)))
  (E : HasWideEqualizers C) : @Initial C.
Proof.
  (* Abbreviate the product object. *)
  set (P0 := iprod (wif_obj W) P) in *.

  (* Weak initiality of [P0]: a chosen map into every object. *)
  pose (wmap := fun c : C =>
          projT2 (wif_cover W c)
            ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c))).

  (* The wide equalizer of the family of ALL endomorphisms of [P0].  The
     index type is the hom-type [P0 ~> P0] and the family is the identity
     assignment, so "the i-th member" IS the endomorphism [i]. *)
  destruct (@wide_equalizer C E (P0 ~> P0) P0 P0 (fun u => u))
    as [I [e Eeq]].

  (* Every endomorphism of [P0] is absorbed by the equalizing map.  This is
     one instance of the wide fork condition — at [u] and at [id] — where
     the original needed the two tuplings through the power. *)
  assert (endo_absorb : ∀ u : P0 ~> P0, u ∘ e ≈ e).
  { intro u.
    transitivity (id[P0] ∘ e).
    - exact (wfork_eq Eeq u id[P0]).
    - apply id_left. }

  (* The equalizing map is monic. *)
  pose proof (wide_equalizer_monic (fun u : P0 ~> P0 => u) Eeq) as Me.
  destruct Me as [mon].

  (* Assemble the initial object as a terminal object of [C^op]. *)
  unshelve refine (@Build_Terminal (C^op) I _ _).
  - (* existence: [I ~> x] via weak initiality post-composed with [e] *)
    intro x.
    exact (wmap x ∘ e).
  - (* uniqueness: any two [f g : I ~> x] agree *)
    intros x f g.
    (* read the goal in [C]: [f], [g] are [C]-morphisms [I ~> x] *)
    change (unop f ≈ unop g).
    (* the wide equalizer of the two-element family {f, g}; no separate
       binary-equalizer supply is needed *)
    destruct (@wide_equalizer C E bool I x
                (fun b : bool => if b then unop f else unop g))
      as [K [k Ek]].
    assert (Hfg : unop f ∘ k ≈ unop g ∘ k)
      by exact (wfork_eq Ek true false).
    (* weak initiality supplies a map [P0 ~> K] *)
    pose (s := wmap K).
    (* [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then cancels it, exhibiting [s ∘ e] as a section of [k]. *)
    assert (Habs : (e ∘ (k ∘ s)) ∘ e ≈ e ∘ id[I]).
    { transitivity e.
      - exact (endo_absorb (e ∘ (k ∘ s))).
      - symmetry; apply id_right. }
    assert (Hk : (k ∘ s) ∘ e ≈ id[I]).
    { apply (mon _ ((k ∘ s) ∘ e) (id[I])).
      transitivity ((e ∘ (k ∘ s)) ∘ e).
      - apply comp_assoc.
      - exact Habs. }
    (* hence [k ∘ (s ∘ e) ≈ id]: [k] is a split epimorphism *)
    assert (Hkr : k ∘ (s ∘ e) ≈ id[I]).
    { transitivity ((k ∘ s) ∘ e).
      - apply comp_assoc.
      - exact Hk. }
    (* [k] equalizes [f] and [g] and is (split) epic, so [f ≈ g] *)
    transitivity (unop f ∘ (k ∘ (s ∘ e))).
    + transitivity (unop f ∘ id[I]).
      * symmetry; apply id_right.
      * apply compose_respects; [ reflexivity | symmetry; exact Hkr ].
    + transitivity (unop g ∘ (k ∘ (s ∘ e))).
      * transitivity ((unop f ∘ k) ∘ (s ∘ e)).
        -- apply comp_assoc.
        -- transitivity ((unop g ∘ k) ∘ (s ∘ e)).
           ++ apply compose_respects; [ exact Hfg | reflexivity ].
           ++ symmetry; apply comp_assoc.
      * transitivity (unop g ∘ id[I]).
        -- apply compose_respects; [ reflexivity | exact Hkr ].
        -- apply id_right.
Qed.
