Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.Representability.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Category.Adjunction.SAFT.Characterization.Cover.

Generalizable All Variables.

(** * Corollaries of the special adjoint functor theorem *)

(*
   nLab:      https://ncatlab.org/nlab/show/representable+functor
   nLab:      https://ncatlab.org/nlab/show/complete+category

   本文件给出推论。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Mac Lane's Corollary: continuous [Sets]-valued functors are representable *)

Definition continuous_Set_functor_representable@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K :=
  representable_of_left_adjoint K (projT2 (SAFT_wellpowered K comp cont G WP)).

(* The representing object is the left adjoint at the singleton. *)
Example continuous_Set_functor_representable_obj@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (cont : @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @repr_obj C K
    (continuous_Set_functor_representable K comp cont G WP
       : Representable@{ra rt su o h} K)
    = fobj[projT1 (SAFT_wellpowered K comp cont G WP)] SetsOne := eq_refl.

Definition continuous_Set_functor_representable_iff@{o h so c w s t su pl pa ra rt +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  Representable@{ra rt su o h} K
    ↔ @PreservesImageLimit@{o h su h pl so pa so} C Sets@{h su} K.
Proof.
  split.
  - exact preserves_image_of_representable.
  - intro cont; exact (continuous_Set_functor_representable K comp cont G WP).
Defined.

(* Riehl's route (the category of elements), with well-poweredness at the
   ONE object the singleton needs, through the d-dependent cover. *)
Definition continuous_Set_functor_representable_at@{o h dp cp w s t su pl pa ra rt +|
    h < dp, h < cp, w <= h, h < su +}
  {C : Category@{o h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h su h pl h pa h} C Sets@{h su} K)
  (G : Cogenerator@{h o h} C)
  (W : WellPoweredAt@{w o s h t} (saft_prod@{o su h h dp} K comp G SetsOne)) :
  Representable@{ra rt su o h} K :=
  representable_of_comma_initial K
    (comma_initial_of_sols K SetsOne comp cont
       (saft_solution_set_at@{o su h h dp cp w s t pl pa h _ _ _}
          K comp cont G SetsOne W)).

(** ** Riehl 4.7.13: the SAFT hypotheses give cocompleteness *)

Definition saft_colim@{o h so c w s t jo fo fa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa +}
  (C : Category@{o h h}) (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C)
  (J : Category@{jo h h}) :
  { L : @Fun@{jo h o h fo h fa} J C ⟶ C & L ⊣ @Diagonal@{fo h fa jo o h} C J } :=
  SAFT_wellpowered (@Diagonal@{fo h fa jo o h} C J) comp
    (Continuous_PreservesImageLimit Diagonal_continuous) G WP.

Definition saft_cocomplete@{o h so c w s t jo fo fa +|
    h <= so, c <= so, w <= h, o <= s, h <= s, h < t, jo <= h,
    o <= fo, h <= fo, h < fa +}
  {C : Category@{o h h}} (comp : @Complete@{so so h o} C)
  (G : Cogenerator@{c o h} C) (WP : WellPowered@{o h w s t} C) :
  @Cocomplete@{h jo h o} C :=
  fun J F => Diagonal_left_adjoint_HasColimits
               (projT2 (saft_colim C comp G WP J
                        : { L : @Fun@{jo h o h fo h fa} J C ⟶ C
                          & L ⊣ @Diagonal@{fo h fa jo o h} C J })) F.

(** ** The two routes to the left adjoint agree up to isomorphism *)

Definition SAFT_cover_wp_iso@{o dobj h dp cp w s t pl pa +|
    h < dp, h < cp, w <= h, o <= s, h <= s, h < t +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h o} C)
  (cont : @PreservesImageLimit@{o h dobj h pl h pa h} C D U)
  (G : Cogenerator@{h o h} C) (WP : WellPowered@{o h w s t} C) :
  projT1 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP)
    ≈ projT1 (SAFT_wellpowered U comp cont G WP) :=
  left_adjoint_iso U _ _
    (projT2 (SAFT_cover_wp@{o dobj h dp cp w s t pl pa _ _ _} U comp cont G WP))
    (projT2 (SAFT_wellpowered U comp cont G WP)).

(** ** The two routes index the same family *)

(* The comma category's cogenerating family is indexed by the arrows out of
   [d], exactly the index of [saft_prod]. *)
Example comma_cogenerator_index@{o dobj h so +| h <= so +}
  {C : Category@{o h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (G : Cogenerator@{so o h} C) :
  cog_index (comma_cogenerator U d G) = saft_index U G d := eq_refl.
