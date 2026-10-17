Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Size.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Representability.
Require Import Category.Adjunction.Representability.Sets.

Generalizable All Variables.

(*
    nLab:      https://ncatlab.org/nlab/show/solution+set+condition
    nLab:      https://ncatlab.org/nlab/show/essentially+small+category
    nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors#General_adjoint_functor_theorem

   本文件给出一般伴随函子定理相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明 Resize 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition resize_solution_set@{i w dobj cobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (S : SolutionSet@{i dobj cobj h} U d)
  (H : SmallType@{w i} (sol_index S)) : SolutionSet@{w dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := st_carrier H
     ; sol_obj := fun s => sol_obj S (st_to H s)
     ; sol_arr := fun s => sol_arr S (st_to H s) |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  exists (st_from H i).
  destruct (st_to_from H i).
  exists t; exact e.
Defined.

(** The element-indexed twin.  [esol_covers] has no [Arguments] line, so
    the functor is explicit: it is [esol_covers K E x], not
    [esol_covers E x].  Outside [Adjunction/Representability/Sets.v]'s own
    section [ElementSolutionSet] takes FOUR universes, not one. *)
Definition resize_element_solution_set@{cobj h su i w}
  {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su})
  (E : ElementSolutionSet@{cobj h su i} K)
  (H : SmallType@{w i} (esol_index E)) : ElementSolutionSet@{cobj h su w} K.
Proof.
  unshelve refine
    {| esol_index := st_carrier H
     ; esol_obj := fun s => esol_obj E (st_to H s)
     ; esol_elem := fun s => esol_elem E (st_to H s) |}.
  intros c x.
  destruct (esol_covers K E x) as [i [t e]].
  exists (st_from H i).
  destruct (st_to_from H i).
  exists t; exact e.
Defined.

(** ** The two weaker premises *)

(** 本节：[C] [D] written out rather than generalized: records are
 declared at top level, so no section variable scope them. （已译） *)

(** 本节：A small type whose image under [sc_to] still covers. Nothing says the
 map injective, surjective, small carrier determines the
 index -- covering survives. （已译） *)
Record SmallCovering@{w +} {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) := {
  sc_carrier : Type@{w};
  sc_to      : sc_carrier → sol_index S;
  sc_covers  : ∀ (c : C) (h : d ~> U c),
                 { s : sc_carrier
                 & { t : sol_obj S (sc_to s) ~> c
                   & fmap[U] t ∘ sol_arr S (sc_to s) ≈ h } }
}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record SmallUpToIso@{w +} {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) := {
  si_carrier : Type@{w};
  si_to      : si_carrier → sol_index S;
  si_rep     : ∀ i : sol_index S,
                 { s : si_carrier
                 & { phi : sol_obj S (si_to s) ≅ sol_obj S i
                   & fmap[U] (to phi) ∘ sol_arr S (si_to s) ≈ sol_arr S i } }
}.

Arguments SmallCovering {C D U d} S.
Arguments sc_carrier {C D U d S} _.
Arguments sc_to {C D U d S} _ _.
Arguments sc_covers {C D U d S} _ _ _.

Arguments SmallUpToIso {C D U d} S.
Arguments si_carrier {C D U d S} _.
Arguments si_to {C D U d S} _ _.
Arguments si_rep {C D U d S} _ _.

(* 相关说明。 （已译） *)

(** 本节：With [SmallCovering] resizing record literal: premise IS
 covering field. （已译） *)
Definition resize_by_covering@{w i dobj cobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (S : SolutionSet@{i dobj cobj h} U d) (H : SmallCovering S)
  : SolutionSet@{w dobj cobj h} U d :=
  {| sol_index := sc_carrier H
   ; sol_obj := fun s => sol_obj S (sc_to H s)
   ; sol_arr := fun s => sol_arr S (sc_to H s)
   ; sol_covers := fun c h => sc_covers H c h |}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition resize_up_to_iso@{w i dobj cobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (S : SolutionSet@{i dobj cobj h} U d) (H : SmallUpToIso S)
  : SolutionSet@{w dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := si_carrier H
     ; sol_obj := fun s => sol_obj S (si_to H s)
     ; sol_arr := fun s => sol_arr S (si_to H s) |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  destruct (si_rep H i) as [s [phi Hphi]].
  exists s, (t ∘ to phi).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite Hphi.
  exact e.
Defined.

(* 相关说明。 （已译） *)

(** Mac Lane's shape implies the minimum. *)
Definition covering_of_iso {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) (H : SmallUpToIso S) : SmallCovering S.
Proof.
  unshelve refine {| sc_carrier := si_carrier H ; sc_to := si_to H |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  destruct (si_rep H i) as [s [phi Hphi]].
  exists s, (t ∘ to phi).
  rewrite fmap_comp, <- comp_assoc, Hphi.
  exact e.
Defined.

(** And so does the strongest. *)
Definition covering_of_smalltype {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) (H : SmallType (sol_index S)) : SmallCovering S.
Proof.
  unshelve refine {| sc_carrier := st_carrier H ; sc_to := st_to H |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  exists (st_from H i).
  destruct (st_to_from H i).
  exists t; exact e.
Defined.

(** ** The consumer *)

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition representable_of_small@{cobj h su i +}
  {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet@{cobj h su i} K)
  (H : SmallType@{h i} (esol_index E)) : Representable K :=
  representability_theorem K comp cont (resize_element_solution_set K E H).
