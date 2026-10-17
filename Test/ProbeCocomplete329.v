Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Chain.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Instance.Sets.Chain.

Generalizable All Variables.

(** * Probe: strength boundaries of Sets cocompleteness *)

(*
   本文件为测试：ProbeCocomplete329。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** No duality shortcut from Sets_Complete

    [Colimit F := Limit (F^op)] is definitional, which makes it tempting
    to think completeness of [Sets] hands over cocompleteness.  It does
    not: [F^op] lands in [Sets^op], not [Sets], and what would give the
    colimit is [Complete (Sets^op)] -- which IS [Cocomplete Sets] again.
    This is a TYPING negative, not a conversion one. *)

Section DualityNegative.

Context (D : Category) (F : D ⟶ Sets).

Fail Check (Sets_Complete (Opposite D) (Opposite_Functor F)).

(* Positive controls naming their own constants: completeness applies at
   the ORIGINAL diagram, and the colimit is a limit of the opposite
   functor -- so the refusal above is about which category the opposite
   functor lands in, not about the constants being unusable. *)
Check (Sets_Complete D F).

Check (Sets_Colimit F).

(* Control naming [Opposite_Functor] itself.  The rename simulation over
   the constants in the NEGATIVES found it named by no control -- it
   occurs only inside the Fail above -- so that negative would have gone
   vacuously green on a rename.  Recorded rather than quietly added. *)
Check (Opposite_Functor F).

(* Control naming [Opposite] -- the CATEGORY opposite -- itself.  The
   audit re-ran the simulation and found it named by no control: it too
   occurs only inside the Fail above, in the SAME expression, so the fix
   recorded just above had been applied to only one of that line's two
   opposites.  Renaming [Opposite] left this file compiling clean while
   the negative passed on a "reference not found" error rather than on
   the mathematics -- the very false-pass mode this header warns about. *)
Check (Opposite D).

End DualityNegative.

(** ** The apex is not the coproduct on the nose

    The colimit apex and the indexed coproduct share a CARRIER but
    differ in [is_setoid] -- the apex carries the coarser generated
    relation.  That difference is the whole construction, so the
    negative and its control together say exactly what the quotient
    adds. *)

Section ApexNegative.

Context (D : Category) (F : D ⟶ Sets).

Fail Definition probe_apex_is_sum :
  Sets_colim_obj F = Sets_colim_sum F := eq_refl.

End ApexNegative.

(* Positive controls naming Cocomplete.v's own constants: the carriers DO
   agree by eq_refl, and the apex equivalence IS the generated relation. *)
Check Sets_colim_carrier_is_coproduct.
Check Sets_colim_equiv_is_rel.
Check Sets_colim_obj.
Check Sets_colim_sum.

(** ** Negative 3: the triangle as a Leibniz equality of WHOLE morphisms

    Conversion negative.  The triangle holds POINTWISE ([Sets_colim_triangle],
    an [Example] in Cocomplete.v), but the composite rebuilds a
    [proper_morphism] certificate, so the two whole morphisms do not
    convert.  Measured in Cocomplete.v's header since it was written and
    pinned NOWHERE until the audit found the gap. *)

Section TriangleNegative.

Context (D : Category) (F : D ⟶ Sets) (N : Cocone F) (d : obj[D]).

Fail Definition probe_triangle_whole_morphism :
  Sets_colim_med F N ∘ Sets_colim_inj F d = vertex_map[N] := eq_refl.

End TriangleNegative.

(* Positive controls naming the negative's own constants.  [vertex_map] is
   guarded twice over: by this control, and because renaming it breaks the
   [vertex_map[N]] NOTATION into a syntax error, which [Fail] does not
   catch -- so that one would fail loudly even with no control at all. *)
Check Sets_colim_med.
Check Sets_colim_inj.
Check @vertex_map.

(** ** Non-vacuity, guarded

    These are the two halves that keep the construction from being
    empty.  READ THE SCOPE: each is a fact about ONE shape, not a
    general non-collapse theorem, and both target headers say so. *)

(* The quotient does not collapse: at the two-object discrete shape the
   two fibres stay apart. *)
Check two_fibres_not_collapsed.

Check two_fibres_not_equal_in_colimit.

Check two_disc_objects_distinct.

Check two_disc_hom_is_eq.

Check colim_rel_separates.

(* The quotient does merge: at the omega shape, stages 0 and 1 are
   identified in the colimit while the coproduct keeps them apart.  A
   discrete shape has no connecting maps and so could not witness this. *)
Check omega_stages_merged.

Check omega_stages_apart_in_coproduct.

(* The degenerate control, labelled as one in its own file. *)
Check empty_shape_colim_empty.

(** ** The headline artifacts *)

Check Sets_Cocomplete.

Check Sets_Omega_Colimit.

Check Sets_Chain_Colimit.

Check Sets_colim_triangle.
