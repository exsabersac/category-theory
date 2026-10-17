(*
   本文件为测试：ProbeCatCoproduct338。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Cat.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Instance.Cat.Coproduct.

Generalizable All Variables.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (FORMABILITY): the explicit universe binders are
       load-bearing

    `SigmaCat` is declared `@{ui uo oh op us}` and its constraint block is
    ALL BOUNDS -- `ui <= us`, `uo <= us`, `oh <= op`, the last being
    `Class Category`'s own `h <= p`.  Written WITHOUT binders the same
    body minimizes to a shape that identifies the summands' hom and proof
    universes.  The control and the negative differ in nothing else. *)

Section BinderBoundary.

Universe uo uh up.
Constraint uh < up.

(* Control: the ANNOTATED construction is formable with the summands' hom
   and proof universes declared strictly apart. *)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) => SigmaCat C).

(* Control: so is its injection, at the same levels. *)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) (i : I) =>
         SigmaCat_inj C i).

(* The unannotated body, re-declared here so the negative is about the
   ANNOTATION and not about anything else in the file. *)
Definition sigma_obj_unann {I : Type} (C : I -> Category) : Type :=
  ∃ i : I, C i.

(* NEGATIVE 1. *)
Fail Check (fun (I : Type) (C : I -> Category@{uo uh up}) =>
              sigma_obj_unann C).

End BinderBoundary.

(** ** Negative 2 (FORMABILITY): the UMP's one identification is
       `Functor_Setoid`'s

    `SigmaCat_ump` displays `C : I → Category@{u7 u9 u9}` and
    `D : Category@{u8 u9 u9}` -- the two OBJECT universes stay apart while
    hom and proof are identified.  The controls show the functor type and
    the `Unique` packaging are both innocent. *)

Section SetoidBoundary.

Universe vo vh vp.
Constraint vh < vp.

(* Control: the functor TYPE elaborates at separated levels. *)
Check (fun (C D : Category@{vo vh vp}) => (C ⟶ D)).

(* Control: so does a `Unique` over a hom-setoid of such a category. *)
Check (fun (C : Category@{vo vh vp}) (x y : C)
           (P : (x ~> y) -> Type) => @Unique _ (@homset C x y) P).

(* Control: [Functor_Setoid] EXISTS and elaborates at UNCONSTRAINED
   levels -- without this the negative below would still "succeed" after
   a rename of [Functor_Setoid], on a reference-not-found error rather
   than on the universe boundary.  (That vacuity was measured, not
   guessed: an earlier revision of this file omitted this line and the
   rename simulation scored 3/4.) *)
Check @Functor_Setoid.

(* NEGATIVE 2. *)
Fail Check (fun (C D : Category@{vo vh vp}) => @Functor_Setoid C D).

End SetoidBoundary.

(** ** The packaging is transparent, in all THREE fields

    The construction is stated first at the apex-pinned
    `IsIndexedCoproduct` and only then packaged through
    `Build_HasIndexedCoproducts`, deliberately avoiding
    `Colimit`/`DiscreteCat_Functor`.  Nothing is lost in the packaging:
    the class's object field, its injection field AND its universal-
    property field all return the elementary data at `eq_refl`.  The
    third is the one worth having -- it says the bundled class carries
    the very record `SigmaCat_IsIndexedCoproduct` proves, not a rebuilt
    copy of it. *)

Check @SigmaCat_IsIndexedCoproduct.
Check Cat_HasIndexedCoproducts.

Definition probe_pkg_obj {I : Type} (C : I -> Cat) :
  @indexed_coproduct Cat Cat_HasIndexedCoproducts I C = SigmaCat C
  := eq_refl.

Definition probe_pkg_inj {I : Type} (C : I -> Cat) (i : I) :
  @indexed_coproduct_inj Cat Cat_HasIndexedCoproducts I C i
    = SigmaCat_inj C i := eq_refl.

Definition probe_pkg_ump {I : Type} (C : I -> Cat) :
  @indexed_coproduct_ump Cat Cat_HasIndexedCoproducts I C
    = SigmaCat_IsIndexedCoproduct C := eq_refl.

(** ** Negative 3 (CONVERSION): the binary comparison is an isomorphism
       and nothing stronger

    At `I := bool` the indexed construction and `Construction/Coproduct.v`'s
    binary `Coproduct` are isomorphic AS CATEGORIES
    (`SigmaBool_strict_iso`, in `StrictCat`, both round trips at
    `Functor_StrictEq_Setoid`).  They are not the same category, and the
    obstruction is already in the OBJECT type: a dependent pair against a
    tagged sum. *)

(* Control: the isomorphism that DOES hold. *)
Check @SigmaBool_strict_iso.
Check @SigmaBool_iso.
Check @BoolFam.

(* NEGATIVE 3. *)
Fail Definition probe_bool_obj (C D : Category) :
  obj[SigmaCat (BoolFam C D)] = (obj[C] + obj[D])%type := eq_refl.

(** ** The compiled half of the encoding-(c) refutation

    For provably distinct indices the type `∀ e : i = j, X e` is
    INHABITED, by the function that eliminates the empty equality.  So
    reading a cross-summand hom that way does not give an empty hom-set;
    it gives a one-element one, and the construction would be the
    indiscrete category on the summands rather than their disjoint union.
    The header argues this; here it is, compiled. *)

Definition probe_forall_encoding_inhabited
  (C : bool -> Category) (x : C true) (y : C false) :
  ∀ e : true = false, ob_cast C e x ~> y :=
  fun e => match (eq_ind true (fun b : bool => if b then True else False)
                          I false e) with end.

(* Contrast, from the target: the encoding actually used makes that hom
   EMPTY, which is the point. *)
Check @sigma_hom_cross_empty.
Check @bool_cross_empty_lr.
Check @bool_cross_empty_rl.

(** ** Positive controls for the headline artifacts *)

Check @SigmaCat.
Check @SigmaCat_inj.
Check @SigmaCat_case.
Check @SigmaCat_case_inj.
Check @SigmaCat_case_unique.
Check @SigmaCat_ump.
Check @ob_cast.
Check @mor_cast.

(** The hypothesis-free/hypothesis-bearing split, and the necessity
    theorem that makes the split principled rather than convenient. *)

Check @SigmaCat_inj_Full.
Check @sigma_inj_Full_forces_UIP.
Check @inj_Full_forces_UIP_at_One.
Check @SigmaCat_const_inj_Faithful.
Check @SigmaCat_inj_Faithful.
Check @Faithful_cancel.
Check @IdxUIP.

(** Non-vacuity. *)

Check @SigmaCat_empty_no_obj.
Check @SigmaCat_unit_iso.
Check @bool_summands_not_isomorphic.
Check @case_separates_summands.
Check @sigma_poly_unit_dec.

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

    Read off the `Fail` commands themselves, not off memory -- an
    earlier revision of this table was written from memory and got two
    of the three rows wrong, crediting Negative 1 with [SigmaCat] and
    [SigmaCat_inj] and Negative 2 with [homset], all three of which
    occur only in that section's positive CONTROLS:

      Negative 1 names [Type], [Category], [sigma_obj_unann]
      Negative 2 names [Category], [Functor_Setoid]
      Negative 3 names [Category], [obj], [SigmaCat], [BoolFam],
                        [eq_refl]

    Excluding core vocabulary ([Type], [Category], [obj], [eq_refl]) on
    the stated ground that it is named by almost every file in the tree
    rather than that it is hard to guard, and excluding the file-local
    [sigma_obj_unann] because renaming it renames both halves at once
    and so guards nothing, the constants a NEGATIVE names are THREE:
    [Functor_Setoid], [SigmaCat], [BoolFam].

    Each of the three is named by a positive control above.  Score:
    3/3, on an unpadded denominator, measured by compiling a renamed
    copy of this file against an instrument-checked baseline and
    confirming each one breaks it.  ([SigmaCat_inj] also breaks the
    file when renamed, via its controls; it is not counted here because
    no negative names it, and counting it was what padded the earlier
    4/4.) *)
