Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Dual.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Adjunction.SAFT.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(*
   本文件为测试：ProbeGenerator447。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check generator_447_no_such_constant.

(** ** Positive controls: every constant the negatives depend on *)

Check @Generator.
Check @Build_Generator.
Check @gen_index.
Check @gen_obj.
Check @gen_separates.
Check @IsSeparator.
Check @JointlyFaithful.
Check @Separates.
Check @generator_iff_jointly_faithful.
Check @Generator_of_separator.
Check @separator_of_generator.
Check @separator_faithful.
Check @faithful_separator.
Check @generator_jointly_faithful.
Check @Cogenerator.
Check @Build_Cogenerator.
Check @cog_index.
Check @cog_obj.
Check @cog_separates.
Check @gen_of_cog.
Check @cog_of_gen.
Check @Faithful.
Check @Build_Faithful.
Check @fmap_inj.
Check @Curried_Hom.
Check @Curried_CoHom.
Check @Separator.
Check @Separator_of_IsSeparator.
Check @IsSeparator_of_Separator.

(** ** Readbacks that HOLD, at the strength stated *)

Section Readbacks.

Context {C : Category}.

(* F1: the duality bridge round-trips on the nose, both ways. *)
Example p447_rt1 (G : Generator C) : gen_of_cog (cog_of_gen G) = G := eq_refl.
Example p447_rt2 (G : Cogenerator (C^op)) :
  cog_of_gen (gen_of_cog G) = G := eq_refl.

(* The single-object round trip is an equation, not a re-inhabitation. *)
Example p447_roundtrip (c : C) (H : IsSeparator c) :
  separator_of_generator (Generator_of_separator c H) tt
    (fun j => match j with tt => eq_refl end) = H := eq_refl.

(* The wrong-variance STATEMENT is well formed -- it says the family
   COseparates -- so negative N3 below pins the DERIVATION and not the
   statement; a refusal of the statement would be vacuous. *)
Definition p447_wrong_variance_type (G : Generator C) : Type :=
  JointlyFaithful (fun j : gen_index G => [Hom ─, gen_obj G j]).

End Readbacks.

(** ** Negatives *)

Section Negatives.

Context {C : Category}.

(* N1 -- CONVERSION.  The bridge needs the two object quantifiers
   exchanged: the field applied at the objects in the order the record
   declares them is refused, "cannot unify "x ~{ C }~> y" and
   "x ~{ C^op }~> y"". *)
Fail Definition n1 (G : Cogenerator (C^op)) : Generator C :=
  @Build_Generator C (cog_index G) (cog_obj G) (@cog_separates (C^op) G).

(* N2 -- CONVERSION.  The two TYPES are not equal: two distinct
   inductives over the same data, "cannot unify "Generator C" and
   "Cogenerator C^op"".  The eq_refl round trips above are therefore the
   strongest statement available. *)
Fail Example n2 : Generator C = Cogenerator (C^op) := eq_refl.

(* N3 -- TYPING.  Deriving the contravariant (coseparating) statement
   from a Generator with the covariant proof term: "The term "k" has type
   "gen_obj G j ~{ C }~> y" while it is expected to have type
   "carrier (fobj[fobj[Curried_CoHom C] (gen_obj G j)] x)"" -- the probe
   object sits at the wrong end of the arrow. *)
Fail Definition n3 (G : Generator C) :
  JointlyFaithful (fun j : gen_index G => [Hom ─, gen_obj G j]) :=
  fun x y f g H => gen_separates G f g (fun j k => H j k).

(* N4 -- TYPING.  The bare coercion from the separation clause to the
   faithfulness class: "The term "H" has type "IsSeparator c" while it is
   expected to have type "Faithful (fobj[C] c)"" -- a class record is not
   a function, hence [Build_Faithful] in [separator_faithful]. *)
Fail Example n4 (c : C) (H : IsSeparator c) : Faithful [Hom c,─] := H.

(* N5 -- TYPING.  The record builder without an explicit category infers
   the record's parameter as C^op from [gen_obj := cog_obj G] and then
   rejects the separation field: "The term "f" has type "x ~{ C^op }~> y"
   while it is expected to have type "y ~{ C^op }~> x"". *)
Fail Definition n5 (G : Cogenerator (C^op)) : Generator C :=
  {| gen_index := cog_index G; gen_obj := cog_obj G;
     gen_separates := fun x y f g H => @cog_separates (C^op) G y x f g H |}.

End Negatives.
