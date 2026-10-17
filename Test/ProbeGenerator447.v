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

(* * ** Positive controls: every 常值 negatives depend on （已译） *)

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

(* 相关说明。 （已译） *)

Section Readbacks.

Context {C : Category}.

(* 相关说明。 （已译） *)
Example p447_rt1 (G : Generator C) : gen_of_cog (cog_of_gen G) = G := eq_refl.
Example p447_rt2 (G : Cogenerator (C^op)) :
  cog_of_gen (gen_of_cog G) = G := eq_refl.

(* The single-object round trip is an equation, not a re-inhabitation. *)
Example p447_roundtrip (c : C) (H : IsSeparator c) :
  separator_of_generator (Generator_of_separator c H) tt
    (fun j => match j with tt => eq_refl end) = H := eq_refl.

(*
   本节说明 ProbeGenerator447 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition p447_wrong_variance_type (G : Generator C) : Type :=
  JointlyFaithful (fun j : gen_index G => [Hom ─, gen_obj G j]).

End Readbacks.

(** ** Negatives *)

Section Negatives.

Context {C : Category}.

(*
   本节说明 ProbeGenerator447 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n1 (G : Cogenerator (C^op)) : Generator C :=
  @Build_Generator C (cog_index G) (cog_obj G) (@cog_separates (C^op) G).

(*
   本节说明 ProbeGenerator447 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example n2 : Generator C = Cogenerator (C^op) := eq_refl.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n3 (G : Generator C) :
  JointlyFaithful (fun j : gen_index G => [Hom ─, gen_obj G j]) :=
  fun x y f g H => gen_separates G f g (fun j k => H j k).

(*
   本节说明 ProbeGenerator447 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example n4 (c : C) (H : IsSeparator c) : Faithful [Hom c,─] := H.

(*
   本节说明 ProbeGenerator447 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition n5 (G : Cogenerator (C^op)) : Generator C :=
  {| gen_index := cog_index G; gen_obj := cog_obj G;
     gen_separates := fun x y f g H => @cog_separates (C^op) G y x f g H |}.

End Negatives.
