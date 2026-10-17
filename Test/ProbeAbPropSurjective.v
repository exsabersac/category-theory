(*
   本文件为测试：ProbeAbPropSurjective。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Preadditive.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** ** NEGATIVE: the propositional witness is not data *)

(*
   本节说明 ProbeAbPropSurjective 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition ab_prop_surjective_is_not_split
  {A B : AbObject} (f : A ~{Ab}~> B) (Hs : AbPropSurjective f) :
  AbSurjective f :=
  ltac:(intro b; destruct (Hs b) as [a Ha]; exists a;
        exact (pequiv_to _ _ Ha)).

(* The same for modules. *)
Fail Definition rmod_prop_surjective_is_not_split
  {R : RingObject} {M N : RModObject R} (f : M ~{RMod R}~> N)
  (Hs : RModPropSurjective f) : RModSurjective f :=
  ltac:(intro b; destruct (Hs b) as [a Ha]; exists a;
        exact (pequiv_to _ _ Ha)).

(** ** CONTROLS: the directions that survive *)

(* The split notion implies the propositional one -- the direction that
   loses nothing, and the positive control for the two negatives above. *)
Example ab_split_implies_prop {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → AbPropSurjective f :=
  ab_surjective_prop f.

Example rmod_split_implies_prop {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModSurjective f → RModPropSurjective f :=
  rmod_surjective_prop f.

(*
   本节说明 ProbeAbPropSurjective 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ab_split_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → Epic f := ab_surjective_epic f.

Example ab_prop_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbPropSurjective f → Epic f := ab_prop_surjective_epic f.

Example rmod_prop_epic {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModPropSurjective f → Epic f :=
  rmod_prop_surjective_epic f.

(* And the headline biconditionals, APPLIED, at their restated strength. *)
Example ab_epic_iff {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f ↔ AbPropSurjective f := ab_epic_iff_surjective f.

Example rmod_epic_iff_readback {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic f ↔ RModPropSurjective f :=
  rmod_epic_iff f.

(** ** The split notions are still there, and still say what they said *)

(* A not-lost check (it holds in the unchanged tree too), not a control of
   the change. *)
Example ab_surjective_is_sigma {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f
    = (∀ b : carrier (cmon_setoid B), { a & cmon_map f a ≈ b })
  := eq_refl.

(** ** Instrument check, scope-free *)

Fail Example probe_ab_prop_surjective_instrument : true = false := eq_refl.
