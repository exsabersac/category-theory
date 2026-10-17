Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Metacategory.General.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.

(* Sets and set-like categories. *)
Require Import Category.Instance.Coq.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ens.
Require Import Category.Instance.EnsV.
Require Import Category.Instance.Rel.
Require Import Category.Instance.Rel.Dagger.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Instance.Sets.Par.
Require Import Category.Instance.Coq.Par.

(* Algebraic categories. *)
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Matr.

(* Order, shape and graph categories. *)
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.Simplex.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Concrete.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.Homotopy.

(*
   本节说明 Roster 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Category.Instance.Comp.

Generalizable All Variables.

(*
   nLab: https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   本节说明 Roster 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Sets and the set-like categories *)

(* Mac Lane's Set, in the library's two readings: setoids, and the
   strict category of Coq types with functions. *)
Example roster_Sets : Category := Sets.
Example roster_Coq : Category := Coq.

(*
   本节说明 Roster 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_Ens : Category := Ens.
Example roster_EnsT (T : Type) : Category := EnsT T.
Example roster_EnsV {V : Type} (El : V → Type) : Category := EnsV El.
Example roster_EnsV_Incl {V : Type} (El : V → Type) : EnsV El ⟶ Coq :=
  EnsV_Incl El.

(* Finite sets, in both presentations: the skeletal one on [nat], and
   finite setoids carrying their counting, with the comparison. *)
Example roster_FinSet : Category := FinSet.
Example roster_Set_f : Category := Set_f.
Example roster_FinSet_Incl : FinSet ⟶ Set_f := FinSet_Incl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_PointedSets : Category := PointedSets.

(* Partial maps, in both readings: over setoids and over types. *)
Example roster_Part : Category := Part.
Example roster_Par : Category := Par.

(* Rel, with the wide embedding of functions as relations.  Note the
   direction: [Relation_Functor] goes from [Coq], not from [Sets]. *)
Example roster_Rel : Category := Rel.
Example roster_Relation_Functor : Coq ⟶ Rel := Relation_Functor.

(** ** The algebraic categories, with their forgetful functors *)

(* Commutative monoids at the set level. *)
Example roster_CMon : Category := CMon.
Example roster_CMon_Forget : CMon ⟶ Sets := CMon_Forget.

(* Groups and abelian groups. *)
Example roster_Grp : Category := Grp.
Example roster_Grp_Forget : Grp ⟶ Sets := Grp_Forget.
Example roster_Ab : Category := Ab.
Example roster_Ab_Forget : Ab ⟶ Sets := Ab_Forget.

(* Rigs, and rings under Mac Lane's name, with the commutative full
   subcategory and both forgetful functors. *)
Example roster_Rig : Category := Rig.
Example roster_Rig_Forget_CMon : Rig ⟶ CMon := Rig_Forget_CMon.
Example roster_Rng : Category := Rng.
Example roster_Rng_Forget : Rng ⟶ Sets := Rng_Forget.
Example roster_Rng_Forget_Ab : Rng ⟶ Ab := Rng_Forget_Ab.
Example roster_CRng : Category := CRng.

(* Modules on both sides, and the bimodule record that justifies the
   right-module definition. *)
Example roster_RMod (R : RingObject) : Category := RMod R.
Example roster_RMod_Forget (R : RingObject) : RMod R ⟶ Sets :=
  RMod_Forget R.
Example roster_RMod_Forget_Ab (R : RingObject) : RMod R ⟶ Ab :=
  RMod_Forget_Ab R.
Example roster_ModR (R : RingObject) : Category := ModR R.
Example roster_Bimodule (R S : RingObject) : Type := Bimodule R S.

(* Vector spaces over a field, and the finite-dimensional refinement
   whose objects carry chosen coordinates. *)
Example roster_Vct_F (F : FieldObject) : Category := Vct_F F.
Example roster_FdVect (F : FieldObject) : Category := FdVect F.
Example roster_FdVect_Forget (F : FieldObject) : FdVect F ⟶ Vct_F F :=
  FdVect_Forget F.

(* Fields.  The category and the determination of its monomorphisms
   are Instance/Field.v's; only the entry is recorded here. *)
Example roster_Field : Category := Field.
Example roster_Field_Forget : Field ⟶ Sets := Field_Forget.
Example roster_Field_Rng : Field ⟶ Rng := Field_Rng.

(* Representations of a group over a ring. *)
Example roster_Rep (K : RingObject) (G : GrpObject) : Category :=
  Rep K G.

(* Matrices over a rig, with Awodey's ℕ-matrix and Mac Lane's integer
   instantiations. *)
Example roster_Matr (R : RigObject) : Category := Matr R.
Example roster_Matr_N : Category := Matr_N.
Example roster_Matr_Z : Category := Matr_Z.

(** ** The Mon residual: internal monoids in (Sets, ∏) *)

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Mon_Sets : Category := @Mon Sets Sets_Product_Monoidal.

Definition Mon_Sets_Forget : Mon_Sets ⟶ Sets :=
  @Mon_Forget Sets Sets_Product_Monoidal.

Example roster_Mon_Sets : Category := Mon_Sets.
Example roster_Mon_Sets_Forget : Mon_Sets ⟶ Sets := Mon_Sets_Forget.
Example roster_Rig_Forget_Mon : Rig ⟶ Mon_Sets := Rig_Forget_Mon.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Order categories, and the Poset/Proset erratum *)

(* ONE preorder as a thin category (Mac Lane's Preord is [Ord]).  The
   witness is (ℕ, ≤). *)
Example roster_Proset {A : Type} {R : A → A → Prop}
  (P : RelationClasses.PreOrder R) : Category := Proset P.
Example roster_Proset_nat : Category := Proset PeanoNat.Nat.le_preorder.

(*
   本节说明 Roster 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_Pos : Category := Pos.
Example roster_Pos_Forget : Pos ⟶ Sets := Pos_Forget.

(** ** Categories of categories, shapes and graphs *)

Example roster_Cat : Category := Cat.
Example roster_StrictCat : Category := StrictCat.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_QuiverCategory : Category := QuiverCategory.
Example roster_QuiverVertices : QuiverCategory ⟶ Sets := QuiverVertices.
Example roster_QuiverArrows : QuiverCategory ⟶ Sets := QuiverArrows.

(* The simplicial category Δ, with its wide inclusion into finite
   sets — faithful, and provably not full. *)
Example roster_Simplex : Category := Simplex.
Example roster_Simplex_FinSet : Simplex ⟶ FinSet := Simplex_FinSet.

(* Mac Lane's §I.1 arrows-only presentation, and the passage from it
   back to a category. *)
Example roster_Metacategory : Type := Metacategory.
Example roster_Category_from_Metacategory (M : Metacategory) : Category :=
  Category_from_Metacategory M.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Sets and the strict variant: the two differ. *)
Example roster_Sets_Terminal : @Terminal Sets := Sets_Terminal.
Example roster_Sets_Initial : @Initial Sets := Sets_Initial.
Example roster_Coq_Terminal : @Terminal Coq := Coq_Terminal.
Example roster_Coq_Initial : @Initial Coq := Coq_Initial.
Example roster_FinSet_Terminal : @Terminal FinSet := FinSet_Terminal.
Example roster_FinSet_Initial : @Initial FinSet := FinSet_Initial.

(* Pointed sets: the singleton is a genuine zero object, which is what
   distinguishes Set_* from Set. *)
Example roster_PointedSets_Zero : ZeroObject PointedSets :=
  PointedSets_Zero.

(* The algebraic entries, where initial and terminal coincide. *)
Example roster_CMon_Zero : ZeroObject CMon := CMon_Zero.
Example roster_Grp_Zero : ZeroObject Grp := Grp_Zero.
Example roster_Ab_Zero : ZeroObject Ab := Ab_Zero.
Example roster_RMod_Zero (R : RingObject) : ZeroObject (RMod R) :=
  RMod_Zero R.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_Rng_Terminal : @Terminal Rng := Rng_Terminal_zero.
Example roster_Rng_Initial : @Initial Rng := Rng_Initial_Z.

(* Relations: a zero object, by self-duality. *)
Example roster_Rel_Zero : ZeroObject Rel := Rel_Zero.

(* Categories of categories. *)
Example roster_Cat_Terminal : @Terminal Cat := Cat_Terminal.
Example roster_Cat_Initial : @Initial Cat := Cat_Initial.
Example roster_StrictCat_Terminal : @Terminal StrictCat :=
  StrictCat_Terminal.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_Field_no_initial : @Initial Field → False :=
  Field_no_initial.
Example roster_Field_no_terminal : @Terminal Field → False :=
  Field_no_terminal.

(*
   本节说明（余）端、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example roster_Top : Category := Top.
Example roster_Top_Forget : Top ⟶ Sets := Top_Forget.
Example roster_Top_Discrete : Sets ⟶ Top := Top_Discrete.
Example roster_Top_Indiscrete : Sets ⟶ Top := Top_Indiscrete.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_Top_Terminal : @Terminal Top := Top_Terminal.
Example roster_Top_Initial : @Initial Top := Top_Initial.
Example roster_Top_no_zero : @ZeroObject Top → False := Top_no_zero_object.

(* The separation full subcategories.  [CompactHausdorffSpaces] is the
   roster entry; its forgetful/monadicity story is disclosed out of
   scope in the header. *)
Example roster_HausdorffSpaces : Category := HausdorffSpaces.
Example roster_CompactHausdorffSpaces : Category :=
  CompactHausdorffSpaces.

(* Top_*: based spaces and based maps.  Still axiom-free — a basepoint
   costs nothing. *)
Example roster_Top_pointed : Category := Top_pointed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_Toph : Category := Toph.
Example roster_TophProj : Top ⟶ Toph := TophProj.
Example roster_Toph_pointed : Category := Toph_pointed.
Example roster_Toph_pointed_Proj : Top_pointed ⟶ Toph_pointed :=
  Toph_pointed_Proj.

(*
   本节说明 Roster 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

(* The category of algebras for an operation signature — the equational
   fragment of Model_T.  Axiom-free. *)
Example roster_Algs (S : UA.OpSignature) : Category := @UA.Algs S.
Example roster_GroupOp : UA.OpSignature := UA.GroupOp.

(*
   本节说明 Roster 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example roster_Group_variety : Type := UA.Group.
Example roster_Group_variety_witness : UA.Group := UA.Bool.
