(*
   本文件为测试：ProbePowerset382。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Closed.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Powerset.

Require Import Category.Instance.Powerset.
Require Import Category.Instance.Powerset.Subobject.
Require Import Category.Instance.FinSet.Subsets.
Require Import Category.Instance.Top.Image.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Negative 1: the instrument *)

(* 相关说明。 （已译） *)
Fail Check probe382_no_such_constant_anywhere.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Check @subset_le.
Check @subset_le_preorder.
Check @Subsets.
Check @Subsets_Complete.
Check @Subsets_Cartesian.
Check @subset_meet.
Check @DirectImage.
Check @InverseImage.
Check @image_preimage_adjunction.
Check @image_preimage_galois.
Check @image_MonotoneFun.
Check @preimage_MonotoneFun.
Check @direct_image_not_meet_preserving.
Check @powerset_sng0.
Check @sub_image.
Check @sub_reindex_monotone.
Check @sub_image_is_Powerset_Prop_image.
Check @sub_reindex_is_Powerset_Prop_preimage.
Check @Powerset_obj.
Check @Powerset_Prop_obj.
Check @Powerset_Prop_image.
Check @Powerset_Prop_preimage.
Check @Powerset_subobject_of_subset.
Check @Powerset_subset_of_subobject.
Check @Powerset_Prop_fin_object.
Check @powerset_const0.
Check @powerset_sng1.
Check @Functor_of_monotone.
Check @MonotoneFun.
Check @Opens.
Check @OpenSet.
Check @Opens_preimage.
Check @open_preimage.
Check @open_union.
Check @IsOpen.
Check @nat_inf_point.
Check @nat_inf_no_left_adjoint.
Check @nat_inf_preimage_adjunction.
Check @NatInf_Top.
Check @Point_Top.
Check @TopSpace.
Check @internal_subseteq.
Check @finpow_subseteq.
Check @finpow_le.
Check @FinSubsets.
Check @FinSubsetsToSubsets.
Check @FinSubsetsToSubsets_Full.
Check @FinSubsetsToSubsets_Faithful.
Check @finpow_image.
Check @finpow_dual.
Check @finpow_preimage.
Check @apples.
Check @relation.
Check SetoidObject.
Check Sets.
Check @carrier.
Check @Complete.
Check @Cartesian.
Check @Full.
Check @Faithful.
Check @sub_le.
Check @sub_reindex.
Check @HasPullbacks.
Check @fin_pair.
Check @sub2_10.
Check @sub2_11.
Check @apple0.
Check @finpow_map.
Check @finpow_subseteq_iff.
Check @image_ne_dual_at_apple0.
Check @Subsets_thin.
Check @Thin.
Check @GaloisConnection.
Check @Powerset_Prop_singleton_pred.
Check @nat_inf_right_adjoint.
Check @sub_image_is_Powerset_Prop_image.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* THE POSITIVE CONTROL FIRST.  Inclusion of Prop-valued subsets IS a
   [relation], which is exactly why Instance/Powerset.v can put a
   [Proset] on it. *)
Definition probe_prop_le@{o} (X : SetoidObject@{o o}) :
  relation (carrier (Powerset_Prop_obj@{o} X)) :=
  fun S T => ∀ x, S x → T x.

(*
   本节说明 ProbePowerset382 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_type_le@{o so} (X : SetoidObject@{o o}) :
  relation (carrier (Powerset_obj@{o so} X)) :=
  fun S T => ∀ x, S x → T x.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_opens_le (X : TopSpace) : relation (OpenSet X) :=
  fun U V => ∀ x : X, `1 U x → `1 V x.

(* 相关说明。 （已译） *)
Definition probe_opens_hom (X : TopSpace) (U V : OpenSet X) : Type :=
  U ~{Opens X}~> V.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_interior@{o} (X : TopSpace@{o}) (P : X → Type@{o}) :
  X → Type@{o} :=
  fun x => { V : OpenSet X & prod (∀ y : X, `1 V y → P y) (`1 V x) }.

(* 相关说明。 （已译） *)
Definition probe_small_union@{o} (X : TopSpace@{o}) (I : Type@{o})
  (U : I → (X → Type@{o})) (HU : ∀ i, IsOpen X (U i)) :
  IsOpen X (fun x => { i : I & U i x }) := open_union X I U HU.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_complete_free@{o u + | Set < u +}
  (X : SetoidObject@{o o}) : @Complete (Subsets@{o u} X) :=
  Subsets_Complete.

(* The control at [Set], which is what Instance/Powerset.v states. *)
Definition probe_complete_at_Set@{o +} (X : SetoidObject@{o o}) :
  @Complete (Subsets@{o Set} X) := Subsets_Complete.

(* 相关说明。 （已译） *)
Definition probe_cartesian_free@{o u + | Set < u +}
  (X : SetoidObject@{o o}) : @Cartesian (Subsets@{o u} X) :=
  Subsets_Cartesian.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 ProbePowerset382 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_image_meet@{o so} :
  Powerset_Prop_image@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    = subset_meet
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o})
  := eq_refl.

(* 相关说明。 （已译） *)
Example probe_preimage_meet@{o so +} :
  Powerset_Prop_preimage@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    = subset_meet
        (Powerset_Prop_preimage@{o} powerset_const0@{o so}
           powerset_sng0@{o})
        (Powerset_Prop_preimage@{o} powerset_const0@{o so}
           powerset_sng1@{o})
  → True.
Proof. intros _; exact I. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_monotone_functor@{o so u}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  Functor_of_monotone (subset_le_preorder@{o} X)
    (subset_le_preorder@{o} Y) (image_MonotoneFun f)
  = DirectImage f := eq_refl.

Example probe_monotone_functor_obj@{o so u +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y)
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} X)
         (subset_le_preorder@{o} Y) (image_MonotoneFun f)] S
  = fobj[DirectImage f] S := eq_refl.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_sub_image_bridge@{o so}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
  = Powerset_Prop_image@{o} f S := eq_refl.

(* The control: same comparison at [≈] Instance/Powerset/
 Subobject.v's own 引理. （已译） *)
Example probe_sub_image_bridge_equiv@{o so +}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (S : carrier (Powerset_Prop_obj@{o} A)) :
  Powerset_subset_of_subobject@{o so}
      (sub_image f (Powerset_subobject_of_subset@{o so} S))
    ≈ Powerset_Prop_image@{o} f S
  := sub_image_is_Powerset_Prop_image f S.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Definition probe_adjunction_exists@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  DirectImage f ⊣ InverseImage f := image_preimage_adjunction f.

Definition probe_no_left_adjoint_exists
  (L : Opens Point_Top ⟶ Opens NatInf_Top)
  (A : L ⊣ Opens_preimage nat_inf_point) : False :=
  nat_inf_no_left_adjoint L A.

Definition probe_right_adjoint_exists :
  Opens_preimage nat_inf_point ⊣ nat_inf_right_adjoint :=
  nat_inf_preimage_adjunction.

Definition probe_finset_full (n : nat) : Full (FinSubsetsToSubsets n) :=
  FinSubsetsToSubsets_Full n.

Definition probe_finset_faithful (n : nat) :
  Faithful (FinSubsetsToSubsets n) := FinSubsetsToSubsets_Faithful n.

Definition probe_reindex_monotone {C : Category} `{@HasPullbacks C}
  {x y : C} (f : y ~> x) (u v : SubObj x) :
  sub_le u v → sub_le (sub_reindex f u) (sub_reindex f v) :=
  sub_reindex_monotone f.

Example probe_internal_subseteq_computes :
  internal_subseteq 2 (fin_pair sub2_10 sub2_11) = fin_true := eq_refl.

Example probe_finpow_image_ne_dual :
  finpow_image apples apple0 = finpow_dual apples apple0 → False :=
  fun H => image_ne_dual_at_apple0 H.

Example probe_finpow_preimage_is_map (T : Fin.t (finpow 2)) :
  finpow_preimage apples T = finpow_map apples T := eq_refl.

Example probe_finpow_subseteq_iff (n : nat) (S T : Fin.t (finpow n)) :
  finpow_subseteq S T = true ↔ finpow_le S T := finpow_subseteq_iff n S T.

Example probe_sub_reindex_bridge@{o so +}
  (A B : SetoidObject@{o o}) (f : A ~{Sets@{o so}}~> B)
  (T : carrier (Powerset_Prop_obj@{o} B)) :
  Powerset_subset_of_subobject@{o so}
      (sub_reindex f (Powerset_subobject_of_subset@{o so} T))
    ≈ Powerset_Prop_preimage@{o} f T
  := sub_reindex_is_Powerset_Prop_preimage f T.

Example probe_subsets_thin (X : SetoidObject) : Thin (Subsets X) :=
  Subsets_thin X.

Example probe_open_preimage_obj {X Y : TopSpace} (g : Y ~{Top}~> X)
  (U : OpenSet X) : fobj[Opens_preimage g] U = open_preimage g U := eq_refl.

Example probe_galois_exists@{o so u +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  GaloisConnection (@subset_le@{o} X) (@subset_le@{o} Y) :=
  image_preimage_galois f.

Example probe_preimage_monotonefun@{o so +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  @MonotoneFun _ (@subset_le@{o} Y) _ (@subset_le@{o} X) :=
  preimage_MonotoneFun f.

Example probe_powerset_sng0_is_singleton@{o +} :
  powerset_sng0@{o}
    = Powerset_Prop_singleton_pred@{o}
        (X:=Powerset_Prop_fin_object@{o} 2) Fin.F1 := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** Negative 9: TYPING -- 伴随 has handedness （已译） *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_wrong_handedness@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  InverseImage f ⊣ DirectImage f := image_preimage_adjunction f.

(* 相关说明。 （已译） *)
Definition probe_right_handedness@{o so u u0 u1 +}
  (X Y : SetoidObject@{o o}) (f : X ~{Sets@{o so}}~> Y) :
  DirectImage f ⊣ InverseImage f := image_preimage_adjunction f.
