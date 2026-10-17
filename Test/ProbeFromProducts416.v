Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Two.

Generalizable All Variables.

Open Scope category_scope.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeFromProducts416。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

Fail Check probe416_no_such_constant.

(** ** Guards *)

Check @limit_of_products_equalizer.
Check @Complete_from_products_equalizers.
Check @Cocomplete_from_coproducts_coequalizers.
Check @continuous_from_products_equalizers.
Check @pe_cone.
Check @pe_limiting.
Check @pe_limit_cone.
Check @pe_gen_cone.
Check @pe_gen_apex.
Check @pe_apex.
Check @pe_image_cone.
Check @pe_image_ConeIso.
Check @ArrowIx.
Check @ArrowIx_Generates.
Check @Generates.
Check @Gen.
Check @gen_id.
Check @gen_idx.
Check @IsIdArrow.
Check @is_id_arrow.
Check @nonid_Generates.
Check @pe_gen_restrict_iso.
Check @HasIndexedProducts.
Check @HasIndexedCoproducts.
Check @HasEqualizers.
Check @HasCoequalizers.
Check @IsIndexedProduct.
Check @IsEqualizer.
Check @indexed_product.
Check @iprod.
Check @Limit.
Check @IsLimitCone.
Check @Cone.
Check @Complete.
Check @FCone.
Check @cone_leg.
Check @vertex_obj.

(* 相关说明。 （已译） *)

Section FullIndex.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context {J : Category} (F : J ⟶ C).

(* Controls: apex, apex 对象 every leg agree nose. （已译） *)
Example probe416_ctrl_full_apex :
  vertex_obj[pe_gen_cone HP HE F ArrowIx_Generates]
    = vertex_obj[pe_limit_cone HP F HE] := eq_refl.

Example probe416_ctrl_full_apex_obj :
  pe_gen_apex HP HE F (idx_arr := @aix_arr J) = pe_apex HP F HE := eq_refl.

Example probe416_ctrl_full_leg (x : J) :
  cone_leg (pe_gen_cone HP HE F ArrowIx_Generates) x
    = cone_leg (pe_limit_cone HP F HE) x := eq_refl.

(* N1: CONVERSION — not as records. *)
Fail Example probe416_n1 :
  pe_gen_cone HP HE F ArrowIx_Generates = pe_limit_cone HP F HE := eq_refl.

(* 相关说明。 （已译） *)
Example probe416_ctrl_limit_cone :
  @limit_cone _ _ _ (limit_of_products_equalizer HP F HE)
    = pe_limit_cone HP F HE := eq_refl.

Example probe416_ctrl_complete_cone :
  @limit_cone _ _ _ (Complete_from_products_equalizers HP HE J F)
    = pe_limit_cone HP F HE := eq_refl.

End FullIndex.

(* 相关说明。 （已译） *)

Section Image.

Context {C D : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (G : C ⟶ D) (GP : PreservesIndexedProducts G)
  (GE : PreservesEqualizers G).
Context {J : Category} (K : J ⟶ C).

(* Control: the apexes agree. *)
Example probe416_ctrl_image_apex :
  vertex_obj[pe_image_cone HP HE G GP GE K]
    = vertex_obj[FCone G (pe_limit_cone HP K HE)] := eq_refl.

(* N2: CONVERSION — a leg is one [fmap_comp] away. *)
Fail Example probe416_n2 (x : J) :
  cone_leg (pe_image_cone HP HE G GP GE K) x
    = cone_leg (FCone G (pe_limit_cone HP K HE)) x := eq_refl.

(* N3: CONVERSION — the whole records. *)
Fail Example probe416_n3 :
  pe_image_cone HP HE G GP GE K = FCone G (pe_limit_cone HP K HE) := eq_refl.

(* 相关说明。 （已译） *)
Check (pe_image_ConeIso HP HE G GP GE K).

End Image.

(* 相关说明。 （已译） *)

Section Handedness.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (HC : HasIndexedCoproducts C) (HQ : HasCoequalizers C).

(* Controls. *)
Check (Complete_from_products_equalizers HP HE).
Check (Cocomplete_from_coproducts_coequalizers HC HQ).

(* N4: TYPING. *)
Fail Check (Complete_from_products_equalizers HP HQ).

(* N5: TYPING. *)
Fail Check (Cocomplete_from_coproducts_coequalizers HP HE).

End Handedness.

(** ** N6: hom = proof, six donors *)

Section HomProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}) (x y : Cu) (f : x ~> y).

(* Controls. *)
Check (x ~> y).
Check (id[x]).
Check (@Functor Cu Cu).

Fail Check (@HasIndexedProducts Cu).
Fail Check (@HasEqualizers Cu).
Fail Check (@IsIndexedProduct Cu).
Fail Check (@IsEqualizer Cu x y f f).
Fail Check (@Limit Cu).
Fail Check (@Complete Cu).

End HomProof.

(* 相关说明。 （已译） *)

Section ShapeHom.

Universes jo jh co ch.
Constraint jh < ch.

Context (Ju : Category@{jo jh jh}) (Cu : Category@{co ch ch}).
Context (Fu : Ju ⟶ Cu).

(* Controls. *)
Check Fu.
Check (@Cone Ju Cu Fu).
Check (@ArrowIx Ju).

Fail Check (@Limit Ju Cu Fu).
Fail Check (@IsLimitCone Ju Cu Fu).

(* Inherited: fires at the diagram argument [Fu]. *)
Fail Check (@pe_cone Ju Cu Fu).

End ShapeHom.

(*
   本节说明 ProbeFromProducts416 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AboveSet.

Universes co ch.
Constraint Set < ch.

Context (Cu : Category@{co ch ch}).
Context (HP : HasIndexedProducts Cu) (HE : HasEqualizers Cu).

(* Controls. *)
Check HP.
Check (@indexed_product Cu HP).
Check (@Complete_from_products_equalizers Cu HP HE).

(* Former N8, now a positive control. *)
Check (@iprod Cu).

End AboveSet.

(** ** The [Sets] instantiation *)

(*
   本节说明伴随、拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition sets_pe_complete : @Complete Sets :=
  Complete_from_products_equalizers Sets_HasIndexedProducts
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks).

Check sets_pe_complete.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition two_gen_fam (_ : unit) : TwoX ~{_2}~> TwoY := TwoXY.

Definition two_Generates : Generates two_gen_fam.
Proof.
  intros x y f.
  destruct f.
  - exact (@gen_id _2 unit _ _ two_gen_fam TwoX).
  - exact (@gen_id _2 unit _ _ two_gen_fam TwoY).
  - exact (@gen_idx _2 unit _ _ two_gen_fam tt).
Defined.

(* 相关说明。 （已译） *)

Example two_arrowix_apart :
  @mk_arrow _2 _ _ TwoXY = @mk_arrow _2 _ _ TwoIdX → False.
Proof. intro H; apply (f_equal (fun a => snd (`1 a))) in H; discriminate. Qed.

(* Being 恒等 decidable [_2], so non-恒等 family of
 target's [nonid_Generates] generates there too. （已译） *)

Definition two_isid_dec (x y : _2) (f : x ~{_2}~> y) :
  IsIdArrow x y f + (IsIdArrow x y f → False).
Proof.
  destruct f.
  - left; exact (@is_id_arrow _2 TwoX TwoIdX (reflexivity _)).
  - left; exact (@is_id_arrow _2 TwoY TwoIdY (reflexivity _)).
  - right; intro H; inversion H.
Defined.

Check (nonid_Generates two_isid_dec).

(* 相关说明。 （已译） *)

Check (fun F : _2 ⟶ Sets =>
  pe_gen_restrict_iso Sets_HasIndexedProducts
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks) F
    two_Generates).
