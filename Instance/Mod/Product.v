Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Structure.Limit.Product.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(*
   本文件给出积相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Section ProdMod.

Context {R : RingObject}.
Context {I : Type}.
Context (V : I → RModObject R).

(* 相关说明。 （已译） *)
Program Definition modprod_setoid : SetoidObject := {|
  carrier := ∀ i : I, carrier (cmon_setoid (V i));
  is_setoid := {| equiv := fun f g => ∀ i, f i ≈ g i |}
|}.
Next Obligation.
  intros; constructor.
  - intros f i; reflexivity.
  - intros f g H i; now symmetry.
  - intros f g h H1 H2 i; now transitivity (g i).
Qed.

(*
   本节说明 Product 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition modprod_cmon : CMonObject := {|
  cmon_setoid := modprod_setoid;
  cmon_zero   := fun i => cmon_zero (V i);
  cmon_plus   := fun f g i => cmon_plus (V i) (f i) (g i);
  cmon_prop   := dep_fun_PropEquiv (is_setoid modprod_setoid)
                   (fun _ _ h => h) (fun _ _ h => h)
                   (fun i => cmon_prop (V i))
|}.
Next Obligation. intros f f' Hf g g' Hg i; now rewrite (Hf i), (Hg i). Qed.
Next Obligation. intros f g h i; apply cmon_plus_assoc. Qed.
Next Obligation. intros f g i; apply cmon_plus_comm. Qed.
Next Obligation. intros f i; apply cmon_plus_zero_l. Qed.

Program Definition modprod_ab : AbObject := {|
  ab_cmon := modprod_cmon;
  ab_neg  := fun f i => ab_neg (V i) (f i)
|}.
Next Obligation. intros f g H i; now rewrite (H i). Qed.
Next Obligation. intros f i; apply ab_neg_left. Qed.

(* The product module: all operations pointwise. *)
Program Definition ProdMod : RModObject R := {|
  rm_ab   := modprod_ab;
  rm_smul := fun r f i => rm_smul (V i) r (f i)
|}.
Next Obligation. intros r s Hrs f g Hfg i; now rewrite Hrs, (Hfg i). Qed.
Next Obligation. intros r f g i; apply rm_smul_distr_l. Qed.
Next Obligation. intros r s f i; apply rm_smul_distr_r. Qed.
Next Obligation. intros r s f i; apply rm_smul_assoc. Qed.
Next Obligation. intros f i; apply rm_smul_one. Qed.

(* The projections. *)
Program Definition prod_proj (i : I) : RModHom ProdMod (V i) := {|
  rm_hom := {| cmon_map := {| morphism := fun f => f i |} |}
|}.
Next Obligation. intros i f g H; exact (H i). Qed.
Next Obligation. intros i; reflexivity. Qed.
Next Obligation. intros i f g; reflexivity. Qed.
Next Obligation. intros i r f; reflexivity. Qed.

(* The mediating map out of a family of maps. *)
Program Definition prod_tuple {Z : RModObject R} (f : ∀ i, RModHom Z (V i)) :
  RModHom Z ProdMod := {|
  rm_hom := {|
    cmon_map := {| morphism := fun z i => cmon_map (rm_hom (f i)) z |}
  |}
|}.
Next Obligation. intros Z f z z' H i; now rewrite H. Qed.
Next Obligation. intros Z f i; apply (cmon_map_zero (rm_hom (f i))). Qed.
Next Obligation. intros Z f a b i; apply (cmon_map_plus (rm_hom (f i))). Qed.
Next Obligation. intros Z f r z i; apply (rm_map_smul (f i)). Qed.

(* The 普遍性质, two clauses [IsIndexedProduct] asks for;
 both [reflexivity] pointwise. （已译） *)
Lemma prod_tuple_proj {Z : RModObject R} (f : ∀ i, RModHom Z (V i)) (i : I) :
  @compose (RMod R) Z ProdMod (V i) (prod_proj i) (prod_tuple f) ≈ f i.
Proof. intro z; reflexivity. Qed.

Lemma prod_tuple_unique {Z : RModObject R} (f : ∀ i, RModHom Z (V i))
  (u : RModHom Z ProdMod)
  (H : ∀ i, @compose (RMod R) Z ProdMod (V i) (prod_proj i) u ≈ f i) :
  u ≈ prod_tuple f.
Proof. intros z i; exact (H i z). Qed.

(* The projections compute. *)
Example prod_proj_component (i : I) (f : carrier (cmon_setoid ProdMod)) :
  cmon_map (rm_hom (prod_proj i)) f = f i := eq_refl.

(* The two clauses assembled 进入 tree's own record: [ProdMod] its
 projections indexed product [RMod R]. （已译） *)
Definition ProdMod_IsIndexedProduct :
  @IsIndexedProduct (RMod R) I V ProdMod prod_proj.
Proof.
  constructor; intros Z pi.
  exists (prod_tuple pi).
  - exact (prod_tuple_proj pi).
  - intros u Hu; symmetry; exact (prod_tuple_unique pi u Hu).
Defined.

(* The record's mediator IS [prod_tuple]. *)
Example prod_iprod_mediator {Z : RModObject R} (pi : ∀ i, RModHom Z (V i)) :
  unique_obj (iprod_desc ProdMod_IsIndexedProduct pi) = prod_tuple pi
  := eq_refl.

End ProdMod.
