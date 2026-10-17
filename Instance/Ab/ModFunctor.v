(* * * R-Mod additive 函子 out B(R) （已译） *)

Require Import Coq.ZArith.ZArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, ibid., §I.8, printed pp. 28-29 —
 nLab:      https://ncatlab.org/nlab/show/Ab-enriched+category
 nLab:      https://ncatlab.org/nlab/show/module
 Wikipedia: https://en.wikipedia.org/wiki/Module_(mathematics)

   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition DeloopRing_AbEnriched (R : RingObject) :
  AbEnriched (DeloopRig (ring_rig R)) := {|
  abenriched_preadditive := DeloopRig_Preadditive (ring_rig R);
  abneg := fun _ _ => ring_neg R
|}.
Next Obligation.
  intros R x y f; simpl.
  rewrite (rig_add_comm (ring_rig R) f (ring_neg R f)).
  exact (ring_neg_l R f).
Qed.
(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example deloop_ring_hom (R : RingObject) :
  (ttt ~{DeloopRig (ring_rig R)}~> ttt)
    = carrier (rig_setoid (ring_rig R)) := eq_refl.

Example deloop_ring_compose (R : RingObject)
  (r s : ttt ~{DeloopRig (ring_rig R)}~> ttt) :
  r ∘ s = rig_mul (ring_rig R) r s := eq_refl.

Example deloop_ring_id (R : RingObject) :
  @id (DeloopRig (ring_rig R)) ttt = rig_one (ring_rig R) := eq_refl.

Example deloop_ring_padd (R : RingObject)
  (r s : ttt ~{DeloopRig (ring_rig R)}~> ttt) :
  @padd _ (DeloopRig_Preadditive (ring_rig R)) ttt ttt r s
    = rig_add (ring_rig R) r s := eq_refl.

Example deloop_ring_abneg (R : RingObject)
  (r : ttt ~{DeloopRig (ring_rig R)}~> ttt) :
  @abneg _ (DeloopRing_AbEnriched R) ttt ttt r = ring_neg R r := eq_refl.

(* * ** The full subcategory additive 函子 （已译） *)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition IsAdditiveFun (R : RingObject)
  (F : DeloopRig (ring_rig R) ⟶ Ab) : Type :=
  @AdditiveFunctor (DeloopRig (ring_rig R)) Ab
    (DeloopRing_AbEnriched R) Ab_AbEnriched F.

(*
   本节说明自然变换、函子、层/筛相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AbFunAdd_sub (R : RingObject) :
  Subcategory ([DeloopRig (ring_rig R), Ab]) :=
  @Build_Subcategory ([DeloopRig (ring_rig R), Ab])
    (fun F => IsAdditiveFun R F)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition AbFunAdd (R : RingObject) : Category :=
  Sub ([DeloopRig (ring_rig R), Ab]) (AbFunAdd_sub R).

Lemma AbFunAdd_Full (R : RingObject) :
  Category.Construction.Subcategory.Full
    ([DeloopRig (ring_rig R), Ab]) (AbFunAdd_sub R).
Proof. intros F G HF HG η; exact I. Qed.

Definition AbFunAdd_Incl (R : RingObject) :
  AbFunAdd R ⟶ [DeloopRig (ring_rig R), Ab] :=
  Incl ([DeloopRig (ring_rig R), Ab]) (AbFunAdd_sub R).

(* * ** From additive 函子 module （已译） *)

(* The action ring element value 函子 at single
 对象: apply Ab-态射 [fmap[F] r]. Every module law below is
 one 函子 law read through 定义. （已译） *)
Definition fun_module_smul {R : RingObject}
  (F : DeloopRig (ring_rig R) ⟶ Ab)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (F ttt : AbObject))) :
  carrier (cmon_setoid (F ttt : AbObject)) :=
  cmon_map (@fmap _ _ F ttt ttt r) m.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition module_of_functor {R : RingObject}
  (F : DeloopRig (ring_rig R) ⟶ Ab) (HF : IsAdditiveFun R F) :
  RModObject R := {|
  rm_ab   := (F ttt : AbObject);
  rm_smul := fun_module_smul F
|}.
Next Obligation.
  intros R F HF r s Hrs m n Hmn; unfold fun_module_smul.
  transitivity (cmon_map (@fmap _ _ F ttt ttt r) n).
  - exact (proper_morphism (cmon_map (@fmap _ _ F ttt ttt r)) m n Hmn).
  - exact (@fmap_respects _ _ F ttt ttt r s Hrs n).
Qed.
Next Obligation.
  intros R F HF r m n; unfold fun_module_smul.
  exact (cmon_map_plus (@fmap _ _ F ttt ttt r) m n).
Qed.
Next Obligation.
  intros R F HF r s m; unfold fun_module_smul.
  exact (@fmap_padd _ _ (DeloopRing_AbEnriched R) Ab_AbEnriched F HF
           ttt ttt r s m).
Qed.
Next Obligation.
  intros R F HF r s m; unfold fun_module_smul.
  exact (@fmap_comp _ _ F ttt ttt ttt r s m).
Qed.
Next Obligation.
  intros R F HF m; unfold fun_module_smul.
  exact (@fmap_id _ _ F ttt m).
Qed.

(* * ** From module additive 函子 （已译） *)

(* Action fixed scalar, 态射 Ab: additivity map
 [rm_smul_distr_l] preservation zero [rm_smul_zero_r]. （已译） *)
Program Definition module_act {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R))) :
  (rm_ab M : Ab) ~{Ab}~> (rm_ab M : Ab) := {|
  cmon_map := {| morphism := fun m => rm_smul M r m |}
|}.
Next Obligation.
  intros R M r m n Hmn.
  exact (rm_smul_respects M r r (reflexivity r) m n Hmn).
Qed.
Next Obligation.
  intros R M r; simpl.
  exact (rm_smul_zero_r M r).
Qed.
Next Obligation.
  intros R M r m n; simpl.
  exact (rm_smul_distr_l M r m n).
Qed.

Program Definition functor_of_module {R : RingObject} (M : RModObject R) :
  DeloopRig (ring_rig R) ⟶ Ab := {|
  fobj := fun _ => (rm_ab M : Ab);
  fmap := fun _ _ r => module_act M r
|}.
Next Obligation.
  intros R M x y r s Hrs m; simpl.
  exact (rm_smul_respects M r s Hrs m m (reflexivity m)).
Qed.
Next Obligation.
  intros R M x m; simpl.
  exact (rm_smul_one M m).
Qed.
Next Obligation.
  intros R M x y z r s m; simpl.
  exact (rm_smul_assoc M r s m).
Qed.

(* 相关说明。 （已译） *)
Definition functor_of_module_additive {R : RingObject} (M : RModObject R) :
  IsAdditiveFun R (functor_of_module M).
Proof.
  constructor; intros x y r s m; simpl.
  exact (rm_smul_distr_r M r s m).
Defined.

(* The action module recovered 函子, definitionally,
 so underlying group. （已译） *)
Example module_round_carrier {R : RingObject} (M : RModObject R) :
  ((functor_of_module M) ttt : AbObject) = rm_ab M := eq_refl.

Example module_round_smul {R : RingObject} (M : RModObject R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  fun_module_smul (functor_of_module M) r m = rm_smul M r m := eq_refl.

(** ** The comparison functors *)

(* A transformation over single 对象 one Ab-态射, its
 自然性 at r IS [rm_map_smul] — collapse. （已译） *)
Program Definition AbFunAdd_to (R : RingObject) :
  AbFunAdd R ⟶ RMod R := {|
  fobj := fun FH => module_of_functor (`1 FH) (`2 FH);
  fmap := fun FH GH η => {| rm_hom := transform[`1 η] ttt |}
|}.
Next Obligation.
  intros R FH GH η r m; simpl.
  exact (@naturality_sym _ _ (`1 FH) (`1 GH) (`1 η) ttt ttt r m).
Qed.
Next Obligation.
  intros R FH GH η θ Hηθ; exact (Hηθ ttt).
Qed.
(* [Fun]'s 恒等 transformation has [fmap[F] id] component,
 so 这是 [fmap_id] rather than [reflexivity] — same step
 Instance/Rep.v's [Rep_to] takes. （已译） *)
Next Obligation.
  intros R FH m; simpl.
  exact (@fmap_id _ _ (`1 FH) ttt m).
Qed.
Next Obligation.
  intros R FH GH KH η θ m; simpl; reflexivity.
Qed.

(* Conversely module map 常值 family, 自然性 being
 [rm_map_smul] again — same equation read other way. （已译） *)
Program Definition AbFunAdd_from (R : RingObject) :
  RMod R ⟶ AbFunAdd R := {|
  fobj := fun M =>
    ((functor_of_module M; functor_of_module_additive M) : AbFunAdd R);
  fmap := fun M N f => ({| transform := fun _ => rm_hom f |}; I)
|}.
Next Obligation.
  intros R M N f [] [] r m; simpl.
  symmetry; exact (rm_map_smul f r m).
Qed.
Next Obligation.
  intros R M N f [] [] r m; simpl.
  exact (rm_map_smul f r m).
Qed.
Next Obligation.
  intros R M N f g Hfg []; exact Hfg.
Qed.
(* The 恒等 [AbFunAdd R] has [fmap] source 恒等 for
 component, i.e. action 1, so 这是 [rm_smul_one] — the
 镜像 [fmap_id] step [AbFunAdd_to]. （已译） *)
Next Obligation.
  intros R M [] m; simpl.
  rewrite (rm_smul_one M m); reflexivity.
Qed.
Next Obligation.
  intros R M N P f g [] m; simpl; reflexivity.
Qed.

(** ** The two round trips *)

(* Module side: recovered module has SAME underlying group and
 SAME action (both [eq_refl] above), so 恒等 group
 homomorphism module map both directions. （已译） *)
Program Definition AbFunAdd_module_round {R : RingObject}
  (M : RModObject R) :
  @Isomorphism (RMod R)
    (module_of_functor (functor_of_module M)
       (functor_of_module_additive M)) M := {|
  to   := {| rm_hom := @cmon_hom_id (rm_ab M) |};
  from := {| rm_hom := @cmon_hom_id (rm_ab M) |}
|}.
Next Obligation. intros R M r m; simpl; reflexivity. Qed.
Next Obligation. intros R M r m; simpl; reflexivity. Qed.
Next Obligation. intros R M m; simpl; reflexivity. Qed.
Next Obligation. intros R M m; simpl; reflexivity. Qed.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition AbFunAdd_functor_round {R : RingObject}
  (FH : AbFunAdd R) :
  @Isomorphism (AbFunAdd R)
    ((functor_of_module (module_of_functor (`1 FH) (`2 FH));
      functor_of_module_additive
        (module_of_functor (`1 FH) (`2 FH))) : AbFunAdd R) FH := {|
  to := ({| transform := fun x =>
    match x return
      (functor_of_module (module_of_functor (`1 FH) (`2 FH)) x
         ~{Ab}~> (`1 FH) x)
    with ttt => id end |}; I);
  from := ({| transform := fun x =>
    match x return
      ((`1 FH) x
         ~{Ab}~> functor_of_module (module_of_functor (`1 FH) (`2 FH)) x)
    with ttt => id end |}; I)
|}.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
Next Obligation. intros R FH [] [] r m; simpl; reflexivity. Qed.
(* Both 恒等 components [fmap] source 恒等, so both
 iso laws [fmap_id] given 函子. （已译） *)
Next Obligation.
  intros R FH [] m; simpl.
  rewrite (@fmap_id _ _ (`1 FH) ttt m); reflexivity.
Qed.
Next Obligation.
  intros R FH [] m; simpl.
  rewrite (@fmap_id _ _ (`1 FH) ttt m); reflexivity.
Qed.

(** ** Mac Lane's Exercise 1 *)

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition RMod_AbFun_equiv (R : RingObject) :
  AbFunAdd R ≅[Cat] RMod R := {|
  to   := AbFunAdd_to R;
  from := AbFunAdd_from R
|}.
Next Obligation.
  (* AbFunAdd_to ◯ AbFunAdd_from ≈ Id, on the module side *)
  intros R.
  exists (fun M => AbFunAdd_module_round M).
  intros M N f m; simpl; reflexivity.
Qed.
Next Obligation.
  (* AbFunAdd_from ◯ AbFunAdd_to ≈ Id, on the functor side *)
  intros R.
  exists (fun FH => AbFunAdd_functor_round FH).
  intros FH GH η [] m; simpl; reflexivity.
Qed.

(** ** Witnesses *)

(* Every ring module over itself (Instance/Mod.v's [Ring_RMod]);
 read across 等价 it 对象 additive-函子
 范畴, action computes over ℤ. （已译） *)
Definition Ring_AbFun (R : RingObject) : AbFunAdd R :=
  ((functor_of_module (Ring_RMod R);
    functor_of_module_additive (Ring_RMod R)) : AbFunAdd R).

Example int_abfun_act :
  cmon_map (@fmap _ _ (functor_of_module Int_RMod) ttt ttt 3%Z) 4%Z
    = 12%Z := eq_refl.

Example int_abfun_round :
  rm_smul (module_of_functor (functor_of_module Int_RMod)
             (functor_of_module_additive Int_RMod)) 3%Z 4%Z
    = 12%Z := eq_refl.

Example int_abfun_neg :
  cmon_map (@fmap _ _ (functor_of_module Int_RMod) ttt ttt
              (ring_neg Int_Ring 3%Z)) 4%Z = (-12)%Z := eq_refl.

(** ** The subcategory is proper *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition unit_act_functor (R : RingObject) :
  DeloopRig (ring_rig R) ⟶ Ab := {|
  fobj := fun _ => (ring_ab R : Ab);
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros R x y r s Hrs m; simpl; reflexivity. Qed.
Next Obligation. intros R x m; simpl; reflexivity. Qed.
Next Obligation. intros R x y z r s m; simpl; reflexivity. Qed.

Lemma unit_act_functor_not_additive :
  IsAdditiveFun Int_Ring (unit_act_functor Int_Ring) → False.
Proof.
  intro H.
  pose proof (@fmap_padd _ _ (DeloopRing_AbEnriched Int_Ring)
                Ab_AbEnriched (unit_act_functor Int_Ring) H
                ttt ttt 1%Z 1%Z 1%Z) as Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition square_act (n : Z) :
  (ring_ab Int_Ring : Ab) ~{Ab}~> (ring_ab Int_Ring : Ab) := {|
  cmon_map := {| morphism := fun m => Z.mul (Z.mul n n) m |}
|}.
(* [proper_morphism] needs no obligation: ℤ's setoid equivalence is
   Leibniz equality ([Z_eqT]), so elaboration discharges it. *)
Next Obligation.
  intros n; simpl.
  exact (Z.mul_0_r (Z.mul n n)).
Qed.
Next Obligation.
  intros n a b; simpl.
  exact (Z.mul_add_distr_l (Z.mul n n) a b).
Qed.

Program Definition square_functor :
  DeloopRig (ring_rig Int_Ring) ⟶ Ab := {|
  fobj := fun _ => (ring_ab Int_Ring : Ab);
  fmap := fun _ _ n => square_act n
|}.
(* 相关说明。 （已译） *)
Next Obligation.
  intros x a; simpl.
  change (Z.mul (Z.mul 1 1) a = a).
  ring.
Qed.
Next Obligation.
  intros x y z n m a; simpl.
  change (Z.mul (Z.mul (Z.mul n m) (Z.mul n m)) a
            = Z.mul (Z.mul n n) (Z.mul (Z.mul m m) a)).
  ring.
Qed.

Lemma square_functor_not_additive :
  IsAdditiveFun Int_Ring square_functor → False.
Proof.
  intro H.
  pose proof (@fmap_padd _ _ (DeloopRing_AbEnriched Int_Ring)
                Ab_AbEnriched square_functor H ttt ttt 1%Z 1%Z 1%Z) as Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma AbFunAdd_proper :
  ((IsAdditiveFun Int_Ring (unit_act_functor Int_Ring) → False)
     * (IsAdditiveFun Int_Ring square_functor → False))%type.
Proof.
  split.
  - exact unit_act_functor_not_additive.
  - exact square_functor_not_additive.
Qed.
