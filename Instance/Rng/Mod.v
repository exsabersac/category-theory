(*
 nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
 nLab: https://ncatlab.org/nlab/show/Grothendieck+construction
 Wikipedia: https://en.wikipedia.org/wiki/Restriction_of_scalars

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.
Require Import Category.Construction.Grothendieck.Fiber.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

(* * Along ρ : R → S, S-module M becomes R-module r acting as
 ρ r does. The underlying 阿贝尔 group is UNCHANGED — [rm_ab] is
 [rm_ab M], same term — which is what makes every comparison
 further down 恒等-carrier one.（已译） *)
Definition RestrictObj {R S : RingObject} (rho : R ~{Rng}~> S)
  (M : RModObject S) : RModObject R.
Proof.
  unshelve notypeclasses refine {|
    rm_ab   := rm_ab M;
    rm_smul := fun r m => rm_smul M (rig_map rho r) m
  |}.
  - (* rm_smul_respects *)
    intros r r' Hr m m' Hm.
    now rewrite Hr, Hm.
  - (* rm_smul_distr_l: no property of ρ is spent *)
    intros r m n.
    apply rm_smul_distr_l.
  - (* rm_smul_distr_r: ρ is additive *)
    intros r r' m.
    rewrite (rig_map_add rho r r').
    apply rm_smul_distr_r.
  - (* rm_smul_assoc: ρ is multiplicative *)
    intros r r' m.
    rewrite (rig_map_mul rho r r').
    apply rm_smul_assoc.
  - (* rm_smul_one: ρ preserves the unit *)
    intros m.
    rewrite (rig_map_one rho).
    apply rm_smul_one.
Defined.

(** 本节：A map S-modules IS map restricted R-modules: same
 homomorphism abelian groups, linearity read at scalar
 ρ r. （已译） *)
Program Definition RestrictHom {R S : RingObject} (rho : R ~{Rng}~> S)
  {M N : RModObject S} (f : M ~{RMod S}~> N) :
  RestrictObj rho M ~{RMod R}~> RestrictObj rho N := {|
  rm_hom := rm_hom f
|}.
Next Obligation.
  intros R S rho M N f r m.
  exact (rm_map_smul f (rig_map rho r) m).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Restrict {R S : RingObject} (rho : R ~{Rng}~> S) :
  RMod S ⟶ RMod R := {|
  fobj := RestrictObj rho;
  fmap := fun M N f => RestrictHom rho f
|}.
Next Obligation. intros R S rho M N f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R S rho M a; reflexivity. Qed.
Next Obligation. intros R S rho M N P f g a; reflexivity. Qed.

(** ** The right-module reading *)

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition RigHom_op {R S : RingObject} (rho : R ~{Rng}~> S) :
  Ring_op R ~{Rng}~> Ring_op S :=
  @Build_RigHom (Rig_op (ring_rig R)) (Rig_op (ring_rig S))
    (rig_map rho) (rig_map_zero rho) (rig_map_add rho)
    (rig_map_one rho) (fun a b => rig_map_mul rho b a).

(* * Restriction scalars RIGHT modules — Mac Lane's own statement
 构造 8. It is [Restrict] at 反 rings, by
 定义; no obligation is discharged second time.（已译） *)
Definition RestrictR {R S : RingObject} (rho : R ~{Rng}~> S) :
  ModR S ⟶ ModR R := Restrict (RigHom_op rho).

(* * ** The comparison isomorphisms, all 恒等-carrier （已译） *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rmod_iso_of_ab {R : RingObject} {M N : RModObject R}
  (h : AbHom (rm_ab M) (rm_ab N)) (k : AbHom (rm_ab N) (rm_ab M))
  (Hh : ∀ r m, cmon_map h (rm_smul M r m) ≈ rm_smul N r (cmon_map h m))
  (Hk : ∀ r n, cmon_map k (rm_smul N r n) ≈ rm_smul M r (cmon_map k n))
  (Hhk : ∀ n, cmon_map h (cmon_map k n) ≈ n)
  (Hkh : ∀ m, cmon_map k (cmon_map h m) ≈ m) :
  M ≅[RMod R] N := {|
  to   := {| rm_hom := h; rm_map_smul := Hh |};
  from := {| rm_hom := k; rm_map_smul := Hk |}
|}.
Next Obligation.
  intros R M N h k Hh Hk Hhk Hkh n; exact (Hhk n).
Qed.
Next Obligation.
  intros R M N h k Hh Hk Hhk Hkh m; exact (Hkh m).
Qed.

(** Reindexing, packaged op-direction fixed once: 态射
 x ~> y [Rng^op] IS ring map y → x, restriction along it
 carries x-modules y-modules. （已译） *)
Definition mod_map {x y : RingObject} (f : x ~{Rng^op}~> y) :
  RMod x ⟶ RMod y := Restrict f.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mod_resp_iso {x y : RingObject} {f g : x ~{Rng^op}~> y}
  (e : f ≈ g) (a : RMod x) : mod_map f a ≅[RMod y] mod_map g a.
Proof.
  (* The two modules pinned explicitly: both comparison maps being
 恒等 ONE group, elaborator would otherwise identify
 source target modules each other. （已译） *)
  unshelve notypeclasses refine
    (@rmod_iso_of_ab y (mod_map f a) (mod_map g a)
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m.
    exact (rm_smul_respects a _ _ (e r) m m (reflexivity m)).
  - intros r n.
    exact (rm_smul_respects a _ _ (symmetry (e r)) n n (reflexivity n)).
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mod_id_iso {x : RingObject} (a : RMod x) :
  mod_map (@id (Rng^op) x) a ≅[RMod x] a.
Proof.
  unshelve notypeclasses refine
    (@rmod_iso_of_ab x (mod_map (@id (Rng^op) x) a) a
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m; reflexivity.
  - intros r n; reflexivity.
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mod_comp_iso {x y z : RingObject} (f : y ~{Rng^op}~> z)
  (g : x ~{Rng^op}~> y) (a : RMod x) :
  mod_map f (mod_map g a) ≅[RMod z] mod_map (f ∘ g) a.
Proof.
  unshelve notypeclasses refine
    (@rmod_iso_of_ab z (mod_map f (mod_map g a)) (mod_map (f ∘ g) a)
       cmon_hom_id cmon_hom_id _ _ _ _).
  - intros r m; reflexivity.
  - intros r n; reflexivity.
  - intros n; reflexivity.
  - intros m; reflexivity.
Defined.

(* * ** The indexed 范畴 modules （已译） *)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ModIndexed : IndexedCat (Rng^op).
Proof.
  unshelve notypeclasses refine
    (@Build_IndexedCat (Rng^op)
       (fun R : RingObject => RMod R)
       (fun x y f => mod_map f)
       (fun x y f g e a => mod_resp_iso e a)
       _ _ _
       (fun x a => mod_id_iso a)
       _
       (fun x y z f g a => mod_comp_iso f g a)
       _ _ _ _ _ _).
  - (* idx_resp_natural *)
    intros x y f g e a b k m; reflexivity.
  - (* idx_resp_id *)
    intros x y f e a m; reflexivity.
  - (* idx_resp_trans *)
    intros x y f g h e1 e2 a m; reflexivity.
  - (* idx_id_natural *)
    intros x a b k m; reflexivity.
  - (* idx_comp_natural *)
    intros x y z f g a b k m; reflexivity.
  - (* idx_comp_resp_l *)
    intros x y z f f' g e e' a m; reflexivity.
  - (* idx_comp_resp_r *)
    intros x y z f g g' e e' a m; reflexivity.
  - (* idx_unit_left *)
    intros x y f a m; reflexivity.
  - (* idx_unit_right *)
    intros x y f a m; reflexivity.
  - (* idx_cocycle *)
    intros w x y z f g h a m; reflexivity.
Defined.

(* * ** The 范畴 all modules: Mac Lane's construction 9 （已译） *)

(** Objects pairs (R; M) M R-module; 态射 described
 below. The name issue's. （已译） *)
Definition ModTotal : Category := Grothendieck ModIndexed.

(* * The projection rings, contravariantly. By
 Construction/Grothendieck/Fibration.v it is opfibration whose
 典范 opcleaving satisfies split laws — cited at that
 strength, not re-proved here.（已译） *)
Definition ModProj : ModTotal ⟶ Rng^op := Grothendieck_Proj ModIndexed.

(* * *** What 对象 态射 are, nose （已译） *)

Example ModTotal_obj_unfold :
  obj[ModTotal] = (∃ R : RingObject, RModObject R) := eq_refl.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ModTotal_hom_unfold (R S : RingObject)
  (M : RModObject R) (N : RModObject S) :
  ((R; M) ~{ModTotal}~> (S; N))
    = (∃ rho : S ~{Rng}~> R, RestrictObj rho M ~{RMod S}~> N) := eq_refl.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ModTotal_cosemilinear {R S : RingObject} {M : RModObject R}
  {N : RModObject S} (rho : S ~{Rng}~> R)
  (g : RestrictObj rho M ~{RMod S}~> N)
  (s : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom g) (rm_smul M (rig_map rho s) m)
    ≈ rm_smul N s (cmon_map (rm_hom g) m).
Proof. exact (rm_map_smul g s m). Qed.

(** 本节：And back: equation all fibre leg is. （已译） *)
Program Definition mod_cosemilinear_hom {R S : RingObject}
  {M : RModObject R} {N : RModObject S} (rho : S ~{Rng}~> R)
  (h : AbHom (rm_ab M) (rm_ab N))
  (Hs : ∀ s m, cmon_map h (rm_smul M (rig_map rho s) m)
                 ≈ rm_smul N s (cmon_map h m)) :
  RestrictObj rho M ~{RMod S}~> N := {|
  rm_hom := h
|}.
Next Obligation.
  intros R S M N rho h Hs s m.
  exact (Hs s m).
Qed.

(* 相关说明。 （已译） *)

(** 本节：The ring components compose [Rng] REVERSE order, the
 nose. （已译） *)
Example ModTotal_compose_ring {X Y Z : ModTotal} (b : Y ~> Z) (a : X ~> Y) :
  `1 (b ∘ a) = `1 a ∘[Rng] `1 b := eq_refl.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ModTotal_compose_carrier {X Y Z : ModTotal} (b : Y ~> Z) (a : X ~> Y)
  (m : carrier (cmon_setoid (rm_ab (`2 X)))) :
  cmon_map (rm_hom (`2 (b ∘ a))) m
    ≈ cmon_map (rm_hom (`2 b)) (cmon_map (rm_hom (`2 a)) m).
Proof. reflexivity. Qed.

(** The projection really does take first components. *)
Example ModProj_fobj (X : ModTotal) : ModProj X = `1 X := eq_refl.

Example ModProj_fmap {X Y : ModTotal} (a : X ~> Y) :
  fmap[ModProj] a = `1 a := eq_refl.

(** *** The fibres *)

Example ModTotal_fibre_target (R : RingObject) :
  idx_fib ModIndexed R = RMod R := eq_refl.

(* * The fibre [ModTotal] over R is equivalent [RMod R], by
 Construction/Grothendieck/Fiber.v's 等价 — which is the
 恒等 对象, both its cells carrying 恒等
 components.（已译） *)
Definition ModTotal_fibre (R : RingObject) :
  EquivalenceOfCategories (Fiber_Grothendieck_To ModIndexed R) :=
  fiber_grothendieck_equiv ModIndexed R.

(* 相关说明。 （已译） *)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition OpModIndexed : IndexedCat (Rng^op).
Proof.
  unshelve notypeclasses refine
    (@Build_IndexedCat (Rng^op)
       (fun R : RingObject => (RMod R)^op)
       (fun x y f => Opposite_Functor (mod_map f))
       (fun x y f g e a => Isomorphism_Opposite (mod_resp_iso e a))
       _ _ _
       (fun x a => Isomorphism_Opposite (mod_id_iso a))
       _
       (fun x y z f g a => Isomorphism_Opposite (mod_comp_iso f g a))
       _ _ _ _ _ _).
  - (* idx_resp_natural *)
    intros x y f g e a b k m; reflexivity.
  - (* idx_resp_id *)
    intros x y f e a m; reflexivity.
  - (* idx_resp_trans *)
    intros x y f g h e1 e2 a m; reflexivity.
  - (* idx_id_natural *)
    intros x a b k m; reflexivity.
  - (* idx_comp_natural *)
    intros x y z f g a b k m; reflexivity.
  - (* idx_comp_resp_l *)
    intros x y z f f' g e e' a m; reflexivity.
  - (* idx_comp_resp_r *)
    intros x y z f g g' e e' a m; reflexivity.
  - (* idx_unit_left *)
    intros x y f a m; reflexivity.
  - (* idx_unit_right *)
    intros x y f a m; reflexivity.
  - (* idx_cocycle *)
    intros w x y z f g h a m; reflexivity.
Defined.

(** Mac Lane's category of all modules over all rings, fibred over
    [Rng]. *)
Definition ModFibred : Category := (Grothendieck OpModIndexed)^op.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ModFibredProj : ModFibred ⟶ Rng :=
  Opposite_Functor (Grothendieck_Proj OpModIndexed).

Example ModFibred_double_op_collapses : (Rng^op)^op = Rng := eq_refl.

(* 相关说明。 （已译） *)

Example ModFibred_obj_unfold :
  obj[ModFibred] = (∃ R : RingObject, RModObject R) := eq_refl.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ModFibred_hom_unfold (R S : RingObject)
  (M : RModObject R) (N : RModObject S) :
  ((R; M) ~{ModFibred}~> (S; N))
    = (∃ rho : R ~{Rng}~> S, M ~{RMod R}~> RestrictObj rho N) := eq_refl.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ModFibred_semilinear {R S : RingObject} {M : RModObject R}
  {N : RModObject S} (rho : R ~{Rng}~> S)
  (f : M ~{RMod R}~> RestrictObj rho N)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  cmon_map (rm_hom f) (rm_smul M r m)
    ≈ rm_smul N (rig_map rho r) (cmon_map (rm_hom f) m).
Proof. exact (rm_map_smul f r m). Qed.

(** 本节：And back: equation all fibre leg is. （已译） *)
Program Definition mod_semilinear_hom {R S : RingObject}
  {M : RModObject R} {N : RModObject S} (rho : R ~{Rng}~> S)
  (h : AbHom (rm_ab M) (rm_ab N))
  (Hs : ∀ r m, cmon_map h (rm_smul M r m)
                 ≈ rm_smul N (rig_map rho r) (cmon_map h m)) :
  M ~{RMod R}~> RestrictObj rho N := {|
  rm_hom := h
|}.
Next Obligation.
  intros R S M N rho h Hs r m.
  exact (Hs r m).
Qed.

(* 相关说明。 （已译） *)

(** 本节：The ring legs compose [Rng] Mac Lane's order, ρ' ∘ ρ, the
 nose. （已译） *)
Example ModFibred_compose_ring {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y) :
  `1 (b ∘ a) = `1 b ∘[Rng] `1 a := eq_refl.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ModFibred_compose_fibre {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y) :
  `2 (b ∘ a)
    ≈ to (mod_comp_iso (`1 a) (`1 b) (`2 Z))
        ∘ fmap[mod_map (`1 a)] (`2 b) ∘ `2 a.
Proof. intro m; reflexivity. Qed.

(** 本节：On carriers comparison invisible fibre legs simply
 compose. （已译） *)
Lemma ModFibred_compose_carrier {X Y Z : ModFibred}
  (b : Y ~> Z) (a : X ~> Y)
  (m : carrier (cmon_setoid (rm_ab (`2 X)))) :
  cmon_map (rm_hom (`2 (b ∘ a))) m
    ≈ cmon_map (rm_hom (`2 b)) (cmon_map (rm_hom (`2 a)) m).
Proof. reflexivity. Qed.

Example ModFibredProj_fobj (X : ModFibred) :
  ModFibredProj X = `1 X := eq_refl.

Example ModFibredProj_fmap {X Y : ModFibred} (a : X ~> Y) :
  fmap[ModFibredProj] a = `1 a := eq_refl.

(** *** The fibres *)

(*
   本节说明（余）极限、等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ModFibred_fibre_target (R : RingObject) :
  (idx_fib OpModIndexed R)^op = RMod R := eq_refl.

Definition ModFibred_fibre_op (R : RingObject) :
  EquivalenceOfCategories (Fiber_Grothendieck_To OpModIndexed R) :=
  fiber_grothendieck_equiv OpModIndexed R.

Definition ModFibred_fibre (R : RingObject) :
  EquivalenceOfCategories
    (Opposite_Functor (Fiber_Grothendieck_To OpModIndexed R)) :=
  EquivalenceOfCategories_op (fiber_grothendieck_equiv OpModIndexed R).

(* 相关说明。 （已译） *)

(** ℤ initial [Rng], so there exactly one ring map ℤ → R, and
 restriction along it underlying-abelian-group 函子 read as
 change base. （已译） *)
Example rng_from_Z_is_initial_arrow (R : RingObject) :
  rng_from_Z R = @zero Rng Rng_Initial_Z R := eq_refl.

Definition ZRestrict (R : RingObject) : RMod R ⟶ RMod Int_Ring :=
  Restrict (rng_from_Z R).

(** The arrow [ModTotal] produces, out EVERY 对象: ring
 leg unique map ℤ → R module leg 恒等,
 because restriction target nose. （已译） *)
Definition mod_to_Z (R : RingObject) (M : RModObject R) :
  (R; M) ~{ModTotal}~> (Int_Ring; ZRestrict R M) :=
  (rng_from_Z R; @id (RMod Int_Ring) (ZRestrict R M)).

Example mod_to_Z_ring_leg (R : RingObject) (M : RModObject R) :
  fmap[ModProj] (mod_to_Z R M) = rng_from_Z R := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition mod_from_Z (R : RingObject) (M : RModObject R) :
  (Int_Ring; ZRestrict R M) ~{ModFibred}~> (R; M) :=
  (rng_from_Z R; @id (RMod Int_Ring) (ZRestrict R M)).

Example mod_from_Z_ring_leg (R : RingObject) (M : RModObject R) :
  fmap[ModFibredProj] (mod_from_Z R M) = rng_from_Z R := eq_refl.

(** At ℤ itself the action computes: restriction along ℤ → ℤ leaves
    multiplication of integers where it was. *)
Example int_ZRestrict_smul :
  rm_smul (ZRestrict Int_Ring Int_RMod) 3%Z 4%Z = 12%Z := eq_refl.

Example int_ZRestrict_group :
  rm_ab (ZRestrict Int_Ring Int_RMod) = rm_ab Int_RMod := eq_refl.

(*
   本节说明 Mod 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example RestrictR_action {R S : RingObject} (rho : R ~{Rng}~> S)
  (M : RModObject (Ring_op S))
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (cmon_setoid (rm_ab M))) :
  rm_smul (RestrictR rho M) r m = rm_smul M (rig_map rho r) m := eq_refl.

Example int_RestrictR_smul :
  rm_smul (RestrictR (rng_from_Z Int_Ring) (Ring_RMod (Ring_op Int_Ring)))
          3%Z 4%Z = 12%Z := eq_refl.
