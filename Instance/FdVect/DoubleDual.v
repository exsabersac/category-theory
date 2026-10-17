(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* [Coq.QArith.QArith] is imported FIRST, mirroring Instance/FdVect.v's
   import order and for its reason: it exports
   [Corelib.Relations.Relation_Definitions.equiv], which would otherwise
   shadow [Category.Lib.Setoid.equiv] and break every [Proper] signature
   below.（标题）（已译） *)
Require Import Coq.QArith.QArith.
Require Import Coq.Vectors.Fin.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rmod_hom_neg {R : RingObject} {M N : RModObject R}
        (f : RModHom M N) : RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros R M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

Section DualSpace.

Context (F : FieldObject).

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dual_setoid (V : RModObject (field_ring F)) : SetoidObject := {|
  carrier   := RModHom V (Ring_RMod (field_ring F));
  is_setoid := @RModHom_Setoid (field_ring F) V (Ring_RMod (field_ring F))
|}.

(** Addition zero functional Instance/Mod.v's, so every
 幺半群 law corresponding law F applied at each vector. （已译） *)
Program Definition dual_cmon (V : RModObject (field_ring F)) :
  CMonObject := {|
  cmon_setoid := dual_setoid V;
  cmon_zero   := @rmod_hom_zero (field_ring F) V (Ring_RMod (field_ring F));
  cmon_plus   := @rmod_hom_add (field_ring F) V (Ring_RMod (field_ring F))
|}.
Next Obligation.
  intros V f f' Hf g g' Hg v; simpl.
  now rewrite (Hf v), (Hg v).
Qed.
Next Obligation. intros V f g h v; simpl; apply rig_add_assoc. Qed.
Next Obligation. intros V f g v; simpl; apply rig_add_comm. Qed.
Next Obligation. intros V f v; simpl; apply rig_add_zero_l. Qed.

Program Definition dual_ab (V : RModObject (field_ring F)) : AbObject := {|
  ab_cmon := dual_cmon V;
  ab_neg  := @rmod_hom_neg (field_ring F) V (Ring_RMod (field_ring F))
|}.
Next Obligation.
  intros V f g Hfg v; simpl.
  now rewrite (Hfg v).
Qed.
Next Obligation. intros V f v; simpl; apply (ring_neg_l F). Qed.

(*
   本节说明分配律、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma dual_smul_zero (V : RModObject (field_ring F))
  (r : carrier (rig_setoid F)) (f : RModHom V (Ring_RMod (field_ring F))) :
  rig_mul F r (cmon_map (rm_hom f) (cmon_zero V)) ≈ rig_zero F.
Proof.
  rewrite (cmon_map_zero (rm_hom f)).
  apply rig_mul_zero_r.
Qed.

Lemma dual_smul_plus (V : RModObject (field_ring F))
  (r : carrier (rig_setoid F)) (f : RModHom V (Ring_RMod (field_ring F))) :
  ∀ v w, rig_mul F r (cmon_map (rm_hom f) (cmon_plus V v w))
           ≈ rig_add F (rig_mul F r (cmon_map (rm_hom f) v))
                       (rig_mul F r (cmon_map (rm_hom f) w)).
Proof.
  intros v w.
  rewrite (cmon_map_plus (rm_hom f) v w).
  apply rig_distr_l.
Qed.

Lemma dual_smul_linear (V : RModObject (field_ring F))
  (r : carrier (rig_setoid F)) (f : RModHom V (Ring_RMod (field_ring F))) :
  ∀ s v, rig_mul F r (cmon_map (rm_hom f) (rm_smul V s v))
           ≈ rig_mul F s (rig_mul F r (cmon_map (rm_hom f) v)).
Proof.
  intros s v.
  rewrite (rm_map_smul f s v).
  rewrite <- (rig_mul_assoc F r s (cmon_map (rm_hom f) v)).
  rewrite (field_comm F r s).
  apply (rig_mul_assoc F s r (cmon_map (rm_hom f) v)).
Qed.

Program Definition dual_smul (V : RModObject (field_ring F))
        (r : carrier (rig_setoid F))
        (f : RModHom V (Ring_RMod (field_ring F))) :
  RModHom V (Ring_RMod (field_ring F)) := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun v =>
                          rig_mul F r (cmon_map (rm_hom f) v) |};
    cmon_map_zero := dual_smul_zero V r f;
    cmon_map_plus := dual_smul_plus V r f
  |};
  rm_map_smul := dual_smul_linear V r f
|}.
Next Obligation.
  intros V r f v w Hvw; simpl.
  now rewrite Hvw.
Qed.

(** Mac Lane §II.2 construction 3's 对象 assignment: dual an
 ARBITRARY F-module, no finiteness 假设. （已译） *)
Program Definition DualMod (V : RModObject (field_ring F)) :
  RModObject (field_ring F) := {|
  rm_ab   := dual_ab V;
  rm_smul := dual_smul V
|}.
Next Obligation.
  intros V r s Hrs f g Hfg v; simpl.
  now rewrite Hrs, (Hfg v).
Qed.
Next Obligation. intros V r f g v; simpl; apply rig_distr_l. Qed.
Next Obligation. intros V r s f v; simpl; apply rig_distr_r. Qed.
Next Obligation. intros V r s f v; simpl; apply rig_mul_assoc. Qed.
Next Obligation. intros V f v; simpl; apply rig_mul_one_l. Qed.

(* * ** The dual 函子

 On arrows dual acts PRECOMPOSITION, why it is
 contravariant: f : V → W carries functional W one V.
 Every law below [reflexivity] at each vector, 复合 of
 functions being associative nose. （已译） *)

Definition dual_precompose {V W : RModObject (field_ring F)}
  (f : RModHom V W) : RModHom (DualMod W) (DualMod V).
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (DualMod W) (DualMod V)
       (@Build_CMonHom (dual_cmon W) (dual_cmon V)
          (@Build_SetoidMorphism _ _ _ _
             (fun g => @rmod_hom_compose (field_ring F) V W
                         (Ring_RMod (field_ring F)) g f) _) _ _) _).
  - intros g g' Hg v; exact (Hg _).
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

(** Mac Lane §II.2 construction 3 / Riehl §1.4 Example 1.4.4(i): the
    dual as a contravariant functor on ALL F-vector spaces. *)
Program Definition Dual : (Vct_F F)^op ⟶ Vct_F F := {|
  fobj := DualMod;
  fmap := fun V W (f : W ~{Vct_F F}~> V) => dual_precompose f
|}.
Next Obligation.
  intros V W f g Hfg h v; simpl.
  apply (proper_morphism (cmon_map (rm_hom h))).
  exact (Hfg v).
Qed.
Next Obligation. intros V f v; simpl; reflexivity. Qed.
Next Obligation. intros V W X f g h v; simpl; reflexivity. Qed.

(** The double dual, shape Structure/Monoidal/StarAutonomous.v
 gives [double_dual]: contravariant 函子 composed own
 opposite, covariant. （已译） *)
Definition DoubleDual : Vct_F F ⟶ Vct_F F := Dual ◯ Dual^op.

(* 相关说明。 （已译） *)

Program Definition dual_ev (V : RModObject (field_ring F))
        (v : carrier (cmon_setoid V)) :
  RModHom (DualMod V) (Ring_RMod (field_ring F)) := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun f => cmon_map (rm_hom f) v |};
    cmon_map_zero := reflexivity _;
    cmon_map_plus := fun f g => reflexivity _
  |};
  rm_map_smul := fun r f => reflexivity _
|}.
Next Obligation. intros V v f g Hfg; simpl; exact (Hfg v). Qed.

Program Definition eta (V : RModObject (field_ring F)) :
  V ~{Vct_F F}~> DoubleDual V := {|
  rm_hom := {|
    cmon_map := {| morphism := dual_ev V |}
  |}
|}.
Next Obligation.
  intros V v w Hvw f; simpl.
  apply (proper_morphism (cmon_map (rm_hom f))).
  exact Hvw.
Qed.
Next Obligation. intros V f; simpl; apply (cmon_map_zero (rm_hom f)). Qed.
Next Obligation.
  intros V v w f; simpl.
  apply (cmon_map_plus (rm_hom f) v w).
Qed.
Next Obligation. intros V r v f; simpl; apply (rm_map_smul f r v). Qed.

(* * Mac Lane §I.4 注记 2 / Awodey §7.5 Example 7.12 / Riehl §1.4
 Example 1.4.4(ii): evaluation is NATURAL, at every dimension. Both
 orientations square hold [reflexivity] at each vector and
 each functional — both composites send (v, φ) φ(f v) — no
 hypothesis V, W f is used.（已译） *)
Program Definition double_dual_natural : Id[Vct_F F] ⟹ DoubleDual := {|
  transform := eta
|}.
Next Obligation. intros V W f v g; simpl; reflexivity. Qed.
Next Obligation. intros V W f v g; simpl; reflexivity. Qed.

End DualSpace.

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FiniteDimensional.

Context (F : FieldObject).

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fdv_basis (V : FdVectObject F) (j : Fin.t (fdv_dim V)) :
  carrier (cmon_setoid (fdv_mod V)) :=
  fdv_expand V (std_basis F (fdv_dim V) j).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma msum_ring {p : nat} (f : Fin.t p → carrier (rig_setoid F)) :
  msum (ab_cmon (rm_ab (Ring_RMod (field_ring F)))) f
    ≈ fin_sum (field_ring F) f.
Proof.
  revert f.
  induction p as [| k IHk]; intros f; simpl.
  - reflexivity.
  - apply rig_add_respects; [ reflexivity |].
    apply (IHk (fun i => f (Fin.FS i))).
Qed.

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fdv_expand_msum (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  fdv_expand V c
    ≈ msum (fdv_mod V)
        (fun j => rm_smul (fdv_mod V) (c j) (fdv_basis V j)).
Proof.
  transitivity (fdv_expand V
    (msum (std_cmon F (fdv_dim V))
       (fun j i => rig_mul F (c j) (std_basis F (fdv_dim V) j i)))).
  { apply fdv_expand_respects; intro i.
    symmetry.
    transitivity (fin_sum (field_ring F)
      (fun j => rig_mul F (c j) (std_basis F (fdv_dim V) j i))).
    - apply (msum_std F
               (fun j i => rig_mul F (c j) (std_basis F (fdv_dim V) j i)) i).
    - transitivity (fin_sum (field_ring F)
        (fun j => rig_mul F (c j) (delta (field_ring F) j i))).
      + apply fin_sum_respects; intro j.
        apply rig_mul_respects; [ reflexivity |].
        apply delta_sym.
      + apply (fin_sum_delta_r (field_ring F) i c). }
  transitivity (msum (fdv_mod V)
    (fun j => fdv_expand V
                (fun i => rig_mul F (c j) (std_basis F (fdv_dim V) j i)))).
  { apply (msum_hom (rm_hom (std_expand_hom F V))
             (fun j i => rig_mul F (c j) (std_basis F (fdv_dim V) j i))). }
  apply msum_respects; intro j.
  apply (fdv_expand_smul V (c j) (std_basis F (fdv_dim V) j)).
Qed.

(** A functional applied to an expanded tuple: linearity spent once,
    against the expansion above. *)
Lemma dual_apply_expand (V : FdVectObject F)
  (f : RModHom (fdv_mod V) (Ring_RMod (field_ring F)))
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  cmon_map (rm_hom f) (fdv_expand V c)
    ≈ fin_sum (field_ring F)
        (fun j => rig_mul F (c j)
                    (cmon_map (rm_hom f) (fdv_basis V j))).
Proof.
  transitivity (cmon_map (rm_hom f)
    (msum (fdv_mod V)
       (fun j => rm_smul (fdv_mod V) (c j) (fdv_basis V j)))).
  { apply (proper_morphism (cmon_map (rm_hom f))).
    apply fdv_expand_msum. }
  transitivity (msum (ab_cmon (rm_ab (Ring_RMod (field_ring F))))
    (fun j => cmon_map (rm_hom f)
                (rm_smul (fdv_mod V) (c j) (fdv_basis V j)))).
  { apply (msum_hom (rm_hom f)
             (fun j => rm_smul (fdv_mod V) (c j) (fdv_basis V j))). }
  transitivity (msum (ab_cmon (rm_ab (Ring_RMod (field_ring F))))
    (fun j => rig_mul F (c j) (cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply msum_respects; intro j.
    apply (rm_map_smul f (c j) (fdv_basis V j)). }
  apply msum_ring.
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma dual_coeffs_zero (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  fin_sum (field_ring F)
    (fun j => rig_mul F (c j) (fdv_coord V (cmon_zero (fdv_mod V)) j))
    ≈ rig_zero F.
Proof.
  transitivity (fin_sum (field_ring F)
    (fun _ : Fin.t (fdv_dim V) => rig_zero F)).
  - apply fin_sum_respects; intro j.
    rewrite (fdv_coord_zero V j).
    apply rig_mul_zero_r.
  - apply fin_sum_zero.
Qed.

Lemma dual_coeffs_plus (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  ∀ v w, fin_sum (field_ring F)
           (fun j => rig_mul F (c j)
                       (fdv_coord V (cmon_plus (fdv_mod V) v w) j))
         ≈ rig_add F
             (fin_sum (field_ring F)
                (fun j => rig_mul F (c j) (fdv_coord V v j)))
             (fin_sum (field_ring F)
                (fun j => rig_mul F (c j) (fdv_coord V w j))).
Proof.
  intros v w.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_add F (rig_mul F (c j) (fdv_coord V v j))
                        (rig_mul F (c j) (fdv_coord V w j)))).
  - apply fin_sum_respects; intro j.
    rewrite (fdv_coord_plus V v w j).
    apply rig_distr_l.
  - apply fin_sum_add.
Qed.

Lemma dual_coeffs_smul (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  ∀ r v, fin_sum (field_ring F)
           (fun j => rig_mul F (c j)
                       (fdv_coord V (rm_smul (fdv_mod V) r v) j))
         ≈ rig_mul F r
             (fin_sum (field_ring F)
                (fun j => rig_mul F (c j) (fdv_coord V v j))).
Proof.
  intros r v.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F r (rig_mul F (c j) (fdv_coord V v j)))).
  - apply fin_sum_respects; intro j.
    rewrite (fdv_coord_smul V r v j).
    rewrite <- (rig_mul_assoc F (c j) r (fdv_coord V v j)).
    rewrite (field_comm F (c j) r).
    apply (rig_mul_assoc F r (c j) (fdv_coord V v j)).
  - symmetry; apply fin_sum_mul_l.
Qed.

Program Definition dual_of_coeffs (V : FdVectObject F)
        (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  RModHom (fdv_mod V) (Ring_RMod (field_ring F)) := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun v => fin_sum (field_ring F)
                          (fun j => rig_mul F (c j) (fdv_coord V v j)) |};
    cmon_map_zero := dual_coeffs_zero V c;
    cmon_map_plus := dual_coeffs_plus V c
  |};
  rm_map_smul := dual_coeffs_smul V c
|}.
Next Obligation.
  intros V c v w Hvw; simpl.
  apply fin_sum_respects; intro j.
  apply rig_mul_respects; [ reflexivity |].
  exact (fdv_coord_respects V v w Hvw j).
Qed.

(** 本节：The first round trip: coefficients expanded tuple the
 tuple back, because j-th basis vector has coordinates delta. （已译） *)
Lemma dual_coord_expand (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F))
  (i : Fin.t (fdv_dim V)) :
  cmon_map (rm_hom (dual_of_coeffs V c)) (fdv_basis V i) ≈ c i.
Proof.
  simpl.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F (c j) (delta (field_ring F) j i))).
  - apply fin_sum_respects; intro j.
    apply rig_mul_respects; [ reflexivity |].
    apply (fdv_coord_expand V (std_basis F (fdv_dim V) i) j).
  - apply (fin_sum_delta_r (field_ring F) i c).
Qed.

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma dual_expand_coord (V : FdVectObject F)
  (f : RModHom (fdv_mod V) (Ring_RMod (field_ring F)))
  (v : carrier (cmon_setoid (fdv_mod V))) :
  cmon_map (rm_hom (dual_of_coeffs V
    (fun j => cmon_map (rm_hom f) (fdv_basis V j)))) v
    ≈ cmon_map (rm_hom f) v.
Proof.
  simpl.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F (fdv_coord V v j)
                (cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply fin_sum_respects; intro j.
    apply field_comm. }
  symmetry.
  transitivity (cmon_map (rm_hom f) (fdv_expand V (fdv_coord V v))).
  { apply (proper_morphism (cmon_map (rm_hom f))).
    symmetry; apply fdv_expand_coord. }
  apply (dual_apply_expand V f (fdv_coord V v)).
Qed.

(** 本节：V* coordinates: same dimension, j-th coordinate a
 functional being value at j-th basis vector. （已译） *)
Program Definition DualFdObj (V : FdVectObject F) : FdVectObject F := {|
  fdv_mod    := DualMod F (fdv_mod V);
  fdv_dim    := fdv_dim V;
  fdv_coord  := fun f j => cmon_map (rm_hom f) (fdv_basis V j);
  fdv_expand := dual_of_coeffs V
|}.
Next Obligation. intros V f g Hfg i; exact (Hfg _). Qed.
Next Obligation.
  intros V c d Hcd v; simpl.
  apply fin_sum_respects; intro j.
  apply rig_mul_respects; [ apply Hcd | reflexivity ].
Qed.
Next Obligation. intros V c i; apply dual_coord_expand. Qed.
Next Obligation. intros V f v; apply dual_expand_coord. Qed.
Next Obligation. intros V f g i; simpl; reflexivity. Qed.
Next Obligation. intros V r f i; simpl; reflexivity. Qed.

(** The dual 函子 restricted finite-dimensional 范畴: the
 same arrow action, precomposition, since hom [FdVect F] IS a
 hom underlying modules. （已译） *)
Program Definition DualFd : (FdVect F)^op ⟶ FdVect F := {|
  fobj := DualFdObj;
  fmap := fun V W (f : W ~{FdVect F}~> V) => dual_precompose F f
|}.
Next Obligation.
  intros V W f g Hfg h v; simpl.
  apply (proper_morphism (cmon_map (rm_hom h))).
  exact (Hfg v).
Qed.
Next Obligation. intros V f v; simpl; reflexivity. Qed.
Next Obligation. intros V W X f g h v; simpl; reflexivity. Qed.

(** 本节：The j-th vector dual basis j-th coordinate
 functional — equation names it dual basis. （已译） *)
Lemma dual_basis_coord (V : FdVectObject F) (j : Fin.t (fdv_dim V))
  (v : carrier (cmon_setoid (fdv_mod V))) :
  cmon_map (rm_hom (fdv_basis (DualFdObj V) j)) v ≈ fdv_coord V v j.
Proof.
  unfold fdv_basis; simpl.
  transitivity (fin_sum (field_ring F)
    (fun l => rig_mul F (delta (field_ring F) j l) (fdv_coord V v l))).
  - apply fin_sum_respects; intro l.
    apply rig_mul_respects; [ apply delta_sym | reflexivity ].
  - apply (fin_sum_delta_l (field_ring F) j (fun l => fdv_coord V v l)).
Qed.

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition eta_inv (V : FdVectObject F) :
  DoubleDual F (fdv_mod V) ~{Vct_F F}~> fdv_mod V := {|
  rm_hom := {|
    cmon_map := {| morphism := fun P =>
      fdv_expand V (fun j => cmon_map (rm_hom P)
                               (fdv_basis (DualFdObj V) j)) |}
  |}
|}.
Next Obligation.
  intros V P Q Hpq; simpl.
  apply fdv_expand_respects; intro j.
  exact (Hpq _).
Qed.
Next Obligation. intros V; simpl; apply fdv_expand_zero. Qed.
Next Obligation. intros V P Q; simpl; apply fdv_expand_plus. Qed.
Next Obligation. intros V r P; simpl; apply fdv_expand_smul. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition double_dual_iso (V : FdVectObject F) :
  IsIsomorphism (eta F (fdv_mod V)) := {|
  two_sided_inverse := eta_inv V
|}.
Next Obligation.
  intros V P f.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F
                (cmon_map (rm_hom P) (fdv_basis (DualFdObj V) j))
                (cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply (dual_apply_expand V f
             (fun j => cmon_map (rm_hom P)
                         (fdv_basis (DualFdObj V) j))). }
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F
                (cmon_map (rm_hom f) (fdv_basis V j))
                (cmon_map (rm_hom P) (fdv_basis (DualFdObj V) j)))).
  { apply fin_sum_respects; intro j; apply field_comm. }
  symmetry.
  transitivity (cmon_map (rm_hom P)
    (dual_of_coeffs V (fun j => cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply (proper_morphism (cmon_map (rm_hom P))).
    intro v; symmetry; apply dual_expand_coord. }
  apply (dual_apply_expand (DualFdObj V) P
           (fun j => cmon_map (rm_hom f) (fdv_basis V j))).
Qed.
Next Obligation.
  intros V v.
  transitivity (fdv_expand V (fdv_coord V v)).
  { apply fdv_expand_respects; intro j.
    apply dual_basis_coord. }
  apply fdv_expand_coord.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition fd_dual_pointwise_iso (V : FdVectObject F) :
  fdv_mod V ≅[Vct_F F] fdv_mod (DualFdObj V) := {|
  to   := @rmod_hom_compose (field_ring F) (fdv_mod V)
            (std_mod F (fdv_dim V)) (fdv_mod (DualFdObj V))
            (std_expand_hom F (DualFdObj V)) (std_coord_hom F V);
  from := @rmod_hom_compose (field_ring F) (fdv_mod (DualFdObj V))
            (std_mod F (fdv_dim V)) (fdv_mod V)
            (std_expand_hom F V) (std_coord_hom F (DualFdObj V))
|}.
Next Obligation.
  intros V f.
  transitivity (fdv_expand (DualFdObj V) (fdv_coord (DualFdObj V) f)).
  { apply fdv_expand_respects; intro j.
    apply (fdv_coord_expand V (fdv_coord (DualFdObj V) f) j). }
  apply fdv_expand_coord.
Qed.
Next Obligation.
  intros V v.
  transitivity (fdv_expand V (fdv_coord V v)).
  { apply fdv_expand_respects; intro j.
    apply (fdv_coord_expand (DualFdObj V) (fdv_coord V v) j). }
  apply fdv_expand_coord.
Qed.

End FiniteDimensional.

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example double_dual_is_dual_twice (F : FieldObject)
  (V : RModObject (field_ring F)) :
  fobj[DoubleDual F] V = DualMod F (DualMod F V) := eq_refl.

Example dual_fd_dim (F : FieldObject) (V : FdVectObject F) :
  fdv_dim (DualFdObj F V) = fdv_dim V := eq_refl.

Example dual_fd_mod (F : FieldObject) (V : FdVectObject F) :
  fdv_mod (DualFdObj F V) = DualMod F (fdv_mod V) := eq_refl.

Example transform_is_eta (F : FieldObject)
  (V : RModObject (field_ring F)) :
  transform[double_dual_natural F] V = eta F V := eq_refl.

(* * *** Dimension two over rationals

 [StdVect Q_Field 2] ℚ², whose chosen coordinates the
 恒等, so every value below reduces rational literal by
 computation. （已译） *)

Definition q2 : FdVectObject Q_Field := StdVect Q_Field 2.

Definition qvec : carrier (cmon_setoid (fdv_mod q2)) :=
  fin2 (5 # 1) (6 # 1).

(*
   本节说明 DoubleDual 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition qphi :
  carrier (cmon_setoid (fdv_mod (DualFdObj Q_Field q2))) :=
  fdv_basis Q_Field (DualFdObj Q_Field q2) Fin.F1.

Example q_dual_basis_first :
  cmon_map (rm_hom qphi) qvec = (5 # 1)%Q := eq_refl.

Example q_dual_basis_second :
  cmon_map (rm_hom (fdv_basis Q_Field (DualFdObj Q_Field q2)
                      (Fin.FS Fin.F1))) qvec = (6 # 1)%Q := eq_refl.

(** Evaluation: η(v) applied to φ is φ applied to v. *)
Example q_eta_apply :
  cmon_map (rm_hom (cmon_map (rm_hom (eta Q_Field (fdv_mod q2))) qvec))
    qphi = (5 # 1)%Q := eq_refl.

(** 本节：The first dual basis vector DOUBLE dual. （已译） *)
Definition qPhi : carrier (cmon_setoid
  (fdv_mod (DualFdObj Q_Field (DualFdObj Q_Field q2)))) :=
  fdv_basis Q_Field (DualFdObj Q_Field (DualFdObj Q_Field q2)) Fin.F1.

(** 本节：The inverse evaluation carries it back first basis vector
 ℚ², namely (1, 0) — computed, not asserted. （已译） *)
Example q_eta_inv_first :
  cmon_map (rm_hom (eta_inv Q_Field q2)) qPhi Fin.F1 = (1 # 1)%Q := eq_refl.

Example q_eta_inv_second :
  cmon_map (rm_hom (eta_inv Q_Field q2)) qPhi (Fin.FS Fin.F1)
    = (0 # 1)%Q := eq_refl.

(** 本节：... evaluating vector recovers Φ: instance of
 [double_dual_iso]'s right triangle whose two sides compute. （已译） *)
Example q_double_dual_roundtrip :
  cmon_map (rm_hom (cmon_map (rm_hom (eta Q_Field (fdv_mod q2)))
    (cmon_map (rm_hom (eta_inv Q_Field q2)) qPhi))) qphi
    = cmon_map (rm_hom qPhi) qphi := eq_refl.

(** The basis-dependent 同构 ℚ² ≅ (ℚ²)*: it carries (5,6) the
 functional 5x + 6y, whose value at (5,6) 61. （已译） *)
Example q_pointwise_iso :
  cmon_map (rm_hom (cmon_map
    (rm_hom (to (fd_dual_pointwise_iso Q_Field q2))) qvec)) qvec
    = (61 # 1)%Q := eq_refl.
