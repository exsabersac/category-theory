Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Monad.Comparison.
Require Import Category.Comonad.Core.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rep.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Instance.Proset.Galois.FixedPoints.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Coq.Monoid.Free.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   本文件为测试：ProbeFixedPoints386。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Instrument check *)

(* 相关说明。 （已译） *)
Fail Check probe386_instrument_no_such_constant.

(** ** Negatives of kind TYPING *)

Section ProbeTyping.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(*
   本节说明伴随、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (adjunction_fixed_point_equivalence A : EquivalenceOfCategories F).

(* Controls: term does elaborate at own type, [F] a
 函子 [EquivalenceOfCategories] accepts 论元. （已译） *)
Check (adjunction_fixed_point_equivalence A).
Check (fun (E : EquivalenceOfCategories F) => quasi_inverse).
Check (FixedL A).
Check (FixedR A).
Check (fixed_point_equivalence_swap A).
Check (fixed_AdjointEquivalence A).
Check (fixed_adjunction A).
Check (UnitFixed A).
Check (CounitFixed A).
Check (UnitFixed_Full A).
Check (CounitFixed_Full A).
Check (counit_iso_of_unit_iso A).
Check (unit_iso_of_counit_iso A).
Check (unit_fixed_iff_image A).
Check (counit_fixed_iff_image A).
Check (unit_iso_of_image A).
Check (counit_iso_of_image A).
Check (fixed_unit_inverse A).
Check (fixed_counit_inverse A).
Check (unit_fixed_reflective_of_idempotent A).
Check (counit_fixed_op_reflective_of_idempotent A).

End ProbeTyping.

Section ProbeTypingComonad.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Coreflective S).

(*
   本节说明 ProbeFixedPoints386 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Reflective_IdempotentMonad R
              : IdempotentComonad
                  (Incl (C^op) (op_subcategory S) ◯ reflector R)
                  (Reflective_Monad R)).

(* 相关说明。 （已译） *)
Check (Coreflective_IdempotentMonad_op R).
Check (Reflective_IdempotentMonad R).
Check (Reflective_Monad R).
Check @Incl.
Check @op_subcategory.
Check @reflector.
Check @sobj.
Check @IsIsomorphism.
Check @IdempotentComonad.
Check @Idempotent_Coreflective.
Check @WLocal_Subcategory.
Check @wlocal_obj_iff.
Check @wlocal_to_extract.
Check @extract_to_wlocal.

End ProbeTypingComonad.

(** ** Negatives of kind CONVERSION *)

Section ProbeConversion.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_counit_fixed_not_op :
  CounitFixed A = op_subcategory (UnitFixed (Opposite_Adjunction F U A))
  := eq_refl.

(* Controls: 态射 identification DOES hold, the
 单子-side bridge, holds whole record. （已译） *)
Check (fun c : C =>
  eq_refl : @unit (D^op) (C^op) (U^op) (F^op) (Opposite_Adjunction F U A) c
              = @counit C D F U A c).
Check (eq_refl : UnitFixed A
                   = @MLocal_Subcategory D (U ◯ F)
                       (Adjunction_Induced_Monad A)).
Check (fun x : Sub D (UnitFixed A) =>
  eq_refl : `1 (@unit _ _ (FixedL A) (FixedR A) (fixed_adjunction A) x)
              = @unit C D F U A `1 x).
Check (fun y : Sub C (CounitFixed A) =>
  eq_refl : `1 (@counit _ _ (FixedL A) (FixedR A) (fixed_adjunction A) y)
              = @counit C D F U A `1 y).
Check (Opposite_Adjunction F U A).

End ProbeConversion.

Section ProbeConversionComonad.

Context {C : Category}.
Context {W : C ⟶ C}.
Context (H : @Comonad C W).

(*
   本节说明 ProbeFixedPoints386 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_wlocal_not_covariant (x : C) :
  sobj C (WLocal_Subcategory H) x = IsIsomorphism (@extract C W H x)
  := eq_refl.

(* 相关说明。 （已译） *)
Check (fun x : C =>
  eq_refl : sobj C (WLocal_Subcategory H) x
              = @IsIsomorphism (C^op) x (W x) (@extract C W H x)).
Check (wlocal_to_extract H).
Check (extract_to_wlocal H).
Check (fun x : C => @extract C W H x).

End ProbeConversionComonad.

Section ProbeConversionGalois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

(*
   本节说明 ProbeFixedPoints386 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_closed_sigma_round
  (p : ∃ a : A, GalClosed_r G a) :
  closed_l_to_r PA G (closed_r_to_l PB G p) = p := eq_refl.

(*
   本节说明 ProbeFixedPoints386 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_closed_not_definitional
  (a : A) (Hc : GalClosed_r G a) : gal_r G (gal_l G a) = a := eq_refl.

(* Controls: relatedness DOES hold no 假设, the
 antisymmetric statement supplies equation. （已译） *)
Check (fun (a : A) (Hc : GalClosed_r G a) =>
  Hc : RA (gal_r G (gal_l G a)) a).
Check (gal_unit G PB).
Check (closed_r_eq PA PB G).
Check (closed_l_eq PA PB G).
Check (closed_r_iff_image_eq PA PB G).
Check (closed_l_iff_image_eq PA PB G).
Check (gal_lrl_eq PA PB G).
Check (gal_rlr_eq PA PB G).
Check (closed_r_to_l PB G).
Check (closed_l_to_r PA G).
Check (closed_round_r PA PB G).
Check (closed_round_l PA PB G).
Check (unit_fixed_iff_closed_r PA PB G).
Check (counit_fixed_iff_closed_l PA PB G).
Check (galois_fixed_point_equivalence PA PB G).
Check (galois_fixed_point_equivalence_swap PA PB G).
Check (GAdj PA PB G).

End ProbeConversionGalois.

(** ** Negatives of kind FORMABILITY *)

Section ProbeUniverses.

Universes uo uh up.
Constraint uh < up.

Context (Cu Du : Category@{uo uh up}).
Context (Fu : Du ⟶ Cu) (Uu : Cu ⟶ Du).

(* Controls at very same declared levels: 范畴's homs its
 identities formable, so 函子 both directions. （已译） *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check Fu.
Check Uu.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (Fu ⊣ Uu).

(* NEGATIVE 8 (FORMABILITY). [Subcategory] does so independently, with
 no 伴随 anywhere command. （已译） *)
Fail Check (Subcategory Cu).

End ProbeUniverses.

(* 相关说明。 （已译） *)
Section ProbeUniversesControl.

Universes vo vh.

Context (Cv Dv : Category@{vo vh vh}).
Context (Fv : Dv ⟶ Cv) (Uv : Cv ⟶ Dv).

Check (Fv ⊣ Uv).
Check (Subcategory Cv).
Check (fun (Av : Fv ⊣ Uv) => UnitFixed Av).
Check (fun (Av : Fv ⊣ Uv) => adjunction_fixed_point_equivalence Av).

End ProbeUniversesControl.

(* * ** Witness: free-幺半群 伴随 （已译） *)

(* Instance/Coq/Monoid/Free.v declares [MonCoq] and [UMon] as [#[local]]
   notations, which do not export; hence these two. *)
Notation MonC := (@Mon Coq Coq_Monoidal).
Notation UMonC := (@Mon_Forget Coq Coq_Monoidal).

(* 相关说明。 （已译） *)
Example probe_free_unit_is_insert (X : Coq) (a : X) :
  @unit MonC Coq FreeMonoid UMonC free_monoid_adjunction X a
    = (a :: nil)%list := eq_refl.

(*
   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_monoid_unit_never_iso (X : Coq) :
  IsIsomorphism (@unit MonC Coq FreeMonoid UMonC free_monoid_adjunction X)
    → False.
Proof.
  intros [k Hr Hl].
  pose proof (Hr nil) as Hn.
  simpl in Hn.
  discriminate Hn.
Qed.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example probe_list_is_U_of_F (X : Coq) :
  fobj[UMonC] (fobj[FreeMonoid] X) = list X := eq_refl.

Theorem probe_image_of_U_not_unit_fixed :
  IsIsomorphism
    (@unit MonC Coq FreeMonoid UMonC free_monoid_adjunction
       (fobj[UMonC] (fobj[FreeMonoid] bool)))
    → False.
Proof. exact (free_monoid_unit_never_iso (list bool)). Qed.

(* The 典范比较 [eps (F x)] 可逆 either, so
 [F eta] inverse: Riehl's "F G F = F" reading a
 statement about Galois connection between POSETS does carry
 over arbitrary 伴随. Whether some OTHER natural
 同构 [F ◯ U ◯ F ≈ F] exists at 伴随 neither
 proved nor refuted here. （已译） *)
(* The 对象 question IS [F]-image, what makes next
 two computations statement about CANONICAL comparison. （已译） *)
Example probe_FreeMon_is_F_bool :
  FreeMon bool = fobj[FreeMonoid] bool := eq_refl.

Example probe_counit_of_two_words :
  `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
        (FreeMon bool)) (cons (@nil bool) nil)
    = @nil bool.
Proof.
  exact (free_monoid_counit_is_free_ext (FreeMon bool)
           (cons (@nil bool) nil)).
Qed.

Example probe_counit_of_empty_word :
  `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
        (FreeMon bool)) (@nil (list bool))
    = @nil bool.
Proof.
  exact (free_monoid_counit_is_free_ext (FreeMon bool)
           (@nil (list bool))).
Qed.

Theorem free_monoid_counit_not_iso :
  IsIsomorphism
    (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
       (FreeMon bool))
    → False.
Proof.
  intros [k Hr Hl].
  assert (Hinj : ∀ u v : list (list bool),
            `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
                  (FreeMon bool)) u
              = `1 (@counit MonC Coq FreeMonoid UMonC
                      free_monoid_adjunction (FreeMon bool)) v → u = v).
  { intros u v Huv.
    transitivity (`1 k
      (`1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
             (FreeMon bool)) u)).
    - symmetry; exact (Hl u).
    - rewrite Huv; exact (Hl v). }
  pose proof (Hinj (cons (@nil bool) nil) (@nil (list bool))) as Hc.
  rewrite probe_counit_of_two_words, probe_counit_of_empty_word in Hc.
  discriminate (Hc eq_refl).
Qed.

(* The general 定理 still applies there, both fixed
 subcategories they are: 这是 control 等价
 asks nothing 伴随. （已译） *)
Check (adjunction_fixed_point_equivalence free_monoid_adjunction).

(* * ** Witness: 恒等 伴随, where every 对象 fixed （已译） *)

(* The other extreme. [adj_id]'s unit [≈ id], so transporting
 invertibility 恒等 along equation makes every 对象
 C unit-fixed, dually. （已译） *)
Definition probe_id_unit_fixed {C : Category} (x : C) :
  sobj C (UnitFixed (@adj_id C)) x.
Proof.
  refine (fixed_IsIso_along (fixed_IsIso_of_iso (@iso_id C x)) _).
  symmetry; exact (@adj_id_unit C x).
Defined.

Definition probe_id_counit_fixed {C : Category} (x : C) :
  sobj C (CounitFixed (@adj_id C)) x.
Proof.
  refine (fixed_IsIso_along (fixed_IsIso_of_iso (@iso_id C x)) _).
  symmetry; exact (@adj_id_counit C x).
Defined.

Check (fun C : Category => adjunction_fixed_point_equivalence (@adj_id C)).

(* 相关说明。 （已译） *)

(* The restricted 左伴随 carries fixed 对象 5 3, by
 computation, 1 not fixed. （已译） *)
Check nat_shift_five_closed.
Check nat_shift_five_fixed.
Check nat_shift_closed_r_iff.
Check nat_shift_closed_l_all.
Check nat_shift_two_one_not_closed.
Check nat_shift_gal_l_five.
Check nat_shift_FixedL_obj.
Check @image_preimage_image.
Check @preimage_image_preimage.
Check @image_closed_l.
Check @preimage_closed_r.
Check @group_action_fixed_point_equivalence.
