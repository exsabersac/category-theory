Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.

Generalizable All Variables.

(*
 nLab:  https://ncatlab.org/nlab/show/quotient+object
 nLab:  https://ncatlab.org/nlab/show/subobject
 nLab:  https://ncatlab.org/nlab/show/coimage

   本文件给出商/商对象相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Quotient 对象 subobjects opposite 范畴 （已译） *)

(* Mac Lane §V.7: a quotient object of x is (an equivalence class of) an
   epimorphism out of x.  Since [Epic] in C is [Monic] in C^op
   (Theory/Morphisms/Duality.v), the definition is one line, the idiom of
   Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)]. *)
Definition QuotObj {C : Category} (x : C) : Type := @SubObj (C^op) x.

Section QuotientAccessors.

Context {C : Category}.
Context {x : C}.

(* Covariant readings of the record's fields: a C^op-arrow into x is a
   C-arrow out of x, definitionally (Construction/Opposite.v). *)
Definition quot_cod (q : QuotObj x) : C := sub_dom q.

Definition quot_epi (q : QuotObj x) : x ~> quot_cod q := sub_mono q.

Definition quot_is_epic (q : QuotObj x) : Epic (quot_epi q) :=
  Epic_of_op_Monic (quot_epi q) (sub_is_monic q).

(* A quotient object from an epimorphism of C. *)
Definition mk_quot {y : C} (e : x ~> y) (He : Epic e) : QuotObj x :=
  @Build_SubObj (C^op) x y e (op_Monic_of_Epic e He).

(* 相关说明。 （已译） *)
#[export] Instance QuotObj_Setoid : Setoid (QuotObj x) :=
  @SubObj_Setoid (C^op) x.

Definition quot_le (q r : QuotObj x) : Type := @sub_le (C^op) x q r.

End QuotientAccessors.

(* * ** Isomorphisms carried across opposite 范畴 （已译） *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section OppositeIso.

Context {C : Category}.

Definition Iso_of_op_Iso {a b : C} (i : @Isomorphism (C^op) a b) : b ≅[C] a :=
  @Build_Isomorphism C b a (to i) (from i) (iso_from_to i) (iso_to_from i).

Definition op_Iso_of_Iso {a b : C} (j : a ≅[C] b) :
  @Isomorphism (C^op) b a :=
  @Build_Isomorphism (C^op) b a (to j) (from j) (iso_from_to j)
    (iso_to_from j).

End OppositeIso.

(** ** The covariant API *)

Section QuotientCovariant.

Context {C : Category}.
Context {x : C}.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example QuotObj_op_is_SubObj : @QuotObj (C^op) x = @SubObj C x := eq_refl.

(* 相关说明。 （已译） *)
Example quot_le_unfold (q r : QuotObj x) :
  quot_le q r
  = { k : quot_cod r ~> quot_cod q & k ∘ quot_epi r ≈ quot_epi q }
  := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example quot_equiv_unfold (q r : QuotObj x) :
  (q ≈ r)
  = { i : @Isomorphism (C^op) (quot_cod q) (quot_cod r)
    & (to i ∘[C] quot_epi r) ≈ quot_epi q }
  := eq_refl.

Definition quot_le_refl (q : QuotObj x) : quot_le q q :=
  @sub_le_refl (C^op) x q.

Definition quot_le_trans (q r s : QuotObj x) :
  quot_le q r → quot_le r s → quot_le q s :=
  @sub_le_trans (C^op) x q r s.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_le_epic (q r : QuotObj x) (H : quot_le q r) :
  @Epic C (quot_cod r) (quot_cod q) (`1 H) :=
  @Epic_of_op_Monic C (quot_cod r) (quot_cod q) (`1 H)
    (@sub_le_monic (C^op) x q r H).

(* 相关说明。 （已译） *)
Definition quot_le_unique (q r : QuotObj x)
  (k k' : quot_cod r ~> quot_cod q) :
  k ∘ quot_epi r ≈ quot_epi q → k' ∘ quot_epi r ≈ quot_epi q → k ≈ k' :=
  @sub_le_unique (C^op) x q r k k'.

(* Mac Lane's equivalence of epis: each factors through the other. *)
Definition quot_equiv_iff_mutual (q r : QuotObj x) :
  (q ≈ r) ↔ (quot_le q r * quot_le r q) :=
  @sub_equiv_iff_mutual (C^op) x q r.

Definition quot_le_antisym (q r : QuotObj x) :
  quot_le q r → quot_le r q → q ≈ r :=
  @sub_le_antisym (C^op) x q r.

Definition quot_le_of_equiv (q r : QuotObj x) : q ≈ r → quot_le q r :=
  @sub_le_of_equiv (C^op) x q r.

Definition quot_ge_of_equiv (q r : QuotObj x) : q ≈ r → quot_le r q :=
  @sub_ge_of_equiv (C^op) x q r.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem quot_equiv_iff_iso (q r : QuotObj x) :
  (q ≈ r) ↔ { i : quot_cod q ≅[C] quot_cod r
            & to i ∘ quot_epi q ≈ quot_epi r }.
Proof.
  split.
  - intros H.
    symmetry in H.
    destruct H as [i Hi].
    exists (Iso_of_op_Iso i).
    exact Hi.
  - intros [j Hj].
    symmetry.
    exists (op_Iso_of_Iso j).
    exact Hj.
Defined.

(* Equivalent epis out x present same quotient 对象, the
 恒等 同构 witnessing it. （已译） *)
Definition mk_quot_respects {y : C} (e e' : x ~> y)
  (He : Epic e) (He' : Epic e') : e ≈ e' → mk_quot e He ≈ mk_quot e' He'.
Proof.
  intros Hee.
  apply quot_equiv_iff_iso.
  exists iso_id.
  simpl.
  rewrite id_left.
  now symmetry.
Defined.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary quot_equiv_of_cod_iso (q r : QuotObj x)
  (i : quot_cod r ≅[C] quot_cod q)
  (H : to i ∘ quot_epi r ≈ quot_epi q) : q ≈ r.
Proof.
  symmetry.
  exact (snd (quot_equiv_iff_iso r q) (i; H)).
Defined.

End QuotientCovariant.

(* 相关说明。 （已译） *)

Definition monic_op_iff_epic {C : Category} {x y : C} (f : x ~> y) :
  (@Monic (C^op) y x f → @Epic C x y f) * (@Epic C x y f → @Monic (C^op) y x f)
  := (Epic_of_op_Monic f, op_Monic_of_Epic f).

Section Bridges.

Context {C : Category}.
Context {x y : C}.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition epic_of_monic_op (f : x ~> y) : @Monic (C^op) y x f → @Epic C x y f
  := fst (monic_op_iff_epic f).

Definition monic_op_of_epic (f : x ~> y) : @Epic C x y f → @Monic (C^op) y x f
  := snd (monic_op_iff_epic f).

End Bridges.

(* * ** The top quotient: x 恒等 （已译） *)

Section QuotientTop.

Context {C : Category}.
Context {x : C}.

(* 相关说明。 （已译） *)
Definition quot_top : QuotObj x := @sub_top (C^op) x.

Example quot_top_cod : quot_cod quot_top = x := eq_refl.
Example quot_top_epi : quot_epi quot_top = @id C x := eq_refl.

Definition quot_top_greatest (q : QuotObj x) : quot_le q quot_top :=
  @sub_top_greatest (C^op) x q.

End QuotientTop.

(* * ** The lattice quotient 对象, transport subobject one （已译） *)

Section QuotientMeet.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context {x : C}.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_meet (q r : QuotObj x) : QuotObj x :=
  @sub_meet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

End QuotientMeet.

(* 相关说明。 （已译） *)

Section QuotientMeetLaws.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context {x : C}.

(* Below both factors: the two pushout injections, read backwards. *)
Definition quot_meet_le_l (q r : QuotObj x) : quot_le (quot_meet q r) q :=
  @sub_meet_le_l (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_meet_le_r (q r : QuotObj x) : quot_le (quot_meet q r) r :=
  @sub_meet_le_r (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_meet_is_glb (q r : QuotObj x) :
  ∀ w : QuotObj x, quot_le w q → quot_le w r → quot_le w (quot_meet q r) :=
  @sub_meet_is_glb (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_meet_IsMeet (q r : QuotObj x) :
  @IsMeet (C^op) x q r (quot_meet q r) :=
  @sub_meet_IsMeet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

#[export] Instance quot_meet_respects :
  Proper (equiv ==> equiv ==> equiv) (@quot_meet C HP x) :=
  @sub_meet_respects (C^op) (HasPullbacks_op_of_HasPushouts HP) x.

Definition quot_meet_comm (q r : QuotObj x) : quot_meet q r ≈ quot_meet r q :=
  @sub_meet_comm (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_meet_assoc (q r s : QuotObj x) :
  quot_meet (quot_meet q r) s ≈ quot_meet q (quot_meet r s) :=
  @sub_meet_assoc (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r s.

Definition quot_meet_idem (q : QuotObj x) : quot_meet q q ≈ q :=
  @sub_meet_idem (C^op) (HasPullbacks_op_of_HasPushouts HP) x q.

(* The 恒等 quotient unit meet. （已译） *)
Definition quot_meet_top (q : QuotObj x) : quot_meet q quot_top ≈ q :=
  @sub_meet_top (C^op) (HasPullbacks_op_of_HasPushouts HP) x q.

(* 相关说明。 （已译） *)
Definition quot_meet_of_le (q r : QuotObj x) :
  quot_le q r → quot_meet q r ≈ q :=
  @sub_meet_of_le (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

Definition quot_le_of_meet (q r : QuotObj x) :
  quot_meet q r ≈ q → quot_le q r :=
  @sub_le_of_meet (C^op) (HasPullbacks_op_of_HasPushouts HP) x q r.

End QuotientMeetLaws.

(* * *** The bottom quotient, under epic arrow 终对象 （已译） *)

Section QuotientBottom.

Context {C : Category}.
Context `{T : @Terminal C}.
Context {x : C}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_bot (He : Epic (@one C T x)) : QuotObj x :=
  @sub_bot (C^op) T x (op_Monic_of_Epic (@one C T x) He).

(* The coarsest quotient: every quotient object of x sits above it. *)
Definition quot_bot_least (He : Epic (@one C T x)) (q : QuotObj x) :
  quot_le (quot_bot He) q :=
  @sub_bot_least (C^op) T x (op_Monic_of_Epic (@one C T x) He) q.

(*
   本节说明子对象、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition one_epic_of_costrict
  (Hco : ∀ (y : C) (f : @terminal_obj C T ~> y),
           @terminal_obj C T ≅[C] y) :
  Epic (@one C T x) :=
  Epic_of_op_Monic (@one C T x)
    (@zero_monic_of_strict (C^op) T x
       (fun y f => op_Iso_of_Iso (Hco y f))).

End QuotientBottom.

(* 相关说明。 （已译） *)

Section QuotientWideMeet.

Context {C : Category}.
Context {x : C}.
Context {J : Type}.
Context (S : J → QuotObj x).

(*
   本节说明拉回/推出、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_wide_meet (j0 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) : QuotObj x :=
  @sub_wide_intersection (C^op) x J S j0 W.

Definition quot_wide_meet_IsIntersection (j0 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) :
  @IsIntersection (C^op) x J S (quot_wide_meet j0 W) :=
  @sub_wide_intersection_IsIntersection (C^op) x J S j0 W.

Definition quot_wide_meet_index_irrelevant (j0 j1 : J)
  (W : @WidePullback (C^op) J (fun j => quot_cod (S j)) x
         (fun j => quot_epi (S j))) :
  quot_wide_meet j0 W ≈ quot_wide_meet j1 W :=
  @sub_wide_intersection_index_irrelevant (C^op) x J S j0 j1 W.

End QuotientWideMeet.

(* 相关说明。 （已译） *)

Section Coimages.

Context {C : Category}.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CoimageOf {x y : C} (f : x ~> y) : Type := @ImageOf (C^op) y x f.

End Coimages.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Notation "'HasCoimages' C" := (@HasImages (C^op))
  (at level 9) : category_theory_scope.
Notation "@HasCoimages C" := (@HasImages (C^op))
  (at level 9) : category_theory_scope.

Section QuotientJoin.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context {x : C}.

(* The copairing C^op pairing C. Spelling it C what
 makes [CoimageOf] below pick right 范畴 (see header). （已译） *)
Definition quot_pairing (q r : QuotObj x) :
  x ~{C}~> @product_obj C CC (quot_cod q) (quot_cod r) :=
  @fork C CC x (quot_cod q) (quot_cod r) (quot_epi q) (quot_epi r).

(* The join two quotient 对象: coimage pairing their
 epis 进入 product codomains, given such coimage. （已译） *)
Definition quot_join_via (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) : QuotObj x :=
  @sub_join_via (C^op) CC x q r I.

Definition quot_join_via_le_l (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  quot_le q (quot_join_via q r I) :=
  @sub_join_via_le_l (C^op) CC x q r I.

Definition quot_join_via_le_r (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  quot_le r (quot_join_via q r I) :=
  @sub_join_via_le_r (C^op) CC x q r I.

(* The coimage LEAST quotient 对象 above both. （已译） *)
Definition quot_join_via_is_lub (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) (w : QuotObj x) :
  quot_le q w → quot_le r w → quot_le (quot_join_via q r I) w :=
  @sub_join_via_is_lub (C^op) CC x q r I w.

Definition quot_join_via_IsJoin (q r : QuotObj x)
  (I : CoimageOf (quot_pairing q r)) :
  @IsJoin (C^op) x q r (quot_join_via q r I) :=
  @sub_join_via_IsJoin (C^op) CC x q r I.

End QuotientJoin.

(* 相关说明。 （已译） *)

Section QuotientJoinLattice.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{HI : @HasCoimages C}.
Context {x : C}.

Definition quot_join (q r : QuotObj x) : QuotObj x :=
  @sub_join (C^op) CC x HI q r.

Definition quot_join_le_l (q r : QuotObj x) : quot_le q (quot_join q r) :=
  @sub_join_le_l (C^op) CC HI x q r.

Definition quot_join_le_r (q r : QuotObj x) : quot_le r (quot_join q r) :=
  @sub_join_le_r (C^op) CC HI x q r.

Definition quot_join_is_lub (q r : QuotObj x) :
  ∀ w : QuotObj x, quot_le q w → quot_le r w → quot_le (quot_join q r) w :=
  @sub_join_is_lub (C^op) CC HI x q r.

Definition quot_join_IsJoin (q r : QuotObj x) :
  @IsJoin (C^op) x q r (quot_join q r) :=
  @sub_join_IsJoin (C^op) CC HI x q r.

#[export] Instance quot_join_respects :
  Proper (equiv ==> equiv ==> equiv) quot_join :=
  @sub_join_respects (C^op) CC HI x.

Definition quot_join_comm (q r : QuotObj x) : quot_join q r ≈ quot_join r q :=
  @sub_join_comm (C^op) CC HI x q r.

Definition quot_join_assoc (q r s : QuotObj x) :
  quot_join (quot_join q r) s ≈ quot_join q (quot_join r s) :=
  @sub_join_assoc (C^op) CC HI x q r s.

Definition quot_join_idem (q : QuotObj x) : quot_join q q ≈ q :=
  @sub_join_idem (C^op) CC HI x q.

Definition quot_join_of_le (q r : QuotObj x) :
  quot_le q r → quot_join q r ≈ r :=
  @sub_join_of_le (C^op) CC HI x q r.

Definition quot_le_of_join (q r : QuotObj x) :
  quot_join q r ≈ r → quot_le q r :=
  @sub_le_of_join (C^op) CC HI x q r.

End QuotientJoinLattice.

(* 相关说明。 （已译） *)

Section QuotientAbsorption.

Context {C : Category}.
Context `{HP : @HasPushouts C}.
Context `{CC : @Cartesian C}.
Context `{HI : @HasCoimages C}.
Context {x : C}.

Definition quot_meet_absorb (q r : QuotObj x) :
  quot_meet q (quot_join q r) ≈ q :=
  @sub_meet_absorb (C^op) (HasPullbacks_op_of_HasPushouts HP) CC HI x q r.

Definition quot_join_absorb (q r : QuotObj x) :
  quot_join q (quot_meet q r) ≈ q :=
  @sub_join_absorb (C^op) (HasPullbacks_op_of_HasPushouts HP) CC HI x q r.

End QuotientAbsorption.
