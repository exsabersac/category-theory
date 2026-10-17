Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The category of groupoids *)

(*
 nLab:      https://ncatlab.org/nlab/show/groupoid
 Wikipedia: https://en.wikipedia.org/wiki/Groupoid
 Book: Riehl, "Category Theory in Context", Dover 2016, §4.1,
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/core
   Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of
   Paper: Hofmann and Streicher, "The groupoid model refutes uniqueness of

   本节说明 Grpd 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The subcategory data *)

(* Full, cut out predicate 对象 alone: [shom] discards its
 态射 论元 entirely. Every closure 证明 therefore [I]. （已译） *)

Definition Grpd_sub : Subcategory Cat :=
  @Build_Subcategory Cat
    IsGroupoid
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Grpd : Category := Sub Cat Grpd_sub.

(*
   本节说明 Grpd 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition grpd_cat (G : Grpd) : Category := `1 G.

Definition grpd_is_groupoid (G : Grpd) : IsGroupoid (grpd_cat G) := `2 G.

(** ** Fullness and the inclusion *)

Definition Grpd_Full : Full Cat Grpd_sub := fun _ _ _ _ _ => I.

Definition Grpd_Incl : Grpd ⟶ Cat := Incl Cat Grpd_sub.

Definition Grpd_Incl_Faithful : Functor.Faithful Grpd_Incl :=
  Incl_Faithful Cat Grpd_sub.

(* The 含入 FULL 函子, not merely full data:
 Construction/Subcategory.v turns one 进入 other. （已译） *)

Definition Grpd_Incl_Full : Functor.Full Grpd_Incl :=
  Full_Implies_Full_Functor Cat Grpd_sub Grpd_Full.

(*
   本节说明 Grpd 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Grpd_ShomRespects : ShomRespects Cat Grpd_sub :=
  fun _ _ _ _ _ _ _ _ => I.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma IsGroupoid_transport (C D : Category) (i : C ≅[Cat] D) :
  IsGroupoid C → IsGroupoid D.
Proof.
  intros HC x y h.
  (* The counit-side natural 同构: i ◯ i ≈ Id[D]. （已译） *)
  destruct (iso_to_from i) as [n Hn].
  pose proof (Hn _ _ h) as Hnat; simpl in Hnat.
  (* 相关说明。 （已译） *)
  assert (Hl : h ∘ to (n x) ≈ to (n y) ∘ fmap[to i] (fmap[from i] h)).
  { rewrite Hnat.
    rewrite !comp_assoc.
    rewrite (iso_to_from (n y)), id_left.
    reflexivity. }
  assert (Hr : from (n y) ∘ h ≈ fmap[to i] (fmap[from i] h) ∘ from (n x)).
  { rewrite Hnat.
    rewrite <- !comp_assoc.
    rewrite (iso_to_from (n x)), id_right.
    reflexivity. }
  unshelve econstructor.
  - exact (to (n x) ∘ fmap[to i] (ginv HC (fmap[from i] h)) ∘ from (n y)).
  - (* h ∘ h⁻¹ ≈ id *)
    rewrite !comp_assoc.
    rewrite Hl.
    rewrite <- (comp_assoc (to (n y))).
    (* 相关说明。 （已译） *)
    rewrite <- (@fmap_comp _ _ (to i) _ _ _
                  (fmap[from i] h) (ginv HC (fmap[from i] h))).
    rewrite ginv_right, fmap_id, id_right.
    apply (iso_to_from (n y)).
  - (* h⁻¹ ∘ h ≈ id *)
    rewrite <- !comp_assoc.
    rewrite Hr.
    rewrite (comp_assoc (fmap[to i] (ginv HC (fmap[from i] h)))).
    rewrite <- fmap_comp.
    rewrite ginv_left, fmap_id, id_left.
    apply (iso_to_from (n x)).
Qed.

Definition Grpd_Replete : Replete Cat Grpd_sub :=
  fun x ox y f => (IsGroupoid_transport x y f ox; (I, I)).

(*
   本节说明 Grpd 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma Grpd_proper_subcategory : sobj Cat Grpd_sub (Deloop Nat_Plus) → False.
Proof. exact deloop_nat_not_groupoid. Qed.

(* 相关说明。 （已译） *)

Definition Grpd_Deloop_Bool : Grpd :=
  (Deloop Bool_Xor_Grp; deloop_bool_groupoid).
