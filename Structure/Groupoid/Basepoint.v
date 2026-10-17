Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.

Generalizable All Variables.

(** * Base points: the vertex groups of a connected groupoid *)

(*
   nLab:      https://ncatlab.org/nlab/show/vertex+group
   nLab:      https://ncatlab.org/nlab/show/delooping
   nLab:      https://ncatlab.org/nlab/show/fully+faithful+functor
   nLab:      https://ncatlab.org/nlab/show/equivalence+of+categories
   Book:      Riehl, "Category Theory in Context", Corollary 1.5.14, printed
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Basepoint 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Fullness and faithfulness are closed under composition *)

(*
   本节说明 Basepoint 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Full_Compose {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  (FF : Full F) (FG : Full G) : Full (F ◯ G).
Proof.
  refine (@Build_Full C E (F ◯ G)
            (fun x y h => @prefmap C D G FG x y
                            (@prefmap D E F FF (G x) (G y) h)) _).
  intros x y h.
  transitivity (@fmap D E F (G x) (G y) (@prefmap D E F FF (G x) (G y) h)).
  - apply (@fmap_respects D E F (G x) (G y)).
    exact (@fmap_sur C D G FG x y (@prefmap D E F FF (G x) (G y) h)).
  - exact (@fmap_sur D E F FF (G x) (G y) h).
Defined.

(* The composite of two faithful functors is faithful: reduce the goal by G's
   injectivity, then by F's, which lands exactly on the hypothesis. *)
Definition Faithful_Compose {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
  (FF : Faithful F) (FG : Faithful G) : Faithful (F ◯ G).
Proof.
  refine (@Build_Faithful C E (F ◯ G) _).
  intros x y f g H.
  apply (@fmap_inj C D G FG x y).
  apply (@fmap_inj D E F FF (G x) (G y)).
  exact H.
Defined.

(** ** A fully faithful functor between deloopings is a monoid isomorphism *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DeloopFullyFaithful.

Context {M N : MonObject}.
Context (F : Deloop M ⟶ Deloop N).
Context (FF : Full F).
Context (Ffaith : Faithful F).

(* The forward map: the hom-map of F at the unique object.  Its type is
   [carrier M → carrier N] on the nose, the hom-setoids of the two deloopings
   being the two carrier setoids. *)
Definition deloop_fwd (a : carrier M) : carrier N := @fmap _ _ F ttt ttt a.

(* The backward map: the chosen section of that hom-map. *)
Definition deloop_bwd (b : carrier N) : carrier M :=
  @prefmap _ _ F FF ttt ttt b.

(* One round trip is the section law verbatim. *)
Lemma deloop_fwd_bwd (b : carrier N) : deloop_fwd (deloop_bwd b) ≈ b.
Proof. exact (@fmap_sur _ _ F FF ttt ttt b). Qed.

(* The other follows from it by faithfulness: the two elements have the same
   image under the injective hom-map. *)
Lemma deloop_bwd_fwd (a : carrier M) : deloop_bwd (deloop_fwd a) ≈ a.
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  exact (@fmap_sur _ _ F FF ttt ttt (deloop_fwd a)).
Qed.

(*
   本节说明函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma deloop_fwd_respects : Proper (equiv ==> equiv) deloop_fwd.
Proof. exact (@fmap_respects _ _ F ttt ttt). Qed.

Lemma deloop_fwd_unit : deloop_fwd mon_unit ≈ mon_unit.
Proof. exact (@fmap_id _ _ F ttt). Qed.

Lemma deloop_fwd_op (a b : carrier M) :
  deloop_fwd (mon_op a b) ≈ mon_op (deloop_fwd a) (deloop_fwd b).
Proof. exact (@fmap_comp _ _ F ttt ttt ttt a b). Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma deloop_bwd_respects : Proper (equiv ==> equiv) deloop_bwd.
Proof using F FF Ffaith.
  intros b b' Hb.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity b; [ exact (deloop_fwd_bwd b) | ].
  transitivity b'; [ exact Hb | ].
  symmetry.
  exact (deloop_fwd_bwd b').
Qed.

Lemma deloop_bwd_unit : deloop_bwd mon_unit ≈ mon_unit.
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity (@mon_unit N); [ exact (deloop_fwd_bwd mon_unit) | ].
  symmetry.
  exact deloop_fwd_unit.
Qed.

Lemma deloop_bwd_op (a b : carrier N) :
  deloop_bwd (mon_op a b) ≈ mon_op (deloop_bwd a) (deloop_bwd b).
Proof using F FF Ffaith.
  apply (@fmap_inj _ _ F Ffaith ttt ttt).
  transitivity (mon_op a b); [ exact (deloop_fwd_bwd (mon_op a b)) | ].
  transitivity (mon_op (deloop_fwd (deloop_bwd a)) (deloop_fwd (deloop_bwd b))).
  - apply (mon_op_respects N); symmetry; apply deloop_fwd_bwd.
  - symmetry.
    exact (deloop_fwd_op (deloop_bwd a) (deloop_bwd b)).
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition deloop_MonHom_fwd : MonHom M N :=
  @Build_MonHom M N deloop_fwd deloop_fwd_respects deloop_fwd_unit
    deloop_fwd_op.

Definition deloop_MonHom_bwd : MonHom N M :=
  @Build_MonHom N M deloop_bwd deloop_bwd_respects deloop_bwd_unit
    deloop_bwd_op.

Definition deloop_ff_moniso : MonIso M N :=
  @Build_MonIso M N deloop_MonHom_fwd deloop_MonHom_bwd
    deloop_fwd_bwd deloop_bwd_fwd.

End DeloopFullyFaithful.

(* The equivalence-level form, by the two halves of the full-and-faithful
   characterization in Theory/Equivalence/FullFaithful.v ([Equivalence_Full]
   and [Equivalence_Faithful]). *)
Definition deloop_equiv_moniso {M N : MonObject} (F : Deloop M ⟶ Deloop N)
  (E : EquivalenceOfCategories F) : MonIso M N :=
  deloop_ff_moniso F (Equivalence_Full E) (Equivalence_Faithful E).

(** ** The headline: base-point independence of the vertex group *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ConnectedVertex.

Context {C : Category}.
Context (G : IsGroupoid C).
Context (K : Connected C).
Context (x y : C).

(* The structure theorem at y. *)
Definition basepoint_equiv : EquivalenceOfCategories (vertex_incl G y) :=
  connected_deloop_equiv G K y.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition basepoint_compare :
  Deloop (vertex_group G x) ⟶ Deloop (vertex_group G y) :=
  @quasi_inverse _ _ _ basepoint_equiv ◯ vertex_incl G x.

(* Its fullness: the right factor by [vertex_incl_Full], the left by
   [Equivalence_Full] at the symmetric equivalence — the quasi-inverse of an
   equivalence is an equivalence, hence full. *)
Definition basepoint_compare_Full : Full basepoint_compare :=
  Full_Compose (@quasi_inverse _ _ _ basepoint_equiv) (vertex_incl G x)
    (@Equivalence_Full _ _ _
       (@EquivalenceOfCategories_sym _ _ _ basepoint_equiv))
    (vertex_incl_Full G x).

(* Its faithfulness, the same way; the left factor is
   [Equivalence_Inverse_Faithful], which is that same symmetric-equivalence
   argument already packaged in Theory/Equivalence/FullFaithful.v. *)
Definition basepoint_compare_Faithful : Faithful basepoint_compare :=
  Faithful_Compose (@quasi_inverse _ _ _ basepoint_equiv) (vertex_incl G x)
    (Equivalence_Inverse_Faithful basepoint_equiv)
    (vertex_incl_Faithful G x).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition connected_vertex_moniso :
  MonIso (vertex_group G x) (vertex_group G y) :=
  deloop_ff_moniso basepoint_compare
    basepoint_compare_Full basepoint_compare_Faithful.

End ConnectedVertex.

(** ** The hypotheses are satisfiable, and the derivation runs *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example Bool_Wide_objects_distinct : (true : Bool_Wide) = false → False.
Proof. discriminate. Qed.

Example Bool_Wide_vertex_monoid_false :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid false) = grp_monoid Bool_Xor_Grp
  := eq_refl.

Example Bool_Wide_vertex_inv_false :
  @grp_inv (vertex_group Bool_Wide_IsGroupoid false) = @grp_inv Bool_Xor_Grp
  := eq_refl.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Bool_Wide_vertex_groups_agree :
  grp_monoid (vertex_group Bool_Wide_IsGroupoid true)
    = grp_monoid (vertex_group Bool_Wide_IsGroupoid false) := eq_refl.

(*
   本节说明 Basepoint 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Bool_Wide_vertex_moniso_trivial :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  @Build_MonIso _ _
    (@Build_MonHom (vertex_group Bool_Wide_IsGroupoid true)
                   (vertex_group Bool_Wide_IsGroupoid false)
       (fun a => a) (fun _ _ H => H) (reflexivity _) (fun a b => reflexivity _))
    (@Build_MonHom (vertex_group Bool_Wide_IsGroupoid false)
                   (vertex_group Bool_Wide_IsGroupoid true)
       (fun a => a) (fun _ _ H => H) (reflexivity _) (fun a b => reflexivity _))
    (fun b => reflexivity b) (fun a => reflexivity a).

Definition Bool_Wide_vertex_moniso :
  MonIso (vertex_group Bool_Wide_IsGroupoid true)
         (vertex_group Bool_Wide_IsGroupoid false) :=
  connected_vertex_moniso Bool_Wide_IsGroupoid Bool_Wide_Connected true false.
