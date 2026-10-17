Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Structure.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Connected.Components.

Generalizable All Variables.

(*
   本文件为测试：ProbeConnected352。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 ProbeConnected352 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Fail Check Category.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Conversion.
Context {C D E : Category}.

(* NEGATIVE 1.  Stripped, this reports:
     The term "eq_refl" has type "zigzag_fmap Id[C] s = zigzag_fmap Id[C] s"
     while it is expected to have type "zigzag_fmap Id[C] s = s"
     (cannot unify "zigzag_fmap Id[C] s" and "s").（标题）（已译） *)
Fail Definition probe_fmap_id_variable (x y : C) (s : ZigZag x y) :
  zigzag_fmap Id[C] s = s := eq_refl.

(* 相关说明。 （已译） *)
Definition probe_fmap_id_nil (x : C) :
  zigzag_fmap Id[C] (zz_nil x) = zz_nil x := eq_refl.

(* 相关说明。 （已译） *)
Fail Definition probe_fmap_comp_variable (F : C ⟶ D) (G : D ⟶ E)
  (x y : C) (s : ZigZag x y) :
  zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s) := eq_refl.

(* CONTROL 2: at the empty chain it closes. *)
Definition probe_fmap_comp_nil (F : C ⟶ D) (G : D ⟶ E) (x : C) :
  zigzag_fmap (G ◯ F) (zz_nil x) = zigzag_fmap G (zigzag_fmap F (zz_nil x))
  := eq_refl.

(* 相关说明。 （已译） *)
Check @zigzag_fmap.
Check @zigzag_fmap_id.
Check @zigzag_fmap_compose.
Check @ZigZag.
Check @zz_nil.

End Conversion.

(*
   本节说明 ProbeConnected352 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Typing.
Universes o so hc hd.
Context {C : Category@{o hc hc}} {D : Category@{o hd hd}} (F : C ⟶ D).

(*
   本节说明 ProbeConnected352 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_proper_as_field :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D :=
  {| morphism := fobj[F]; proper_morphism := @zigzag_fmap C D F |}.

(* CONTROL 3a: the LITERAL rejected term, supplied by a one-step script. *)
Definition probe_proper_literal :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof using C D F.
  unshelve refine {| morphism := fobj[F] |}.
  exact (@zigzag_fmap C D F).
Defined.

(* 相关说明。 （已译） *)
Definition probe_proper_by_script :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof using C D F.
  unshelve refine {| morphism := fobj[F] |}.
  intros x y s; exact (zigzag_fmap F s).
Defined.

End Typing.

(*
   本节说明 ProbeConnected352 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check @proper_morphism.

Check @pi0.
Check @pi0_fmap.
Check @pi0_fmap_at.

(*
   本节说明 ProbeConnected352 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* An unannotated clone of [zigzag_fmap]. *)
Fixpoint probe_zigzag_fmap_unann {C D : Category} (F : C ⟶ D) {x y : C}
  (s : ZigZag x y) : ZigZag (F x) (F y) :=
  match s in ZigZag a b return ZigZag (F a) (F b) with
  | zz_nil w    => zz_nil (F w)
  | zz_fwd f s' => zz_fwd (fmap[F] f) (probe_zigzag_fmap_unann F s')
  | zz_bwd f s' => zz_bwd (fmap[F] f) (probe_zigzag_fmap_unann F s')
  end.

(* Unannotated clones of the [pi0_proj] chain. *)
Definition probe_ObjSetoid_unann (C : Category) : SetoidObject :=
  {| carrier   := obj[C]
   ; is_setoid := {| equiv        := @eq obj[C]
                   ; setoid_equiv := @eq_equivalence obj[C] |} |}.

Definition probe_coarser_unann (C : Category) :
  SetoidCoarser (A:=probe_ObjSetoid_unann C) (@ZigZag C) :=
  fun x y (e : x = y) =>
    match e in _ = z return ZigZag x z with eq_refl => zz_nil x end.

Definition probe_pi0_unann (C : Category) : SetoidObject :=
  SetsQuotient (probe_ObjSetoid_unann C) (@ZigZag C) (zigzag_Equivalence C).

Definition probe_pi0_proj_unann (C : Category) :
  probe_ObjSetoid_unann C ~{Sets}~> probe_pi0_unann C :=
  sets_quot_proj (probe_ObjSetoid_unann C) (@ZigZag C)
    (zigzag_Equivalence C) (probe_coarser_unann C).

Section FormabilityHom.
Universes uo uhc uhd.
Constraint uhc < uhd.
Context (Cu : Category@{uo uhc uhc}) (Du : Category@{uo uhd uhd}).
Context (Fu : Cu ⟶ Du) (a b : Cu) (s : ZigZag a b).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check Cu.
Check Du.
Check Fu.
Check s.

(* CONTROL 5: the SHIPPED, annotated [zigzag_fmap] applies across them. *)
Check (zigzag_fmap Fu s).

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (probe_zigzag_fmap_unann Fu s).

End FormabilityHom.

Section FormabilityObj.
Universes vo vh.
Constraint vh < vo.
Context (Cv : Category@{vo vh vh}).

(* CONTROLS at a category whose homs sit STRICTLY BELOW its objects. *)
Check Cv.
Check (obj[Cv]).

(* 相关说明。 （已译） *)
Check (pi0_proj Cv).

(*
   本节说明 ProbeConnected352 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (probe_pi0_proj_unann Cv).

End FormabilityObj.

(* 相关说明。 （已译） *)
Check @pi0_proj.
Check @pi0_proj_at.
Check @ObjSetoid.
Check @pi0_coarser.
Check @zigzag_Equivalence.
Check @sets_quot_proj.
Check @SetsQuotient.
Check @SetoidCoarser.

(* 相关说明。 （已译） *)
Check @Connected.
Check @ConnectedNonempty.
Check @Zero_Connected.
Check @Zero_not_ConnectedNonempty.
Check @connected_readings_differ.
Check @connected_iff_pi0_subsingleton.
Check @ConnectedComponent.
Check @Component_Incl.
Check @Component_Connected.
Check @Component_reindex_equiv.
Check @eso_connected.
Check @equivalence_connected.
Check @image_connected_not_connected.
Check @DiscreteCat_bool_not_connected.
Check @Parallel_Connected.
Check @Pi0.

(* 相关说明。 （已译） *)
Check @ConnectedDiagram.
Check @ConnectedNonemptyDiagram.
Check @connected_diagram_of_nonempty.
Check @connected_diagram_reindex.
Check @connected_diagram_pi0.
Check @pi0_connected_diagram.
Check @Parallel_ConnectedDiagram.
Check @bool_diagram_not_connected.
