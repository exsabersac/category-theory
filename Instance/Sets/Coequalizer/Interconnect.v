Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Coequalizer.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

(*
   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Interconnect 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The circuit *)

Inductive ic_port : Set := IcP0 | IcP1 | IcP2 | IcP3 | IcP4 | IcP5.
Inductive ic_wire : Set := IcW0 | IcW1 | IcW2.
Inductive ic_terminal : Set := IcT0 | IcT1 | IcT2.

Definition IcPortSet : SetoidObject :=
  {| carrier := ic_port ; is_setoid := eq_Setoid ic_port |}.
Definition IcWireSet : SetoidObject :=
  {| carrier := ic_wire ; is_setoid := eq_Setoid ic_wire |}.
Definition IcTerminalSet : SetoidObject :=
  {| carrier := ic_terminal ; is_setoid := eq_Setoid ic_terminal |}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ic_wire_src_fun (w : ic_wire) : ic_port :=
  match w with IcW0 => IcP0 | IcW1 => IcP1 | IcW2 => IcP4 end.

Definition ic_wire_dst_fun (w : ic_wire) : ic_port :=
  match w with IcW0 => IcP1 | IcW1 => IcP2 | IcW2 => IcP5 end.

Definition ic_wire_src : IcWireSet ~{Sets}~> IcPortSet.
Proof. unshelve refine {| morphism := ic_wire_src_fun |}. Defined.

Definition ic_wire_dst : IcWireSet ~{Sets}~> IcPortSet.
Proof. unshelve refine {| morphism := ic_wire_dst_fun |}. Defined.

(* 相关说明。 （已译） *)

Definition Interconnect : SetoidObject := SetsCoeq ic_wire_src ic_wire_dst.

Definition interconnect_proj : IcPortSet ~{Sets}~> Interconnect :=
  sets_coeq_proj ic_wire_src ic_wire_dst.

(* It IS the object [Sets_HasCoequalizers] chooses, by conversion. *)
Example interconnect_is_chosen :
  `1 (@coeq Sets Sets_HasCoequalizers IcWireSet IcPortSet ic_wire_src ic_wire_dst)
    = Interconnect.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Example interconnect_proj_is_chosen :
  `1 (`2 (@coeq Sets Sets_HasCoequalizers IcWireSet IcPortSet ic_wire_src ic_wire_dst))
    = interconnect_proj.
Proof. reflexivity. Qed.

(* The carrier ic_port type nose, coequalizing map is
 恒等 function it: `≈` moved. （已译） *)
Example interconnect_carrier : carrier Interconnect = ic_port.
Proof. reflexivity. Qed.

Example interconnect_proj_at (p : ic_port) : interconnect_proj p = p.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

Definition ic_label_fun (p : ic_port) : ic_terminal :=
  match p with
  | IcP0 => IcT0 | IcP1 => IcT0 | IcP2 => IcT0
  | IcP3 => IcT1
  | IcP4 => IcT2 | IcP5 => IcT2
  end.

Definition ic_label : IcPortSet ~{Sets}~> IcTerminalSet.
Proof. unshelve refine {| morphism := ic_label_fun |}. Defined.

Example label_P0 : ic_label IcP0 = IcT0. Proof. reflexivity. Qed.
Example label_P1 : ic_label IcP1 = IcT0. Proof. reflexivity. Qed.
Example label_P2 : ic_label IcP2 = IcT0. Proof. reflexivity. Qed.
Example label_P3 : ic_label IcP3 = IcT1. Proof. reflexivity. Qed.
Example label_P4 : ic_label IcP4 = IcT2. Proof. reflexivity. Qed.
Example label_P5 : ic_label IcP5 = IcT2. Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma ic_label_coforks : ic_label ∘ ic_wire_src ≈ ic_label ∘ ic_wire_dst.
Proof. intros [ | | ]; reflexivity. Qed.

(* The terminal set has exactly three elements: three cases no
 others, three pairwise distinct. Without both halves the
 同构 below would pin no count. （已译） *)
Lemma ic_terminal_cases (t : ic_terminal) : ((t = IcT0) ∨ (t = IcT1)) ∨ (t = IcT2).
Proof. destruct t; [ left; left | left; right | right ]; reflexivity. Qed.

Lemma ic_terminal_distinct :
  ((IcT0 = IcT1 → False) ∧ (IcT0 = IcT2 → False)) ∧ (IcT1 = IcT2 → False).
Proof. repeat split; intro E; discriminate E. Qed.

(** ** The universal property, run *)

(*
   本节说明 Interconnect 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition interconnect_med : Interconnect ~{Sets}~> IcTerminalSet :=
  unique_obj
    (coeq_desc (sets_coeq_IsCoequalizer ic_wire_src ic_wire_dst) ic_label ic_label_coforks).

Example interconnect_med_at_P0 : interconnect_med IcP0 = IcT0.
Proof. reflexivity. Qed.
Example interconnect_med_at_P2 : interconnect_med IcP2 = IcT0.
Proof. reflexivity. Qed.
Example interconnect_med_at_P3 : interconnect_med IcP3 = IcT1.
Proof. reflexivity. Qed.
Example interconnect_med_at_P5 : interconnect_med IcP5 = IcT2.
Proof. reflexivity. Qed.

(*
   本节说明 Interconnect 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example interconnect_med_is_label (p : ic_port) : interconnect_med p = ic_label p.
Proof. reflexivity. Qed.

Example interconnect_triangle : interconnect_med ∘ interconnect_proj ≈ ic_label.
Proof. intro p; reflexivity. Qed.

(* 相关说明。 （已译） *)

(* Directly joined by a wire. *)
Lemma port_P0_P1_merged : @equiv _ Interconnect IcP0 IcP1.
Proof. exact (cq_glue ic_wire_src ic_wire_dst IcW0). Qed.

Lemma port_P4_P5_merged : @equiv _ Interconnect IcP4 IcP5.
Proof. exact (cq_glue ic_wire_src ic_wire_dst IcW2). Qed.

(* Joined through third port: 这是 where transitivity the
 generated 关系 does work, it DERIVATION, not a
 computation. （已译） *)
Lemma port_P0_P2_merged : @equiv _ Interconnect IcP0 IcP2.
Proof.
  exact (cq_trans ic_wire_src ic_wire_dst IcP0 IcP1 IcP2
           (cq_glue ic_wire_src ic_wire_dst IcW0) (cq_glue ic_wire_src ic_wire_dst IcW1)).
Qed.

(** ** What it does not join *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma interconnect_apart (p q : ic_port) (H : ic_label_fun p = ic_label_fun q → False) :
  @equiv _ Interconnect p q → False.
Proof.
  intro Hpq.
  exact (H (@proper_morphism _ _ _ _ interconnect_med p q Hpq)).
Qed.

Lemma port_P0_P3_apart : @equiv _ Interconnect IcP0 IcP3 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

Lemma port_P0_P4_apart : @equiv _ Interconnect IcP0 IcP4 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

Lemma port_P3_P4_apart : @equiv _ Interconnect IcP3 IcP4 → False.
Proof. apply interconnect_apart; intro E; discriminate E. Qed.

(** ** The count, as an isomorphism *)

(* A chosen port in each group. *)
Definition ic_rep_fun (t : ic_terminal) : ic_port :=
  match t with IcT0 => IcP0 | IcT1 => IcP3 | IcT2 => IcP4 end.

(*
   本节说明 Interconnect 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ic_rep : IcTerminalSet ~{Sets}~> Interconnect.
Proof.
  unshelve refine
    (@Build_SetoidMorphism ic_terminal (is_setoid IcTerminalSet)
       ic_port (is_setoid Interconnect) ic_rep_fun _).
Defined.

(* One leg computes: labelling a chosen representative returns its own
   terminal, for all three, by [eq_refl]. *)
Lemma ic_label_of_rep (t : ic_terminal) : ic_label_fun (ic_rep_fun t) = t.
Proof. destruct t; reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma ic_rep_of_label (p : ic_port) : @equiv _ Interconnect (ic_rep_fun (ic_label_fun p)) p.
Proof.
  destruct p.
  - apply coeq_rel_refl.
  - exact port_P0_P1_merged.
  - exact port_P0_P2_merged.
  - apply coeq_rel_refl.
  - apply coeq_rel_refl.
  - exact port_P4_P5_merged.
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition interconnect_iso : @Isomorphism Sets Interconnect IcTerminalSet.
Proof.
  unshelve refine {| to := interconnect_med ; from := ic_rep |}.
  - intro t; exact (ic_label_of_rep t).
  - intro p; exact (ic_rep_of_label p).
Defined.

(* Both legs read off, by conversion. *)
Example interconnect_iso_to (p : ic_port) : to interconnect_iso p = ic_label_fun p.
Proof. reflexivity. Qed.

Example interconnect_iso_from (t : ic_terminal) : from interconnect_iso t = ic_rep_fun t.
Proof. reflexivity. Qed.

(* The 同构 not vacuous either direction: it identifies
 three ports same terminal separates ports different
 groups. （已译） *)
Example interconnect_iso_groups :
  ((to interconnect_iso IcP0 = IcT0) ∧ (to interconnect_iso IcP2 = IcT0))
    ∧ (to interconnect_iso IcP3 = IcT1).
Proof. repeat split; reflexivity. Qed.
