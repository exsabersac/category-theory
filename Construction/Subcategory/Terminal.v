Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

Section TerminalSubcategory.

Context {C : Category}.

(*
   本文件给出终对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TerminalObjects : Subcategory C :=
  @Build_Subcategory C
    (fun c => IsTerminalObj c)          (* the terminal objects *)
    (fun _ _ _ _ _ => True)             (* full: every C-morphism is kept *)
    (fun _ _ _ _ _ _ _ _ _ _ => I)      (* closed under composition *)
    (fun _ _ => I).                     (* closed under identities *)

Notation "'TSub'" := (Sub C TerminalObjects).

Definition TerminalObjects_Full :
  Construction.Subcategory.Full C TerminalObjects := fun _ _ _ _ _ => I.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TerminalObjects_Replete : Replete C TerminalObjects :=
  fun x ox y f =>
    (IsTerminalObj_from_Terminal
       (Terminal_iso (Terminal_from_IsTerminalObj ox) y f); (I, I)).

(* Each hom-set INHABITED: target terminal, so it receives an
 arrow source, fullness lets it 进入 subcategory. （已译） *)
Definition terminal_sub_hom (a b : TSub) : a ~{TSub}~> b :=
  (@is_terminal_one C (`1 b) (`2 b) (`1 a); I).

(* ... it SINGLETON up ≈, since subcategory's hom-setoid
 compares underlying C-态射 target terminal. （已译） *)
Lemma terminal_sub_hom_unique (a b : TSub) (f g : a ~{TSub}~> b) : f ≈ g.
Proof. exact (is_terminal_unique (`2 b) (`1 f) (`1 g)). Qed.

(* The two facts packaged Lemma 1.6.16's "exactly one 态射 each
 hom-set", library's own [Unique] idiom. （已译） *)
Definition terminal_sub_hom_contractible (a b : TSub) :
  Unique (fun _ : a ~{TSub}~> b => True) :=
  {| unique_obj       := terminal_sub_hom a b
   ; unique_property  := I
   ; uniqueness       := fun v _ =>
       terminal_sub_hom_unique a b (terminal_sub_hom a b) v |}.

(* It GROUPOID: reverse arrow exists same reason, and
 both round trips arrows terminal 对象, hence identities. （已译） *)
Definition terminal_sub_IsIso {a b : TSub} (f : a ~{TSub}~> b) :
  IsIsomorphism f.
Proof.
  unshelve econstructor.
  - exact (terminal_sub_hom b a).
  - apply (terminal_sub_hom_unique b b).
  - apply (terminal_sub_hom_unique a a).
Defined.

Definition terminal_sub_iso (a b : TSub) : @Isomorphism TSub a b.
Proof.
  unshelve econstructor.
  - exact (terminal_sub_hom a b).
  - exact (terminal_sub_hom b a).
  - apply (terminal_sub_hom_unique b b).
  - apply (terminal_sub_hom_unique a a).
Defined.

(* A bundled [Terminal] structure 对象 subcategory; 这是
 what makes it non-empty, it 假设 contractibility
 statement Block E. （已译） *)
Definition terminal_sub_obj (T : @Terminal C) : TSub :=
  (@terminal_obj C T; IsTerminalObj_from_Terminal T).

End TerminalSubcategory.

Section InitialSubcategory.

Context {C : Category}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition InitialObjects : Subcategory C :=
  @Build_Subcategory C
    (fun c => IsInitialObj c)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Notation "'ISub'" := (Sub C InitialObjects).

Definition InitialObjects_Full :
  Construction.Subcategory.Full C InitialObjects := fun _ _ _ _ _ => I.

Definition InitialObjects_Replete : Replete C InitialObjects :=
  fun x ox y f =>
    (IsInitialObj_from_Initial
       (Initial_iso (Initial_from_IsInitialObj ox) y f); (I, I)).

Definition initial_sub_hom (a b : ISub) : a ~{ISub}~> b :=
  (@is_initial_zero C (`1 a) (`2 a) (`1 b); I).

Lemma initial_sub_hom_unique (a b : ISub) (f g : a ~{ISub}~> b) : f ≈ g.
Proof. exact (is_initial_unique (`2 a) (`1 f) (`1 g)). Qed.

Definition initial_sub_hom_contractible (a b : ISub) :
  Unique (fun _ : a ~{ISub}~> b => True) :=
  {| unique_obj      := initial_sub_hom a b
   ; unique_property := I
   ; uniqueness      := fun v _ =>
       initial_sub_hom_unique a b (initial_sub_hom a b) v |}.

Definition initial_sub_IsIso {a b : ISub} (f : a ~{ISub}~> b) :
  IsIsomorphism f.
Proof.
  unshelve econstructor.
  - exact (initial_sub_hom b a).
  - apply (initial_sub_hom_unique b b).
  - apply (initial_sub_hom_unique a a).
Defined.

Definition initial_sub_iso (a b : ISub) : @Isomorphism ISub a b.
Proof.
  unshelve econstructor.
  - exact (initial_sub_hom a b).
  - exact (initial_sub_hom b a).
  - apply (initial_sub_hom_unique b b).
  - apply (initial_sub_hom_unique a a).
Defined.

Definition initial_sub_obj (I0 : @Initial C) : ISub :=
  (@initial_obj C I0; IsInitialObj_from_Initial I0).

End InitialSubcategory.
