Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Construction.Subcategory.Terminal.

Generalizable All Variables.

(*
   本文件给出终对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma terminal_transport_unique {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) (d : D)
  (f g : d ~{D}~> F (@terminal_obj C T)) : f ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  apply (monic (Monic := iso_from_monic
                  (@equivalence_unit_at C D F E (@terminal_obj C T)))).
  apply (@one_unique C T).
Qed.

(* Existence: cross the counit backwards into the image of the
   quasi-inverse, then apply F to the unique arrow G d ~> 1. *)
Definition terminal_transport_arrow {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) (d : D) :
  d ~{D}~> F (@terminal_obj C T) :=
  fmap[F] (@one C T (@quasi_inverse C D F E d))
    ∘ from (@equivalence_counit_at C D F E d).

Definition Terminal_transport {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) : @Terminal D :=
  @Build_Terminal D (F (@terminal_obj C T))
    (fun d => terminal_transport_arrow E T d)
    (fun d f g => terminal_transport_unique E T d f g).

(*
   本节说明（余）极限、等价、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma initial_transport_unique {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) (d : D)
  (f g : F (@initial_obj C I0) ~{D}~> d) : f ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  apply (epic (Epic := iso_to_epic
                 (@equivalence_unit_at C D F E (@initial_obj C I0)))).
  apply (@zero_unique C I0).
Qed.

Definition initial_transport_arrow {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) (d : D) :
  F (@initial_obj C I0) ~{D}~> d :=
  to (@equivalence_counit_at C D F E d)
    ∘ fmap[F] (@zero C I0 (@quasi_inverse C D F E d)).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Initial_transport {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) : @Initial D :=
  @Build_Terminal (D^op) (F (@initial_obj C I0))
    (fun d => initial_transport_arrow E I0 d)
    (fun d f g => initial_transport_unique E I0 d f g).

(* The transported structures choose the image of the original, on the nose. *)
Corollary Terminal_transport_obj {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (T : @Terminal C) :
  @terminal_obj D (Terminal_transport E T) = F (@terminal_obj C T).
Proof. reflexivity. Qed.

Corollary Initial_transport_obj {C D : Category} {F : C ⟶ D}
  (E : @EquivalenceOfCategories C D F) (I0 : @Initial C) :
  @initial_obj D (Initial_transport E I0) = F (@initial_obj C I0).
Proof. reflexivity. Qed.

Section TerminalSubContractible.

Context {C : Category}.

(*
   本节说明函子、hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition terminal_sub_point (T : @Terminal C) :
  _1 ⟶ Sub C TerminalObjects := {|
  fobj := fun _ => terminal_sub_obj T;
  fmap := fun _ _ _ => id
|}.

Lemma terminal_sub_counit (T : @Terminal C) :
  Erase (Sub C TerminalObjects) ◯ terminal_sub_point T ≈ Id[_1].
Proof. apply (@one_unique Cat Cat_Terminal). Qed.

Lemma terminal_sub_unit (T : @Terminal C) :
  Id[Sub C TerminalObjects]
    ≈ terminal_sub_point T ◯ Erase (Sub C TerminalObjects).
Proof.
  unshelve eexists.
  - intro a; exact (terminal_sub_iso a (terminal_sub_obj T)).
  - intros a b f; apply terminal_sub_hom_unique.
Qed.

Definition terminal_sub_contractible (T : @Terminal C) :
  EquivalenceOfCategories (Erase (Sub C TerminalObjects)) :=
  @Build_EquivalenceOfCategories (Sub C TerminalObjects) _1
    (Erase (Sub C TerminalObjects))
    (terminal_sub_point T)
    (terminal_sub_counit T)
    (terminal_sub_unit T).

End TerminalSubContractible.

Section InitialSubContractible.

Context {C : Category}.

Program Definition initial_sub_point (I0 : @Initial C) :
  _1 ⟶ Sub C InitialObjects := {|
  fobj := fun _ => initial_sub_obj I0;
  fmap := fun _ _ _ => id
|}.

Lemma initial_sub_counit (I0 : @Initial C) :
  Erase (Sub C InitialObjects) ◯ initial_sub_point I0 ≈ Id[_1].
Proof. apply (@one_unique Cat Cat_Terminal). Qed.

Lemma initial_sub_unit (I0 : @Initial C) :
  Id[Sub C InitialObjects]
    ≈ initial_sub_point I0 ◯ Erase (Sub C InitialObjects).
Proof.
  unshelve eexists.
  - intro a; exact (initial_sub_iso a (initial_sub_obj I0)).
  - intros a b f; apply initial_sub_hom_unique.
Qed.

Definition initial_sub_contractible (I0 : @Initial C) :
  EquivalenceOfCategories (Erase (Sub C InitialObjects)) :=
  @Build_EquivalenceOfCategories (Sub C InitialObjects) _1
    (Erase (Sub C InitialObjects))
    (initial_sub_point I0)
    (initial_sub_counit I0)
    (initial_sub_unit I0).

End InitialSubContractible.
