Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Slice.Pullback.
Require Import Category.Instance.Sets.Pullback.

Generalizable All Variables.

(** * Boundary probe for the base change adjunction Σ_f ⊣ f* *)

(*
   本文件为测试：ProbeBaseChange387。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Instrument check: a name that cannot exist. *)
Fail Check probe_base_change_387_no_such_name.

(* ===================================================================== *)
(** ** (A) Conversion boundaries, over an abstract base category         *)

Section Abstract.

Context `{C : Category}.
Context (pullbacks : ∀ (X Y Z : C) (f : Y ~> Z) (g : X ~> Z), Pullback f g).
Context `(f : a ~> b).

(* Controls: every constant the negatives below name, outside any
   rejected command. *)
Check @Bang_Functor.
Check @Star_Functor.
Check @Base_Functor_Adjunction.
Check @base_to_mor.
Check @bang_star_unit.
Check @bang_star_unit_mor.
Check @bang_star_counit.
Check @bang_star_counit_mor.
Check @unit.
Check @counit.
Check (Base_Functor_Adjunction pullbacks f).
Check (Bang_Functor f ⊣ Star_Functor pullbacks f).

(* Control: the class's unit IS the transpose of the slice identity, on
   the nose. *)
Example ctrl_unit_strict (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (o; h))
  = base_to_mor pullbacks f (id[Bang_Functor f (o; h)]) := eq_refl.

(* Negative 1 (CONVERSION): against the named mediator it is only ≈. *)
Fail Example neg_unit_strict (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (o; h))
  = bang_star_unit_mor pullbacks f o h := eq_refl.

(* Control for negative 1: the ≈ statement does hold. *)
Check (bang_star_unit_is_unit pullbacks f).

(* Control: the class's counit is the projection with one residual
   identity, which is what ε := ⌈id⌉ produces. *)
Example ctrl_counit_strict (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (p; k))
  = bang_star_counit_mor pullbacks f p k ∘ id := eq_refl.

(* Negative 2 (CONVERSION): the residue cannot be removed by conversion. *)
Fail Example neg_counit_strict (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
        (p; k))
  = bang_star_counit_mor pullbacks f p k := eq_refl.

(* Control for negative 2. *)
Check (bang_star_counit_is_counit pullbacks f).

(* Negative 3 (CONVERSION): nor at the level of the whole slice
   morphism, where the commuting witnesses differ as well. *)
Fail Example neg_counit_record (p : C) (k : p ~> b) :
  @counit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
    (p; k)
  = bang_star_counit pullbacks f p k := eq_refl.

(* (D), first half: the reversed orientation is FORMABLE.  It is a
   statement, not a type error -- which is exactly why the deleted stub
   could be written down at all. *)
Check (Star_Functor pullbacks f ⊣ Bang_Functor f).

End Abstract.

(* ===================================================================== *)
(** ** (C) The universe identification, and its donors                   *)

Section Universes.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : Cu).

(* Controls at the very same declared levels. *)
Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@Functor Cu Cu).

(* Controls naming, outside any rejected command, every constant the
   negatives below name -- without these a rename would leave those
   negatives green for the wrong reason. *)
Check @Slice.
Check @Pullback.
Check @Adjunction.

(* Negative 4 (FORMABILITY): the headline is not formable when hom and
   proof are declared apart. *)
Fail Check (@Base_Functor_Adjunction Cu).

(* Negatives 5-7 (FORMABILITY): three donors, each rejected alone.
   [Functor] above is accepted at the same levels, so it is not one. *)
Fail Check (@Slice Cu xu).
Fail Check (@Pullback Cu).
Fail Check (@Adjunction Cu Cu).

End Universes.

(* ===================================================================== *)
(** ** (E) Discharging the hypothesis at Sets                            *)

(* Instance/Sets/Pullback.v's [Sets_HasPullbacks] supplies the target's
   section hypothesis directly; the issue's appended note that Sets has
   no pullback instance is stale.  This lives here rather than in the
   target because requiring Instance/Sets/Pullback there would take that
   file's transitive dependency closure from 27 modules to 44. *)
Definition sets_pullbacks (X Y Z : Sets)
      (u : Y ~{Sets}~> Z) (v : X ~{Sets}~> Z) : Pullback u v :=
  @pullback Sets Sets_HasPullbacks _ _ _ u v.

Definition Sets_Base_Functor_Adjunction {a b : Sets} (f : a ~{Sets}~> b) :
  Bang_Functor f ⊣ Star_Functor sets_pullbacks f :=
  Base_Functor_Adjunction sets_pullbacks f.

Definition sets_one : Sets :=
  {| carrier := poly_unit; is_setoid := unit_setoid |}.

Definition sets_bool : Sets :=
  {| carrier := bool; is_setoid := eq_Setoid bool |}.

Program Definition sets_pick : sets_one ~{Sets}~> sets_bool := {|
  morphism := fun _ => true
|}.

Definition sets_x : @Slice Sets sets_one :=
  existT (fun o : obj[Sets] => o ~{Sets}~> sets_one) sets_one id.

Definition sets_y : @Slice Sets sets_bool :=
  existT (fun o : obj[Sets] => o ~{Sets}~> sets_bool) sets_bool id.

Program Definition sets_g :
  Bang_Functor sets_pick sets_x ~{@Slice Sets sets_bool}~> sets_y :=
  (sets_pick; _).

Definition sets_transpose :
  sets_x ~{@Slice Sets sets_one}~>
    Star_Functor sets_pullbacks sets_pick sets_y :=
  to (@adj (@Slice Sets sets_bool) (@Slice Sets sets_one)
        (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
        (Sets_Base_Functor_Adjunction sets_pick) sets_x sets_y) sets_g.

(* The transpose COMPUTES: at the point of the singleton it is the pair
   ⟨the given morphism, the structure map⟩ inside the agreement
   sub-setoid of Instance/Sets/Pullback.v. *)
Example sets_transpose_fst :
  fst (`1 ((`1 sets_transpose) ttt)) = true := eq_refl.

Example sets_transpose_snd :
  snd (`1 ((`1 sets_transpose) ttt)) = ttt := eq_refl.

(* And so does the backward transpose, which reads the first coordinate
   back off. *)
Definition sets_untranspose :
  Bang_Functor sets_pick sets_x ~{@Slice Sets sets_bool}~> sets_y :=
  from (@adj (@Slice Sets sets_bool) (@Slice Sets sets_one)
          (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
          (Sets_Base_Functor_Adjunction sets_pick) sets_x sets_y)
       sets_transpose.

Example sets_untranspose_computes :
  (`1 sets_untranspose) ttt = true := eq_refl.

(* Base change along the point [true] genuinely cuts the identity object
   over bool down to the fibre over true: every element of f* (bool; id)
   has [true] in its first coordinate. *)
Lemma sets_star_is_fibre
      (e : carrier (`1 (Star_Functor sets_pullbacks sets_pick sets_y))) :
  fst (`1 e) = true.
Proof. exact (`2 e). Qed.

Definition sets_fibre_pt :
  carrier (`1 (Star_Functor sets_pullbacks sets_pick sets_y)) :=
  ((true, ttt); eq_refl).

(* The counit at (bool; id) is the pullback projection, and it computes
   on that element. *)
Example sets_counit_computes :
  (`1 (@counit (@Slice Sets sets_bool) (@Slice Sets sets_one)
         (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
         (Sets_Base_Functor_Adjunction sets_pick) sets_y)) sets_fibre_pt
  = true := eq_refl.

(* And so does the unit at (1; id), whose value is the comparison of the
   singleton into the pullback. *)
Example sets_unit_computes :
  fst (`1 ((`1 (@unit (@Slice Sets sets_bool) (@Slice Sets sets_one)
                  (Bang_Functor sets_pick)
                  (Star_Functor sets_pullbacks sets_pick)
                  (Sets_Base_Functor_Adjunction sets_pick) sets_x)) ttt))
  = ttt := eq_refl.

(* ===================================================================== *)
(** ** (B) and (D) The reversed orientation                              *)

Definition sets_empty : Sets :=
  {| carrier := False; is_setoid := eq_Setoid False |}.

Program Definition sets_bang : sets_empty ~{Sets}~> sets_one := {|
  morphism := fun x => False_rect poly_unit x
|}.

(* Negative 8 (TYPING): the delivered adjunction is not of the reversed
   type.  A plain mismatch -- no universe clause. *)
Fail Definition neg_wrong_orientation :
  Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang :=
  Base_Functor_Adjunction sets_pullbacks sets_bang.

(* Control for negative 8: the delivered orientation. *)
Check (Base_Functor_Adjunction sets_pullbacks sets_bang).
Check (Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang).

Definition rev_x : @Slice Sets sets_one :=
  existT (fun o : obj[Sets] => o ~{Sets}~> sets_one) sets_one id.

(* The stub's orientation is well typed and REFUTED: over Sets, along
   ∅ ~> 1, base change carries every object over 1 to the empty object,
   while Σ leaves the underlying object alone, so the unit at (1; id)
   would be a map from the singleton into the empty setoid. *)
Theorem reversed_orientation_refuted :
  Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang → False.
Proof.
  intro A.
  pose proof (`1 (@unit (@Slice Sets sets_empty) (@Slice Sets sets_one)
                    (Star_Functor sets_pullbacks sets_bang)
                    (Bang_Functor sets_bang) A rev_x) ttt) as e.
  destruct e as [[u v] Hv].
  exact v.
Qed.
