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

(** * 边界探针：基变换伴随 Σ_f ⊣ f* *)

(*
   本文件为测试：ProbeBaseChange387。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* Instrument check: a name that cannot exist. *)
Fail Check probe_base_change_387_no_such_name.

(* ===================================================================== *)
(* * ** (A) Conversion boundaries, over abstract base 范畴 （已译） *)

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

(* Control: class's unit IS transpose slice 恒等, on
 nose. （已译） *)
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

(* 相关说明。 （已译） *)
Check (bang_star_unit_is_unit pullbacks f).

(* Control: class's counit projection one residual
 恒等, what ε := ⌈id⌉ produces. （已译） *)
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

(* Negative 3 (CONVERSION): nor at level whole slice
 态射, where commuting witnesses differ well. （已译） *)
Fail Example neg_counit_record (p : C) (k : p ~> b) :
  @counit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor pullbacks f) (Base_Functor_Adjunction pullbacks f)
    (p; k)
  = bang_star_counit pullbacks f p k := eq_refl.

(* 相关说明。 （已译） *)
Check (Star_Functor pullbacks f ⊣ Bang_Functor f).

End Abstract.

(* ===================================================================== *)
(* 相关说明。 （已译） *)

Section Universes.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : Cu).

(* Controls at the very same declared levels. *)
Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@Functor Cu Cu).

(* Controls naming, outside any rejected command, every 常值 the
 negatives below name -- without these rename would leave those
 negatives green wrong reason. （已译） *)
Check @Slice.
Check @Pullback.
Check @Adjunction.

(* Negative 4 (FORMABILITY): headline not formable hom and
 证明 declared apart. （已译） *)
Fail Check (@Base_Functor_Adjunction Cu).

(* Negatives 5-7 (FORMABILITY): three donors, each rejected alone.
   [Functor] above is accepted at the same levels, so it is not one. *)
Fail Check (@Slice Cu xu).
Fail Check (@Pullback Cu).
Fail Check (@Adjunction Cu Cu).

End Universes.

(* ===================================================================== *)
(* * ** (E) Discharging 假设 at Sets （已译） *)

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(* The transpose COMPUTES: at point singleton it pair
 ⟨the given 态射, structure map⟩ inside agreement
 sub-setoid Instance/Sets/Pullback.v. （已译） *)
Example sets_transpose_fst :
  fst (`1 ((`1 sets_transpose) ttt)) = true := eq_refl.

Example sets_transpose_snd :
  snd (`1 ((`1 sets_transpose) ttt)) = ttt := eq_refl.

(* 相关说明。 （已译） *)
Definition sets_untranspose :
  Bang_Functor sets_pick sets_x ~{@Slice Sets sets_bool}~> sets_y :=
  from (@adj (@Slice Sets sets_bool) (@Slice Sets sets_one)
          (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
          (Sets_Base_Functor_Adjunction sets_pick) sets_x sets_y)
       sets_transpose.

Example sets_untranspose_computes :
  (`1 sets_untranspose) ttt = true := eq_refl.

(* Base change along point [true] genuinely cuts 恒等 对象
 over bool down fibre over true: every element f* (bool; id)
 has [true] first coordinate. （已译） *)
Lemma sets_star_is_fibre
      (e : carrier (`1 (Star_Functor sets_pullbacks sets_pick sets_y))) :
  fst (`1 e) = true.
Proof. exact (`2 e). Qed.

Definition sets_fibre_pt :
  carrier (`1 (Star_Functor sets_pullbacks sets_pick sets_y)) :=
  ((true, ttt); eq_refl).

(* 相关说明。 （已译） *)
Example sets_counit_computes :
  (`1 (@counit (@Slice Sets sets_bool) (@Slice Sets sets_one)
         (Bang_Functor sets_pick) (Star_Functor sets_pullbacks sets_pick)
         (Sets_Base_Functor_Adjunction sets_pick) sets_y)) sets_fibre_pt
  = true := eq_refl.

(* And so does unit at (1; id), whose value comparison the
 singleton 进入 pullback. （已译） *)
Example sets_unit_computes :
  fst (`1 ((`1 (@unit (@Slice Sets sets_bool) (@Slice Sets sets_one)
                  (Bang_Functor sets_pick)
                  (Star_Functor sets_pullbacks sets_pick)
                  (Sets_Base_Functor_Adjunction sets_pick) sets_x)) ttt))
  = ttt := eq_refl.

(* ===================================================================== *)
(* 相关说明。 （已译） *)

Definition sets_empty : Sets :=
  {| carrier := False; is_setoid := eq_Setoid False |}.

Program Definition sets_bang : sets_empty ~{Sets}~> sets_one := {|
  morphism := fun x => False_rect poly_unit x
|}.

(* Negative 8 (TYPING): delivered 伴随 not reversed
 type. A plain mismatch -- no universe clause. （已译） *)
Fail Definition neg_wrong_orientation :
  Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang :=
  Base_Functor_Adjunction sets_pullbacks sets_bang.

(* 相关说明。 （已译） *)
Check (Base_Functor_Adjunction sets_pullbacks sets_bang).
Check (Star_Functor sets_pullbacks sets_bang ⊣ Bang_Functor sets_bang).

Definition rev_x : @Slice Sets sets_one :=
  existT (fun o : obj[Sets] => o ~{Sets}~> sets_one) sets_one id.

(*
   本节说明 ProbeBaseChange387 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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
