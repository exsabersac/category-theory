(*
   本文件为测试：ProbeSplitFork478。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Instance.Zero.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.Terminal.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.SplitFork.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** The instrument *)

(* The instrument *)
Fail Check p478_absent_name.

(* ------------------------------------------------------------------------ *)
(** ** Law 2 at a variable object or arrow of 1 *)

Section LawTwo.

Context {C : Category}.
Context `{T : @Terminal C}.

(* C1: at the object of 1, on the nose. *)
Example p478_c1_law2_obj :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] ttt = fobj[Id[_1]] ttt
  := eq_refl.

(* R1 *)
Fail Example p478_r1_law2_obj_var (x : _1) :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] x = fobj[Id[_1]] x
  := eq_refl.

(* C2: at every object, by a case analysis. *)
Lemma p478_c2_law2_obj_cases (x : _1) :
  fobj[Erase C ◯ Diagonal _1 (@terminal_obj C T)] x = fobj[Id[_1]] x.
Proof. destruct x; reflexivity. Qed.

(* C3: at the identity arrow of 1, on the nose. *)
Example p478_c3_law2_map :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] (@id _1 ttt)
    = fmap[Id[_1]] (@id _1 ttt) := eq_refl.

(* R2 *)
Fail Example p478_r2_law2_map_var (f : ttt ~{_1}~> ttt) :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] f = fmap[Id[_1]] f
  := eq_refl.

(* C4: at every arrow, by a case analysis. *)
Lemma p478_c4_law2_map_cases (f : ttt ~{_1}~> ttt) :
  fmap[Erase C ◯ Diagonal _1 (@terminal_obj C T)] f = fmap[Id[_1]] f.
Proof. destruct f; reflexivity. Qed.

End LawTwo.

(* ------------------------------------------------------------------------ *)
(** ** The laws are not equalities of functor records *)

Section Records.

Context {C : Category}.

(* C5: law 1 on objects, on the nose. *)
Example p478_c5_law1_obj (x : @Arrow C) :
  fobj[Erase C ◯ Arrow_dom] x = fobj[Erase C ◯ Arrow_cod] x := eq_refl.

(* C6: law 1 on arrows, on the nose. *)
Example p478_c6_law1_map {x y : @Arrow C} (f : x ~> y) :
  fmap[Erase C ◯ Arrow_dom] f = fmap[Erase C ◯ Arrow_cod] f := eq_refl.

(* R3 *)
Fail Example p478_r3_law1_records :
  Erase C ◯ Arrow_dom = Erase C ◯ Arrow_cod := eq_refl.

End Records.

(* C7: law 1 in StrictCat. *)
Definition p478_c7_law1_strict@{o h +} (C : Category@{o h h}) :
  Erase C ∘[StrictCat] Arrow_dom ≈[StrictCat] Erase C ∘[StrictCat] Arrow_cod
  := arrow_fork_law1_strict C.

(* C8: law 1 in Cat. *)
Definition p478_c8_law1@{o h +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod
  := arrow_fork_law1 C.

Section RecordsSplit.

Context {C : Category}.
Context `{T : @Terminal C}.

(* R4 *)
Fail Example p478_r4_law2_records :
  Erase C ◯ Diagonal _1 (@terminal_obj C T) = Id[_1] := eq_refl.

(* C10: law 3 on objects, on the nose. *)
Example p478_c10_law3_obj (c : C) :
  fobj[Arrow_dom ◯ arrow_fork_t] c = c := eq_refl.

(* C11: law 3 on arrows, on the nose. *)
Example p478_c11_law3_map {c d : C} (f : c ~> d) :
  fmap[Arrow_dom ◯ arrow_fork_t] f = f := eq_refl.

(* R5 *)
Fail Example p478_r5_law3_records :
  Arrow_dom ◯ arrow_fork_t = Id[C] := eq_refl.

(* C13: law 4 on objects, on the nose. *)
Example p478_c13_law4_obj (c : C) :
  fobj[Arrow_cod ◯ arrow_fork_t] c = @terminal_obj C T := eq_refl.

(* C14: law 4 on arrows, on the nose. *)
Example p478_c14_law4_map {c d : C} (f : c ~> d) :
  fmap[Arrow_cod ◯ arrow_fork_t] f = @id C (@terminal_obj C T) := eq_refl.

(* R6 *)
Fail Example p478_r6_law4_records :
  Arrow_cod ◯ arrow_fork_t = Diagonal _1 (@terminal_obj C T) ◯ Erase C
  := eq_refl.

End RecordsSplit.

(* C9: law 2 in StrictCat. *)
Definition p478_c9_law2_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Erase C ∘[StrictCat] Diagonal _1 (@terminal_obj C T)
    ≈[StrictCat] @id StrictCat _1 := arrow_fork_law2_strict.

(* C12: law 3 in StrictCat. *)
Definition p478_c12_law3_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_dom ∘[StrictCat] arrow_fork_t ≈[StrictCat] @id StrictCat C
  := arrow_fork_law3_strict.

(* C15: law 4 in StrictCat. *)
Definition p478_c15_law4_strict@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  Arrow_cod ∘[StrictCat] arrow_fork_t
    ≈[StrictCat] Diagonal _1 (@terminal_obj C T) ∘[StrictCat] Erase C
  := arrow_fork_law4_strict.

(* ------------------------------------------------------------------------ *)
(** ** Universes: the fork needs h <= o *)

(* R7 *)
Fail Definition p478_r7_law1_o_lt_h@{o h + | o < h +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod
  := arrow_fork_law1 C.

(* C16: the same at h < o. *)
Definition p478_c16_law1_h_lt_o@{o h + | h < o +} (C : Category@{o h h}) :
  Erase C ∘[Cat] Arrow_dom ≈[Cat] Erase C ∘[Cat] Arrow_cod
  := arrow_fork_law1 C.

(* ------------------------------------------------------------------------ *)
(** ** Restatements of the target's readbacks *)

Section Readbacks.

Context {C : Category}.
Context `{T : @Terminal C}.

(* C17: e is Cat's terminal map. *)
Example p478_c17_e_one : Erase C = @one Cat Cat_Terminal C := eq_refl.

(* C18: e is StrictCat's terminal map. *)
Example p478_c18_e_one_strict :
  Erase C = @one StrictCat StrictCat_Terminal C := eq_refl.

(* C19: s sends the object of 1 to a₀. *)
Example p478_c19_s_obj (x : _1) :
  fobj[Diagonal _1 (@terminal_obj C T)] x = @terminal_obj C T := eq_refl.

(* C20: t sends c to the unique arrow c → a₀. *)
Example p478_c20_t_obj (c : C) :
  fobj[arrow_fork_t] c = ((c, @terminal_obj C T); @one C T c) := eq_refl.

(* C21: t sends f to the square (f, 1). *)
Example p478_c21_t_map {c d : C} (f : c ~> d) :
  `1 (fmap[arrow_fork_t] f) = (f, @id C (@terminal_obj C T)) := eq_refl.

End Readbacks.

(* C22: the split fork in Cat has e for its coequalizing arrow. *)
Example p478_c22_split_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e (@arrow_fork_split C T) = Erase C := eq_refl.

(* C23: ... s for the section of e. *)
Example p478_c23_split_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s (@arrow_fork_split C T) = Diagonal _1 (@terminal_obj C T)
  := eq_refl.

(* C24: ... and t for the section of ∂₀. *)
Example p478_c24_split_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t (@arrow_fork_split C T) = @arrow_fork_t C T := eq_refl.

(* C25: the splitting at C := Cat, whose terminal object is 1. *)
Definition p478_c25_split_at_Cat :
  @SplitCoequalizer Cat (@Arrow Cat) Cat Arrow_dom Arrow_cod :=
  @arrow_fork_split Cat Cat_Terminal.

(* C26: at the empty category, e is not a coequalizer. *)
Example p478_c26_not_coequalizer_0 :
  @IsCoequalizer Cat _ _ Arrow_dom Arrow_cod _1 (Erase _0) → False :=
  arrow_fork_not_coequalizer _0 (fun x => match x with end).

(* ------------------------------------------------------------------------ *)
(** ** The components of the two split forks in Cat *)

(* R8 *)
Fail Example p478_r8_split_law3_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (scoeq_law3 (@arrow_fork_split C T)) c) = id := eq_refl.

(* C27: the same at the direct split fork. *)
Example p478_c27_split_direct_law3_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (scoeq_law3 (@arrow_fork_split_direct C T)) c) = id := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Restatements: components, the direct split fork, the Corollary *)

(* C28: law 3 in StrictCat has the object component [eq_refl]. *)
Example p478_c28_law3_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law3_strict C T) = fun _ => eq_refl := eq_refl.

(* C29: ... and so has law 4. *)
Example p478_c29_law4_strict_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  projT1 (@arrow_fork_law4_strict C T) = fun _ => eq_refl := eq_refl.

(* C30: law 3 in Cat, directly, has identity components. *)
Example p478_c30_law3_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law3_direct C T) c) = id := eq_refl.

(* C31: ... and so has law 4. *)
Example p478_c31_law4_direct_component@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} (c : C) :
  to (projT1 (@arrow_fork_law4_direct C T) c) = id := eq_refl.

(* C32: the direct split fork has e for its coequalizing arrow. *)
Example p478_c32_split_direct_e@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_e (@arrow_fork_split_direct C T) = Erase C := eq_refl.

(* C33: ... s for the section of e. *)
Example p478_c33_split_direct_s@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_s (@arrow_fork_split_direct C T) = Diagonal _1 (@terminal_obj C T)
  := eq_refl.

(* C34: ... and t for the section of ∂₀. *)
Example p478_c34_split_direct_t@{o h +} {C : Category@{o h h}}
  `{T : @Terminal C} :
  scoeq_t (@arrow_fork_split_direct C T) = @arrow_fork_t C T := eq_refl.

(* C35: the corollary out of StrictCat is the Corollary, applied. *)
Example p478_c35_preserved_absolute_strict@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : StrictCat ⟶ D) :
  @arrow_fork_preserved_strict C T D F = @arrow_fork_absolute_strict C T D F
  := eq_refl.

(* C36: ... and so is the one out of Cat. *)
Example p478_c36_preserved_absolute@{o h do dh +}
  {C : Category@{o h h}} `{T : @Terminal C} {D : Category@{do dh dh}}
  (F : Cat ⟶ D) :
  @arrow_fork_preserved C T D F = @arrow_fork_absolute C T D F := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Guard: every constant of the target, by name *)

Check @Category.Instance.Cat.SplitFork.arrow_fork_e_one.
Check @Category.Instance.Cat.SplitFork.arrow_fork_e_one_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law1_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_s_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_t.
Check @Category.Instance.Cat.SplitFork.arrow_fork_t_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_t_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_strict_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_strict_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_obj.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_map.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_e.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_s.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_t.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law2_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law3_direct_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_law4_direct_component.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct_e.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct_s.
Check @Category.Instance.Cat.SplitFork.arrow_fork_split_direct_t.
Check @Category.Instance.Cat.SplitFork.arrow_fork_coequalizer_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_coequalizer.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved.
Check @Category.Instance.Cat.SplitFork.arrow_fork_absolute_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_absolute.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved_absolute_strict.
Check @Category.Instance.Cat.SplitFork.arrow_fork_preserved_absolute.
Check @Category.Instance.Cat.SplitFork.arrow_fork_not_coequalizer.
Check @Category.Instance.Cat.SplitFork.arrow_fork_not_coequalizer_0.
