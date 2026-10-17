Require Import Coq.NArith.NArith.

Require Import Category.Lib.
Require Import Category.Lib.MapDecide.
Require Import Category.Theory.Metacategory.ArrowsOnly.

Generalizable All Variables.

Open Scope N_scope.

(** Worked examples for the arrows-only metacategory decision procedure *)

(*
 nLab: https://ncatlab.org/nlab/show/metacategory
   nLab: https://ncatlab.org/nlab/show/category

   本文件给出可判定性例子。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   Sanity check on the raw decider [formula_反向] (the Gallina 核

   本节说明相关定义、性质与动机。 behind [map_decide]), bypassing reflection wrapper. The reified formula is tautology [P -> P] one fixed [P], goal asserts that decider lands its [Proved] branch ([then True]) rather than [No]/[Uncertain] ([else False]);

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example formula_backward_example (x y z w : N) :
  if formula_backward
       (Impl (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty))
             (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty)))
       {| vars := fun p =>
           if (p =? 1)%positive then x else
           if (p =? 2)%positive then y else
           if (p =? 3)%positive then z else
           if (p =? 4)%positive then w else 9%N |}
  then True else False.
Proof. vm_compute; constructor. Qed.

(*
   本节说明相关定义、性质与动机。 Smallest end-to-end use reflective tactic [solve_map]: same. two-element map appears 假设 conclusion, so [MapsTo (x,y) f] follows trivially.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example map_decide_test  x y f :
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))) ->
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))).
Proof. solve_map. Qed.

(*
   The real content: the 结合律 coherence of [composable_pairs n].

   本节说明相关定义、性质与动机。 Following [ArrowsOnly]'s convention, [M.find (f, g) = Some fg] reads "g f compose fg" (i.e. [f ∘ g = fg]). So hypotheses say [f ∘ g = fg], [g ∘ h = gh] [fg ∘ h = fgh]; conclusion says [f ∘ gh = fgh], i.e.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example problem3 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 3 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
(*
  destruct_maps; try nomega. (* takes 1.68s *)
  Undo.
*)
  map_decide.                (* takes 0.016s *)
Qed.

(*
   Same 结合律 goal at larger n, showing how the two approaches scale.

   本节说明相关定义、性质与动机。 Brute force grows combinatorially table size (timings noted below: 30.15s at n = 4, 2501s at n = 5), while reflection stays tens milliseconds;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example problem4 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 4 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 30.15s *) *)
  (* Undo. *)
  map_decide.                (* takes 0.035s *)
Qed.

Example problem5 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 5 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 2501s *) *)
  (* Undo. *)
  map_decide.                (* takes 0.085s *)
Qed.

(*
   本节说明相关定义、性质与动机。 Largest instance exercised here. Despite name, this uses. [composable_pairs 10] (a 10-对象 table, 100 alludes roughly hundred-entry map), is only case where reflection itself takes appreciable time (2.445s);

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example problem100 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 10 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. *)
  (* Undo. *)
  map_decide.                (* takes 2.445s *)
Qed.
