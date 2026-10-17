Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Slice.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cocartesian.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   Reference: Steve Awodey, "Category Theory", 2nd ed., §9.9, Exercise 6
   nLab:      https://ncatlab.org/nlab/show/under+category
   nLab:      https://ncatlab.org/nlab/show/over+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)


(* * ** Block A: coslice projection 左伴随 （已译） *)

Section CosliceAdjunction.

Context {C : Category}.
Context {CC : @Cocartesian C}.
Context (a : C).

Program Definition Coslice_Proj : @Coslice C a ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Definition Coslice_Coprod : C ⟶ @Coslice C a := {|
  fobj := fun c => (a + c; inl);
  fmap := fun _ _ f => (right f; _)
|}.
Next Obligation. symmetry; apply inl_right. Qed.
Next Obligation. proper; now rewrite X. Qed.
Next Obligation. apply right_id. Qed.
Next Obligation. apply right_comp. Qed.

Program Definition coslice_adj_to (c : C) (y : @Coslice C a) :
  {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
   ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |}
    ~{Sets}~>
  {| carrier   := c ~{C}~> Coslice_Proj y
   ; is_setoid := @homset C c (Coslice_Proj y) |} := {|
  morphism := fun h => `1 h ∘ inr
|}.

(* The exercise words arrow action "id + f"; tree spells that
 [cover id f], [right f] same 态射 redundant
 [∘ id] removed. （已译） *)
Lemma coslice_fmap_is_cover (x y : C) (f : x ~> y) :
  `1 (fmap[Coslice_Coprod] f) ≈ cover id f.
Proof.
  simpl; unfold right, cover.
  apply merge_respects; [ now rewrite id_right | reflexivity ].
Qed.

Program Definition coslice_transpose (c : C) (y : @Coslice C a)
  (k : c ~> `1 y) : Coslice_Coprod c ~{@Coslice C a}~> y := (`2 y ▽ k; _).

Program Definition coslice_adj_from (c : C) (y : @Coslice C a) :
  {| carrier   := c ~{C}~> Coslice_Proj y
   ; is_setoid := @homset C c (Coslice_Proj y) |}
    ~{Sets}~>
  {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
   ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |} := {|
  morphism := coslice_transpose c y
|}.
Next Obligation. intros k1 k2 Hk; simpl; now rewrite Hk. Qed.

Program Definition coslice_adj (c : C) (y : @Coslice C a) :
  @Isomorphism Sets
    {| carrier   := Coslice_Coprod c ~{@Coslice C a}~> y
     ; is_setoid := @homset (@Coslice C a) (Coslice_Coprod c) y |}
    {| carrier   := c ~{C}~> Coslice_Proj y
     ; is_setoid := @homset C c (Coslice_Proj y) |} := {|
  to   := coslice_adj_to c y;
  from := coslice_adj_from c y
|}.
Next Obligation.
  rewrite X, merge_comp, merge_inl_inr.
  apply id_right.
Qed.

Definition Coslice_Projection_Adjunction : Coslice_Coprod ⊣ Coslice_Proj.
Proof.
  unshelve eapply (@Build_Adjunction' (@Coslice C a) C
                     Coslice_Coprod Coslice_Proj coslice_adj).
  - intros x y z f g; simpl.
    rewrite <- !comp_assoc.
    now rewrite inr_right.
  - intros x y z f g; simpl.
    now rewrite <- !comp_assoc.
Defined.

Definition coslice_projection_unit (c : C) : c ~> a + c := inr.

Program Definition coslice_projection_counit (x : @Coslice C a) :
  Coslice_Coprod (Coslice_Proj x) ~{@Coslice C a}~> x := (`2 x ▽ id; _).

Example coslice_unit_strict (c : C) :
  @unit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction c = id ∘ coslice_projection_unit c
  := eq_refl.

Lemma coslice_unit_is_inr (c : C) :
  @unit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction c ≈ coslice_projection_unit c.
Proof. apply id_left. Qed.

Example coslice_counit_strict (x : @Coslice C a) :
  `1 (@counit (@Coslice C a) C Coslice_Coprod Coslice_Proj
        Coslice_Projection_Adjunction x) = `2 x ▽ id := eq_refl.

Lemma coslice_counit_is_merge (x : @Coslice C a) :
  @counit (@Coslice C a) C Coslice_Coprod Coslice_Proj
    Coslice_Projection_Adjunction x ≈ coslice_projection_counit x.
Proof. simpl; reflexivity. Qed.

End CosliceAdjunction.

(* * ** Block B: slice projection 右伴随 （已译） *)

Section SliceAdjunction.

Context {C : Category}.
Context {CA : @Cartesian C}.
Context (a : C).

Program Definition Slice_Proj : @Slice C a ⟶ C := {|
  fobj := fun x => `1 x;
  fmap := fun _ _ f => `1 f
|}.

Program Definition Slice_Prod : C ⟶ @Slice C a := {|
  fobj := fun x => (x × a; exr);
  fmap := fun _ _ f => (first f; _)
|}.
Next Obligation. apply exr_first. Qed.
Next Obligation. proper; now rewrite X. Qed.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(* 相关说明。 （已译） *)
Lemma slice_fmap_is_split (x y : C) (f : x ~> y) :
  `1 (fmap[Slice_Prod] f) ≈ split f id.
Proof.
  simpl; unfold first, split.
  apply fork_respects; [ reflexivity | now rewrite id_left ].
Qed.

Program Definition slice_transpose (x : @Slice C a) (y : C)
  (k : `1 x ~> y) : x ~{@Slice C a}~> Slice_Prod y := (k △ `2 x; _).

Program Definition slice_adj_to (x : @Slice C a) (y : C) :
  {| carrier   := Slice_Proj x ~{C}~> y
   ; is_setoid := @homset C (Slice_Proj x) y |}
    ~{Sets}~>
  {| carrier   := x ~{@Slice C a}~> Slice_Prod y
   ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |} := {|
  morphism := slice_transpose x y
|}.
Next Obligation. intros k1 k2 Hk; simpl; now rewrite Hk. Qed.

Program Definition slice_adj_from (x : @Slice C a) (y : C) :
  {| carrier   := x ~{@Slice C a}~> Slice_Prod y
   ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |}
    ~{Sets}~>
  {| carrier   := Slice_Proj x ~{C}~> y
   ; is_setoid := @homset C (Slice_Proj x) y |} := {|
  morphism := fun h => exl ∘ `1 h
|}.

Program Definition slice_adj (x : @Slice C a) (y : C) :
  @Isomorphism Sets
    {| carrier   := Slice_Proj x ~{C}~> y
     ; is_setoid := @homset C (Slice_Proj x) y |}
    {| carrier   := x ~{@Slice C a}~> Slice_Prod y
     ; is_setoid := @homset (@Slice C a) x (Slice_Prod y) |} := {|
  to   := slice_adj_to x y;
  from := slice_adj_from x y
|}.
Next Obligation.
  rewrite <- X, fork_comp, fork_exl_exr.
  apply id_left.
Qed.

Definition Slice_Projection_Adjunction : Slice_Proj ⊣ Slice_Prod.
Proof.
  unshelve eapply (@Build_Adjunction' C (@Slice C a)
                     Slice_Proj Slice_Prod slice_adj).
  - intros x y z f g; simpl.
    rewrite <- fork_comp.
    now rewrite (`2 g).
  - intros x y z f g; simpl.
    now rewrite first_fork.
Defined.

Program Definition slice_projection_unit (x : @Slice C a) :
  x ~{@Slice C a}~> Slice_Prod (Slice_Proj x) := (id △ `2 x; _).

Definition slice_projection_counit (y : C) :
  Slice_Proj (Slice_Prod y) ~> y := exl.

Example slice_unit_strict (x : @Slice C a) :
  `1 (@unit C (@Slice C a) Slice_Proj Slice_Prod
        Slice_Projection_Adjunction x) = id △ `2 x := eq_refl.

Lemma slice_unit_is_fork (x : @Slice C a) :
  @unit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction x ≈ slice_projection_unit x.
Proof. simpl; reflexivity. Qed.

Example slice_counit_strict (y : C) :
  @counit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction y = slice_projection_counit y ∘ id
  := eq_refl.

Lemma slice_counit_is_exl (y : C) :
  @counit C (@Slice C a) Slice_Proj Slice_Prod
    Slice_Projection_Adjunction y ≈ slice_projection_counit y.
Proof. apply id_right. Qed.

End SliceAdjunction.

(* 相关说明。 （已译） *)

Section SliceSettle.

Context {C : Category}.
Context (a : C).

Definition slice_id_obj : @Slice C a :=
  existT (fun x : C => x ~> a) a id.
Definition coslice_id_obj : @Coslice C a :=
  existT (fun x : C => a ~> x) a id.

Program Definition slice_id_IsTerminalObj :
  @IsTerminalObj (@Slice C a) slice_id_obj := fun x => {|
  unique_obj := (`2 x; _);
  unique_property := I
|}.
Next Obligation. rewrite <- X; apply id_left. Qed.

Program Definition coslice_id_IsInitialObj :
  @IsInitialObj (@Coslice C a) coslice_id_obj := fun x => {|
  unique_obj := (`2 x; _);
  unique_property := I
|}.
Next Obligation. rewrite X; apply id_right. Qed.

Lemma slice_left_adjoint_terminal (L : C ⟶ @Slice C a)
  (A : L ⊣ Slice_Proj a) : IsTerminalObj a.
Proof.
  intro c.
  unshelve econstructor.
  - exact (to (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj)
             (unique_obj (slice_id_IsTerminalObj (L c)))).
  - exact I.
  - intros v _.
    transitivity
      (to (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj)
         (from (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj) v)).
    + apply proper_morphism.
      apply (uniqueness (slice_id_IsTerminalObj (L c)) _ I).
    + apply (iso_to_from
               (@adj (@Slice C a) C L (Slice_Proj a) A c slice_id_obj) v).
Qed.

Program Definition slice_terminal_left_adjoint (H : IsTerminalObj a) :
  C ⟶ @Slice C a := {|
  fobj := fun x => (x; is_terminal_one H);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply (is_terminal_unique H). Qed.

Program Definition slice_terminal_adj (H : IsTerminalObj a)
  (x : C) (y : @Slice C a) :
  @Isomorphism Sets
    {| carrier   := slice_terminal_left_adjoint H x ~{@Slice C a}~> y
     ; is_setoid :=
         @homset (@Slice C a) (slice_terminal_left_adjoint H x) y |}
    {| carrier   := x ~{C}~> Slice_Proj a y
     ; is_setoid := @homset C x (Slice_Proj a y) |} := {|
  to   := {| morphism := fun h => `1 h |};
  from := {| morphism := fun k => (k; _) |}
|}.
Next Obligation. apply (is_terminal_unique H). Qed.

Definition slice_terminal_left_adjoint_adj (H : IsTerminalObj a) :
  slice_terminal_left_adjoint H ⊣ Slice_Proj a.
Proof.
  unshelve eapply (@Build_Adjunction' (@Slice C a) C
                     (slice_terminal_left_adjoint H) (Slice_Proj a)
                     (slice_terminal_adj H)).
  - intros x y z f g; simpl; reflexivity.
  - intros x y z f g; simpl; reflexivity.
Defined.

Theorem slice_proj_left_adjoint_iff_terminal :
  { L : C ⟶ @Slice C a & L ⊣ Slice_Proj a } ↔ IsTerminalObj a.
Proof.
  split.
  - intros [L A]; exact (slice_left_adjoint_terminal L A).
  - intro H.
    exists (slice_terminal_left_adjoint H).
    exact (slice_terminal_left_adjoint_adj H).
Defined.

Lemma coslice_right_adjoint_initial (R : C ⟶ @Coslice C a)
  (A : Coslice_Proj a ⊣ R) : IsInitialObj a.
Proof.
  intro c.
  unshelve econstructor.
  - exact (from (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c)
             (unique_obj (coslice_id_IsInitialObj (R c)))).
  - exact I.
  - intros v _.
    transitivity
      (from (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c)
         (to (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c) v)).
    + apply proper_morphism.
      apply (uniqueness (coslice_id_IsInitialObj (R c)) _ I).
    + apply (iso_from_to
               (@adj C (@Coslice C a) (Coslice_Proj a) R A coslice_id_obj c) v).
Qed.

Program Definition coslice_initial_right_adjoint (H : IsInitialObj a) :
  C ⟶ @Coslice C a := {|
  fobj := fun x => (x; is_initial_zero H);
  fmap := fun _ _ f => (f; _)
|}.
Next Obligation. apply (is_initial_unique H). Qed.

Program Definition coslice_initial_adj (H : IsInitialObj a)
  (x : @Coslice C a) (y : C) :
  @Isomorphism Sets
    {| carrier   := Coslice_Proj a x ~{C}~> y
     ; is_setoid := @homset C (Coslice_Proj a x) y |}
    {| carrier   := x ~{@Coslice C a}~> coslice_initial_right_adjoint H y
     ; is_setoid :=
         @homset (@Coslice C a) x
           (coslice_initial_right_adjoint H y) |} := {|
  to   := {| morphism := fun k => (k; _) |};
  from := {| morphism := fun h => `1 h |}
|}.
Next Obligation. apply (is_initial_unique H). Qed.

Definition coslice_initial_right_adjoint_adj (H : IsInitialObj a) :
  Coslice_Proj a ⊣ coslice_initial_right_adjoint H.
Proof.
  unshelve eapply (@Build_Adjunction' C (@Coslice C a)
                     (Coslice_Proj a) (coslice_initial_right_adjoint H)
                     (coslice_initial_adj H)).
  - intros x y z f g; simpl; reflexivity.
  - intros x y z f g; simpl; reflexivity.
Defined.

Theorem coslice_proj_right_adjoint_iff_initial :
  { R : C ⟶ @Coslice C a & Coslice_Proj a ⊣ R } ↔ IsInitialObj a.
Proof.
  split.
  - intros [R A]; exact (coslice_right_adjoint_initial R A).
  - intro H.
    exists (coslice_initial_right_adjoint H).
    exact (coslice_initial_right_adjoint_adj H).
Defined.

End SliceSettle.

(* 相关说明。 （已译） *)

Definition Sets_Coslice_Projection_Adjunction (a : Sets) :
  Coslice_Coprod a ⊣ Coslice_Proj a := Coslice_Projection_Adjunction a.

Definition Sets_Slice_Projection_Adjunction (a : Sets) :
  Slice_Proj a ⊣ Slice_Prod a := Slice_Projection_Adjunction a.

Definition sets_bipoint : Sets :=
  @Coprod Sets Sets_Cocartesian
    (@terminal_obj Sets Sets_Terminal)
    (@terminal_obj Sets Sets_Terminal).

Definition sets_bipoint_l : carrier sets_bipoint := Datatypes.inl ttt.
Definition sets_bipoint_r : carrier sets_bipoint := Datatypes.inr ttt.

Lemma sets_bipoint_distinct : sets_bipoint_l ≈ sets_bipoint_r → False.
Proof. intro H; exact H. Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_point (b : carrier sets_bipoint) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> sets_bipoint :=
  {| morphism        := fun _ => b
   ; proper_morphism := fun _ _ _ => reflexivity b |}.

Definition sets_bipoint_const (b : carrier sets_bipoint) :
  sets_bipoint ~{Sets}~> sets_bipoint :=
  {| morphism        := fun _ => b
   ; proper_morphism := fun _ _ _ => reflexivity b |}.

Lemma sets_bipoint_not_terminal : IsTerminalObj sets_bipoint → False.
Proof.
  intro H.
  exact (is_terminal_unique H (sets_point sets_bipoint_l)
           (sets_point sets_bipoint_r) ttt).
Qed.

Lemma sets_bipoint_not_initial : IsInitialObj sets_bipoint → False.
Proof.
  intro H.
  exact (is_initial_unique H id (sets_bipoint_const sets_bipoint_l)
           sets_bipoint_r).
Qed.

Theorem sets_slice_proj_no_left_adjoint :
  { L : Sets ⟶ @Slice Sets sets_bipoint & L ⊣ Slice_Proj sets_bipoint } → False.
Proof.
  intro X.
  exact (sets_bipoint_not_terminal
           (fst (slice_proj_left_adjoint_iff_terminal sets_bipoint) X)).
Qed.

Theorem sets_coslice_proj_no_right_adjoint :
  { R : Sets ⟶ @Coslice Sets sets_bipoint & Coslice_Proj sets_bipoint ⊣ R }
    → False.
Proof.
  intro X.
  exact (sets_bipoint_not_initial
           (fst (coslice_proj_right_adjoint_iff_initial sets_bipoint) X)).
Qed.

Definition sets_slice_proj_left_adjoint_at_terminal :
  { L : Sets ⟶ @Slice Sets (@terminal_obj Sets Sets_Terminal)
      & L ⊣ Slice_Proj (@terminal_obj Sets Sets_Terminal) } :=
  snd (slice_proj_left_adjoint_iff_terminal
         (@terminal_obj Sets Sets_Terminal))
    (IsTerminalObj_from_Terminal Sets_Terminal).

Definition sets_coslice_proj_right_adjoint_at_initial :
  { R : Sets ⟶ @Coslice Sets (@initial_obj Sets Sets_Initial)
      & Coslice_Proj (@initial_obj Sets Sets_Initial) ⊣ R } :=
  snd (coslice_proj_right_adjoint_iff_initial
         (@initial_obj Sets Sets_Initial))
    (IsInitialObj_from_Initial Sets_Initial).

Example sets_coslice_transpose_computes (a c : Sets)
  (y : @Coslice Sets a) (k : c ~{Sets}~> Coslice_Proj a y)
  (z : carrier c) :
  `1 (coslice_transpose a c y k) (Datatypes.inr z) = k z := eq_refl.

Example sets_slice_transpose_is_fork (a : Sets) (x : @Slice Sets a)
  (y : Sets) (k : `1 x ~{Sets}~> y) :
  `1 (slice_transpose a x y k) = k △ `2 x := eq_refl.

Example sets_slice_transpose_computes (a : Sets) (x : @Slice Sets a)
  (y : Sets) (k : `1 x ~{Sets}~> y) (z : carrier (`1 x)) :
  Datatypes.fst ((k △ `2 x) z) = k z := eq_refl.

Lemma sets_coslice_unit_not_iso (a c : Sets) (x : carrier a) :
  IsIsomorphism (@coslice_projection_unit Sets Sets_Cocartesian a c)
    → False.
Proof.
  intros [g Hr Hl].
  exact (Hr (Datatypes.inl x)).
Qed.
