(** * Cat has set-indexed coproducts *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Instance.Cat.
Require Category.Instance.StrictCat.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := program_simpl.

(*
 Book:      Riehl, "Category Theory in Context", 2nd ed., §3.6 —

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The indexed coproduct in Cat *)

(* 相关说明。 （已译） *)
Definition SigmaCat_IsIndexedCoproduct {I : Type} (C : I → Cat) :
  IsIndexedCoproduct C (SigmaCat C) (SigmaCat_inj C) :=
  Build_IsIndexedCoproduct C (SigmaCat C) (SigmaCat_inj C)
    (fun D F => SigmaCat_ump F).

#[export]
Instance Cat_HasIndexedCoproducts : @HasIndexedCoproducts Cat :=
  Build_HasIndexedCoproducts
    (fun A C => SigmaCat C)
    (fun A C a => SigmaCat_inj C a)
    (fun A C => SigmaCat_IsIndexedCoproduct C).

(* 相关说明。 （已译） *)

(* The terminal 范畴's homs do not depend endpoints, so
 inhabitation 假设 [sigma_inj_Full_forces_UIP] is
 discharged [ttt]. （已译） *)
Theorem inj_Full_forces_UIP_at_One {I : Type} (i : I)
  (H : Full (SigmaCat_inj (fun _ : I => _1) i)) :
  ∀ e : i = i, e = eq_refl.
Proof.
  exact (sigma_inj_Full_forces_UIP (fun _ : I => _1) i ttt (fun _ => ttt) H).
Qed.

(** ** The singleton index *)

Program Definition SigmaCat_unit_iso (D : Category) :
  SigmaCat (fun _ : poly_unit => D) ≅[Cat] D := {|
  to := SigmaCat_unit_collapse;
  from := SigmaCat_unit_expand;
  iso_to_from := SigmaCat_unit_round_l;
  iso_from_to := SigmaCat_unit_round_r
|}.

(* 相关说明。 （已译） *)

Definition BoolFam (C D : Category) (b : bool) : Category :=
  if b then C else D.

(* Across summands the hom is empty. *)
Lemma bool_cross_empty_lr (C D : Category) (x : C) (y : D) :
  ((true; x) ~{SigmaCat (BoolFam C D)}~> (false; y)) → False.
Proof. apply sigma_hom_cross_empty; simpl; discriminate. Qed.

Lemma bool_cross_empty_rl (C D : Category) (x : D) (y : C) :
  ((false; x) ~{SigmaCat (BoolFam C D)}~> (true; y)) → False.
Proof. apply sigma_hom_cross_empty; simpl; discriminate. Qed.

(* …so 对象 different summands not isomorphic: summands
 not merged. （已译） *)
Lemma bool_summands_not_isomorphic (C D : Category) (x : C) (y : D) :
  @Isomorphism (SigmaCat (BoolFam C D)) (true; x) (false; y) → False.
Proof. intros iso; exact (bool_cross_empty_lr C D x y (to iso)). Qed.

(* The case 函子 genuinely does case analysis: over two-对象
 family it takes two summands two DIFFERENT 对象 the
 target, computation. （已译） *)
Program Definition PointX : _1 ⟶ _2 := {|
  fobj := fun _ => TwoX;
  fmap := fun _ _ _ => id
|}.

Program Definition PointY : _1 ⟶ _2 := {|
  fobj := fun _ => TwoY;
  fmap := fun _ _ _ => id
|}.

Definition TwoPointFuns (b : bool) : BoolFam _1 _1 b ⟶ _2 :=
  if b as b0 return (BoolFam _1 _1 b0 ⟶ _2) then PointX else PointY.

Example case_at_true :
  SigmaCat_case TwoPointFuns (true; ttt) = TwoX := eq_refl.

Example case_at_false :
  SigmaCat_case TwoPointFuns (false; ttt) = TwoY := eq_refl.

Lemma case_separates_summands :
  fobj[SigmaCat_case TwoPointFuns] (true; ttt)
    ≠ fobj[SigmaCat_case TwoPointFuns] (false; ttt).
Proof. discriminate. Qed.

(* 相关说明。 （已译） *)

(* The 对象 arrow actions comparison, factored out so that
 [bool] case analysis happens once. （已译） *)
Definition bool_to_obj (C D : Category) (b : bool) :
  BoolFam C D b → obj[C ∐ D] :=
  match b as b0 return BoolFam C D b0 → obj[C ∐ D] with
  | true => Datatypes.inl
  | false => Datatypes.inr
  end.

Definition bool_to_map (C D : Category) (b : bool) (x y : BoolFam C D b)
  (f : x ~> y) : bool_to_obj C D b x ~> bool_to_obj C D b y :=
  (match b as b0 return
     ∀ x0 y0 : BoolFam C D b0, (x0 ~> y0) →
       (bool_to_obj C D b0 x0 ~> bool_to_obj C D b0 y0)
   with
   | true => fun _ _ h => h
   | false => fun _ _ h => h
   end) x y f.

Definition sb_map (C D : Category)
  {X Y : sigma_obj (BoolFam C D)} (f : sigma_hom X Y) :
  bool_to_obj C D (`1 X) (`2 X) ~> bool_to_obj C D (`1 Y) (`2 Y) :=
  (match `1 f as e0 in _ = m return
     ∀ y0 : BoolFam C D m, (ob_cast (BoolFam C D) e0 (`2 X) ~> y0) →
       (bool_to_obj C D (`1 X) (`2 X) ~> bool_to_obj C D m y0)
   with
   | eq_refl => fun y0 h => bool_to_map C D (`1 X) (`2 X) y0 h
   end) (`2 Y) (`2 f).

#[local] Obligation Tactic := idtac.

Program Definition SigmaBool_to (C D : Category) :
  SigmaCat (BoolFam C D) ⟶ C ∐ D := {|
  fobj := fun X => bool_to_obj C D (`1 X) (`2 X);
  fmap := fun X Y f => sb_map C D f
|}.
Next Obligation.
  intros C D [b x] [c y]; simpl.
  intros [e1 f] [e2 g] [p Hp]; simpl in *.
  destruct p; simpl in *.
  destruct e1; simpl in *.
  destruct b; simpl in *; exact Hp.
Qed.
Next Obligation.
  intros C D [b x]; destruct b; simpl; reflexivity.
Qed.
Next Obligation.
  intros C D [b x] [c y] [d z] [e1 f] [e2 g]; simpl in *.
  destruct e1, e2; simpl in *.
  destruct b; simpl; reflexivity.
Qed.

Definition sb_from_obj (C D : Category) (x : obj[C] + obj[D]) :
  sigma_obj (BoolFam C D) :=
  match x with
  | Datatypes.inl c => (true; c)
  | Datatypes.inr d => (false; d)
  end.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sb_from_map (C D : Category) (x y : obj[C] + obj[D])
  (f : x ~{C ∐ D}~> y) :
  sigma_hom (sb_from_obj C D x) (sb_from_obj C D y) :=
  (match x as x0 return
     ∀ f0 : x0 ~{C ∐ D}~> y,
       sigma_hom (sb_from_obj C D x0) (sb_from_obj C D y)
   with
   | Datatypes.inl c =>
     (match y as y0 return
        ∀ f0 : Datatypes.inl c ~{C ∐ D}~> y0,
          sigma_hom (sb_from_obj C D (Datatypes.inl c))
                    (sb_from_obj C D y0)
      with
      | Datatypes.inl c' => fun f0 => (eq_refl; f0)
      | Datatypes.inr d' => fun f0 => False_rect _ f0
      end)
   | Datatypes.inr d =>
     (match y as y0 return
        ∀ f0 : Datatypes.inr d ~{C ∐ D}~> y0,
          sigma_hom (sb_from_obj C D (Datatypes.inr d))
                    (sb_from_obj C D y0)
      with
      | Datatypes.inl c' => fun f0 => False_rect _ f0
      | Datatypes.inr d' => fun f0 => (eq_refl; f0)
      end)
   end) f.

Program Definition SigmaBool_from (C D : Category) :
  C ∐ D ⟶ SigmaCat (BoolFam C D) := {|
  fobj := sb_from_obj C D;
  fmap := sb_from_map C D
|}.
Next Obligation.
  intros C D x y f g H.
  destruct x, y; simpl in *; try contradiction;
  exists eq_refl; exact H.
Qed.
Next Obligation.
  intros C D x; destruct x; simpl; exists eq_refl; reflexivity.
Qed.
Next Obligation.
  intros C D x y z f g.
  destruct x, y, z; simpl in *; try contradiction;
  exists eq_refl; reflexivity.
Qed.

#[local] Obligation Tactic := program_simpl.

Lemma SigmaBool_round_to (C D : Category) :
  SigmaBool_to C D ◯ SigmaBool_from C D ≈ Id[C ∐ D].
Proof.
  unshelve eexists.
  - intros [c|d]; exact iso_id.
  - intros [c|d] [c'|d'] f; simpl in *; try contradiction;
    rewrite id_left, id_right; reflexivity.
Qed.

Lemma SigmaBool_round_from (C D : Category) :
  SigmaBool_from C D ◯ SigmaBool_to C D ≈ Id[SigmaCat (BoolFam C D)].
Proof.
  unshelve eexists.
  - intros [b x]; destruct b; exact iso_id.
  - intros [b x] [c y] [e f]; simpl in *.
    destruct e; simpl in *.
    destruct b; simpl in *; exists eq_refl; simpl;
    rewrite id_left, id_right; reflexivity.
Qed.

Program Definition SigmaBool_iso (C D : Category) :
  SigmaCat (BoolFam C D) ≅[Cat] C ∐ D := {|
  to := SigmaBool_to C D;
  from := SigmaBool_from C D;
  iso_to_from := SigmaBool_round_to C D;
  iso_from_to := SigmaBool_round_from C D
|}.

(* The comparison STRICT: both round trips hold at
 [Functor_StrictEq_Setoid], every 对象 component [eq_refl], so
 two 范畴 ISOMORPHIC not merely equivalent. （已译） *)
Lemma SigmaBool_strict_to (C D : Category) :
  @equiv _ Functor_StrictEq_Setoid
    (SigmaBool_to C D ◯ SigmaBool_from C D) (Id[C ∐ D]).
Proof.
  unshelve eexists.
  - intros [c|d]; exact eq_refl.
  - intros [c|d] [c'|d'] f; simpl in *; try contradiction; reflexivity.
Qed.

Lemma SigmaBool_strict_from (C D : Category) :
  @equiv _ Functor_StrictEq_Setoid
    (SigmaBool_from C D ◯ SigmaBool_to C D)
    (Id[SigmaCat (BoolFam C D)]).
Proof.
  unshelve eexists.
  - intros [b x]; destruct b; exact eq_refl.
  - intros [b x] [c y] [e f]; simpl in *.
    destruct e; simpl in *.
    destruct b; simpl in *; exists eq_refl; reflexivity.
Qed.

Program Definition SigmaBool_strict_iso (C D : Category) :
  SigmaCat (BoolFam C D) ≅[Category.Instance.StrictCat.StrictCat] C ∐ D
  := {|
  to := SigmaBool_to C D;
  from := SigmaBool_from C D;
  iso_to_from := SigmaBool_strict_to C D;
  iso_from_to := SigmaBool_strict_from C D
|}.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example SigmaBool_obj_strict (C D : Category) :
  obj[SigmaCat (BoolFam C D)] = obj[C ∐ D] := eq_refl.

Fail Example SigmaBool_cat_strict (C D : Category) :
  SigmaCat (BoolFam C D) = (C ∐ D) := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Smallness.
  Universe a b c d e.

  Check (fun (C : obj[Cat@{a b c d e}] → obj[Cat@{a b c d e}]) =>
           SigmaCat C).

  Fail Check (fun (C : obj[Cat@{a b c d e}] → obj[Cat@{a b c d e}]) =>
                SigmaCat_IsIndexedCoproduct C).
End Smallness.
