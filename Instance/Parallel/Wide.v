Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * The wide walking parallel pair *)

(*
 nLab:      https://ncatlab.org/nlab/show/wide+pullback
 Wikipedia: https://en.wikipedia.org/wiki/Equaliser_(mathematics)

   本文件给出 wide 子范畴相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The shape *)

(* 相关说明。 （已译） *)
Inductive WParVoid@{i} : Type@{i} := .

(* The hom-family wide shape, computed two 对象. Note
 [WParHom I ParX ParY] reduces [I] itself. （已译） *)
Definition WParHom@{i} (I : Type@{i}) (x y : ParObj) : Type@{i} :=
  match x, y with
  | ParX, ParX => poly_unit@{i}
  | ParY, ParY => poly_unit@{i}
  | ParX, ParY => I
  | ParY, ParX => WParVoid@{i}
  end.

(* 相关说明。 （已译） *)
Lemma WParHom_Y_X_absurd@{i} {I : Type@{i}} : WParHom@{i} I ParY ParX → False.
Proof. intro e; destruct e. Qed.

Definition wpar_id@{i} {I : Type@{i}} (x : ParObj) : WParHom@{i} I x x :=
  match x with ParX => ttt | ParY => ttt end.

(* Composition forced: 恒等 either side returns other
 论元, four 对象 triples would need arrow
 ParY ~> ParX refuted empty hom-set. （已译） *)
Definition wpar_compose@{i} {I : Type@{i}} {x y z : ParObj} :
  WParHom@{i} I y z → WParHom@{i} I x y → WParHom@{i} I x z :=
  match x, y, z
    return WParHom@{i} I y z → WParHom@{i} I x y → WParHom@{i} I x z with
  | ParX, ParX, ParX => fun _ _ => ttt
  | ParX, ParX, ParY => fun f _ => f
  | ParX, ParY, ParX => fun f _ => match f with end
  | ParX, ParY, ParY => fun _ g => g
  | ParY, ParX, ParX => fun _ g => match g with end
  | ParY, ParX, ParY => fun _ g => match g with end
  | ParY, ParY, ParX => fun f _ => match f with end
  | ParY, ParY, ParY => fun _ _ => ttt
  end.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition WideParallel@{i p} (I : Type@{i}) : Category@{Set i p} := {|
  obj     := ParObj;
  hom     := WParHom@{i} I;
  homset  := fun x y =>
    {| equiv := @eq (WParHom@{i} I x y)
     ; setoid_equiv := @eq_equivalence@{i p} (WParHom@{i} I x y) |};
  id      := @wpar_id@{i} I;
  compose := @wpar_compose@{i} I
|}.
Next Obligation. destruct x, y; simpl in *; try destruct f; reflexivity. Qed.
Next Obligation. destruct x, y; simpl in *; try destruct f; reflexivity. Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  try destruct f; try destruct g; try destruct h; reflexivity.
Qed.
Next Obligation.
  destruct x, y, z, w; simpl in *;
  try destruct f; try destruct g; try destruct h; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Example wide_hom_XY (I : Type) : (ParX ~{WideParallel I}~> ParY) = I := eq_refl.
Example wide_hom_XX (I : Type) :
  (ParX ~{WideParallel I}~> ParX) = poly_unit := eq_refl.
Example wide_hom_YY (I : Type) :
  (ParY ~{WideParallel I}~> ParY) = poly_unit := eq_refl.

(* 相关说明。 （已译） *)

(* Object action: ParX ↦ x, ParY ↦ y. *)
Definition wdiag@{o h p} {C : Category@{o h p}} (x y : C) (p : ParObj) : C :=
  match p with ParX => x | ParY => y end.

(* 相关说明。 （已译） *)
Definition awide_fmap@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) {a b : ParObj} :
  WParHom@{i} I a b → wdiag@{o h p} x y a ~{C}~> wdiag@{o h p} x y b :=
  match a, b return WParHom@{i} I a b
                    → wdiag@{o h p} x y a ~{C}~> wdiag@{o h p} x y b with
  | ParX, ParX => fun _ => id[x]
  | ParY, ParY => fun _ => id[y]
  | ParX, ParY => fun i => fs i
  | ParY, ParX => fun e => match e with end
  end.

Lemma awide_fmap_id@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) (a : ParObj) :
  awide_fmap@{i o h p} fs (@wpar_id@{i} I a) ≈ id{C}.
Proof. destruct a; reflexivity. Qed.

Lemma awide_fmap_comp@{i o h p} {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) (a b c : ParObj) :
  ∀ (f : WParHom@{i} I b c) (g : WParHom@{i} I a b),
    awide_fmap@{i o h p} fs (@wpar_compose@{i} I a b c f g)
      ≈ awide_fmap@{i o h p} fs f ∘ awide_fmap@{i o h p} fs g.
Proof.
  destruct a, b, c; intros f g; simpl in *;
  try destruct f; try destruct g; cat.
Qed.

(* 相关说明。 （已译） *)
Program Definition AWide@{i k o h p}
  {I : Type@{i}} {C : Category@{o h p}} {x y : C}
  (fs : I → x ~{C}~> y) : WideParallel@{i k} I ⟶ C := {|
  fobj := wdiag@{o h p} x y;
  fmap := fun a b m => awide_fmap@{i o h p} fs m;
  fmap_id := fun a => awide_fmap_id@{i o h p} fs a;
  fmap_comp := fun a b c f g => awide_fmap_comp@{i o h p} fs a b c f g
|}.

(* 相关说明。 （已译） *)
Example awide_fmap_arr {I : Type} {C : Category} {x y : C}
  (fs : I → x ~> y) (i : I) :
  fmap[AWide fs] (i : ParX ~{WideParallel I}~> ParY) = fs i := eq_refl.

Example awide_obj_X {I : Type} {C : Category} {x y : C} (fs : I → x ~> y) :
  fobj[AWide fs] ParX = x := eq_refl.
Example awide_obj_Y {I : Type} {C : Category} {x y : C} (fs : I → x ~> y) :
  fobj[AWide fs] ParY = y := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition wide_of_par_map@{i u v} {a b : ParObj} :
  (a ~{Parallel@{u v}}~> b) → WParHom@{i} bool a b :=
  match a, b return (a ~{Parallel@{u v}}~> b) → WParHom@{i} bool a b with
  | ParX, ParX => fun _ => ttt
  | ParY, ParY => fun _ => ttt
  | ParX, ParY => fun h => ``h
  | ParY, ParX => fun h => False_rect _ (ParHom_Y_X_absurd _ (projT2 h))
  end.

Definition par_of_wide_map@{i u v} {a b : ParObj} :
  WParHom@{i} bool a b → (a ~{Parallel@{u v}}~> b) :=
  match a, b return WParHom@{i} bool a b → (a ~{Parallel@{u v}}~> b) with
  | ParX, ParX => fun _ => (true; ParIdX)
  | ParY, ParY => fun _ => (true; ParIdY)
  | ParX, ParY => fun c => if c then (true; ParOne) else (false; ParTwo)
  | ParY, ParX => fun e => match e with end
  end.

Program Definition Wide_of_Par@{i p u v} :
  Parallel@{u v} ⟶ WideParallel@{i p} bool := {|
  fobj := fun p => p;
  fmap := fun a b h => wide_of_par_map@{i u v} h
|}.
Next Obligation.
  proper.
  destruct x, y; simpl in *; try assumption; try reflexivity;
  destruct (ParHom_Y_X_absurd _ e).
Qed.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  destruct x, y, z, f, g;
  pose proof (ParHom_inv _ _ _ X0) as HX0;
  pose proof (ParHom_inv _ _ _ X) as HX;
  simpl in HX0, HX; try contradiction;
  subst; reflexivity.
Qed.

Program Definition Par_of_Wide@{i p u v} :
  WideParallel@{i p} bool ⟶ Parallel@{u v} := {|
  fobj := fun p => p;
  fmap := fun a b m => par_of_wide_map@{i u v} m
|}.
Next Obligation. destruct x; reflexivity. Qed.
Next Obligation.
  destruct x, y, z; simpl in *;
  try destruct f; try destruct g; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma par_endo_tag (a : ParObj) (f : a ~{Parallel}~> a) : ``f = true.
Proof.
  destruct f as [bf hf]; destruct a, bf; simpl; try reflexivity;
  destruct (ParHom_inv _ _ _ hf).
Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Par_of_Wide_Wide_of_Par :
  @equiv _ (@Functor_StrictEq_Setoid Parallel Parallel)
    (Par_of_Wide ◯ Wide_of_Par) (Id[Parallel]).
Proof.
  exists (fun _ => eq_refl).
  intros a b f; simpl; unfold Logic.transport_r, Logic.transport; simpl.
  destruct a, b; simpl in *.
  - symmetry; exact (par_endo_tag ParX f).
  - destruct f as [bf hf]; destruct bf; reflexivity.
  - destruct f as [bf hf]; destruct (ParHom_Y_X_absurd _ hf).
  - symmetry; exact (par_endo_tag ParY f).
Qed.

Lemma Wide_of_Par_Par_of_Wide :
  @equiv _ (@Functor_StrictEq_Setoid (WideParallel bool) (WideParallel bool))
    (Wide_of_Par ◯ Par_of_Wide) (Id[WideParallel bool]).
Proof.
  exists (fun _ => eq_refl).
  intros a b m; simpl.
  destruct a, b; simpl in *;
  try destruct m; reflexivity.
Qed.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition WideParallel_bool_Parallel :
  @Isomorphism StrictCat (WideParallel bool) Parallel := {|
  to   := Par_of_Wide;
  from := Wide_of_Par
|}.
Next Obligation. exact Par_of_Wide_Wide_of_Par. Qed.
Next Obligation. exact Wide_of_Par_Par_of_Wide. Qed.

(* The weaker reading, derived: 同构 [Cat] EQUIVALENCE of
 范畴, so says strictly less than statement above. （已译） *)
Program Definition WideParallel_bool_Parallel_Cat :
  @Isomorphism Cat (WideParallel bool) Parallel := {|
  to   := Par_of_Wide;
  from := Wide_of_Par
|}.
Next Obligation.
  exact (strict_equiv_implies_fun_equiv _ _ Par_of_Wide_Wide_of_Par).
Qed.
Next Obligation.
  exact (strict_equiv_implies_fun_equiv _ _ Wide_of_Par_Par_of_Wide).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma AWide_bool_APair {C : Category} {x y : C} (f g : x ~> y) :
  @equiv _ (@Functor_StrictEq_Setoid (WideParallel bool) C)
    (AWide (fun b : bool => if b then f else g))
    (APair f g ◯ Par_of_Wide).
Proof.
  unshelve eexists.
  - intro p; destruct p; reflexivity.
  - intros a b m; simpl; unfold Logic.transport_r, Logic.transport; simpl.
    destruct a, b; simpl in *;
    try destruct m; reflexivity.
Qed.
