Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/exponential+object
   nLab: https://ncatlab.org/nlab/show/natural+transformation

   本文件给出自然变换相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section PointwiseNatural.

Context {D E : Category}.
Context {F G : D ⟶ E}.

Lemma natural_flip_from (comp : ∀ p, F p ≅ G p)
      (nat : ∀ (x y : D) (m : x ~> y),
          fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m) :
  ∀ (x y : D) (m : x ~> y),
    fmap[F] m ∘ from (comp x) ≈ from (comp y) ∘ fmap[G] m.
Proof.
  intros x y m.
  assert (HA : from (comp y) ∘ (fmap[G] m ∘ to (comp x)) ≈ fmap[F] m).
  { rewrite nat, comp_assoc, iso_from_to; now rewrite id_left. }
  rewrite <- HA, <- !comp_assoc, iso_to_from.
  now rewrite id_right.
Qed.

Lemma natural_flip_to (comp : ∀ p, F p ≅ G p)
      (nat : ∀ (x y : D) (m : x ~> y),
          fmap[F] m ∘ from (comp x) ≈ from (comp y) ∘ fmap[G] m) :
  ∀ (x y : D) (m : x ~> y),
    fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m.
Proof.
  intros x y m.
  assert (HA : to (comp y) ∘ (fmap[F] m ∘ from (comp x)) ≈ fmap[G] m).
  { rewrite nat, comp_assoc, iso_to_from; now rewrite id_left. }
  rewrite <- HA, <- !comp_assoc, iso_from_to.
  now rewrite id_right.
Qed.

(* 相关说明。 （已译） *)
Program Definition NaturalIso_of_pointwise (comp : ∀ p, F p ≅ G p)
        (nat : ∀ (x y : D) (m : x ~> y),
            fmap[G] m ∘ to (comp x) ≈ to (comp y) ∘ fmap[F] m) :
  @Isomorphism ([D, E]) F G := {|
  to   := {| transform := fun p => to (comp p) |};
  from := {| transform := fun p => from (comp p) |}
|}.
(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Ltac natiso_obligation :=
  intros;
  try rewrite fmap_id;
  first [ now apply nat
        | symmetry; now apply nat
        | now apply natural_flip_from
        | symmetry; now apply natural_flip_from
        | now apply iso_to_from
        | now apply iso_from_to ].
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.
Next Obligation. natiso_obligation. Qed.

End PointwiseNatural.

Section ExpNatural.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(* 相关说明。 （已译） *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ihom {a b c d : C} (f : b ~> a) (h : c ~> d) : c^a ~> d^b :=
  curry (h ∘ eval ∘ second f).

(* [simpl] is used below only to reduce the pair projections of a product
   category; it must not go on to unfold [ihom] into its transpose. *)
Arguments ihom : simpl never.

#[export] Program Instance ihom_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@ihom a b c d).
Next Obligation. proper; unfold ihom; now rewrites. Qed.

Lemma ihom_id {a c : C} : ihom (id[a]) (id[c]) ≈ id[c^a].
Proof. unfold ihom; unfork; cat. Qed.

Lemma ihom_comp {a b b' c d e : C}
      (f : b ~> a) (f' : b' ~> b) (h : c ~> d) (h' : d ~> e) :
  ihom f' h' ∘ ihom f h ≈ ihom (f ∘ f') (h' ∘ h).
Proof.
  unfold ihom.
  symmetry.
  rewrite <- !comp_assoc.
  rewrite curry_comp.
  symmetry.
  rewrite curry_comp.
  rewrite <- comp_assoc.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    rewrite curry_comp_l.
    rewrite <- !comp_assoc.
    rewrite <- first_second.
    rewrite !comp_assoc.
    rewrite ump_exponents.
    rewrite <- !comp_assoc.
    rewrite <- second_comp.
    reflexivity.
Qed.

(* The identification asserted above, machine-checked: [ihom] IS the arrow
   action of [InternalHomFunctor], read in C, at Leibniz equality -- not
   merely up to [≈].  ((a, c) ~> (b, d) in C^op ∏ C is a pair of f : b ~> a
   in C and h : c ~> d.) *)
Example ihom_is_InternalHomFunctor_fmap {a b c d : C} (f : b ~> a) (h : c ~> d) :
  @fmap _ _ (InternalHomFunctor C) (a, c) (b, d) (f, h) = ihom f h := eq_refl.

(* 相关说明。 （已译） *)

Lemma first_as_split {x y z : C} (f : x ~> y) : first (z:=z) f ≈ split f id.
Proof. unfold first, split; cat. Qed.

Lemma second_as_split {x y z : C} (f : x ~> y) : second (z:=z) f ≈ split id f.
Proof. unfold second, split; cat. Qed.

(*
   本节说明同构、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma prod_assoc_to_natural {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  to prod_assoc ∘ split (split f g) h ≈ split f (split g h) ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

Lemma prod_assoc_from_natural {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  from prod_assoc ∘ split f (split g h) ≈ split (split f g) h ∘ from prod_assoc.
Proof. simpl; unfork. Qed.

(* Two instances of associator naturality, in the exact shapes the squares
   below produce (the middle factor of each composite is an identity, so
   neither is a bare instance of [prod_assoc_to_natural]). *)
Lemma prod_assoc_second_first {a x y x' y' : C} (f : x' ~> x) (g : y' ~> y) :
  to prod_assoc ∘ (second g ∘ first (second (z:=a) f))
    ≈ second (split f g) ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

Lemma prod_assoc_first_first {a b x y : C} (k : a ~> b) :
  to prod_assoc ∘ first (z:=y) (first (z:=x) k) ≈ first (z:=x × y) k ∘ to prod_assoc.
Proof. simpl; unfork. Qed.

(* [eval_first] under a further composite, so that no [comp_assoc] step has to
   be aimed by hand at one side of a naturality square. *)
Corollary eval_first_comp {a b c w : C} (k : a ~> c^b) (m : w ~> a × b) :
  eval ∘ (first k ∘ m) ≈ uncurry k ∘ m.
Proof. rewrite comp_assoc, eval_first; reflexivity. Qed.

(* Postcomposition internal-hom action, computed through transpose:
 这是 single calculation every 自然性 square below reduces to. （已译） *)
Lemma ihom_curry {a b b' c c' : C} (f : b' ~> b) (h : c ~> c') (m : a × b ~> c) :
  ihom f h ∘ curry m ≈ curry (h ∘ m ∘ second f).
Proof.
  unfold ihom.
  rewrite curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- first_second.
  rewrite (comp_assoc eval).
  rewrite eval_first, uncurry_curry.
  now rewrite comp_assoc.
Qed.

(*
   本节说明hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition opobj (a : C^op) : C := a.
Definition oparr {a b : C^op} (f : a ~{C^op}~> b) : opobj b ~{C}~> opobj a := f.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Lemma exp_prod_l_to_unfold {x y z : C} :
  to (@exp_prod_l C _ _ x y z) ≈ curry (curry (eval ∘ to prod_assoc)).
Proof. reflexivity. Qed.

Lemma exp_prod_l_from_unfold {x y z : C} :
  from (@exp_prod_l C _ _ x y z) ≈ curry (uncurry eval ∘ from prod_assoc).
Proof. reflexivity. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition expProdL_lhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p)) × opobj (snd (fst p))).

Definition expProdL_lhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expProdL_lhs x ~> expProdL_lhs y :=
  ihom (split (oparr (fst (fst m))) (oparr (snd (fst m)))) (snd m).

Program Definition ExpProdL_LHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expProdL_lhs;
  fmap := @expProdL_lhs_map
|}.
Next Obligation.
  proper.
  unfold expProdL_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdL_lhs_map, expProdL_lhs, oparr; simpl.
  now rewrite split_id, ihom_id.
Qed.
Next Obligation.
  unfold expProdL_lhs_map, expProdL_lhs, oparr; simpl.
  now rewrite ihom_comp, split_comp.
Qed.

Definition expProdL_rhs (p : (C^op ∏ C^op) ∏ C) : C :=
  ((snd p)^(opobj (snd (fst p))))^(opobj (fst (fst p))).

Definition expProdL_rhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expProdL_rhs x ~> expProdL_rhs y :=
  ihom (oparr (fst (fst m))) (ihom (oparr (snd (fst m))) (snd m)).

Program Definition ExpProdL_RHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expProdL_rhs;
  fmap := @expProdL_rhs_map
|}.
Next Obligation.
  proper.
  unfold expProdL_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdL_rhs_map, expProdL_rhs, oparr; simpl.
  now rewrite !ihom_id.
Qed.
Next Obligation.
  unfold expProdL_rhs_map, expProdL_rhs, oparr; simpl.
  now rewrite !ihom_comp.
Qed.

(* The two 对象 actions, recorded so shape each side Law 1 is
 machine-checked rather than asserted header. （已译） *)
Example ExpProdL_LHS_obj (x y : C^op) (z : C) :
  fobj[ExpProdL_LHS] ((x, y), z) = z^(opobj x × opobj y) := eq_refl.

Example ExpProdL_RHS_obj (x y : C^op) (z : C) :
  fobj[ExpProdL_RHS] ((x, y), z) = (z^(opobj y))^(opobj x) := eq_refl.

(* The 自然性 square proper. Both sides normalise double transpose
 [ihom_curry] [curry_comp_l]; what remains under two [curry]s is
 自然性 associator. （已译） *)
Lemma exp_prod_l_square {x y z x' y' z' : C}
      (f : x' ~> x) (g : y' ~> y) (h : z ~> z') :
  ihom f (ihom g h) ∘ to (@exp_prod_l C _ _ x y z)
    ≈ to (@exp_prod_l C _ _ x' y' z') ∘ ihom (split f g) h.
Proof.
  rewrite !exp_prod_l_to_unfold.
  rewrite !ihom_curry.
  rewrite !curry_comp_l.
  f_equiv; f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_second_first, prod_assoc_first_first.
  unfold ihom.
  rewrite eval_first_comp, uncurry_curry.
  now rewrite <- !comp_assoc.
Qed.

Definition exp_prod_l_iso (p : (C^op ∏ C^op) ∏ C) :
  ExpProdL_LHS p ≅ ExpProdL_RHS p :=
  @exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p).

Definition exp_prod_l_natural :
  @Isomorphism ([(C^op ∏ C^op) ∏ C, C]) ExpProdL_LHS ExpProdL_RHS :=
  NaturalIso_of_pointwise exp_prod_l_iso
    (fun _ _ m => exp_prod_l_square (oparr (fst (fst m))) (oparr (snd (fst m)))
                                    (snd m)).

(* 相关说明。 （已译） *)
Lemma exp_prod_l_natural_component (p : (C^op ∏ C^op) ∏ C) :
  transform[to exp_prod_l_natural] p
    ≈ to (@exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p)).
Proof. reflexivity. Qed.

Lemma exp_prod_l_natural_component_from (p : (C^op ∏ C^op) ∏ C) :
  transform[from exp_prod_l_natural] p
    ≈ from (@exp_prod_l C _ _ (opobj (fst (fst p))) (opobj (snd (fst p))) (snd p)).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Corollary exp_prod_l_natural_in_base {x y z z' : C} (h : z ~> z') :
  ihom (id[x]) (ihom (id[y]) h) ∘ to (@exp_prod_l C _ _ x y z)
    ≈ to (@exp_prod_l C _ _ x y z') ∘ ihom (id[x × y]) h.
Proof.
  pose proof (exp_prod_l_square (id[x]) (id[y]) h) as HA.
  now rewrite split_id in HA.
Qed.

(*
   本节说明伴随、同构、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma prod_assoc_from_first {a b x y : C} (k : a ~> b) :
  from prod_assoc ∘ first (z:=x × y) k
    ≈ first (z:=y) (first (z:=x) k) ∘ from prod_assoc.
Proof. simpl; unfork. Qed.

Lemma exp_prod_l_transpose {w x y z : C} (f : w ~> z^(x × y)) :
  to (@exp_prod_l C _ _ x y z) ∘ f ≈ curry (curry (uncurry f ∘ to prod_assoc)).
Proof.
  rewrite exp_prod_l_to_unfold.
  rewrite !curry_comp_l.
  f_equiv; f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_first_first.
  now rewrite eval_first_comp.
Qed.

Lemma exp_prod_l_untranspose {w x y z : C} (g : w ~> (z^y)^x) :
  from (@exp_prod_l C _ _ x y z) ∘ g
    ≈ curry (uncurry (uncurry g) ∘ from prod_assoc).
Proof.
  rewrite exp_prod_l_from_unfold.
  rewrite curry_comp_l.
  f_equiv.
  rewrite <- !comp_assoc.
  rewrite prod_assoc_from_first.
  rewrite comp_assoc.
  now rewrite <- uncurry_comp, eval_first.
Qed.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma exp_prod_r_to_unfold {x y z : C} :
  to (@exp_prod_r C _ _ x y z) ≈ curry (exl ∘ eval) △ curry (exr ∘ eval).
Proof. reflexivity. Qed.

(* Two readings [ihom] one 论元 恒等, used recognise the
 legs [exp_prod_r] [exp_coprod] internal-hom actions. （已译） *)
Lemma ihom_id_l {a c d : C} (k : c ~> d) : ihom (id[a]) k ≈ curry (k ∘ eval).
Proof. unfold ihom; now rewrite second_id, id_right. Qed.

Lemma ihom_id_r {a b c : C} (k : b ~> a) :
  ihom k (id[c]) ≈ curry (eval ∘ second k).
Proof. unfold ihom; now rewrite id_left. Qed.

Definition expProdR_lhs (p : C^op ∏ (C ∏ C)) : C :=
  (fst (snd p) × snd (snd p))^(opobj (fst p)).

Definition expProdR_lhs_map {x y : C^op ∏ (C ∏ C)} (m : x ~> y) :
  expProdR_lhs x ~> expProdR_lhs y :=
  ihom (oparr (fst m)) (split (fst (snd m)) (snd (snd m))).

Program Definition ExpProdR_LHS : (C^op ∏ (C ∏ C)) ⟶ C := {|
  fobj := expProdR_lhs;
  fmap := @expProdR_lhs_map
|}.
Next Obligation.
  proper.
  unfold expProdR_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdR_lhs_map, expProdR_lhs, oparr; simpl.
  now rewrite split_id, ihom_id.
Qed.
Next Obligation.
  unfold expProdR_lhs_map, expProdR_lhs, oparr; simpl.
  now rewrite ihom_comp, split_comp.
Qed.

Definition expProdR_rhs (p : C^op ∏ (C ∏ C)) : C :=
  (fst (snd p))^(opobj (fst p)) × (snd (snd p))^(opobj (fst p)).

Definition expProdR_rhs_map {x y : C^op ∏ (C ∏ C)} (m : x ~> y) :
  expProdR_rhs x ~> expProdR_rhs y :=
  split (ihom (oparr (fst m)) (fst (snd m))) (ihom (oparr (fst m)) (snd (snd m))).

Program Definition ExpProdR_RHS : (C^op ∏ (C ∏ C)) ⟶ C := {|
  fobj := expProdR_rhs;
  fmap := @expProdR_rhs_map
|}.
Next Obligation.
  proper.
  unfold expProdR_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expProdR_rhs_map, expProdR_rhs, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold expProdR_rhs_map, expProdR_rhs, oparr; simpl.
  now rewrite split_comp, !ihom_comp.
Qed.

Example ExpProdR_LHS_obj (x : C^op) (y z : C) :
  fobj[ExpProdR_LHS] (x, (y, z)) = (y × z)^(opobj x) := eq_refl.

Example ExpProdR_RHS_obj (x : C^op) (y z : C) :
  fobj[ExpProdR_RHS] (x, (y, z)) = y^(opobj x) × z^(opobj x) := eq_refl.

(* 相关说明。 （已译） *)
Lemma exp_prod_r_square {x y z x' y' z' : C}
      (f : x' ~> x) (g : y ~> y') (h : z ~> z') :
  split (ihom f g) (ihom f h) ∘ to (@exp_prod_r C _ _ x y z)
    ≈ to (@exp_prod_r C _ _ x' y' z') ∘ ihom f (split g h).
Proof.
  rewrite !exp_prod_r_to_unfold.
  rewrite <- !ihom_id_l.
  rewrite split_fork.
  rewrite <- fork_comp.
  apply fork_inv; split;
  rewrite !ihom_comp, id_left, id_right;
  [ now rewrite exl_split | now rewrite exr_split ].
Qed.

Definition exp_prod_r_iso (p : C^op ∏ (C ∏ C)) :
  ExpProdR_LHS p ≅ ExpProdR_RHS p :=
  @exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p)).

Definition exp_prod_r_natural :
  @Isomorphism ([C^op ∏ (C ∏ C), C]) ExpProdR_LHS ExpProdR_RHS :=
  NaturalIso_of_pointwise exp_prod_r_iso
    (fun _ _ m => exp_prod_r_square (oparr (fst m)) (fst (snd m)) (snd (snd m))).

Lemma exp_prod_r_natural_component (p : C^op ∏ (C ∏ C)) :
  transform[to exp_prod_r_natural] p
    ≈ to (@exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

Lemma exp_prod_r_natural_component_from (p : C^op ∏ (C ∏ C)) :
  transform[from exp_prod_r_natural] p
    ≈ from (@exp_prod_r C _ _ (opobj (fst p)) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

Context `{@Cocartesian C}.

(* 相关说明。 （已译） *)
Lemma cover_inl {x y z w : C} (f : x ~> y) (g : z ~> w) :
  cover f g ∘ inl ≈ inl ∘ f.
Proof. unfold cover; now rewrite inl_merge. Qed.

Lemma cover_inr {x y z w : C} (f : x ~> y) (g : z ~> w) :
  cover f g ∘ inr ≈ inr ∘ g.
Proof. unfold cover; now rewrite inr_merge. Qed.

(* 相关说明。 （已译） *)

Lemma prod_coprod_r_from_unfold {x y z : C} :
  from (@prod_coprod_r C _ _ _ x y z) ≈ second inl ▽ second inr.
Proof. reflexivity. Qed.

Definition prodCoprodR_lhs (p : C ∏ (C ∏ C)) : C :=
  (fst p) × (fst (snd p) + snd (snd p)).

Definition prodCoprodR_lhs_map {x y : C ∏ (C ∏ C)} (m : x ~> y) :
  prodCoprodR_lhs x ~> prodCoprodR_lhs y :=
  split (fst m) (cover (fst (snd m)) (snd (snd m))).

Program Definition ProdCoprodR_LHS : (C ∏ (C ∏ C)) ⟶ C := {|
  fobj := prodCoprodR_lhs;
  fmap := @prodCoprodR_lhs_map
|}.
Next Obligation. proper; unfold prodCoprodR_lhs_map; now rewrites. Qed.
Next Obligation.
  unfold prodCoprodR_lhs_map, prodCoprodR_lhs; simpl.
  now rewrite cover_id, split_id.
Qed.
Next Obligation.
  unfold prodCoprodR_lhs_map, prodCoprodR_lhs; simpl.
  now rewrite split_comp, cover_comp.
Qed.

Definition prodCoprodR_rhs (p : C ∏ (C ∏ C)) : C :=
  (fst p × fst (snd p)) + (fst p × snd (snd p)).

Definition prodCoprodR_rhs_map {x y : C ∏ (C ∏ C)} (m : x ~> y) :
  prodCoprodR_rhs x ~> prodCoprodR_rhs y :=
  cover (split (fst m) (fst (snd m))) (split (fst m) (snd (snd m))).

Program Definition ProdCoprodR_RHS : (C ∏ (C ∏ C)) ⟶ C := {|
  fobj := prodCoprodR_rhs;
  fmap := @prodCoprodR_rhs_map
|}.
Next Obligation. proper; unfold prodCoprodR_rhs_map; now rewrites. Qed.
Next Obligation.
  unfold prodCoprodR_rhs_map, prodCoprodR_rhs; simpl.
  now rewrite !split_id, cover_id.
Qed.
Next Obligation.
  unfold prodCoprodR_rhs_map, prodCoprodR_rhs; simpl.
  now rewrite cover_comp, !split_comp.
Qed.

Example ProdCoprodR_LHS_obj (x y z : C) :
  fobj[ProdCoprodR_LHS] (x, (y, z)) = x × (y + z) := eq_refl.

Example ProdCoprodR_RHS_obj (x y z : C) :
  fobj[ProdCoprodR_RHS] (x, (y, z)) = x × y + x × z := eq_refl.

(* 相关说明。 （已译） *)
Lemma prod_coprod_r_from_square {x y z x' y' z' : C}
      (f : x ~> x') (g : y ~> y') (h : z ~> z') :
  split f (cover g h) ∘ from (@prod_coprod_r C _ _ _ x y z)
    ≈ from (@prod_coprod_r C _ _ _ x' y' z') ∘ cover (split f g) (split f h).
Proof.
  rewrite !prod_coprod_r_from_unfold.
  unfold cover.
  rewrite <- !merge_comp.
  apply merge_inv; split.
  - rewrite split_second, inl_merge.
    rewrite comp_assoc, inl_merge.
    now rewrite second_split.
  - rewrite split_second, inr_merge.
    rewrite comp_assoc, inr_merge.
    now rewrite second_split.
Qed.

Definition prod_coprod_r_iso (p : C ∏ (C ∏ C)) :
  ProdCoprodR_LHS p ≅ ProdCoprodR_RHS p :=
  @prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p)).

Definition prod_coprod_r_natural :
  @Isomorphism ([C ∏ (C ∏ C), C]) ProdCoprodR_LHS ProdCoprodR_RHS :=
  NaturalIso_of_pointwise prod_coprod_r_iso
    (natural_flip_to prod_coprod_r_iso
       (fun _ _ m => prod_coprod_r_from_square (fst m) (fst (snd m)) (snd (snd m)))).

Lemma prod_coprod_r_natural_component (p : C ∏ (C ∏ C)) :
  transform[to prod_coprod_r_natural] p
    ≈ to (@prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

Lemma prod_coprod_r_natural_component_from (p : C ∏ (C ∏ C)) :
  transform[from prod_coprod_r_natural] p
    ≈ from (@prod_coprod_r C _ _ _ (fst p) (fst (snd p)) (snd (snd p))).
Proof. reflexivity. Qed.

(*
   本节说明 Natural 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma exp_coprod_to_unfold {x y z : C} :
  to (@exp_coprod C _ _ _ x y z)
    ≈ curry (eval ∘ second inl) △ curry (eval ∘ second inr).
Proof. reflexivity. Qed.

Definition expCoprod_lhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p)) + opobj (snd (fst p))).

Definition expCoprod_lhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expCoprod_lhs x ~> expCoprod_lhs y :=
  ihom (cover (oparr (fst (fst m))) (oparr (snd (fst m)))) (snd m).

Program Definition ExpCoprod_LHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expCoprod_lhs;
  fmap := @expCoprod_lhs_map
|}.
Next Obligation.
  proper.
  unfold expCoprod_lhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expCoprod_lhs_map, expCoprod_lhs, oparr; simpl.
  now rewrite cover_id, ihom_id.
Qed.
Next Obligation.
  unfold expCoprod_lhs_map, expCoprod_lhs, oparr; simpl.
  now rewrite ihom_comp, cover_comp.
Qed.

Definition expCoprod_rhs (p : (C^op ∏ C^op) ∏ C) : C :=
  (snd p)^(opobj (fst (fst p))) × (snd p)^(opobj (snd (fst p))).

Definition expCoprod_rhs_map {x y : (C^op ∏ C^op) ∏ C} (m : x ~> y) :
  expCoprod_rhs x ~> expCoprod_rhs y :=
  split (ihom (oparr (fst (fst m))) (snd m)) (ihom (oparr (snd (fst m))) (snd m)).

Program Definition ExpCoprod_RHS : ((C^op ∏ C^op) ∏ C) ⟶ C := {|
  fobj := expCoprod_rhs;
  fmap := @expCoprod_rhs_map
|}.
Next Obligation.
  proper.
  unfold expCoprod_rhs_map, oparr.
  now rewrites.
Qed.
Next Obligation.
  unfold expCoprod_rhs_map, expCoprod_rhs, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold expCoprod_rhs_map, expCoprod_rhs, oparr; simpl.
  now rewrite split_comp, !ihom_comp.
Qed.

Example ExpCoprod_LHS_obj (y z : C^op) (x : C) :
  fobj[ExpCoprod_LHS] ((y, z), x) = x^(opobj y + opobj z) := eq_refl.

Example ExpCoprod_RHS_obj (y z : C^op) (x : C) :
  fobj[ExpCoprod_RHS] ((y, z), x) = x^(opobj y) × x^(opobj z) := eq_refl.

Lemma exp_coprod_square {x y z x' y' z' : C}
      (g : y' ~> y) (h : z' ~> z) (f : x ~> x') :
  split (ihom g f) (ihom h f) ∘ to (@exp_coprod C _ _ _ x y z)
    ≈ to (@exp_coprod C _ _ _ x' y' z') ∘ ihom (cover g h) f.
Proof.
  rewrite !exp_coprod_to_unfold.
  rewrite <- !ihom_id_r.
  rewrite split_fork.
  rewrite <- fork_comp.
  apply fork_inv; split;
  rewrite !ihom_comp, id_left, id_right;
  [ now rewrite cover_inl | now rewrite cover_inr ].
Qed.

Definition exp_coprod_iso (p : (C^op ∏ C^op) ∏ C) :
  ExpCoprod_LHS p ≅ ExpCoprod_RHS p :=
  @exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p))).

Definition exp_coprod_natural :
  @Isomorphism ([(C^op ∏ C^op) ∏ C, C]) ExpCoprod_LHS ExpCoprod_RHS :=
  NaturalIso_of_pointwise exp_coprod_iso
    (fun _ _ m => exp_coprod_square (oparr (fst (fst m))) (oparr (snd (fst m)))
                                    (snd m)).

Lemma exp_coprod_natural_component (p : (C^op ∏ C^op) ∏ C) :
  transform[to exp_coprod_natural] p
    ≈ to (@exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p)))).
Proof. reflexivity. Qed.

Lemma exp_coprod_natural_component_from (p : (C^op ∏ C^op) ∏ C) :
  transform[from exp_coprod_natural] p
    ≈ from (@exp_coprod C _ _ _ (snd p) (opobj (fst (fst p))) (opobj (snd (fst p)))).
Proof. reflexivity. Qed.

(* The single-variable specimen Law 4: 自然性 first summand. （已译） *)
Corollary exp_coprod_natural_in_first_summand {x y z y' : C} (g : y' ~> y) :
  split (ihom g (id[x])) (ihom (id[z]) (id[x])) ∘ to (@exp_coprod C _ _ _ x y z)
    ≈ to (@exp_coprod C _ _ _ x y' z) ∘ ihom (cover g (id[z])) (id[x]).
Proof. exact (exp_coprod_square g (id[z]) (id[x])). Qed.

End ExpNatural.
