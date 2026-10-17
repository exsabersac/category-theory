Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Fun.Exponential.
Require Import Category.Instance.Omega.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* * * Cartesian closure NOT inherited 函子 范畴 （已译） *)

(*
 Book:      Awodey, Category Theory, §8.7 "Exponentials in categories
 nLab:      https://ncatlab.org/nlab/show/functor+category
 nLab:      https://ncatlab.org/nlab/show/cartesian+closed+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category

   本文件给出闭结构实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** A: points exponential, any 笛卡尔闭 范畴 （已译） *)

Section CCCPoints.

Context {C : Category}.
Context {CC : @Cartesian C}.
Context {CT : @Terminal C}.
Context {CL : @Closed C CC}.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ccc_point {P Q : C} (f : P ~> Q) :
  @terminal_obj C CT ~> @exponent_obj C CC CL P Q :=
  @curry C CC CL _ P Q (f ∘ exr).

(* Distinct 态射 have distinct points. Uncurrying undoes [curry]
 ([uncurry_curry]), [exr o (one /\ id) ~ id] ([exr_fork]) cancels
 projection. （已译） *)
Lemma ccc_point_inj {P Q : C} (f g : P ~> Q) :
  ccc_point f ≈ ccc_point g -> f ≈ g.
Proof.
  intro H.
  unfold ccc_point in H.
  assert (Hu : f ∘ (@exr C CC (@terminal_obj C CT) P) ≈ g ∘ exr).
  { rewrite <- (uncurry_curry (f ∘ exr)).
    rewrite <- (uncurry_curry (g ∘ exr)).
    now rewrite H. }
  rewrite <- (id_right f), <- (id_right g).
  rewrite <- (exr_fork (@one C CT P) (id[P])).
  rewrite !comp_assoc.
  now rewrite Hu.
Qed.

End CCCPoints.

(* * ** B: transformation out 常值 函子 determined at
 initial index （已译） *)

Section ConstantPoints.

Context {J A : Category}.
Context {JI : @Initial J}.
Context {AT : @Terminal A}.

(* [Functor_Category_Terminal AT]'s object is [Constant_Terminal_Functor
   AT], the constant functor at 1_A, so a component of [a] at [j] has
   type [1_A ~> E j] on the nose -- no transport is involved. *)
Definition fun_const_point {E : J ⟶ A}
  (a : @terminal_obj ([J, A]) (Functor_Category_Terminal AT)
         ~{[J, A]}~> E) :
  @terminal_obj A AT ~{A}~> E (@initial_obj J JI) :=
  @transform _ _ _ _ a (@initial_obj J JI).

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fun_const_point_inj {E : J ⟶ A}
  (a b : @terminal_obj ([J, A]) (Functor_Category_Terminal AT)
           ~{[J, A]}~> E) :
  fun_const_point a ≈ fun_const_point b -> a ≈ b.
Proof.
  intros H j.
  pose proof (@naturality _ _ _ _ a _ _ (@zero J JI j)) as Na.
  pose proof (@naturality _ _ _ _ b _ _ (@zero J JI j)) as Nb.
  simpl in Na, Nb.
  rewrite id_right in Na, Nb.
  rewrite <- Na, <- Nb.
  unfold fun_const_point in H.
  now rewrite H.
Qed.

End ConstantPoints.

(** ** C: the engine *)

Section Engine.

Context {J A : Category}.
Context {JI : @Initial J}.
Context {AT : @Terminal A}.
Context {CC : @Cartesian ([J, A])}.
Context {CL : @Closed ([J, A]) CC}.

(* Hom_{[J,A]}(P, Q) injects Hom_A(1_A, (Q^P) 0). The [Cartesian]
 structure [CC] arbitrary; TERMINAL 对象 supplied here as
 pointwise one, what makes section B applicable. （已译） *)
Definition fun_hom_point {P Q : [J, A]} (f : P ~{[J, A]}~> Q) :
  @terminal_obj A AT
    ~{A}~> (@exponent_obj _ CC CL P Q) (@initial_obj J JI) :=
  @fun_const_point J A JI AT (@exponent_obj _ CC CL P Q)
    (@ccc_point ([J, A]) CC (Functor_Category_Terminal AT) CL P Q f).

Lemma fun_hom_point_inj {P Q : [J, A]} (f g : P ~{[J, A]}~> Q) :
  fun_hom_point f ≈ fun_hom_point g -> f ≈ g.
Proof.
  intro H.
  apply (@ccc_point_inj ([J, A]) CC (Functor_Category_Terminal AT) CL).
  apply (@fun_const_point_inj J A JI AT).
  exact H.
Qed.

End Engine.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma nodup_map_inj {A B : Type} (h : A -> B) (l : list A) :
  (forall x y, h x = h y -> x = y) ->
  List.NoDup l -> List.NoDup (List.map h l).
Proof.
  intros Hinj Hnd.
  induction Hnd as [| a l Hnin Hnd IH]; simpl.
  - constructor.
  - constructor; [ | exact IH ].
    intro Hin.
    apply List.in_map_iff in Hin.
    destruct Hin as [b [Hb Hb']].
    apply Hinj in Hb; subst.
    contradiction.
Qed.

(* There is no injective family [nat -> Fin.t N]: restrict it along
   [Fin.to_nat] to get [S N] distinct elements of an [N]-element type. *)
Lemma fin_no_nat_injection {N : nat} (w : nat -> Fin.t N)
  (winj : forall i j, w i = w j -> i = j) : False.
Proof.
  pose (v := fun i : Fin.t (S N) => w (proj1_sig (Fin.to_nat i))).
  assert (vinj : forall i j, v i = v j -> i = j).
  { intros i j Hij; apply Fin.to_nat_inj; now apply winj. }
  assert (Hnd : List.NoDup (List.map v (fin_enum (S N))))
    by (apply nodup_map_inj; [ exact vinj | apply fin_enum_nodup ]).
  assert (Hincl : List.incl (List.map v (fin_enum (S N))) (fin_enum N))
    by (intros x _; apply fin_enum_full).
  pose proof (List.NoDup_incl_length Hnd Hincl) as Hle.
  rewrite length_of_map, !fin_enum_length in Hle.
  exact (Nat.nle_succ_diag_l N Hle).
Qed.

(** ** E: Mac Lane §IV.6 Exercise 5 *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition FinSet_is_cartesian_closed : @Closed FinSet FinSet_Cartesian :=
  FinSet_Closed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition two_map@{h} {n m : nat} (f : le_t@{h} n m) : Fin.t 2 -> Fin.t 2 :=
  match f with
  | le_t_n   => fun i => i
  | le_t_S _ => fun _ => Fin.F1
  end.

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition TwoFun@{o h p u u0 u1 u2 +}
  : Omega@{o h p} ⟶ FinSet@{u u0 u1 u2} := {|
  fobj := fun _ => 2%nat;
  fmap := fun _ _ f => two_map f
|}.
Next Obligation. now destruct f. Qed.

(* The k-th family: 恒等 at stage [S k], 常值 map at
 [Fin.F1] everywhere else. （已译） *)
Definition alpha_fam (k n : nat) : Fin.t 2 -> Fin.t 2 :=
  match Nat.eq_dec n (S k) with
  | left  _ => fun i => i
  | right _ => fun _ => Fin.F1
  end.

Lemma alpha_fam_F1 (k n : nat) : alpha_fam k n Fin.F1 = Fin.F1.
Proof. unfold alpha_fam; destruct (Nat.eq_dec n (S k)); reflexivity. Qed.

(* Naturality.  At [le_t_n] the square is an identity; at [le_t_S _]
   both sides reduce to [Fin.F1], because every component of
   [alpha_fam k] preserves [Fin.F1]. *)
Program Definition Alpha@{o h p u u0 u1 u2 +} (k : nat)
  : TwoFun@{o h p u u0 u1 u2} ⟹ TwoFun@{o h p u u0 u1 u2} := {|
  transform := fun n => alpha_fam k n
|}.
Next Obligation.
  destruct f; simpl; [ reflexivity | symmetry; apply alpha_fam_F1 ].
Qed.
Next Obligation.
  destruct f; simpl; [ reflexivity | apply alpha_fam_F1 ].
Qed.

(* 相关说明。 （已译） *)
Lemma Alpha_distinct (k j : nat) : Alpha k ≈ Alpha j -> k = j.
Proof.
  intro H.
  destruct (Nat.eq_dec k j) as [Hkj | Hkj]; [ exact Hkj | ].
  exfalso.
  specialize (H (S k) (Fin.FS Fin.F1)).
  simpl in H; unfold alpha_fam in H.
  destruct (Nat.eq_dec (S k) (S k)) as [_ | Hne]; [ | now apply Hne ].
  destruct (Nat.eq_dec (S k) (S j)) as [He | _].
  - apply Hkj; now injection He.
  - discriminate H.
Qed.

(* In [FinSet] every element of the one-element object is [Fin.F1]
   ([fin1_unique]), so a morphism [1 ~> n] is determined by its value
   there.  The [=] is [fun_setoid]'s pointwise Leibniz equality. *)
Lemma finset_point_eq {n : nat}
  (u v : @hom FinSet 1%nat n) : u Fin.F1 = v Fin.F1 -> u ≈ v.
Proof.
  intros H i.
  now rewrite (fin1_unique i).
Qed.

Section MacLaneEx5.

(* An ARBITRARY cartesian structure 函子 范畴, an
 arbitrary 笛卡尔闭 structure over it. （已译） *)
Context (CC : @Cartesian ([Omega, FinSet])).
Context (CL : @Closed ([Omega, FinSet]) CC).

(* The 对象 [FinSet] -- natural number -- at engine
 lands: value at stage 0 exponential [TwoFun] by
 itself. （已译） *)
Definition exp_card : nat :=
  (@exponent_obj _ CC CL TwoFun TwoFun)
    (@initial_obj Omega Omega_Initial).

(* Each [Alpha k] becomes an element of an [exp_card]-element set. *)
Definition alpha_index (k : nat) : Fin.t exp_card :=
  @fun_hom_point Omega FinSet Omega_Initial FinSet_Terminal CC CL
    TwoFun TwoFun (Alpha k) Fin.F1.

Lemma alpha_index_inj (k j : nat) : alpha_index k = alpha_index j -> k = j.
Proof.
  intro H.
  apply Alpha_distinct.
  apply (@fun_hom_point_inj Omega FinSet Omega_Initial FinSet_Terminal
           CC CL TwoFun TwoFun).
  now apply finset_point_eq.
Qed.

End MacLaneEx5.

(* Mac Lane §IV.6 Exercise 5: [FinSet] cartesian closed, [Omega] a
 small 范畴, 函子 范畴 cartesian closed --
 under ANY cartesian structure it, merely pointwise one. （已译） *)
Theorem fun_not_cartesian_closed
  (CC : @Cartesian ([Omega, FinSet])) :
  @Closed ([Omega, FinSet]) CC -> False.
Proof.
  intro CL.
  exact (fin_no_nat_injection (alpha_index CC CL) (alpha_index_inj CC CL)).
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary fun_pointwise_not_cartesian_closed :
  @Closed ([Omega, FinSet])
    (Functor_Category_Cartesian Omega FinSet FinSet_Cartesian) -> False.
Proof. exact (fun_not_cartesian_closed _). Qed.

(* * ** F: Awodey §8.7 -- objectwise formula gives wrong 对象 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition TwoOpInitial : @Initial (_2^op) := Two_Terminal.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PObj (x : TwoObj) : Sets :=
  match x with
  | TwoX => @terminal_obj Sets Sets_Terminal
  | TwoY => @initial_obj Sets Sets_Initial
  end.

Definition PMap (a b : TwoObj) :
  @hom (_2^op) a b -> (PObj a ~{Sets}~> PObj b).
Proof.
  destruct a, b; intro f.
  - exact id.
  - exact (False_rect _ (TwoHom_Y_X_absurd f)).
  - exact (@zero Sets Sets_Initial _).
  - exact id.
Defined.

(* Any two 态射 out empty setoid agree, discharges
 every case [fmap_comp] not 恒等. （已译） *)
Program Definition PresheafP : _2^op ⟶ Sets := {|
  fobj := PObj;
  fmap := PMap
|}.
Next Obligation. now destruct x. Qed.
Next Obligation.
  destruct x, y, z; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f)
          | contradiction (TwoHom_Y_X_absurd g) ].
Qed.

(* The two-element setoid, under Leibniz equality on [bool]. *)
Definition two_elt : Sets :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Definition PresheafQ : _2^op ⟶ Sets := Constant_Functor two_elt.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition PQNat (b : bool) : PresheafP ⟹ PresheafQ := {|
  transform := fun x =>
    match x return PObj x ~{Sets}~> two_elt with
    | TwoX => {| morphism := fun _ => b
               ; proper_morphism := fun _ _ _ => reflexivity b |}
    | TwoY => @zero Sets Sets_Initial two_elt
    end
|}.
Next Obligation.
  destruct x, y; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f) ].
Qed.
Next Obligation.
  destruct x, y; simpl;
    solve [ reflexivity | now destruct x0
          | contradiction (TwoHom_Y_X_absurd f) ].
Qed.

Lemma PQNat_distinct : PQNat true ≈ PQNat false -> False.
Proof.
  intro H.
  exact (Bool.diff_true_false (H TwoX ttt)).
Qed.

Section AwodeyPointwise.

Context (CC : @Cartesian ([_2^op, Sets])).
Context (CL : @Closed ([_2^op, Sets]) CC).

(* The engine at presheaf 范畴: two distinct points of
 (Q^P) TwoY. （已译） *)
Definition pq_point (b : bool) :
  @terminal_obj Sets Sets_Terminal
    ~{Sets}~> (@exponent_obj _ CC CL PresheafP PresheafQ) TwoY :=
  @fun_hom_point (_2^op) Sets TwoOpInitial Sets_Terminal CC CL
    PresheafP PresheafQ (PQNat b).

Lemma pq_point_distinct : pq_point true ≈ pq_point false -> False.
Proof.
  intro H.
  apply PQNat_distinct.
  exact (@fun_hom_point_inj (_2^op) Sets TwoOpInitial Sets_Terminal
           CC CL PresheafP PresheafQ (PQNat true) (PQNat false) H).
Qed.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition objectwise_candidate : Sets :=
  @exponent_obj Sets Sets_Cartesian Sets_Closed
    (PresheafP TwoY) (PresheafQ TwoY).

Lemma objectwise_candidate_subsingleton
  (u v : @terminal_obj Sets Sets_Terminal ~{Sets}~> objectwise_candidate) :
  u ≈ v.
Proof. intros x; simpl; intros []. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem awodey_pointwise_not_exponential :
  @Isomorphism Sets
    ((@exponent_obj _ CC CL PresheafP PresheafQ) TwoY)
    objectwise_candidate -> False.
Proof.
  intro i.
  apply pq_point_distinct.
  apply (@monic Sets _ _ (to i) (iso_to_monic i)).
  apply objectwise_candidate_subsingleton.
Qed.

End AwodeyPointwise.

(** ** G: section F, unconditionally *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Psh2_Cart : @Cartesian ([_2^op, Sets]) :=
  @Functor_Category_Cartesian (_2^op) Sets Sets_Cartesian.

Definition Psh2_Closed : @Closed ([_2^op, Sets]) Psh2_Cart :=
  Functor_Category_Closed _2.

(* Two provably distinct points of (Q^P) TwoY, with no hypothesis. *)
Definition pq_point_distinct_unconditional :
  pq_point Psh2_Cart Psh2_Closed true
    ≈ pq_point Psh2_Cart Psh2_Closed false -> False
  := pq_point_distinct Psh2_Cart Psh2_Closed.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition awodey_pointwise_not_exponential_unconditional :
  @Isomorphism Sets
    ((@exponent_obj _ Psh2_Cart Psh2_Closed PresheafP PresheafQ) TwoY)
    objectwise_candidate -> False
  := awodey_pointwise_not_exponential Psh2_Cart Psh2_Closed.
