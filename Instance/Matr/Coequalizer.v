(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.QArith.QArith.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Field.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Parallel.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Instance.Matr.Elimination.
Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section MatrCoequalizer.

(** ** The base: a field with a zero test

    [Kdec] has the type Instance/Field.v's [field_dec_stable] takes; see
    the header for why nothing weaker will do. *)

Context (K : FieldObject).
Context (Kdec : ∀ a b : carrier (rig_setoid K), (a ≈ b) + (a ≈ b → False)).

(** ** The construction

    A basis of the left null space of the difference.  Everything else in
    this section reads that one record through the category's
    vocabulary. *)

Definition matr_lnb {m n : nat} (A B : n ~{Matr K}~> m) :
  LeftNullBasis K (mat_sub K A B) :=
  left_null_basis K Kdec (mat_sub K A B).

(* The coequalizer object: the dimension of the left null space of
   A − B.  Typed as an object of [Matr K], which is [nat]. *)
Definition matr_coeq_obj {m n : nat} (A B : n ~{Matr K}~> m) : Matr K :=
  lnb_dim (matr_lnb A B).

(* The coequalizing map: a basis matrix with k rows and m columns, which
   is what an arrow [m ~> k] of [Matr K] is. *)
Definition matr_coeq_map {m n : nat} (A B : n ~{Matr K}~> m) :
  m ~{Matr K}~> matr_coeq_obj A B :=
  lnb_basis (matr_lnb A B).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition matr_coeq_cofork {m n : nat} (A B : n ~{Matr K}~> m) :
  matr_coeq_map A B ∘ A ≈[Matr K] matr_coeq_map A B ∘ B :=
  fst (mat_mul_sub_zero_iff K Kdec (matr_coeq_map A B) A B)
    (lnb_annih (matr_lnb A B)).

(* Kept a transparent [Definition] on purpose: this is the field whose
   reduction the computing witnesses at the end of the file use. *)
Definition matr_coeq_desc {m n : nat} (A B : n ~{Matr K}~> m)
  (z : Matr K) (h : m ~{Matr K}~> z) (Hh : h ∘ A ≈[Matr K] h ∘ B) :
  ∃! u : matr_coeq_obj A B ~{Matr K}~> z,
    u ∘ matr_coeq_map A B ≈[Matr K] h :=
  lnb_univ (matr_lnb A B) z h
    (snd (mat_mul_sub_zero_iff K Kdec h A B) Hh).

(** ** Mac Lane §III.3 Exercise 3

    The elementary coequalizer of an arbitrary parallel pair, and then
    the class quantifying over every parallel pair. *)

Definition matr_IsCoequalizer {m n : nat} (A B : n ~{Matr K}~> m) :
  IsCoequalizer A B (matr_coeq_obj A B) (matr_coeq_map A B) :=
  {| cofork    := matr_coeq_cofork A B
   ; coeq_desc := fun z h Hh => matr_coeq_desc A B z h Hh |}.

(* Deliberately a [Definition] and not an [Instance]; see the header. *)
Definition Matr_HasCoequalizers : HasCoequalizers (Matr K) :=
  {| coeq := fun x y f g =>
       existT _ (matr_coeq_obj f g)
         (existT _ (matr_coeq_map f g) (matr_IsCoequalizer f g)) |}.

(** ** What the generic API then gives

    Nothing here is new content: each is an instantiation of a result of
    Structure/Coequalizer.v at the coequalizer just built. *)

(* A coequalizing map is an epimorphism ([coequalizer_epic]).  So every
   basis matrix the elimination engine returns is epic in [Matr K] — a
   fact about matrices reached with no matrix proof. *)
Definition matr_coeq_epic {m n : nat} (A B : n ~{Matr K}~> m) :
  Epic (matr_coeq_map A B) :=
  coequalizer_epic A B (matr_IsCoequalizer A B).

(*
   本节说明同构、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition matr_coeq_iso {m n : nat} (A B : n ~{Matr K}~> m)
  {q : Matr K} {e : m ~{Matr K}~> q} (E : IsCoequalizer A B q e) :
  q ≅ matr_coeq_obj A B :=
  coequalizer_unique A B E (matr_IsCoequalizer A B).

(* The colimit packaging: the same data as a colimit over the walking
   parallel pair ([is_coequalizer_colimit]). *)
Definition matr_coeq_colimit {m n : nat} (A B : n ~{Matr K}~> m) :
  Coequalizer (APair A B) :=
  is_coequalizer_colimit A B (matr_IsCoequalizer A B).

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition matr_IsEqualizer_op {m n : nat} (A B : n ~{Matr K}~> m) :
  @IsEqualizer ((Matr K)^op) m n A B
    (matr_coeq_obj A B) (matr_coeq_map A B) :=
  IsEqualizer_op_of_IsCoequalizer (matr_IsCoequalizer A B).

Definition Matr_op_HasEqualizers : @HasEqualizers ((Matr K)^op) :=
  HasEqualizers_op_of_HasCoequalizers Matr_HasCoequalizers.

End MatrCoequalizer.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coeq_f2_A : 1%nat ~{Matr F2_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => true | _ => false end.

Definition coeq_f2_B : 1%nat ~{Matr F2_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => false | _ => true end.

Definition coeq_f2_obj : Matr F2_Field :=
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_B.

Definition coeq_f2_map : 2%nat ~{Matr F2_Field}~> coeq_f2_obj :=
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_B.

Definition coeq_f2 :
  IsCoequalizer coeq_f2_A coeq_f2_B coeq_f2_obj coeq_f2_map :=
  matr_IsCoequalizer F2_Field f2_dec coeq_f2_A coeq_f2_B.

(* The object and both entries of the coequalizing map, COMPUTED. *)
Example coeq_f2_obj_computes : coeq_f2_obj = 1%nat := eq_refl.

Example coeq_f2_map_0 : coeq_f2_map Fin.F1 Fin.F1 = true := eq_refl.

Example coeq_f2_map_1 :
  coeq_f2_map Fin.F1 (Fin.FS Fin.F1) = true := eq_refl.

(* The common composite E·A is the 1 × 1 matrix (1): the coequalizer
   does not collapse everything in sight. *)
Example coeq_f2_composite :
  (coeq_f2_map ∘ coeq_f2_A) Fin.F1 Fin.F1 = true := eq_refl.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma coeq_f2_obj_not_zero : coeq_f2_obj ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_f2_obj_not_two : coeq_f2_obj ≠ 2%nat.
Proof. discriminate. Qed.

Lemma coeq_f2_pair_distinct :
  coeq_f2_A ≈[Matr F2_Field] coeq_f2_B → False.
Proof.
  intro H.
  specialize (H Fin.F1 Fin.F1).
  discriminate H.
Qed.

Lemma coeq_f2_map_not_monic : Monic coeq_f2_map → False.
Proof.
  intros [HM].
  apply coeq_f2_pair_distinct.
  exact (HM 1%nat coeq_f2_A coeq_f2_B (cofork coeq_f2)).
Qed.

Definition coeq_f2_map_epic : Epic coeq_f2_map :=
  matr_coeq_epic F2_Field f2_dec coeq_f2_A coeq_f2_B.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coeq_f2_h : 2%nat ~{Matr F2_Field}~> 1%nat := fun _ _ => true.

Lemma coeq_f2_h_coforks :
  coeq_f2_h ∘ coeq_f2_A ≈[Matr F2_Field] coeq_f2_h ∘ coeq_f2_B.
Proof. intros i j; reflexivity. Qed.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coeq_f2_mediator :=
  coeq_desc coeq_f2 coeq_f2_h coeq_f2_h_coforks.

Example coeq_f2_mediator_computes :
  unique_obj coeq_f2_mediator Fin.F1 Fin.F1 = true := eq_refl.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example coeq_f2_map_h_agree_at :
  coeq_f2_map Fin.F1 Fin.F1 = coeq_f2_h Fin.F1 Fin.F1 := eq_refl.

(* The positive control for refuted attempt (iv): the duality bridge is
   definitional at this instantiation, even though the two record TYPES
   are not identified. *)
Example coeq_f2_op_is_bridge :
  matr_IsEqualizer_op F2_Field f2_dec coeq_f2_A coeq_f2_B
  = IsEqualizer_op_of_IsCoequalizer coeq_f2 := eq_refl.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example coeq_f2_self_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f2_A coeq_f2_A = 2%nat := eq_refl.

Example coeq_f2_self_map_diag :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A Fin.F1 Fin.F1 = true
  := eq_refl.

Example coeq_f2_self_map_off :
  matr_coeq_map F2_Field f2_dec coeq_f2_A coeq_f2_A
    Fin.F1 (Fin.FS Fin.F1) = false := eq_refl.

(* (ii) A difference that is invertible: the left null space is zero, so
   the coequalizer object is 0 and the coequalizing map has no rows. *)

Definition coeq_f2_I : 2%nat ~{Matr F2_Field}~> 2%nat :=
  fun i j => delta F2_Field i j.

Definition coeq_f2_O : 2%nat ~{Matr F2_Field}~> 2%nat := fun _ _ => false.

Example coeq_f2_iden_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f2_I coeq_f2_O = 0%nat := eq_refl.

(* (iii) Height 3, difference (1, 1, 0)ᵀ: the left null space is the
   plane {(a, b, c) : a + b = 0}, of dimension 2 — again neither 0 nor
   m = 3. *)

Definition coeq_f3_A : 1%nat ~{Matr F2_Field}~> 3%nat :=
  fun i _ => match i with
             | Fin.F1 => true
             | Fin.FS Fin.F1 => true
             | _ => false
             end.

Definition coeq_f3_B : 1%nat ~{Matr F2_Field}~> 3%nat := fun _ _ => false.

Example coeq_f3_obj :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B = 2%nat := eq_refl.

Lemma coeq_f3_obj_not_zero :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_f3_obj_not_three :
  matr_coeq_obj F2_Field f2_dec coeq_f3_A coeq_f3_B ≠ 3%nat.
Proof. discriminate. Qed.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition coeq_q_A : 1%nat ~{Matr Q_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => 3%Q | _ => 5%Q end.

Definition coeq_q_B : 1%nat ~{Matr Q_Field}~> 2%nat :=
  fun i _ => match i with Fin.F1 => 2%Q | _ => 3%Q end.

Definition coeq_q_obj : Matr Q_Field :=
  matr_coeq_obj Q_Field q_dec coeq_q_A coeq_q_B.

Definition coeq_q_map : 2%nat ~{Matr Q_Field}~> coeq_q_obj :=
  matr_coeq_map Q_Field q_dec coeq_q_A coeq_q_B.

Definition coeq_q :
  IsCoequalizer coeq_q_A coeq_q_B coeq_q_obj coeq_q_map :=
  matr_IsCoequalizer Q_Field q_dec coeq_q_A coeq_q_B.

Example coeq_q_obj_computes : coeq_q_obj = 1%nat := eq_refl.

Example coeq_q_map_0 : coeq_q_map Fin.F1 Fin.F1 = (-2 # 1)%Q := eq_refl.

Example coeq_q_map_1 :
  coeq_q_map Fin.F1 (Fin.FS Fin.F1) = (1 # 1)%Q := eq_refl.

(* Both legs of the cofork, computed on closed rational input. *)
Example coeq_q_left :
  (coeq_q_map ∘ coeq_q_A) Fin.F1 Fin.F1 = (-1 # 1)%Q := eq_refl.

Example coeq_q_right :
  (coeq_q_map ∘ coeq_q_B) Fin.F1 Fin.F1 = (-1 # 1)%Q := eq_refl.

Lemma coeq_q_obj_not_zero : coeq_q_obj ≠ 0%nat.
Proof. discriminate. Qed.

Lemma coeq_q_obj_not_two : coeq_q_obj ≠ 2%nat.
Proof. discriminate. Qed.

Lemma coeq_q_pair_distinct :
  coeq_q_A ≈[Matr Q_Field] coeq_q_B → False.
Proof.
  intro H.
  specialize (H Fin.F1 Fin.F1).
  discriminate H.
Qed.

Lemma coeq_q_map_not_monic : Monic coeq_q_map → False.
Proof.
  intros [HM].
  apply coeq_q_pair_distinct.
  exact (HM 1%nat coeq_q_A coeq_q_B (cofork coeq_q)).
Qed.

Definition coeq_q_map_epic : Epic coeq_q_map :=
  matr_coeq_epic Q_Field q_dec coeq_q_A coeq_q_B.
