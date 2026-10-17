Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Thin.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.

Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.

Generalizable All Variables.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance edgeset.

(*
   nLab: https://ncatlab.org/nlab/show/commutative+square
   nLab: https://ncatlab.org/nlab/show/free+category
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   Book: Riehl, Category Theory in Context, Dover 2016, §1.6,
   Book: Fong and Spivak, Seven Sketches in Compositionality, CUP 2019,

   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreeSquare : Category := FreeOnQuiver SquareQuiver.

(** The four generating edges, as one-step paths of the free category. *)
Definition wsq_f : Sq_A ~{FreeSquare}~> Sq_B :=
  tlist_singleton (B:=@edges SquareQuiver) Sq_f.
Definition wsq_g : Sq_A ~{FreeSquare}~> Sq_C :=
  tlist_singleton (B:=@edges SquareQuiver) Sq_g.
Definition wsq_h : Sq_B ~{FreeSquare}~> Sq_D :=
  tlist_singleton (B:=@edges SquareQuiver) Sq_h.
Definition wsq_k : Sq_C ~{FreeSquare}~> Sq_D :=
  tlist_singleton (B:=@edges SquareQuiver) Sq_k.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example free_diag_fh_is_composite :
  @compose FreeSquare _ _ _ wsq_h wsq_f = square_diag_fh := eq_refl.

Example free_diag_gk_is_composite :
  @compose FreeSquare _ _ _ wsq_k wsq_g = square_diag_gk := eq_refl.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wsq_spec (y : SquareNode) :
  ∀ x : SquareNode, (x ~{FreeSquare}~> y) → Type :=
  match y as y0 return ∀ x : SquareNode, (x ~{FreeSquare}~> y0) → Type with
  | Sq_A => fun x => match x as x0 return (x0 ~{FreeSquare}~> Sq_A) → Type with
      | Sq_A => fun p => p = tnil
      | Sq_B => fun _ => False
      | Sq_C => fun _ => False
      | Sq_D => fun _ => False
      end
  | Sq_B => fun x => match x as x0 return (x0 ~{FreeSquare}~> Sq_B) → Type with
      | Sq_A => fun p => p = wsq_f
      | Sq_B => fun p => p = tnil
      | Sq_C => fun _ => False
      | Sq_D => fun _ => False
      end
  | Sq_C => fun x => match x as x0 return (x0 ~{FreeSquare}~> Sq_C) → Type with
      | Sq_A => fun p => p = wsq_g
      | Sq_B => fun _ => False
      | Sq_C => fun p => p = tnil
      | Sq_D => fun _ => False
      end
  | Sq_D => fun x => match x as x0 return (x0 ~{FreeSquare}~> Sq_D) → Type with
      | Sq_A => fun p => ((p = square_diag_fh) + (p = square_diag_gk))%type
      | Sq_B => fun p => p = wsq_h
      | Sq_C => fun p => p = wsq_k
      | Sq_D => fun p => p = tnil
      end
  end.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem wsq_classify (y x : SquareNode) (p : x ~{FreeSquare}~> y) :
  wsq_spec y x p.
Proof.
  induction p as [ | i j e p IH ].
  - destruct y; reflexivity.
  - destruct e; destruct y; simpl in *;
      try contradiction;
      try (rewrite IH; reflexivity).
    + left;  rewrite IH; reflexivity.
    + right; rewrite IH; reflexivity.
Qed.

(** The seven empty hom-sets of the free square, read off the
    classification. *)
Corollary free_square_no_path_BA (p : Sq_B ~{FreeSquare}~> Sq_A) : False.
Proof. exact (wsq_classify _ _ p). Qed.

Corollary free_square_no_path_CA (p : Sq_C ~{FreeSquare}~> Sq_A) : False.
Proof. exact (wsq_classify _ _ p). Qed.

Corollary free_square_no_path_DA (p : Sq_D ~{FreeSquare}~> Sq_A) : False.
Proof. exact (wsq_classify _ _ p). Qed.

Corollary free_square_no_path_BC (p : Sq_B ~{FreeSquare}~> Sq_C) : False.
Proof. exact (wsq_classify _ _ p). Qed.

Corollary free_square_no_path_CB (p : Sq_C ~{FreeSquare}~> Sq_B) : False.
Proof. exact (wsq_classify _ _ p). Qed.

Corollary free_square_no_path_DB (p : Sq_D ~{FreeSquare}~> Sq_B) : False.
Proof. exact (wsq_classify _ _ p). Qed.

Corollary free_square_no_path_DC (p : Sq_D ~{FreeSquare}~> Sq_C) : False.
Proof. exact (wsq_classify _ _ p). Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition SquareEqn_count (x y : SquareQuiver) : nat :=
  match x, y with Sq_A, Sq_D => 1 | _, _ => 0 end.

Definition SquareEqn_lhs (x y : SquareQuiver) :
  Fin.t (SquareEqn_count x y) → x ~{FreeSquare}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact square_diag_fh ].
Defined.

Definition SquareEqn_rhs (x y : SquareQuiver) :
  Fin.t (SquareEqn_count x y) → x ~{FreeSquare}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact square_diag_gk ].
Defined.

Definition SquareEqns : FiniteEquations SquareQuiver := {|
  fe_count := SquareEqn_count;
  fe_lhs   := SquareEqn_lhs;
  fe_rhs   := SquareEqn_rhs
|}.

(** The quiver is finite, with the enumeration carried as data. *)
Definition Square_node (i : Fin.t 4) : SquareNode :=
  match i with
  | Fin.F1 => Sq_A
  | Fin.FS j =>
      match j with
      | Fin.F1 => Sq_B
      | Fin.FS l =>
          match l with
          | Fin.F1 => Sq_C
          | Fin.FS _ => Sq_D
          end
      end
  end.

Definition Square_index (x : SquareNode) : Fin.t 4 :=
  match x with
  | Sq_A => Fin.F1
  | Sq_B => Fin.FS Fin.F1
  | Sq_C => Fin.FS (Fin.FS Fin.F1)
  | Sq_D => Fin.FS (Fin.FS (Fin.FS Fin.F1))
  end.

Lemma Square_node_rt (x : SquareNode) : Square_node (Square_index x) = x.
Proof. destruct x; reflexivity. Qed.

Definition Square_ecount (x y : SquareNode) : nat :=
  match x, y with
  | Sq_A, Sq_B => 1
  | Sq_A, Sq_C => 1
  | Sq_B, Sq_D => 1
  | Sq_C, Sq_D => 1
  | _, _ => 0
  end.

Definition Square_edge (x y : SquareNode) :
  Fin.t (Square_ecount x y) → SquareEdge x y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i)
          | exact Sq_f | exact Sq_g | exact Sq_h | exact Sq_k ].
Defined.

Definition Square_eindex (x y : SquareNode) (e : SquareEdge x y) :
  Fin.t (Square_ecount x y) :=
  match e in SquareEdge a b return Fin.t (Square_ecount a b) with
  | Sq_f => Fin.F1
  | Sq_g => Fin.F1
  | Sq_h => Fin.F1
  | Sq_k => Fin.F1
  end.

Lemma Square_edge_rt (x y : SquareNode) (e : SquareEdge x y) :
  Square_edge x y (Square_eindex x y e) = e.
Proof. destruct e; reflexivity. Qed.

Definition SquareFinite : FiniteQuiver SquareQuiver :=
  @Build_FiniteQuiver SquareQuiver 4 Square_node Square_index Square_node_rt
    Square_ecount Square_edge Square_eindex Square_edge_rt.

Definition SquarePresentation : FinitePresentation := {|
  fp_quiver := SquareQuiver;
  fp_finite := SquareFinite;
  fp_eqns   := SquareEqns
|}.

(** The walking commutative square. *)
Definition Square : Category := FinitelyPresented SquarePresentation.

(** ...which is the presented category of the quiver and the relation,
    definitionally. *)
Example Square_is_presented :
  Square = PresentedQuiver SquareQuiver (fe_rel SquareEqns) := eq_refl.

(** The hom TYPES of [Square] are the free ones: equations merge, and
    never add. *)
Example Square_hom_is_free (x y : SquareNode) :
  (x ~{Square}~> y) = (x ~{FreeSquare}~> y) := eq_refl.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition square_f : Sq_A ~{Square}~> Sq_B :=
  @pgen SquareQuiver (fe_rel SquareEqns) _ _ Sq_f.
Definition square_g : Sq_A ~{Square}~> Sq_C :=
  @pgen SquareQuiver (fe_rel SquareEqns) _ _ Sq_g.
Definition square_h : Sq_B ~{Square}~> Sq_D :=
  @pgen SquareQuiver (fe_rel SquareEqns) _ _ Sq_h.
Definition square_k : Sq_C ~{Square}~> Sq_D :=
  @pgen SquareQuiver (fe_rel SquareEqns) _ _ Sq_k.

(** The imposed equation holds. *)
Lemma square_relation_holds :
  @equiv _ (@homset Square Sq_A Sq_D) square_diag_fh square_diag_gk.
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

(** The square commutes.  Both composites reduce to the corresponding
    two-step path definitionally, so this is [square_relation_holds]
    with no transport. *)
Theorem square_commutes :
  square_h ∘ square_f ≈ square_k ∘ square_g.
Proof. exact square_relation_holds. Qed.

(** The diagonal: the common value of the two composites.  It is DEFINED
    as one of them, and proved equal to the other. *)
Definition square_diagonal : Sq_A ~{Square}~> Sq_D := square_h ∘ square_f.

Example square_diagonal_via_B : square_diagonal = square_h ∘ square_f := eq_refl.

Lemma square_diagonal_via_C : square_diagonal ≈ square_k ∘ square_g.
Proof. exact square_commutes. Qed.

(** The diagonal is not a generator: the quiver has exactly four edges,
    computed from the [FiniteQuiver] data rather than asserted. *)
Definition square_generator_total : nat :=
  fold_right (fun q n => fq_edges SquareQuiver SquareFinite (fst q) (snd q) + n)%nat
             0%nat
    (list_prod (Sq_A :: Sq_B :: Sq_C :: Sq_D :: nil)
               (Sq_A :: Sq_B :: Sq_C :: Sq_D :: nil)).

Example square_generator_total_4 : square_generator_total = 4%nat := eq_refl.

(** ** Thinness, and the empty hom-sets

    Everything below is read off [wsq_classify]. *)

(** Any two parallel arrows of [Square] agree.  The only case with
    anything to prove is A → D, where the two classified paths are
    identified by exactly the imposed relation. *)
Theorem Square_Thin : Thin Square.
Proof.
  intros x y p q; destruct x, y;
    pose proof (wsq_classify _ _ p) as Hp;
    pose proof (wsq_classify _ _ q) as Hq;
    simpl in Hp, Hq;
    try contradiction;
    try (rewrite Hp, Hq; reflexivity).
  destruct Hp as [Hp|Hp], Hq as [Hq|Hq]; rewrite Hp, Hq.
  - reflexivity.
  - exact square_relation_holds.
  - symmetry; exact square_relation_holds.
  - reflexivity.
Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary square_endo_id {x : Square} (p : x ~> x) : p ≈ id.
Proof. exact (Square_Thin x x p id). Qed.

(** The seven hom-sets that carry no arrow.  [Square]'s hom types are
    the free ones, so these are the free emptiness results verbatim. *)
Corollary square_no_hom_BA (p : Sq_B ~{Square}~> Sq_A) : False.
Proof. exact (free_square_no_path_BA p). Qed.

Corollary square_no_hom_CA (p : Sq_C ~{Square}~> Sq_A) : False.
Proof. exact (free_square_no_path_CA p). Qed.

Corollary square_no_hom_DA (p : Sq_D ~{Square}~> Sq_A) : False.
Proof. exact (free_square_no_path_DA p). Qed.

Corollary square_no_hom_BC (p : Sq_B ~{Square}~> Sq_C) : False.
Proof. exact (free_square_no_path_BC p). Qed.

Corollary square_no_hom_CB (p : Sq_C ~{Square}~> Sq_B) : False.
Proof. exact (free_square_no_path_CB p). Qed.

Corollary square_no_hom_DB (p : Sq_D ~{Square}~> Sq_B) : False.
Proof. exact (free_square_no_path_DB p). Qed.

Corollary square_no_hom_DC (p : Sq_D ~{Square}~> Sq_C) : False.
Proof. exact (free_square_no_path_DC p). Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** Membership in a literal list, proved by walking it: try the head,
    otherwise step past it.  The walk terminates because [right] fails at
    the empty tail. *)
Local Ltac wsq_in := simpl; repeat (try (left; reflexivity); right).

Definition wsq_nodes : list SquareNode := Sq_A :: Sq_B :: Sq_C :: Sq_D :: nil.

Lemma wsq_nodes_complete (x : SquareNode) : In x wsq_nodes.
Proof. destruct x; wsq_in. Qed.

Lemma wsq_nodes_nodup : NoDup wsq_nodes.
Proof. repeat constructor; simpl; intuition congruence. Qed.

Definition wsq_all_pairs : list (SquareNode * SquareNode) :=
  list_prod wsq_nodes wsq_nodes.

Example wsq_all_pairs_16 : length wsq_all_pairs = 16%nat := eq_refl.

Lemma wsq_all_pairs_complete (x y : SquareNode) : In (x, y) wsq_all_pairs.
Proof.
  apply in_prod; apply wsq_nodes_complete.
Qed.

(** The nine inhabited endpoint pairs: the four loops, the four sides,
    and the diagonal. *)
Definition wsq_pairs : list (SquareNode * SquareNode) :=
  (Sq_A, Sq_A) :: (Sq_B, Sq_B) :: (Sq_C, Sq_C) :: (Sq_D, Sq_D) ::
  (Sq_A, Sq_B) :: (Sq_A, Sq_C) :: (Sq_B, Sq_D) :: (Sq_C, Sq_D) ::
  (Sq_A, Sq_D) :: nil.

Lemma wsq_pairs_nodup : NoDup wsq_pairs.
Proof. repeat constructor; simpl; intuition congruence. Qed.

(** Soundness: each listed pair really does carry an arrow. *)
Theorem wsq_pairs_sound (q : SquareNode * SquareNode) :
  In q wsq_pairs → fst q ~{Square}~> snd q.
Proof.
  destruct q as [x y]; intro H; destruct x, y; simpl in H;
    solve [ exact id
          | exact square_f | exact square_g
          | exact square_h | exact square_k
          | exact square_diagonal
          | exfalso; intuition congruence ].
Qed.

(** Completeness: no other pair does. *)
Theorem wsq_pairs_complete (x y : SquareNode) :
  (x ~{Square}~> y) → In (x, y) wsq_pairs.
Proof.
  intro p; destruct x, y;
    solve [ wsq_in | exfalso; exact (wsq_classify _ _ p) ].
Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wsq_homcount (x y : SquareNode) : nat :=
  match x, y with
  | Sq_A, Sq_A => 1 | Sq_A, Sq_B => 1 | Sq_A, Sq_C => 1 | Sq_A, Sq_D => 1
  | Sq_B, Sq_B => 1 | Sq_B, Sq_D => 1
  | Sq_C, Sq_C => 1 | Sq_C, Sq_D => 1
  | Sq_D, Sq_D => 1
  | _, _ => 0
  end.

Lemma wsq_homcount_pairs (x y : SquareNode) :
  (wsq_homcount x y = 1%nat) ↔ In (x, y) wsq_pairs.
Proof.
  destruct x, y; split; intro H;
    solve [ reflexivity | wsq_in | discriminate
          | exfalso; simpl in H; intuition congruence ].
Qed.

Definition square_arrow_total : nat :=
  fold_right (fun q n => wsq_homcount (fst q) (snd q) + n)%nat 0%nat
    wsq_all_pairs.

(** Mac Lane §II.8 Exercise 1: nine arrows. *)
Theorem square_arrow_total_9 : square_arrow_total = 9%nat.
Proof. reflexivity. Qed.

Definition square_identity_total : nat :=
  fold_right (fun x n => wsq_homcount x x + n)%nat 0%nat wsq_nodes.

(** ...four of them identities. *)
Theorem square_identity_total_4 : square_identity_total = 4%nat.
Proof. reflexivity. Qed.

Definition square_nonidentity_total : nat :=
  (square_arrow_total - square_identity_total)%nat.

(** ...and five of them not. *)
Theorem square_nonidentity_total_5 : square_nonidentity_total = 5%nat.
Proof. reflexivity. Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wsq_nonidentity_pairs : list (SquareNode * SquareNode) :=
  (Sq_A, Sq_B) :: (Sq_A, Sq_C) :: (Sq_B, Sq_D) :: (Sq_C, Sq_D) ::
  (Sq_A, Sq_D) :: nil.

Example wsq_nonidentity_pairs_5 : length wsq_nonidentity_pairs = 5%nat := eq_refl.

Lemma wsq_nonidentity_pairs_nodup : NoDup wsq_nonidentity_pairs.
Proof. repeat constructor; simpl; intuition congruence. Qed.

Lemma wsq_nonidentity_not_endo (q : SquareNode * SquareNode) :
  In q wsq_nonidentity_pairs → fst q = snd q → False.
Proof.
  destruct q as [x y]; destruct x, y; simpl;
    solve [ intros _ H; discriminate H
          | intro H; exfalso; intuition congruence ].
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition wsq_free_homcount (x y : SquareNode) : nat :=
  match x, y with
  | Sq_A, Sq_A => 1 | Sq_A, Sq_B => 1 | Sq_A, Sq_C => 1 | Sq_A, Sq_D => 2
  | Sq_B, Sq_B => 1 | Sq_B, Sq_D => 1
  | Sq_C, Sq_C => 1 | Sq_C, Sq_D => 1
  | Sq_D, Sq_D => 1
  | _, _ => 0
  end.

Definition free_square_arrow_total : nat :=
  fold_right (fun q n => wsq_free_homcount (fst q) (snd q) + n)%nat 0%nat
    wsq_all_pairs.

Theorem free_square_arrow_total_10 : free_square_arrow_total = 10%nat.
Proof. reflexivity. Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem free_square_diagonals_neq : square_diag_fh = square_diag_gk → False.
Proof.
  intro H; apply free_square_diagonals_distinct; rewrite H; reflexivity.
Qed.

Theorem square_quotient_merges_one :
  ((square_diag_fh = square_diag_gk → False) *
   @equiv _ (@homset Square Sq_A Sq_D) square_diag_fh square_diag_gk)%type.
Proof. exact (free_square_diagonals_neq, square_relation_holds). Qed.

(** The arithmetic of the merge, as a computation. *)
Example square_merge_arithmetic :
  (free_square_arrow_total - square_arrow_total)%nat = 1%nat := eq_refl.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** *** Rank: every edge raises it by exactly one *)

Definition wsq_rank (x : SquareNode) : nat :=
  match x with Sq_A => 0 | Sq_B => 1 | Sq_C => 1 | Sq_D => 2 end.

Lemma wsq_edge_rank {x y : SquareNode} (e : SquareEdge x y) :
  wsq_rank y = S (wsq_rank x).
Proof. destruct e; reflexivity. Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wsq_path_rank (x y : SquareNode) (p : x ~{FreeSquare}~> y) :
  wsq_rank y = (wsq_rank x + tlist_length p)%nat.
Proof.
  induction p as [ | i j e p IH ]; simpl.
  - now rewrite PeanoNat.Nat.add_0_r.
  - rewrite IH, (wsq_edge_rank e); simpl.
    now rewrite PeanoNat.Nat.add_succ_r.
Qed.

(** Five of the seven empty hom-sets, re-derived by arithmetic alone. *)
Corollary wsq_rank_no_path_BA (p : Sq_B ~{FreeSquare}~> Sq_A) : False.
Proof. pose proof (wsq_path_rank _ _ p) as H; discriminate H. Qed.

Corollary wsq_rank_no_path_CA (p : Sq_C ~{FreeSquare}~> Sq_A) : False.
Proof. pose proof (wsq_path_rank _ _ p) as H; discriminate H. Qed.

Corollary wsq_rank_no_path_DA (p : Sq_D ~{FreeSquare}~> Sq_A) : False.
Proof. pose proof (wsq_path_rank _ _ p) as H; discriminate H. Qed.

Corollary wsq_rank_no_path_DB (p : Sq_D ~{FreeSquare}~> Sq_B) : False.
Proof. pose proof (wsq_path_rank _ _ p) as H; discriminate H. Qed.

Corollary wsq_rank_no_path_DC (p : Sq_D ~{FreeSquare}~> Sq_C) : False.
Proof. pose proof (wsq_path_rank _ _ p) as H; discriminate H. Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary wsq_rank_cannot_decide_BC (p : Sq_B ~{FreeSquare}~> Sq_C) :
  tlist_length p = 0%nat.
Proof.
  pose proof (wsq_path_rank _ _ p) as H; simpl in H.
  now injection H.
Qed.

(*
   本节说明hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem square_hom_length (x y : SquareNode) (p : x ~{Square}~> y) :
  (wsq_rank x + tlist_length p)%nat = wsq_rank y.
Proof. symmetry; exact (wsq_path_rank x y p). Qed.

(** *** Length: invariant under the imposed congruence *)

(** Equivalent paths of the free category have equal length —
    [tlist'_equiv_lengths] ([Construction/Free/Quiver.v]) at this
    quiver. *)
Lemma wsq_equiv_length {x y : SquareNode} (p q : x ~{FreeSquare}~> y) :
  p ≈ q → tlist_length p = tlist_length q.
Proof. intro H; exact (tlist'_equiv_lengths _ _ _ _ _ _ _ H). Qed.

(** The single imposed equation relates two paths of the SAME length —
    both diagonals are two-step — which is what makes length survive the
    quotient. *)
Lemma wsq_relation_length {x y : SquareNode}
  (p q : x ~{FreeSquare}~> y) (Hr : fe_rel SquareEqns x y p q) :
  tlist_length p = tlist_length q.
Proof.
  destruct Hr as [i [Hp Hq]].
  destruct x, y; simpl in i; try solve [ exact (Fin.case0 _ i) ].
  simpl in Hp, Hq.
  rewrite (wsq_equiv_length _ _ Hp), (wsq_equiv_length _ _ Hq).
  reflexivity.
Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wsq_comp_length {G : Quiver} {x y z : FreeOnQuiver G}
  (f : y ~> z) (g : x ~> y) :
  tlist_length (f ∘ g) = (tlist_length g + tlist_length f)%nat.
Proof. exact (tlist_app_length g f). Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem square_length_invariant {x y : SquareNode} (p q : x ~{Square}~> y) :
  p ≈ q → tlist_length p = tlist_length q.
Proof.
  intro H.
  induction H as [ x y p q Hr | x y p q He | x y p q _ IH
                 | x y p q r _ IH1 _ IH2 | x y z f f' g g' _ IH1 _ IH2 ].
  - exact (wsq_relation_length p q Hr).
  - exact (wsq_equiv_length p q He).
  - now symmetry.
  - now transitivity (tlist_length q).
  - rewrite !wsq_comp_length.
    now rewrite IH1, IH2.
Qed.

(** The contrapositive, which is the form a reader wants: arrows of
    different length are never identified. *)
Corollary square_no_collapse {x y : SquareNode} (p q : x ~{Square}~> y) :
  (tlist_length p = tlist_length q → False) → p ≈ q → False.
Proof. intros Hne H; exact (Hne (square_length_invariant p q H)). Qed.

(** *** The diagonal is a composite, measured

    Each generator is a one-step path and the diagonal a two-step one,
    by computation. *)
Example square_f_length : tlist_length square_f = 1%nat := eq_refl.
Example square_g_length : tlist_length square_g = 1%nat := eq_refl.
Example square_h_length : tlist_length square_h = 1%nat := eq_refl.
Example square_k_length : tlist_length square_k = 1%nat := eq_refl.

Example square_diagonal_length : tlist_length square_diagonal = 2%nat := eq_refl.

(** Every generator's image is one step, uniformly. *)
Lemma square_gen_length {x y : SquareNode} (e : SquareEdge x y) :
  tlist_length (@pgen SquareQuiver (fe_rel SquareEqns) x y e) = 1%nat.
Proof. reflexivity. Qed.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem square_diagonal_is_two_steps (p : Sq_A ~{Square}~> Sq_D) :
  p ≈ square_diagonal → tlist_length p = 2%nat.
Proof.
  intro H.
  now rewrite (square_length_invariant p square_diagonal H).
Qed.

(** The other half of "not a generator", from the presentation rather
    than from the grading: the quiver has no edge A → D at all. *)
Lemma square_no_diagonal_edge (e : SquareEdge Sq_A Sq_D) : False.
Proof. inversion e. Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record CommutingSquare (C : Category) : Type := {
  csq_a : C;
  csq_b : C;
  csq_c : C;
  csq_d : C;
  csq_f : csq_a ~> csq_b;
  csq_g : csq_a ~> csq_c;
  csq_h : csq_b ~> csq_d;
  csq_k : csq_c ~> csq_d;
  csq_commutes : csq_h ∘ csq_f ≈ csq_k ∘ csq_g
}.

Arguments csq_a {C} _.
Arguments csq_b {C} _.
Arguments csq_c {C} _.
Arguments csq_d {C} _.
Arguments csq_f {C} _.
Arguments csq_g {C} _.
Arguments csq_h {C} _.
Arguments csq_k {C} _.
Arguments csq_commutes {C} _.

Section IndexShape.

Context {C : Category}.

Definition csq_node (S : CommutingSquare C) (n : SquareNode) : C :=
  match n with
  | Sq_A => csq_a S
  | Sq_B => csq_b S
  | Sq_C => csq_c S
  | Sq_D => csq_d S
  end.

Definition csq_edgemap (S : CommutingSquare C) (x y : SquareNode)
  (e : SquareEdge x y) : csq_node S x ~> csq_node S y :=
  match e in SquareEdge a b return csq_node S a ~> csq_node S b with
  | Sq_f => csq_f S
  | Sq_g => csq_g S
  | Sq_h => csq_h S
  | Sq_k => csq_k S
  end.

Definition square_quiver_hom (S : CommutingSquare C) :
  QuiverHomomorphism SquareQuiver (QuiverOfCat C).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact (csq_node S).
  - exact (csq_edgemap S).
  - intros x y u v Huv; simpl in Huv; subst; reflexivity.
Defined.

(** The one imposed relation is merged: that is exactly the square's
    commuting equation, modulo the trailing identity a [tlist] fold
    leaves behind. *)
Lemma square_quiver_hom_merges (S : CommutingSquare C) :
  ∀ x y (p q : x ~{FreeSquare}~> y), fe_rel SquareEqns x y p q →
    fmap[@InducedFunctor SquareQuiver C (square_quiver_hom S)] p
      ≈ fmap[@InducedFunctor SquareQuiver C (square_quiver_hom S)] q.
Proof.
  intros x y p q [i [Hp Hq]].
  destruct x, y; simpl in i; try solve [ exact (Fin.case0 _ i) ].
  simpl in Hp, Hq; rewrite Hp, Hq; simpl.
  rewrite !id_left.
  exact (csq_commutes S).
Qed.

(** The functor a commutative square names. *)
Definition SquareFunctor (S : CommutingSquare C) : Square ⟶ C :=
  @PresentedFunctor SquareQuiver (fe_rel SquareEqns) C
    (square_quiver_hom S) (square_quiver_hom_merges S).

(** It has the given objects, on the nose. *)
Example SquareFunctor_A (S : CommutingSquare C) :
  fobj[SquareFunctor S] Sq_A = csq_a S := eq_refl.
Example SquareFunctor_B (S : CommutingSquare C) :
  fobj[SquareFunctor S] Sq_B = csq_b S := eq_refl.
Example SquareFunctor_C (S : CommutingSquare C) :
  fobj[SquareFunctor S] Sq_C = csq_c S := eq_refl.
Example SquareFunctor_D (S : CommutingSquare C) :
  fobj[SquareFunctor S] Sq_D = csq_d S := eq_refl.

(** ...and the given morphisms, up to the fold's trailing identity. *)
Lemma SquareFunctor_f (S : CommutingSquare C) :
  fmap[SquareFunctor S] square_f ≈ csq_f S.
Proof.
  exact (@PresentedFunctor_gen SquareQuiver (fe_rel SquareEqns) C
           (square_quiver_hom S) (square_quiver_hom_merges S) _ _ Sq_f).
Qed.

Lemma SquareFunctor_g (S : CommutingSquare C) :
  fmap[SquareFunctor S] square_g ≈ csq_g S.
Proof.
  exact (@PresentedFunctor_gen SquareQuiver (fe_rel SquareEqns) C
           (square_quiver_hom S) (square_quiver_hom_merges S) _ _ Sq_g).
Qed.

Lemma SquareFunctor_h (S : CommutingSquare C) :
  fmap[SquareFunctor S] square_h ≈ csq_h S.
Proof.
  exact (@PresentedFunctor_gen SquareQuiver (fe_rel SquareEqns) C
           (square_quiver_hom S) (square_quiver_hom_merges S) _ _ Sq_h).
Qed.

Lemma SquareFunctor_k (S : CommutingSquare C) :
  fmap[SquareFunctor S] square_k ≈ csq_k S.
Proof.
  exact (@PresentedFunctor_gen SquareQuiver (fe_rel SquareEqns) C
           (square_quiver_hom S) (square_quiver_hom_merges S) _ _ Sq_k).
Qed.

(** The converse: a functor out of [Square] IS a commutative square, the
    equation coming from [square_commutes] under [fmap_respects]. *)
Lemma functor_square_commutes (F : Square ⟶ C) :
  fmap[F] square_h ∘ fmap[F] square_f ≈ fmap[F] square_k ∘ fmap[F] square_g.
Proof.
  rewrite <- !fmap_comp.
  apply fmap_respects.
  exact square_commutes.
Qed.

Definition CommutingSquareOfFunctor (F : Square ⟶ C) : CommutingSquare C := {|
  csq_a := fobj[F] Sq_A;
  csq_b := fobj[F] Sq_B;
  csq_c := fobj[F] Sq_C;
  csq_d := fobj[F] Sq_D;
  csq_f := fmap[F] square_f;
  csq_g := fmap[F] square_g;
  csq_h := fmap[F] square_h;
  csq_k := fmap[F] square_k;
  csq_commutes := functor_square_commutes F
|}.

(** Round trip one, on the square side: the objects come back on the
    nose and the morphisms up to [≈]. *)
Example square_round_obj_a (S : CommutingSquare C) :
  csq_a (CommutingSquareOfFunctor (SquareFunctor S)) = csq_a S := eq_refl.
Example square_round_obj_b (S : CommutingSquare C) :
  csq_b (CommutingSquareOfFunctor (SquareFunctor S)) = csq_b S := eq_refl.
Example square_round_obj_c (S : CommutingSquare C) :
  csq_c (CommutingSquareOfFunctor (SquareFunctor S)) = csq_c S := eq_refl.
Example square_round_obj_d (S : CommutingSquare C) :
  csq_d (CommutingSquareOfFunctor (SquareFunctor S)) = csq_d S := eq_refl.

Theorem square_round_morphisms (S : CommutingSquare C) :
  ((csq_f (CommutingSquareOfFunctor (SquareFunctor S)) ≈ csq_f S) *
   (csq_g (CommutingSquareOfFunctor (SquareFunctor S)) ≈ csq_g S) *
   (csq_h (CommutingSquareOfFunctor (SquareFunctor S)) ≈ csq_h S) *
   (csq_k (CommutingSquareOfFunctor (SquareFunctor S)) ≈ csq_k S))%type.
Proof.
  repeat split;
    [ exact (SquareFunctor_f S) | exact (SquareFunctor_g S)
    | exact (SquareFunctor_h S) | exact (SquareFunctor_k S) ].
Qed.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition square_round_obj (F : Square ⟶ C) (x : SquareNode) :
  fobj[F] x = csq_node (CommutingSquareOfFunctor F) x :=
  match x with
  | Sq_A => eq_refl
  | Sq_B => eq_refl
  | Sq_C => eq_refl
  | Sq_D => eq_refl
  end.

Theorem square_functor_round (F : Square ⟶ C) :
  ∀ (x y : SquareNode) (p : x ~{Square}~> y),
    hom_cast (square_round_obj F x) (square_round_obj F y) (fmap[F] p)
      ≈ fmap[SquareFunctor (CommutingSquareOfFunctor F)] p.
Proof.
  apply (@PresentedFunctor_unique SquareQuiver (fe_rel SquareEqns) C
           (square_quiver_hom (CommutingSquareOfFunctor F))
           (square_quiver_hom_merges (CommutingSquareOfFunctor F))
           F (square_round_obj F)).
  intros x y e; destruct e; reflexivity.
Qed.

(** ...and the same, packaged as an equality of functors in
    [StrictCat]. *)
Theorem square_functor_round_strict (F : Square ⟶ C) :
  @equiv _ (@Functor_StrictEq_Setoid Square C)
    F (SquareFunctor (CommutingSquareOfFunctor F)).
Proof.
  apply (strict_of_hom_cast F (SquareFunctor (CommutingSquareOfFunctor F))
           (square_round_obj F)).
  exact (square_functor_round F).
Qed.

(** The universal property, bundled: to give a functor out of [Square]
    is exactly to give a commutative square, and the functor is unique
    at strict strength. *)
Theorem square_universal (S : CommutingSquare C) :
  { F : Square ⟶ C &
  { Hobj : ∀ x : SquareNode, fobj[F] x = csq_node S x &
    (((hom_cast (Hobj Sq_A) (Hobj Sq_B) (fmap[F] square_f) ≈ csq_f S) *
      (hom_cast (Hobj Sq_A) (Hobj Sq_C) (fmap[F] square_g) ≈ csq_g S) *
      (hom_cast (Hobj Sq_B) (Hobj Sq_D) (fmap[F] square_h) ≈ csq_h S) *
      (hom_cast (Hobj Sq_C) (Hobj Sq_D) (fmap[F] square_k) ≈ csq_k S)) *
     (∀ (K : Square ⟶ C) (Hobj' : ∀ x : SquareNode, fobj[K] x = csq_node S x),
        (∀ (x y : SquareNode) (e : SquareEdge x y),
           hom_cast (Hobj' x) (Hobj' y)
             (fmap[K] (@pgen SquareQuiver (fe_rel SquareEqns) x y e))
             ≈ csq_edgemap S x y e) →
        ∀ (x y : SquareNode) (p : x ~{Square}~> y),
          hom_cast (Hobj' x) (Hobj' y) (fmap[K] p)
            ≈ hom_cast (Hobj x) (Hobj y) (fmap[F] p)))%type } }.
Proof.
  exists (SquareFunctor S), (fun _ => eq_refl).
  split; [ repeat split | ].
  - exact (SquareFunctor_f S).
  - exact (SquareFunctor_g S).
  - exact (SquareFunctor_h S).
  - exact (SquareFunctor_k S).
  - intros K Hobj' Hgen x y p.
    exact (@PresentedFunctor_unique SquareQuiver (fe_rel SquareEqns) C
             (square_quiver_hom S) (square_quiver_hom_merges S)
             K Hobj' Hgen x y p).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition arrow_dom (S : CommutingSquare C) : @Arrow C :=
  ((csq_a S, csq_c S); csq_g S).

Definition arrow_cod (S : CommutingSquare C) : @Arrow C :=
  ((csq_b S, csq_d S); csq_h S).

Definition arrow_of_square (S : CommutingSquare C) :
  arrow_dom S ~{@Arrow C}~> arrow_cod S :=
  ((csq_f S, csq_k S); csq_commutes S).

Definition square_of_arrow {x y : @Arrow C} (u : x ~> y) : CommutingSquare C := {|
  csq_a := fst (``x);
  csq_b := fst (``y);
  csq_c := snd (``x);
  csq_d := snd (``y);
  csq_f := fst (``u);
  csq_g := `2 x;
  csq_h := `2 y;
  csq_k := snd (``u);
  csq_commutes := `2 u
|}.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example square_arrow_round (S : CommutingSquare C) :
  square_of_arrow (arrow_of_square S) = S := eq_refl.

(*
   本节说明 Square 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma arrow_square_round_dom (x y : @Arrow C) (u : x ~> y) :
  arrow_dom (square_of_arrow u) = x.
Proof. destruct x as [[a c] v]; reflexivity. Qed.

Lemma arrow_square_round_cod (x y : @Arrow C) (u : x ~> y) :
  arrow_cod (square_of_arrow u) = y.
Proof. destruct y as [[b d] w]; reflexivity. Qed.

(** ...and so does the morphism.  Stated with the endpoints already in
    pair form, since otherwise the two sides do not even have the same
    type. *)
Lemma arrow_square_round_mor (a b c d : C) (v : a ~> c) (w : b ~> d)
  (u : ((a, c); v) ~{@Arrow C}~> ((b, d); w)) :
  arrow_of_square (square_of_arrow u) = u.
Proof. destruct u as [[p q] Hu]; reflexivity. Qed.

End IndexShape.

Arguments SquareFunctor {C} _.
Arguments CommutingSquareOfFunctor {C} _.
Arguments arrow_dom {C} _.
Arguments arrow_cod {C} _.
Arguments arrow_of_square {C} _.
Arguments square_of_arrow {C x y} _.
