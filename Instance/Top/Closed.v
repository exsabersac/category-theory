Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Top.

Generalizable All Variables.

(** * Closed sets, and the complementation duality *)

(*
 nLab:      https://ncatlab.org/nlab/show/closed+subset
 nLab:      https://ncatlab.org/nlab/show/frame
 Wikipedia: https://en.wikipedia.org/wiki/Closed_set

   本文件给出闭结构实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab: https://ncatlab.org/nlab/show/excluded+middle
   nLab: https://ncatlab.org/nlab/show/double+negation

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Opens and closed sets of a space *)

(* An open of X, as an object: the predicate together with its openness. *)
Definition OpenSet (X : TopSpace) : Type := { U : X → Type & IsOpen X U }.

(* A closed set of X: the closed predicate, its complementing open (as
   data, per design note 1), and the agreement between the two. *)
Record ClosedSet (X : TopSpace) := {
  closed_pred : X → Type;                       (* the closed predicate *)
  closed_compl : X → Type;                      (* its complementing open *)
  closed_compl_open : IsOpen X closed_compl;    (* which is indeed open *)

  (* the closed predicate is the negation of the complementing open *)
  closed_agree : ∀ x : X, closed_pred x ↔ ¬ (closed_compl x)
}.

Arguments closed_pred {X} _ _.
Arguments closed_compl {X} _ _.
Arguments closed_compl_open {X} _.
Arguments closed_agree {X} _ _.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition open_complement {X : TopSpace} (U : OpenSet X) : ClosedSet X := {|
  closed_pred       := fun x => ¬ (`1 U x);
  closed_compl      := `1 U;
  closed_compl_open := `2 U;
  closed_agree      := fun x => (fun h => h, fun h => h)
|}.

(* ... and back: a closed set already carries its complementing open. *)
Definition closed_interior {X : TopSpace} (C : ClosedSet X) : OpenSet X :=
  (closed_compl C; closed_compl_open C).

(* The chosen order on closed sets implies inclusion of the closed
   predicates — the direction that survives without excluded middle. *)
Lemma closed_order_implies_inclusion {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_compl D x → closed_compl C x) →
  ∀ x : X, closed_pred C x → closed_pred D x.
Proof.
  intros Hincl x Hc.
  exact (snd (closed_agree D x) (fun hd => fst (closed_agree C x) Hc (Hincl x hd))).
Qed.

(* Likewise for the setoid: agreement of complementing opens implies
   agreement of the closed predicates. *)
Lemma closed_equiv_implies_pred_equiv {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_compl C x ↔ closed_compl D x) →
  ∀ x : X, closed_pred C x ↔ closed_pred D x.
Proof.
  intros Heq x; split.
  - exact (closed_order_implies_inclusion C D (fun y h => snd (Heq y) h) x).
  - exact (closed_order_implies_inclusion D C (fun y h => fst (Heq y) h) x).
Qed.

(** ** The two thin categories *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Opens (X : TopSpace) : Category := {|
  obj     := OpenSet X;
  hom     := fun U V => ∀ x : X, `1 U x → `1 V x;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun U x u => u;
  compose := fun U V W g f x u => g x (f x u)
|}.

(* The closed sets of X as a thin category, ordered by REVERSE inclusion of
   the complementing opens (design note 2).  By
   [closed_order_implies_inclusion] an arrow `C ~> D` does entail
   `C ⊆ D` on the closed predicates. *)
Program Definition Closeds (X : TopSpace) : Category := {|
  obj     := ClosedSet X;
  hom     := fun C D => ∀ x : X, closed_compl D x → closed_compl C x;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun C x u => u;
  compose := fun C D E g f x u => f x (g x u)
|}.

(** ** Complementation as an isomorphism of categories *)

(* Forward: an open goes to its complement.  An inclusion `U ⊆ V` is
   literally the arrow required in `(Closeds X)^op`, namely the inclusion
   of the complementing opens. *)
Program Definition OpenCompl (X : TopSpace) : Opens X ⟶ (Closeds X)^op := {|
  fobj := fun U => open_complement U;
  fmap := fun U V g => g
|}.

(* Backward: a closed set goes to its complementing open. *)
Program Definition ClosedCompl (X : TopSpace) : (Closeds X)^op ⟶ Opens X := {|
  fobj := fun C => closed_interior C;
  fmap := fun C D g => g
|}.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Opens_Closeds_iso (X : TopSpace) :
  Opens X ≅[Cat] (Closeds X)^op := {|
  to   := OpenCompl X;
  from := ClosedCompl X
|}.
Next Obligation.
  unshelve eexists.
  - intro C; unshelve econstructor.
    + exact (fun x h => h).
    + exact (fun x h => h).
    + exact I.
    + exact I.
  - intros A B g; exact I.
Defined.
Next Obligation.
  unshelve eexists.
  - intro U; unshelve econstructor.
    + exact (fun x h => h).
    + exact (fun x h => h).
    + exact I.
    + exact I.
  - intros A B g; exact I.
Defined.

(** ** The two presheaves on Top *)

(* Preimage of an open along a continuous map is open — that IS continuity,
   and it is what makes the opens contravariantly functorial. *)
Definition open_preimage {X Y : TopSpace} (g : Y ~{Top}~> X) (U : OpenSet X) :
  OpenSet Y :=
  (fun y => `1 U (g y); continuity g (`1 U) (`2 U)).

(* Preimage of a closed set: both components are pulled back, the
   complementing open stays open by continuity, and the agreement field
   transports pointwise. *)
Definition closed_preimage {X Y : TopSpace} (g : Y ~{Top}~> X)
           (C : ClosedSet X) : ClosedSet Y := {|
  closed_pred       := fun y => closed_pred C (g y);
  closed_compl      := fun y => closed_compl C (g y);
  closed_compl_open := continuity g (closed_compl C) (closed_compl_open C);
  closed_agree      := fun y => closed_agree C (g y)
|}.

(* The setoid of opens of X, as an object of [Sets]: two opens are
   identified when their predicates agree pointwise (up to the library's
   Type-valued `↔`). *)
Definition OpenSets (X : TopSpace) : obj[Sets].
Proof.
  refine {| carrier   := OpenSet X
          ; is_setoid := {| equiv := fun U V => ∀ x : X, `1 U x ↔ `1 V x |} |}.
  constructor.
  - intros U x; split; exact (fun h => h).
  - intros U V H x; split; [ exact (snd (H x)) | exact (fst (H x)) ].
  - intros U V W H1 H2 x; split.
    + exact (fun h => fst (H2 x) (fst (H1 x) h)).
    + exact (fun h => snd (H1 x) (snd (H2 x) h)).
Defined.

(* The setoid of closed sets of X, compared through their complementing
   opens (design note 2). *)
Definition ClosedSets (X : TopSpace) : obj[Sets].
Proof.
  refine {| carrier   := ClosedSet X
          ; is_setoid := {| equiv := fun C D => ∀ x : X,
                              closed_compl C x ↔ closed_compl D x |} |}.
  constructor.
  - intros C x; split; exact (fun h => h).
  - intros C D H x; split; [ exact (snd (H x)) | exact (fst (H x)) ].
  - intros C D E H1 H2 x; split.
    + exact (fun h => fst (H2 x) (fst (H1 x) h)).
    + exact (fun h => snd (H1 x) (snd (H2 x) h)).
Defined.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Obligation Tactic := idtac.

(* The presheaf of opens: contravariant on [Top], acting by preimage. *)
Program Definition OpensF : Top^op ⟶ Sets := {|
  fobj := fun X => OpenSets X;
  fmap := fun X Y f => {| morphism := open_preimage (unop f) |}
|}.
Next Obligation.
  (* the preimage map respects `≈` of opens *)
  intros X Y f U V H y; exact (H (unop f y)).
Qed.
Next Obligation.
  (* fmap respects `≈` of morphisms: equivalent maps have, pointwise,
     equivalent preimages, because an open respects the carrier's `≈` *)
  intros X Y f g Hfg U y; split.
  - exact (open_proper X (`1 U) (`2 U) (unop f y) (unop g y) (Hfg y)).
  - exact (open_proper X (`1 U) (`2 U) (unop g y) (unop f y)
             (symmetry (Hfg y))).
Qed.
Next Obligation.
  (* the preimage along the identity is the identity *)
  intros X U y; split; exact (fun h => h).
Qed.
Next Obligation.
  (* preimages compose contravariantly, definitionally *)
  intros X Y Z f g U y; split; exact (fun h => h).
Qed.

(* The presheaf of closed sets, likewise.  Everything happens on the
   complementing open, which is exactly the component the setoid compares. *)
Program Definition ClosedsF : Top^op ⟶ Sets := {|
  fobj := fun X => ClosedSets X;
  fmap := fun X Y f => {| morphism := closed_preimage (unop f) |}
|}.
Next Obligation.
  intros X Y f C D H y; exact (H (unop f y)).
Qed.
Next Obligation.
  intros X Y f g Hfg C y; split.
  - exact (open_proper X (closed_compl C) (closed_compl_open C)
             (unop f y) (unop g y) (Hfg y)).
  - exact (open_proper X (closed_compl C) (closed_compl_open C)
             (unop g y) (unop f y) (symmetry (Hfg y))).
Qed.
Next Obligation.
  intros X C y; split; exact (fun h => h).
Qed.
Next Obligation.
  intros X Y Z f g C y; split; exact (fun h => h).
Qed.

(** ** Complementation is natural *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition complement_at (X : TopSpace) :
  OpenSets X ~{Sets}~> ClosedSets X := {|
  morphism := @open_complement X
|}.
Next Obligation. intros X U V H x; exact (H x). Qed.

Program Definition interior_at (X : TopSpace) :
  ClosedSets X ~{Sets}~> OpenSets X := {|
  morphism := @closed_interior X
|}.
Next Obligation. intros X C D H x; exact (H x). Qed.

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition complement_transform : OpensF ⟹ ClosedsF := {|
  transform := complement_at
|}.
Next Obligation. intros X Y f U y; split; exact (fun h => h). Qed.
Next Obligation. intros X Y f U y; split; exact (fun h => h). Qed.

Program Definition interior_transform : ClosedsF ⟹ OpensF := {|
  transform := interior_at
|}.
Next Obligation. intros X Y f C y; split; exact (fun h => h). Qed.
Next Obligation. intros X Y f C y; split; exact (fun h => h). Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition complement_natural : OpensF ≅[Fun] ClosedsF := {|
  to   := complement_transform;
  from := interior_transform
|}.
Next Obligation. intros X C y; split; exact (fun h => h). Qed.
Next Obligation. intros X U y; split; exact (fun h => h). Qed.

(* ------------------------------------------------------------------------ *)
(** ** The exact price of the classical reading *)

(*
   本节说明 Closed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pred_comparison_forces_DNE :
  (∀ (X : TopSpace) (C D : ClosedSet X),
      (∀ x : X, closed_pred C x ↔ closed_pred D x) →
      (∀ x : X, closed_compl C x ↔ closed_compl D x)) →
  ∀ P : Type, ¬ ¬ P → P.
Proof.
  intros Hconv P.
  pose (CP := open_complement (X:=Point_Top)
                ((fun _ : Point_Top => P); open_const Point_Top P)).
  pose (CN := open_complement (X:=Point_Top)
                ((fun _ : Point_Top => (¬ ¬ P : Type));
                 open_const Point_Top (¬ ¬ P : Type))).
  assert (Hpred : ∀ x : Point_Top, closed_pred CP x ↔ closed_pred CN x).
  { intro x; split.
    - intros np nnp; exact (nnp np).
    - intros nnnp p; exact (nnnp (fun np => np p)). }
  exact (snd (Hconv Point_Top CP CN Hpred ttt)).
Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Classical.

Hypothesis DNE : ∀ P : Type, ¬ ¬ P → P.

Lemma closed_inclusion_implies_order_classical
  {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_pred C x → closed_pred D x) →
  (∀ x : X, closed_compl D x → closed_compl C x).
Proof using DNE.
  intros Hincl x Hd.
  apply (DNE (closed_compl C x)).
  intro Hnc.
  exact (fst (closed_agree D x) (Hincl x (snd (closed_agree C x) Hnc)) Hd).
Qed.

Lemma closed_pred_equiv_implies_equiv_classical
  {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_pred C x ↔ closed_pred D x) →
  (∀ x : X, closed_compl C x ↔ closed_compl D x).
Proof using DNE.
  intros H x; split.
  - intro Hc; exact (closed_inclusion_implies_order_classical D C
                       (fun y => snd (H y)) x Hc).
  - intro Hd; exact (closed_inclusion_implies_order_classical C D
                       (fun y => fst (H y)) x Hd).
Qed.

End Classical.
