Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Free.Quiver.

Generalizable All Variables.

(** * Coproducts of quivers *)

(*
   nLab: https://ncatlab.org/nlab/show/quiver
   nLab: https://ncatlab.org/nlab/show/coproduct

   本文件给出余积实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Open Scope category_scope.

Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
Local Existing Instance edgeset.

(** ** The empty edge setoid *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition False_Setoid@{h p} : Setoid@{h p} False := {|
  equiv := fun f (_ : False) => match f return Type@{p} with end;
  setoid_equiv :=
    {| Equivalence_Reflexive := fun x : False => match x with end
     ; Equivalence_Symmetric := fun x : False => match x with end
     ; Equivalence_Transitive := fun x : False => match x with end |}
|}.

(** ** The coproduct quiver *)

Section CoproductQuiver.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coprod_edges@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : (@nodes G + @nodes H)%type) : Type@{h} :=
  match x with
  | Datatypes.inl a =>
      match y with
      | Datatypes.inl b => @edges G a b
      | Datatypes.inr _ => False
      end
  | Datatypes.inr a =>
      match y with
      | Datatypes.inl _ => False
      | Datatypes.inr b => @edges H a b
      end
  end.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coprod_edgeset@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : (@nodes G + @nodes H)%type)
  : Setoid@{h p} (coprod_edges@{o1 h1 p1 o2 h2 p2 o h p} G H x y) :=
  match x with
  | Datatypes.inl a =>
      match y with
      | Datatypes.inl b => @edgeset G a b
      | Datatypes.inr _ => False_Setoid
      end
  | Datatypes.inr a =>
      match y with
      | Datatypes.inl _ => False_Setoid
      | Datatypes.inr b => @edgeset H a b
      end
  end.

Definition QuiverCoprod@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) : Quiver@{o h p} := {|
  nodes   := (@nodes G + @nodes H)%type;
  edges   := coprod_edges@{o1 h1 p1 o2 h2 p2 o h p} G H;
  edgeset := coprod_edgeset@{o1 h1 p1 o2 h2 p2 o h p} G H
|}.

(* What the fields unfold to, recorded rather than described. *)

Definition QuiverCoprod_nodes@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) :
  @nodes (QuiverCoprod@{o1 h1 p1 o2 h2 p2 o h p} G H)
    = (@nodes G + @nodes H)%type := eq_refl.

Context {G H : Quiver}.

Definition QuiverCoprod_edges_ll (a b : @nodes G) :
  @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inl b)
    = @edges G a b := eq_refl.

Definition QuiverCoprod_edges_rr (a b : @nodes H) :
  @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inr b)
    = @edges H a b := eq_refl.

(* 相关说明。 （已译） *)

Definition QuiverCoprod_edges_lr (a : @nodes G) (b : @nodes H) :
  @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inr b)
    = False := eq_refl.

Definition QuiverCoprod_edges_rl (a : @nodes H) (b : @nodes G) :
  @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inl b)
    = False := eq_refl.

(* …and again eliminators, form consumer wants. Both are
 恒等 function: edge set IS [False], so nothing proved by
 these beyond making fact quotable. （已译） *)

Definition quiver_coprod_no_edge_lr (a : @nodes G) (b : @nodes H)
  (e : @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inr b))
  : False := e.

Definition quiver_coprod_no_edge_rl (a : @nodes H) (b : @nodes G)
  (e : @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inl b))
  : False := e.

(* 相关说明。 （已译） *)
Definition quiver_coprod_nodes_disjoint (a : @nodes G) (b : @nodes H)
  (p : @eq (@nodes (QuiverCoprod G H))
         (Datatypes.inl a) (Datatypes.inr b)) : False.
Proof. discriminate p. Defined.

End CoproductQuiver.

(** ** The two injections *)

Section Injections.

(* Both injections 恒等 edges: [edges (QuiverCoprod G H)
 (inl x) (inl y)] iota-reduces [edges G x y], so no map needed and
 respectfulness 恒等 too. （已译） *)

Definition QuiverInl@{o h p} {G H : Quiver@{o h p}} : G ⇨ QuiverCoprod G H :=
  Build_QuiverHomomorphism G (QuiverCoprod G H)
    Datatypes.inl
    (fun x y (e : @edges G x y) => e)
    (fun x y f g (e : f ≈ g) => e).

Definition QuiverInr@{o h p} {G H : Quiver@{o h p}} : H ⇨ QuiverCoprod G H :=
  Build_QuiverHomomorphism H (QuiverCoprod G H)
    Datatypes.inr
    (fun x y (e : @edges H x y) => e)
    (fun x y f g (e : f ≈ g) => e).

End Injections.

(** ** The copairing *)

Section Copair.

Context {G H R : Quiver}.
Context (F : G ⇨ R) (F' : H ⇨ R).

Definition copair_nodes (x : @nodes (QuiverCoprod G H)) : @nodes R :=
  match x with
  | Datatypes.inl a => F a
  | Datatypes.inr b => F' b
  end.

Definition copair_edges (x y : @nodes (QuiverCoprod G H))
  : @edges (QuiverCoprod G H) x y
      -> @edges R (copair_nodes x) (copair_nodes y).
Proof.
  destruct x as [a|a], y as [b|b]; cbn.
  - exact (@fedgemap _ _ F a b).
  - exact (fun e => match e with end).
  - exact (fun e => match e with end).
  - exact (@fedgemap _ _ F' a b).
Defined.

Definition copair_edges_respects (x y : @nodes (QuiverCoprod G H))
  : Proper (equiv ==> equiv) (copair_edges x y).
Proof.
  destruct x as [a|a], y as [b|b]; cbn.
  - exact (@fedgemap_respects _ _ F a b).
  - intros e; exact (match e with end).
  - intros e; exact (match e with end).
  - exact (@fedgemap_respects _ _ F' a b).
Defined.

Definition QuiverCopair : QuiverCoprod G H ⇨ R :=
  Build_QuiverHomomorphism (QuiverCoprod G H) R
    copair_nodes copair_edges copair_edges_respects.

End Copair.

Arguments QuiverCopair {G H R} F F'.

(* * ** The 普遍性质 coproduct quiver （已译） *)

Section CoproductUniversal.

Context {G H R : Quiver}.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition QuiverCopair_Inl (F : G ⇨ R) (F' : H ⇨ R) :
  @compose QuiverCategory G (QuiverCoprod G H) R (QuiverCopair F F')
    QuiverInl = F := eq_refl.

Definition QuiverCopair_Inr (F : G ⇨ R) (F' : H ⇨ R) :
  @compose QuiverCategory H (QuiverCoprod G H) R (QuiverCopair F F')
    QuiverInr = F' := eq_refl.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuiverCopair_eta (M : QuiverCoprod G H ⇨ R) :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R)
    M (QuiverCopair
         (@compose QuiverCategory G (QuiverCoprod G H) R M QuiverInl)
         (@compose QuiverCategory H (QuiverCoprod G H) R M QuiverInr)).
Proof.
  unshelve eexists.
  - intros [a|a]; reflexivity.
  - intros [a|a] [b|b] e; try (exact (match e with end)); cbn; reflexivity.
Defined.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuiverCopair_unique (M : QuiverCoprod G H ⇨ R)
  (F : G ⇨ R) (F' : H ⇨ R)
  (p : @equiv _ (@homset QuiverCategory G R)
         (@compose QuiverCategory G (QuiverCoprod G H) R M QuiverInl) F)
  (q : @equiv _ (@homset QuiverCategory H R)
         (@compose QuiverCategory H (QuiverCoprod G H) R M QuiverInr) F') :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R)
    M (QuiverCopair F F').
Proof.
  destruct p as [pn pc], q as [qn qc].
  unshelve eexists.
  - intros [a|a]; [ exact (pn a) | exact (qn a) ].
  - intros [a|a] [b|b] e; try (exact (match e with end)).
    + exact (pc a b e).
    + exact (qc a b e).
Defined.

(* 相关说明。 （已译） *)
Definition QuiverCopair_respects :
  Proper (@equiv _ (@homset QuiverCategory G R) ==>
          @equiv _ (@homset QuiverCategory H R) ==>
          @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R))
         (@QuiverCopair G H R).
Proof.
  intros F1 F2 [pn pc] F1' F2' [qn qc].
  unshelve eexists.
  - intros [a|a]; [ exact (pn a) | exact (qn a) ].
  - intros [a|a] [b|b] e; try (exact (match e with end)).
    + exact (pc a b e).
    + exact (qc a b e).
Defined.

End CoproductUniversal.

(** ** Exchange of the two summands *)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuiverCoswap {G H : Quiver} :
  QuiverCoprod G H ⇨ QuiverCoprod H G := QuiverCopair QuiverInr QuiverInl.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuiverCoswap_invol {G H : Quiver} :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) (QuiverCoprod G H))
    (@compose QuiverCategory (QuiverCoprod G H) (QuiverCoprod H G)
       (QuiverCoprod G H) (@QuiverCoswap H G) (@QuiverCoswap G H))
    (@id QuiverCategory (QuiverCoprod G H)).
Proof.
  unshelve eexists.
  - intros [a|a]; reflexivity.
  - intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance QuiverCategory_Cocartesian : @Cocartesian QuiverCategory.
Proof.
  unshelve refine (@Build_Cartesian (QuiverCategory^op)
                     QuiverCoprod
                     (fun _ _ _ F F' => QuiverCopair F F')
                     (fun _ _ => QuiverInl)
                     (fun _ _ => QuiverInr)
                     _ _).
  - intros x y z; exact QuiverCopair_respects.
  - simpl; intros x y z F F' M; split.
    + intro Heq; split.
      * exact (@compose_respects QuiverCategory _ _ _ _ _ Heq _ _
                 (reflexivity QuiverInl)).
      * exact (@compose_respects QuiverCategory _ _ _ _ _ Heq _ _
                 (reflexivity QuiverInr)).
    + intros [p q]; exact (QuiverCopair_unique M F F' p q).
Defined.

(* 相关说明。 （已译） *)

Definition Coprod_is_QuiverCoprod (G H : Quiver) :
  @Coprod QuiverCategory QuiverCategory_Cocartesian G H
    = QuiverCoprod G H := eq_refl.

Definition cocartesian_inl_is_QuiverInl (G H : Quiver) :
  @Structure.Cocartesian.inl QuiverCategory QuiverCategory_Cocartesian G H
    = @QuiverInl G H := eq_refl.

Definition cocartesian_inr_is_QuiverInr (G H : Quiver) :
  @Structure.Cocartesian.inr QuiverCategory QuiverCategory_Cocartesian G H
    = @QuiverInr G H := eq_refl.

Definition merge_is_QuiverCopair {G H R : Quiver} (F : G ⇨ R) (F' : H ⇨ R) :
  @merge QuiverCategory QuiverCategory_Cocartesian R G H F F'
    = QuiverCopair F F' := eq_refl.

(* * ** Preservation forgetful 函子 （已译） *)

Section Preservation.

Context (C D : Category).

(* 相关说明。 （已译） *)
Definition QuiverOfCat_Coproduct_nodes :
  @nodes (QuiverOfCat (C ∐ D))
    = @nodes (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)) := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition QuiverOfCat_Coproduct_edges_ll (a b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_rr (a b : obj[D]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inr a) (Datatypes.inr b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inr a) (Datatypes.inr b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_lr (a : obj[C]) (b : obj[D]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inr b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inr b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_rl (a : obj[D]) (b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inr a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inr a) (Datatypes.inl b) := eq_refl.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition QuiverOfCat_Coproduct_to :
  QuiverOfCat (C ∐ D) ⇨ QuiverCoprod (QuiverOfCat C) (QuiverOfCat D).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact Datatypes.id.
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun e => e) | exact (fun e : False => match e with end) ].
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun f g e => e)
            | exact (fun f : False => match f with end) ].
Defined.

Definition QuiverOfCat_Coproduct_from :
  QuiverCoprod (QuiverOfCat C) (QuiverOfCat D) ⇨ QuiverOfCat (C ∐ D).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact Datatypes.id.
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun e => e) | exact (fun e : False => match e with end) ].
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun f g e => e)
            | exact (fun f : False => match f with end) ].
Defined.

Definition QuiverOfCat_Coproduct_iso :
  @Isomorphism QuiverCategory (QuiverOfCat (C ∐ D))
    (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)).
Proof.
  unshelve eapply Build_Isomorphism.
  - exact QuiverOfCat_Coproduct_to.
  - exact QuiverOfCat_Coproduct_from.
  - unshelve eexists.
    + intros [a|a]; reflexivity.
    + intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
  - unshelve eexists.
    + intros [a|a]; reflexivity.
    + intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition CoproductInl : C ⟶ C ∐ D.
Proof.
  unshelve eapply Build_Functor.
  - exact Datatypes.inl.
  - intros x y f; exact f.
  - intros x y f g Hfg; exact Hfg.
  - intro x; reflexivity.
  - intros x y z f g; reflexivity.
Defined.

Definition CoproductInr : D ⟶ C ∐ D.
Proof.
  unshelve eapply Build_Functor.
  - exact Datatypes.inr.
  - intros x y f; exact f.
  - intros x y f g Hfg; exact Hfg.
  - intro x; reflexivity.
  - intros x y z f g; reflexivity.
Defined.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Forgetful_preserves_coprod_inl :
  @equiv _ (@homset QuiverCategory (QuiverOfCat C)
              (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)))
    (@compose QuiverCategory _ _ _ QuiverOfCat_Coproduct_to
       (QuiverHomomorphismOfFunctor _ _ CoproductInl))
    QuiverInl.
Proof.
  unshelve eexists.
  - intro a; reflexivity.
  - intros a b e; reflexivity.
Defined.

Definition Forgetful_preserves_coprod_inr :
  @equiv _ (@homset QuiverCategory (QuiverOfCat D)
              (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)))
    (@compose QuiverCategory _ _ _ QuiverOfCat_Coproduct_to
       (QuiverHomomorphismOfFunctor _ _ CoproductInr))
    QuiverInr.
Proof.
  unshelve eexists.
  - intro a; reflexivity.
  - intros a b e; reflexivity.
Defined.

End Preservation.

(** ** Non-degeneracy *)

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition LoopQ : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => poly_unit).

Definition TwoQ : Quiver :=
  Build_Quiver_Standard_Eq bool (fun _ _ => bool).

(* 相关说明。 （已译） *)

Definition loop_edge : @edges LoopQ ttt ttt := ttt.

Definition coprod_loop_edge_left :
  @edges (QuiverCoprod LoopQ LoopQ)
    (Datatypes.inl ttt) (Datatypes.inl ttt) := ttt.

Definition coprod_loop_edge_right :
  @edges (QuiverCoprod LoopQ LoopQ)
    (Datatypes.inr ttt) (Datatypes.inr ttt) := ttt.

Definition coprod_no_cross_edge
  (e : @edges (QuiverCoprod LoopQ LoopQ)
         (Datatypes.inl ttt) (Datatypes.inr ttt)) : False := e.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition injections_not_equivalent
  (p : @equiv _ (@homset QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ))
         QuiverInl QuiverInr) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

Section Witness.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Ffalse : LoopQ ⇨ TwoQ :=
  Build_QuiverHomomorphism LoopQ TwoQ
    (fun _ => false) (fun _ _ _ => false) (fun _ _ _ _ _ => eq_refl).

Definition Ftrue : LoopQ ⇨ TwoQ :=
  Build_QuiverHomomorphism LoopQ TwoQ
    (fun _ => true) (fun _ _ _ => true) (fun _ _ _ _ _ => eq_refl).

(* 相关说明。 （已译） *)

Definition copair_node_left :
  @fnodes _ _ (QuiverCopair Ffalse Ftrue) (Datatypes.inl ttt)
    = false := eq_refl.

Definition copair_node_right :
  @fnodes _ _ (QuiverCopair Ffalse Ftrue) (Datatypes.inr ttt)
    = true := eq_refl.

Definition copair_edge_left :
  @fedgemap _ _ (QuiverCopair Ffalse Ftrue)
    (Datatypes.inl ttt) (Datatypes.inl ttt) ttt = false := eq_refl.

Definition copair_edge_right :
  @fedgemap _ _ (QuiverCopair Ffalse Ftrue)
    (Datatypes.inr ttt) (Datatypes.inr ttt) ttt = true := eq_refl.

(* 相关说明。 （已译） *)
Definition Ffalse_neq_Ftrue
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ) Ffalse Ftrue) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

(* 相关说明。 （已译） *)
Definition copair_order_matters
  (p : @equiv _ (@homset QuiverCategory (QuiverCoprod LoopQ LoopQ) TwoQ)
         (QuiverCopair Ffalse Ftrue) (QuiverCopair Ftrue Ffalse)) : False.
Proof. destruct p as [pn _]; discriminate (pn (Datatypes.inl ttt)). Defined.

(*
   本节说明 Coproduct 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition copair_swap_fails_left
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ)
         (@compose QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ) TwoQ
            (QuiverCopair Ftrue Ffalse) QuiverInl)
         Ffalse) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

Definition copair_swap_fails_right
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ)
         (@compose QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ) TwoQ
            (QuiverCopair Ftrue Ffalse) QuiverInr)
         Ftrue) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

End Witness.
