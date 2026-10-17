Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Free.Quiver.

Generalizable All Variables.

(** * Opposite and product quivers *)

(*
   nLab: https://ncatlab.org/nlab/show/quiver

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Local Open Scope category_scope.

Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
Local Existing Instance edgeset.

(** ** The opposite quiver *)

Section OppositeQuiver.

(* Same nodes, every edge reversed.  The endpoint-indexed encoding makes this a
   pure reindexing: [edges y x] is already a type, so nothing is transported
   and no equality on nodes is consumed. *)
Definition QuiverOp@{o h p} (G : Quiver@{o h p}) : Quiver@{o h p} := {|
  nodes   := @nodes G;
  edges   := fun x y => @edges G y x;
  edgeset := fun x y => @edgeset G y x
|}.

(* What the three fields unfold to, recorded rather than described. *)
Definition QuiverOp_nodes@{o h p} (G : Quiver@{o h p}) :
  @nodes (QuiverOp G) = @nodes G := eq_refl.

Definition QuiverOp_edges@{o h p} (G : Quiver@{o h p}) (x y : @nodes G) :
  @edges (QuiverOp G) x y = @edges G y x := eq_refl.

Definition QuiverOp_edgeset@{o h p} (G : Quiver@{o h p}) (x y : @nodes G) :
  @edgeset (QuiverOp G) x y = @edgeset G y x := eq_refl.

(* Involution, at Leibniz equality of the whole [Quiver] record.  [Quiver] has
   primitive projections with eta conversion, so the doubly-reversed record is
   convertible to [G] itself rather than merely isomorphic to it. *)
Definition QuiverOp_invol@{o h p} (G : Quiver@{o h p}) :
  QuiverOp (QuiverOp G) = G := eq_refl.

(* 相关说明。 （已译） *)
Definition QuiverOp_map@{o1 h1 p1 o2 h2 p2}
  {G : Quiver@{o1 h1 p1}} {G' : Quiver@{o2 h2 p2}} (F : G ⇨ G') :
  QuiverOp G ⇨ QuiverOp G' :=
  Build_QuiverHomomorphism (QuiverOp G) (QuiverOp G')
    (@fnodes _ _ F)
    (fun x y => @fedgemap _ _ F y x)
    (fun x y => @fedgemap_respects _ _ F y x).

Definition QuiverOp_map_invol@{o1 h1 p1 o2 h2 p2}
  {G : Quiver@{o1 h1 p1}} {G' : Quiver@{o2 h2 p2}} (F : G ⇨ G') :
  QuiverOp_map (QuiverOp_map F) = F := eq_refl.

End OppositeQuiver.

(** ** The product quiver *)

Section ProductQuiver.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition edgeset_prod@{h1 p1 h2 p2 h p}
  {A : Type@{h1}} {B : Type@{h2}}
  (SA : Setoid@{h1 p1} A) (SB : Setoid@{h2 p2} B) : Setoid@{h p} (A * B) := {|
  equiv := fun f g =>
    (@equiv _ SA (fst f) (fst g) * @equiv _ SB (snd f) (snd g));
  setoid_equiv :=
    {| Equivalence_Reflexive := fun x =>
         (@Equivalence_Reflexive _ _ (@setoid_equiv _ SA) (fst x),
          @Equivalence_Reflexive _ _ (@setoid_equiv _ SB) (snd x))
     ; Equivalence_Symmetric := fun x y f =>
         (@Equivalence_Symmetric _ _ (@setoid_equiv _ SA) (fst x) (fst y) (fst f),
          @Equivalence_Symmetric _ _ (@setoid_equiv _ SB) (snd x) (snd y) (snd f))
     ; Equivalence_Transitive := fun x y z f g =>
         (@Equivalence_Transitive _ _ (@setoid_equiv _ SA)
            (fst x) (fst y) (fst z) (fst f) (fst g),
          @Equivalence_Transitive _ _ (@setoid_equiv _ SB)
            (snd x) (snd y) (snd z) (snd f) (snd g)) |}
|}.

(* 相关说明。 （已译） *)
Definition QuiverProd@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) : Quiver@{o h p} := {|
  nodes   := (@nodes G * @nodes H)%type;
  edges   := fun x y =>
    (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type;
  edgeset := fun x y =>
    edgeset_prod (@edgeset G (fst x) (fst y)) (@edgeset H (snd x) (snd y))
|}.

Definition QuiverProd_nodes@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) :
  @nodes (QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H)
    = (@nodes G * @nodes H)%type := eq_refl.

Definition QuiverProd_edges@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : @nodes G * @nodes H) :
  @edges (QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H) x y
    = (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type := eq_refl.

(* The two projections, as quiver homomorphisms. *)
Definition QuiverFst@{o1 h1 p1 o2 h2 p2 o h p}
  {G : Quiver@{o1 h1 p1}} {H : Quiver@{o2 h2 p2}} :
  QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H ⇨ G :=
  Build_QuiverHomomorphism (QuiverProd G H) G
    fst
    (fun x y => fst)
    (fun x y f g e => fst e).

Definition QuiverSnd@{o1 h1 p1 o2 h2 p2 o h p}
  {G : Quiver@{o1 h1 p1}} {H : Quiver@{o2 h2 p2}} :
  QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H ⇨ H :=
  Build_QuiverHomomorphism (QuiverProd G H) H
    snd
    (fun x y => snd)
    (fun x y f g e => snd e).

(* 相关说明。 （已译） *)
Definition QuiverPair
  {K G H : Quiver} (F : K ⇨ G) (F' : K ⇨ H) : K ⇨ QuiverProd G H :=
  Build_QuiverHomomorphism K (QuiverProd G H)
    (fun x => (F x, F' x))
    (fun x y e => (@fedgemap _ _ F x y e, @fedgemap _ _ F' x y e))
    (fun x y f g e =>
       (@fedgemap_respects _ _ F x y f g e, @fedgemap_respects _ _ F' x y f g e)).

(* Exchange of the two factors. *)
Definition QuiverSwap {G H : Quiver} : QuiverProd G H ⇨ QuiverProd H G :=
  Build_QuiverHomomorphism (QuiverProd G H) (QuiverProd H G)
    (fun x => (snd x, fst x))
    (fun x y e => (snd e, fst e))
    (fun x y f g e => (snd e, fst e)).

(* 相关说明。 （已译） *)
Definition QuiverSwap_is_pair {G H : Quiver} :
  @QuiverSwap G H = QuiverPair QuiverSnd QuiverFst := eq_refl.

End ProductQuiver.

(* * ** The 普遍性质 product quiver （已译） *)

Section ProductUniversal.

Context {K G H : Quiver}.

(*
   本节说明 Constructions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuiverPair_Fst (F : K ⇨ G) (F' : K ⇨ H) :
  @compose QuiverCategory K (QuiverProd G H) G QuiverFst (QuiverPair F F') = F
  := eq_refl.

Definition QuiverPair_Snd (F : K ⇨ G) (F' : K ⇨ H) :
  @compose QuiverCategory K (QuiverProd G H) H QuiverSnd (QuiverPair F F') = F'
  := eq_refl.

(*
   本节说明 Constructions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuiverPair_eta (M : K ⇨ QuiverProd G H) :
  @equiv _ (@homset QuiverCategory K (QuiverProd G H))
    M (QuiverPair (@compose QuiverCategory K (QuiverProd G H) G QuiverFst M)
                  (@compose QuiverCategory K (QuiverProd G H) H QuiverSnd M)).
Proof.
  unshelve eexists.
  - intro x; cbn; destruct (@fnodes _ _ M x); reflexivity.
  - intros x y f; cbn.
    generalize (@fedgemap _ _ M x y f).
    destruct (@fnodes _ _ M x), (@fnodes _ _ M y).
    intro e; cbn; split; reflexivity.
Defined.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QuiverPair_unique (M : K ⇨ QuiverProd G H) (F : K ⇨ G) (F' : K ⇨ H)
  (p : @compose QuiverCategory K (QuiverProd G H) G QuiverFst M = F)
  (q : @compose QuiverCategory K (QuiverProd G H) H QuiverSnd M = F') :
  @equiv _ (@homset QuiverCategory K (QuiverProd G H)) M (QuiverPair F F').
Proof.
  destruct p, q; exact (QuiverPair_eta M).
Defined.

End ProductUniversal.

(* Swapping twice 恒等, up [≈]; see header why one
 cannot [eq_refl]. （已译） *)
Definition QuiverSwap_invol {G H : Quiver} :
  @equiv _ (@homset QuiverCategory (QuiverProd G H) (QuiverProd G H))
    (@compose QuiverCategory (QuiverProd G H) (QuiverProd H G) (QuiverProd G H)
       QuiverSwap QuiverSwap)
    (@id QuiverCategory (QuiverProd G H)).
Proof.
  unshelve eexists.
  - intro x; destruct x; reflexivity.
  - intros [a b] [c d] e; cbn; split; reflexivity.
Defined.

(* * ** Preservation forgetful 函子 （已译） *)

Section Preservation.

(*
   本节说明 Constructions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition QuiverOfCat_Opposite@{o h p} (C : Category@{o h p}) :
  QuiverOfCat@{o h p} (C^op) = QuiverOp@{o h p} (QuiverOfCat@{o h p} C) := eq_refl.

Definition QuiverOfCat_Product@{o1 h1 p1 o2 h2 p2 o h p}
  (C : Category@{o1 h1 p1}) (D : Category@{o2 h2 p2}) :
  QuiverOfCat@{o h p} (C ∏ D)
    = QuiverProd@{o1 h1 p1 o2 h2 p2 o h p}
        (QuiverOfCat@{o1 h1 p1} C) (QuiverOfCat@{o2 h2 p2} D) := eq_refl.

(*
   本节说明 Constructions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Forgetful_fobj (C : Category) :
  fobj[Forgetful] C = QuiverOfCat C := eq_refl.

Definition Forgetful_preserves_op (C : Category) :
  fobj[Forgetful] (C^op) = QuiverOp (fobj[Forgetful] C) := eq_refl.

Definition Forgetful_preserves_prod (C D : Category) :
  fobj[Forgetful] (C ∏ D) = QuiverProd (fobj[Forgetful] C) (fobj[Forgetful] D)
  := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Forgetful_preserves_op_fmap
  {C D : Category} (F : C ⟶ D) :
  QuiverHomomorphismOfFunctor _ _ (Opposite_Functor F)
    = QuiverOp_map (QuiverHomomorphismOfFunctor _ _ F) := eq_refl.

(*
   本节说明 Constructions 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Forgetful_preserves_fst (C D : Category) :
  @equiv _ (@homset QuiverCategory (QuiverOfCat (C ∏ D)) (QuiverOfCat C))
    (QuiverHomomorphismOfFunctor _ _ (@Fst C D))
    (@QuiverFst (QuiverOfCat C) (QuiverOfCat D)).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Definition Forgetful_preserves_snd (C D : Category) :
  @equiv _ (@homset QuiverCategory (QuiverOfCat (C ∏ D)) (QuiverOfCat D))
    (QuiverHomomorphismOfFunctor _ _ (@Snd C D))
    (@QuiverSnd (QuiverOfCat C) (QuiverOfCat D)).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

End Preservation.
