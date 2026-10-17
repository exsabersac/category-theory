Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.

Generalizable All Variables.

(** * Split coequalizers are absolute *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Coequaliser
   nLab: absolute colimit), and split coequalizers are the archetypal

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The equational data: a cofork e over the pair, a section s splitting e,
   and a section t of f mediating between s ∘ e and the pair. *)
Record SplitCoequalizer {C : Category} {x y : C} (f g : x ~> y) := {
  scoeq_obj : C;

  scoeq_e : y ~> scoeq_obj;   (* the coequalizing map *)
  scoeq_s : scoeq_obj ~> y;   (* section of e *)
  scoeq_t : y ~> x;           (* section of f *)

  scoeq_law1 : scoeq_e ∘ f ≈ scoeq_e ∘ g;       (* e coforks the pair *)
  scoeq_law2 : scoeq_e ∘ scoeq_s ≈ id;          (* s splits e *)
  scoeq_law3 : f ∘ scoeq_t ≈ id;                (* t splits f *)
  scoeq_law4 : g ∘ scoeq_t ≈ scoeq_s ∘ scoeq_e  (* g ∘ t computes s ∘ e *)
}.

Arguments scoeq_obj  {_ _ _ _ _} _.
Arguments scoeq_e    {_ _ _ _ _} _.
Arguments scoeq_s    {_ _ _ _ _} _.
Arguments scoeq_t    {_ _ _ _ _} _.
Arguments scoeq_law1 {_ _ _ _ _} _.
Arguments scoeq_law2 {_ _ _ _ _} _.
Arguments scoeq_law3 {_ _ _ _ _} _.
Arguments scoeq_law4 {_ _ _ _ _} _.

(** ** A split coequalizer is a coequalizer *)

(* Descent through a split coequalizer: a coforking map h descends as
   h ∘ s, and the splitting of e makes this the only possibility. *)
Lemma split_coeq_desc {C : Category} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : scoeq_obj S ~> z, u ∘ scoeq_e S ≈ h.
Proof.
  unshelve eapply Build_Unique.
  - exact (h ∘ scoeq_s S).
  - (* (h ∘ s) ∘ e ≈ h: trade s ∘ e for g ∘ t (law 4), g for f under h
       (the cofork hypothesis), then cancel t against f (law 3) *)
    rewrite <- comp_assoc.
    rewrite <- (scoeq_law4 S).
    rewrite comp_assoc.
    rewrite <- Hh.
    rewrite <- comp_assoc.
    rewrite (scoeq_law3 S).
    apply id_right.
  - (* uniqueness: any v with v ∘ e ≈ h is v ∘ (e ∘ s) ≈ h ∘ s by law 2 *)
    intros v Hv.
    rewrite <- Hv.
    rewrite <- comp_assoc.
    rewrite (scoeq_law2 S).
    apply id_right.
Qed.

(* The elementary coequalizer carried by a split coequalizer. *)
Theorem split_coequalizer_is_coequalizer {C : Category} {x y : C}
  (f g : x ~> y) (S : SplitCoequalizer f g) :
  IsCoequalizer f g (scoeq_obj S) (scoeq_e S).
Proof.
  exact {| cofork    := scoeq_law1 S
         ; coeq_desc := fun z h Hh => split_coeq_desc S h Hh |}.
Defined.

(** ** Absoluteness: every functor preserves split coequalizers *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem functor_preserves_split@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  SplitCoequalizer f g → SplitCoequalizer (fmap[F] f) (fmap[F] g).
Proof.
  intros S.
  unshelve refine
    {| scoeq_obj := F (scoeq_obj S)
     ; scoeq_e   := fmap[F] (scoeq_e S)
     ; scoeq_s   := fmap[F] (scoeq_s S)
     ; scoeq_t   := fmap[F] (scoeq_t S) |}.
  - (* law 1 *)
    rewrite <- !fmap_comp.
    now rewrite (scoeq_law1 S).
  - (* law 2 *)
    rewrite <- fmap_comp.
    rewrite (scoeq_law2 S).
    apply fmap_id.
  - (* law 3 *)
    rewrite <- fmap_comp.
    rewrite (scoeq_law3 S).
    apply fmap_id.
  - (* law 4 *)
    rewrite <- !fmap_comp.
    now rewrite (scoeq_law4 S).
Defined.

(* The headline: the coequalizer of a split pair is preserved, in the
   elementary [IsCoequalizer] sense, by an arbitrary functor. *)
Corollary split_coequalizer_preserved@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) (S : SplitCoequalizer f g) :
  IsCoequalizer (fmap[F] f) (fmap[F] g)
    (F (scoeq_obj S)) (fmap[F] (scoeq_e S)).
Proof.
  exact (split_coequalizer_is_coequalizer
           (fmap[F] f) (fmap[F] g) (functor_preserves_split F f g S)).
Defined.
