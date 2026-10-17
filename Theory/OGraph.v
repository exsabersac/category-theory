Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * O-图、可复合对积，以及范畴 *)

(* nLab:      https://ncatlab.org/nlab/show/quiver
   nLab:      https://ncatlab.org/nlab/show/monoidal+category

   O-图 (O-graph)：带有序节点对上箭头的图结构，支撑自由范畴/自由幺半等构造。本文件给出
   O-图范畴与保持节点恒等的态射。原英文文首极长；本波次译为定义性导言，细节后续可续译。 *)

(** ** O-graphs *)

Record OGraph@{o h p} (O : Type@{o}) : Type@{max(o,h+1,p+1)} := {
  oedges : O → O → Type@{h};                 (* arrows, indexed by endpoints *)
  oedgeset : ∀ x y, Setoid@{h p} (oedges x y)  (* each arrow set is a setoid *)
}.

Arguments oedges {_} _ _ _.
Arguments oedgeset {_} _ _ _.

#[export] Existing Instance oedgeset.

(*
   本节说明 OGraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record OGraphHom@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  : Type@{max(o,h,p)} := {
  oemap : ∀ x y, oedges A x y → oedges B x y;
  oemap_respects : ∀ x y,
    Proper@{h p} (respectful@{h p h p h p}
                    (@equiv@{h p} _ (oedgeset A x y))
                    (@equiv@{h p} _ (oedgeset B x y)))
      (oemap x y)
}.

Arguments oemap {_ _ _} _ _ _ _.
Arguments oemap_respects {_ _ _} _ _ _.

#[export] Existing Instance oemap_respects.

Definition OGraphHomEquiv@{o h p hh} {O : Type@{o}} {A B : OGraph@{o h p} O}
  (F G : OGraphHom@{o h p} A B) : Type@{hh} :=
  ∀ x y (f : oedges A x y),
    @equiv@{h p} _ (oedgeset B x y) (oemap F x y f) (oemap G x y f).

Lemma OGraphHomEquiv_Equivalence@{o h p hh} {O : Type@{o}}
  (A B : OGraph@{o h p} O) :
  Equivalence@{hh hh} (@OGraphHomEquiv@{o h p hh} O A B).
Proof.
  constructor.
  - intros F x y f; reflexivity.
  - intros F G H x y f; symmetry; apply H.
  - intros F G K H1 H2 x y f.
    transitivity (oemap G x y f); [ apply H1 | apply H2 ].
Qed.

Definition OGraphHom_Setoid@{o h p hh} {O : Type@{o}} (A B : OGraph@{o h p} O)
  : Setoid@{hh hh} (OGraphHom@{o h p} A B) := {|
  equiv := @OGraphHomEquiv@{o h p hh} O A B;
  setoid_equiv := OGraphHomEquiv_Equivalence@{o h p hh} A B
|}.

Definition ograph_id@{o h p} {O : Type@{o}} (A : OGraph@{o h p} O)
  : OGraphHom@{o h p} A A := {|
  oemap := fun _ _ f => f;
  oemap_respects := fun x y f g (H : @equiv@{h p} _ (oedgeset A x y) f g) => H
|}.

Definition ograph_compose@{o h p} {O : Type@{o}} {A B C : OGraph@{o h p} O}
  (F : OGraphHom@{o h p} B C) (G : OGraphHom@{o h p} A B)
  : OGraphHom@{o h p} A C := {|
  oemap := fun x y f => oemap F x y (oemap G x y f);
  oemap_respects := fun x y f g (H : @equiv@{h p} _ (oedgeset A x y) f g) =>
    oemap_respects F x y _ _ (oemap_respects G x y _ _ H)
|}.

Lemma ograph_compose_respects@{o h p hh} {O : Type@{o}}
  (A B C : OGraph@{o h p} O) :
  Proper@{hh hh}
    (respectful@{hh hh hh hh hh hh} (@OGraphHomEquiv@{o h p hh} O B C)
       (respectful@{hh hh hh hh hh hh} (@OGraphHomEquiv@{o h p hh} O A B)
          (@OGraphHomEquiv@{o h p hh} O A C)))
    (@ograph_compose@{o h p} O A B C).
Proof.
  intros F F' HF G G' HG x y f; simpl.
  rewrite (HG x y f).
  now apply HF.
Qed.

Lemma ograph_id_left@{o h p hh} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A B (ograph_compose (ograph_id B) F) F.
Proof. now intros x y f. Qed.

Lemma ograph_id_right@{o h p hh} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A B (ograph_compose F (ograph_id A)) F.
Proof. now intros x y f. Qed.

Lemma ograph_comp_assoc@{o h p hh} {O : Type@{o}} (A B C D : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} C D) (G : OGraphHom@{o h p} B C)
  (H : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A D
    (ograph_compose F (ograph_compose G H))
    (ograph_compose (ograph_compose F G) H).
Proof. now intros x y f. Qed.

Lemma ograph_comp_assoc_sym@{o h p hh} {O : Type@{o}}
  (A B C D : OGraph@{o h p} O)
  (F : OGraphHom@{o h p} C D) (G : OGraphHom@{o h p} B C)
  (H : OGraphHom@{o h p} A B) :
  @OGraphHomEquiv@{o h p hh} O A D
    (ograph_compose (ograph_compose F G) H)
    (ograph_compose F (ograph_compose G H)).
Proof. now intros x y f. Qed.

(*
   本节说明幺半结构、hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition OGrph@{o h p hh oo} (O : Type@{o}) : Category@{oo hh hh} := {|
  obj     := OGraph@{o h p} O;
  hom     := fun A B => OGraphHom@{o h p} A B;
  homset  := @OGraphHom_Setoid@{o h p hh} O;
  id      := @ograph_id@{o h p} O;
  compose := @ograph_compose@{o h p} O;

  compose_respects := @ograph_compose_respects@{o h p hh} O;

  id_left  := @ograph_id_left@{o h p hh} O;
  id_right := @ograph_id_right@{o h p hh} O;

  comp_assoc     := @ograph_comp_assoc@{o h p hh} O;
  comp_assoc_sym := @ograph_comp_assoc_sym@{o h p hh} O
|}.

(** ** The trivial O-graph *)

(* Leibniz equality as a setoid, with the carrier universe and the relation
   universe kept apart (Lib/Setoid.v's [eq_Setoid] identifies them). *)
Definition eq_setoid_poly@{a b} (A : Type@{a}) : Setoid@{a b} A := {|
  equiv := @eq A;
  setoid_equiv := eq_equivalence@{a b}
|}.

(*
   本节说明 OGraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition OGraph_unit@{o h p} (O : Type@{o}) : OGraph@{o h p} O := {|
  oedges := fun x y => x = y;
  oedgeset := fun x y => eq_setoid_poly@{h p} (x = y)
|}.

(** ** The bridge to Quiver *)

Definition QuiverOfOGraph@{o h p} {O : Type@{o}} (A : OGraph@{o h p} O)
  : Quiver@{o h p} := {|
  nodes := O;
  edges := oedges A;
  edgeset := oedgeset A
|}.

Definition QuiverHomOfOGraphHom@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O}
  (F : OGraphHom@{o h p} A B) :
  QuiverHomomorphism@{o h p o h p} (QuiverOfOGraph A) (QuiverOfOGraph B).
Proof.
  unshelve refine (@Build_QuiverHomomorphism
                     (QuiverOfOGraph A) (QuiverOfOGraph B)
                     (fun x => x) (fun x y f => oemap F x y f) _).
  intros x y f g Hfg.
  now apply oemap_respects.
Defined.

Definition OGrph_Quiver@{o h p hh oo +|+} (O : Type@{o}) :
  OGrph@{o h p hh oo} O ⟶ QuiverCategory.
Proof.
  unshelve refine (@Build_Functor (OGrph@{o h p hh oo} O) QuiverCategory
                     (@QuiverOfOGraph@{o h p} O)
                     (@QuiverHomOfOGraphHom@{o h p} O) _ _ _).
  - intros A B F G HFG.
    exists (fun _ => eq_refl).
    intros x y f.
    exact (HFG x y f).
  - intros A.
    exists (fun _ => eq_refl).
    now intros x y f.
  - intros A B C F G.
    exists (fun _ => eq_refl).
    now intros x y f.
Defined.

(* The comparison is the identity on nodes, definitionally: that is the whole
   content of "identity on objects". *)
Example OGrph_Quiver_nodes {O : Type} {A B : OGraph O} (F : OGraphHom A B) :
  @fnodes _ _ (QuiverHomOfOGraphHom F) = fun x : O => x := eq_refl.

(*
   本节说明幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition NodeUIP (O : Type) : Type := ∀ (x : O) (p : x = x), p = eq_refl.

Lemma OGrph_Quiver_Faithful (O : Type) : NodeUIP O → Faithful (OGrph_Quiver O).
Proof.
  intros uip.
  constructor.
  intros A B F G HFG x y f.
  destruct HFG as [node_equiv coher].
  specialize (coher x y f); simpl in coher.
  rewrite (uip _ (node_equiv x)), (uip _ (node_equiv y)) in coher.
  exact coher.
Qed.

(** ** The composable-pairs product A ×_O B *)

(* An arrow of A ×_O B from x to z is Mac Lane's composable pair <g, f>: a
   middle node [cmid], an arrow [cleft] of A into z and an arrow [cright] of
   B out of x meeting at it.  Kept as a primitive-projection record, so that
   [composable_eta] below holds by [eq_refl]. *)
Record Composable@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O) (x z : O)
  : Type@{max(o,h)} := {
  cmid : O;
  cleft : oedges A cmid z;
  cright : oedges B x cmid
}.

Arguments cmid {_ _ _ _ _} _.
Arguments cleft {_ _ _ _ _} _.
Arguments cright {_ _ _ _ _} _.

Definition cpair@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O} {x z : O}
  (y : O) (g : oedges A y z) (f : oedges B x y)
  : Composable@{o h p} A B x z := {|
  cmid := y; cleft := g; cright := f
|}.

(* Record eta, definitionally, thanks to primitive projections. *)
Example composable_eta@{o h p +|+} {O : Type@{o}} {A B : OGraph@{o h p} O}
  {x z : O} (u : Composable@{o h p} A B x z)
  : cpair (cmid u) (cleft u) (cright u) = u := eq_refl.

(*
   本节说明等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition CompEquiv@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O} {x z : O}
  (u v : Composable@{o h p} A B x z) : Type@{p} :=
  { q : cmid u = cmid v &
      ((@equiv@{h p} _ (oedgeset A (cmid v) z)
          (match q in _ = m return oedges A m z with eq_refl => cleft u end)
          (cleft v)) *
       (@equiv@{h p} _ (oedgeset B x (cmid v))
          (match q in _ = m return oedges B x m with eq_refl => cright u end)
          (cright v)))%type }.

Lemma CompEquiv_Equivalence@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (x z : O) : Equivalence@{h p} (@CompEquiv@{o h p} O A B x z).
Proof.
  constructor.
  - intros u.
    exists eq_refl; simpl.
    now split.
  - intros [y g f] [y' g' f'] [q [Hg Hf]]; simpl in *.
    destruct q; simpl in *.
    exists eq_refl; simpl.
    now split; symmetry.
  - intros [y1 g1 f1] [y2 g2 f2] [y3 g3 f3] [q [Hg Hf]] [q' [Hg' Hf']];
      simpl in *.
    destruct q, q'; simpl in *.
    exists eq_refl; simpl.
    now split; [ transitivity g2 | transitivity f2 ].
Qed.

Definition Composable_Setoid@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  (x z : O) : Setoid@{h p} (Composable@{o h p} A B x z) := {|
  equiv := @CompEquiv@{o h p} O A B x z;
  setoid_equiv := CompEquiv_Equivalence@{o h p} A B x z
|}.

Definition OGraph_prod@{o h p} {O : Type@{o}} (A B : OGraph@{o h p} O)
  : OGraph@{o h p} O := {|
  oedges := Composable@{o h p} A B;
  oedgeset := @Composable_Setoid@{o h p} O A B
|}.

(* The common special case of [CompEquiv]: same middle node, legs `≈`. *)
Lemma cpair_equiv@{o h p} {O : Type@{o}} {A B : OGraph@{o h p} O} {x z : O}
  (y : O) (g g' : oedges A y z) (f f' : oedges B x y) :
  @equiv@{h p} _ (oedgeset A y z) g g' →
  @equiv@{h p} _ (oedgeset B x y) f f' →
  @CompEquiv@{o h p} O A B x z (cpair y g f) (cpair y g' f').
Proof. intros Hg Hf; exists eq_refl; now split. Qed.

(** ** The tensor bifunctor *)

Definition ograph_prod_map@{o h p} {O : Type@{o}} {A A' B B' : OGraph@{o h p} O}
  (F : OGraphHom@{o h p} A A') (G : OGraphHom@{o h p} B B') :
  OGraphHom@{o h p} (OGraph_prod A B) (OGraph_prod A' B').
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod A B) (OGraph_prod A' B')
                     (fun x z u =>
    cpair (cmid u) (oemap F _ _ (cleft u)) (oemap G _ _ (cright u))) _).
  intros x z u v.
  destruct u as [y g f], v as [y' g' f']; simpl.
  intros [q [Hg Hf]]; simpl in *.
  destruct q; simpl in *.
  apply cpair_equiv; now apply oemap_respects.
Defined.

Definition OGraph_Tensor@{o h p hh oo +|+} (O : Type@{o}) :
  OGrph@{o h p hh oo} O ∏ OGrph@{o h p hh oo} O ⟶ OGrph@{o h p hh oo} O.
Proof.
  unshelve refine (@Build_Functor (OGrph@{o h p hh oo} O ∏ OGrph@{o h p hh oo} O)
                     (OGrph@{o h p hh oo} O)
    (fun p => OGraph_prod (fst p) (snd p))
    (fun p q FG => ograph_prod_map (fst FG) (snd FG)) _ _ _).
  - intros [A B] [A' B'] [F G] [F' G'] [HF HG] x z u; simpl in *.
    destruct u as [y g f]; simpl.
    apply cpair_equiv; [ apply HF | apply HG ].
  - intros [A B] x z u; simpl.
    destruct u as [y g f]; simpl.
    now apply cpair_equiv.
  - intros [A B] [A' B'] [A'' B''] [F G] [F' G'] x z u; simpl.
    destruct u as [y g f]; simpl.
    now apply cpair_equiv.
Defined.

(** ** The unitors *)

Definition oul_to@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod (OGraph_unit@{o h p} O) X) X.
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod (OGraph_unit O) X) X (fun x z u =>
    match cleft u in _ = m return oedges X x m with eq_refl => cright u end) _).
  intros x z u v.
  destruct u as [y p f], v as [y' p' f']; simpl.
  intros [q [Hp Hf]]; simpl in *.
  destruct q; simpl in *.
  destruct Hp; simpl.
  now destruct p.
Defined.

Definition oul_from@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} X (OGraph_prod (OGraph_unit@{o h p} O) X).
Proof.
  unshelve refine (@Build_OGraphHom O X (OGraph_prod (OGraph_unit O) X)
                     (fun x z f => @cpair O (OGraph_unit O) X x z z eq_refl f) _).
  intros x z f f' Hf.
  now apply cpair_equiv.
Defined.

Definition OGraph_unit_left@{o h p hh oo +|+} {O : Type@{o}}
  (X : OGraph@{o h p} O) :
  @Isomorphism (OGrph@{o h p hh oo} O)
    (OGraph_prod (OGraph_unit@{o h p} O) X) X.
Proof.
  unshelve refine (@Build_Isomorphism (OGrph@{o h p hh oo} O)
                     (OGraph_prod (OGraph_unit@{o h p} O) X) X
                     (oul_to X) (oul_from X) _ _).
  - now intros x z f.
  - intros x z u; simpl.
    destruct u as [y p f]; simpl.
    destruct p; simpl.
    now apply cpair_equiv.
Defined.

Definition our_to@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod X (OGraph_unit@{o h p} O)) X.
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod X (OGraph_unit O)) X (fun x z u =>
    match cright u in _ = m return oedges X m z → oedges X x z with
    | eq_refl => fun g => g
    end (cleft u)) _).
  intros x z u v.
  destruct u as [y g p], v as [y' g' p']; simpl.
  intros [q [Hg Hp]]; simpl in *.
  destruct q; simpl in *.
  destruct Hp; simpl.
  now destruct p.
Defined.

Definition our_from@{o h p} {O : Type@{o}} (X : OGraph@{o h p} O) :
  OGraphHom@{o h p} X (OGraph_prod X (OGraph_unit@{o h p} O)).
Proof.
  unshelve refine (@Build_OGraphHom O X (OGraph_prod X (OGraph_unit O))
                     (fun x z g => @cpair O X (OGraph_unit O) x z x g eq_refl) _).
  intros x z g g' Hg.
  now apply cpair_equiv.
Defined.

Definition OGraph_unit_right@{o h p hh oo +|+} {O : Type@{o}}
  (X : OGraph@{o h p} O) :
  @Isomorphism (OGrph@{o h p hh oo} O)
    (OGraph_prod X (OGraph_unit@{o h p} O)) X.
Proof.
  unshelve refine (@Build_Isomorphism (OGrph@{o h p hh oo} O)
                     (OGraph_prod X (OGraph_unit@{o h p} O)) X
                     (our_to X) (our_from X) _ _).
  - now intros x z g.
  - intros x z u; simpl.
    destruct u as [y g p]; simpl.
    destruct p; simpl.
    now apply cpair_equiv.
Defined.

(** ** The associator *)

Definition oassoc_to@{o h p} {O : Type@{o}} (A B C : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod (OGraph_prod A B) C)
                    (OGraph_prod A (OGraph_prod B C)).
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod (OGraph_prod A B) C)
                     (OGraph_prod A (OGraph_prod B C)) (fun x w u =>
    @cpair O A (OGraph_prod B C) x w (cmid (cleft u)) (cleft (cleft u))
      (@cpair O B C x (cmid (cleft u)) (cmid u) (cright (cleft u)) (cright u))) _).
  intros x w u v.
  destruct u as [y [z a b] c], v as [y' [z' a' b'] c']; simpl.
  intros [q [Hab Hc]]; simpl in *.
  destruct q; simpl in *.
  destruct Hab as [q' [Ha Hb]]; simpl in *.
  destruct q'; simpl in *.
  apply cpair_equiv; [ assumption | now apply cpair_equiv ].
Defined.

Definition oassoc_from@{o h p} {O : Type@{o}} (A B C : OGraph@{o h p} O) :
  OGraphHom@{o h p} (OGraph_prod A (OGraph_prod B C))
                    (OGraph_prod (OGraph_prod A B) C).
Proof.
  unshelve refine (@Build_OGraphHom O (OGraph_prod A (OGraph_prod B C))
                     (OGraph_prod (OGraph_prod A B) C) (fun x w v =>
    @cpair O (OGraph_prod A B) C x w (cmid (cright v))
      (@cpair O A B (cmid (cright v)) w (cmid v) (cleft v) (cleft (cright v)))
      (cright (cright v))) _).
  intros x w u v.
  destruct u as [z a [y b c]], v as [z' a' [y' b' c']]; simpl.
  intros [q [Ha Hbc]]; simpl in *.
  destruct q; simpl in *.
  destruct Hbc as [q' [Hb Hc]]; simpl in *.
  destruct q'; simpl in *.
  apply cpair_equiv; [ now apply cpair_equiv | assumption ].
Defined.

Definition OGraph_assoc@{o h p hh oo +|+} {O : Type@{o}}
  (A B C : OGraph@{o h p} O) :
  @Isomorphism (OGrph@{o h p hh oo} O)
    (OGraph_prod (OGraph_prod A B) C) (OGraph_prod A (OGraph_prod B C)).
Proof.
  unshelve refine (@Build_Isomorphism (OGrph@{o h p hh oo} O)
                     (OGraph_prod (OGraph_prod A B) C)
                     (OGraph_prod A (OGraph_prod B C))
                     (oassoc_to A B C) (oassoc_from A B C) _ _).
  - intros x w v; simpl.
    exists eq_refl; simpl.
    now split; [ reflexivity | exists eq_refl; split ].
  - intros x w u; simpl.
    exists eq_refl; simpl.
    now split; [ exists eq_refl; split | reflexivity ].
Defined.

(** ** Coherence *)

Lemma ograph_to_unit_left_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose g (oul_to X))
    (ograph_compose (oul_to Y) (ograph_prod_map (ograph_id _) g)).
Proof.
  intros x z u; simpl.
  destruct u as [y p f]; simpl.
  now destruct p.
Qed.

Lemma ograph_from_unit_left_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map (ograph_id _) g) (oul_from X))
    (ograph_compose (oul_from Y) g).
Proof. intros x z f; simpl; now apply cpair_equiv. Qed.

Lemma ograph_to_unit_right_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose g (our_to X))
    (ograph_compose (our_to Y) (ograph_prod_map g (ograph_id _))).
Proof.
  intros x z u; simpl.
  destruct u as [y h p]; simpl.
  now destruct p.
Qed.

Lemma ograph_from_unit_right_natural@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) (g : OGraphHom@{o h p} X Y) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map g (ograph_id _)) (our_from X))
    (ograph_compose (our_from Y) g).
Proof. intros x z f; simpl; now apply cpair_equiv. Qed.

Lemma ograph_to_assoc_natural@{o h p hh +|+} {O : Type@{o}}
  (A A' B B' C C' : OGraph@{o h p} O)
  (g : OGraphHom@{o h p} A A') (h : OGraphHom@{o h p} B B')
  (i : OGraphHom@{o h p} C C') :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map g (ograph_prod_map h i)) (oassoc_to A B C))
    (ograph_compose (oassoc_to A' B' C') (ograph_prod_map (ograph_prod_map g h) i)).
Proof.
  intros x w u; simpl.
  destruct u as [y [z a b] c]; simpl.
  apply cpair_equiv; [ reflexivity | now apply cpair_equiv ].
Qed.

Lemma ograph_from_assoc_natural@{o h p hh +|+} {O : Type@{o}}
  (A A' B B' C C' : OGraph@{o h p} O)
  (g : OGraphHom@{o h p} A A') (h : OGraphHom@{o h p} B B')
  (i : OGraphHom@{o h p} C C') :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose (ograph_prod_map (ograph_prod_map g h) i) (oassoc_from A B C))
    (ograph_compose (oassoc_from A' B' C') (ograph_prod_map g (ograph_prod_map h i))).
Proof.
  intros x w u; simpl.
  destruct u as [z a [y b c]]; simpl.
  apply cpair_equiv; [ now apply cpair_equiv | reflexivity ].
Qed.

Lemma ograph_triangle@{o h p hh +|+} {O : Type@{o}}
  (X Y : OGraph@{o h p} O) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_prod_map (our_to X) (ograph_id Y))
    (ograph_compose (ograph_prod_map (ograph_id X) (oul_to Y))
                    (oassoc_to X (OGraph_unit O) Y)).
Proof.
  intros x z u; simpl.
  destruct u as [m [n g e] q]; simpl.
  destruct e; simpl.
  now apply cpair_equiv.
Qed.

Lemma ograph_pentagon@{o h p hh +|+} {O : Type@{o}}
  (A B C D : OGraph@{o h p} O) :
  @OGraphHomEquiv@{o h p hh} O _ _
    (ograph_compose
       (ograph_compose (ograph_prod_map (ograph_id A) (oassoc_to B C D))
                       (oassoc_to A (OGraph_prod B C) D))
       (ograph_prod_map (oassoc_to A B C) (ograph_id D)))
    (ograph_compose (oassoc_to A B (OGraph_prod C D))
                    (oassoc_to (OGraph_prod A B) C D)).
Proof.
  intros x w u; simpl.
  destruct u as [m [n [k a b] c] d]; simpl.
  apply cpair_equiv; [ reflexivity | ].
  apply cpair_equiv; [ reflexivity | ].
  now apply cpair_equiv.
Qed.

(** ** O-Grph is monoidal under ×_O *)

Definition OGrph_Monoidal@{o h p hh oo +|+} (O : Type@{o}) :
  @Monoidal (OGrph@{o h p hh oo} O).
Proof.
  unshelve refine (@Build_Monoidal (OGrph@{o h p hh oo} O)
                     (OGraph_unit@{o h p} O) (OGraph_Tensor@{o h p hh oo} O)
                     (@OGraph_unit_left@{o h p hh oo} O)
                     (@OGraph_unit_right@{o h p hh oo} O)
                     (@OGraph_assoc@{o h p hh oo} O) _ _ _ _ _ _ _ _).
  - exact (@ograph_to_unit_left_natural O).
  - exact (@ograph_from_unit_left_natural O).
  - exact (@ograph_to_unit_right_natural O).
  - exact (@ograph_from_unit_right_natural O).
  - exact (@ograph_to_assoc_natural O).
  - exact (@ograph_from_assoc_natural O).
  - exact (@ograph_triangle O).
  - exact (@ograph_pentagon O).
Defined.

#[export] Existing Instance OGrph_Monoidal.

(** ** Monoids in O-Grph *)

Definition OMonoid@{o h p hh oo +|+} {O : Type@{o}} (A : OGraph@{o h p} O)
  : Type@{hh} :=
  @Monoid (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A.

Definition omul@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) : OGraphHom@{o h p} (OGraph_prod A A) A :=
  @mu (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A M.

Definition ounit@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A)
  : OGraphHom@{o h p} (OGraph_unit@{o h p} O) A :=
  @eta (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A M.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma omonoid_assoc@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) :
  @OGraphHomEquiv@{o h p hh} O (OGraph_prod (OGraph_prod A A) A) A
    (ograph_compose (omul M) (ograph_prod_map (omul M) (ograph_id A)))
    (ograph_compose
       (ograph_compose (omul M) (ograph_prod_map (ograph_id A) (omul M)))
       (oassoc_to A A A)).
Proof.
  exact (@mu_assoc (OGrph@{o h p hh oo} O) (OGrph_Monoidal@{o h p hh oo} O) A M).
Qed.

Lemma omonoid_unit_left@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) :
  @OGraphHomEquiv@{o h p hh} O (OGraph_prod (OGraph_unit@{o h p} O) A) A
    (ograph_compose (omul M) (ograph_prod_map (ounit M) (ograph_id A)))
    (oul_to A).
Proof.
  exact (@mu_unit_left (OGrph@{o h p hh oo} O)
           (OGrph_Monoidal@{o h p hh oo} O) A M).
Qed.

Lemma omonoid_unit_right@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) :
  @OGraphHomEquiv@{o h p hh} O (OGraph_prod A (OGraph_unit@{o h p} O)) A
    (ograph_compose (omul M) (ograph_prod_map (ograph_id A) (ounit M)))
    (our_to A).
Proof.
  exact (@mu_unit_right (OGrph@{o h p hh oo} O)
           (OGrph_Monoidal@{o h p hh oo} O) A M).
Qed.

(** ** From a category to a monoid in O-Grph *)

Definition OGraphOfCat@{o h p} (C : Category@{o h p}) : OGraph@{o h p} (obj[C])
  := {|
  oedges := @hom C;
  oedgeset := @homset C
|}.

Definition ocat_mu@{o h p +|+} (C : Category@{o h p}) :
  OGraphHom@{o h p} (OGraph_prod (OGraphOfCat C) (OGraphOfCat C))
                    (OGraphOfCat C).
Proof.
  unshelve refine (@Build_OGraphHom obj[C]
                     (OGraph_prod (OGraphOfCat C) (OGraphOfCat C)) (OGraphOfCat C)
                     (fun x z u => cleft u ∘ cright u) _).
  intros x z u v.
  destruct u as [y g f], v as [y' g' f']; simpl.
  intros [q [Hg Hf]]; simpl in *.
  destruct q; simpl in *.
  now rewrite Hg, Hf.
Defined.

Definition ocat_eta@{o h p +|+} (C : Category@{o h p}) :
  OGraphHom@{o h p} (OGraph_unit@{o h p} (obj[C])) (OGraphOfCat C).
Proof.
  unshelve refine (@Build_OGraphHom obj[C] (OGraph_unit obj[C]) (OGraphOfCat C)
                     (fun x z p =>
                        match p in _ = m return x ~{C}~> m with
                        | eq_refl => id
                        end)
                     (fun x z p p' (Hp : p = p') => _)).
  now destruct Hp.
Defined.

Definition MonoidOfCat@{o h p hh oo +|+} (C : Category@{o h p}) :
  OMonoid@{o h p hh oo} (OGraphOfCat@{o h p} C).
Proof.
  unshelve refine (@Build_Monoid (OGrph@{o h p hh oo} obj[C])
                     (OGrph_Monoidal@{o h p hh oo} obj[C])
                     (OGraphOfCat C) (ocat_mu C) (ocat_eta C) _ _ _).
  - intros x w u; simpl.
    destruct u as [y [z f g] h]; simpl.
    now rewrite comp_assoc.
  - intros x z u; simpl.
    destruct u as [y p f]; simpl.
    destruct p; simpl.
    now rewrite id_left.
  - intros x z u; simpl.
    destruct u as [y f p]; simpl.
    destruct p; simpl.
    now rewrite id_right.
Defined.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ocat_mu_is_compose (C : Category) (x y z : obj[C])
  (g : y ~{C}~> z) (f : x ~{C}~> y) :
  oemap (omul (MonoidOfCat C)) x z
    (@cpair obj[C] (OGraphOfCat C) (OGraphOfCat C) x z y g f) = g ∘ f := eq_refl.

Example ocat_eta_is_id (C : Category) (x : obj[C]) :
  oemap (ounit (MonoidOfCat C)) x x eq_refl = id[x] := eq_refl.

(** ** From a monoid in O-Grph to a category *)

Definition omon_id@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x : O) : oedges A x x :=
  oemap (ounit M) x x eq_refl.

Definition omon_compose@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) {x y z : O}
  (g : oedges A y z) (f : oedges A x y) : oedges A x z :=
  oemap (omul M) x z (cpair y g f).

Lemma omon_compose_respects@{o h p hh oo +|+} {O : Type@{o}}
  {A : OGraph@{o h p} O} (M : OMonoid@{o h p hh oo} A) (x y z : O) :
  Proper@{h p} (respectful@{h p h p h p}
                  (@equiv@{h p} _ (oedgeset A y z))
                  (respectful@{h p h p h p}
                     (@equiv@{h p} _ (oedgeset A x y))
                     (@equiv@{h p} _ (oedgeset A x z))))
    (@omon_compose@{o h p hh oo} O A M x y z).
Proof.
  intros g g' Hg f f' Hf.
  unfold omon_compose.
  apply oemap_respects.
  now apply cpair_equiv.
Qed.

Lemma omon_id_left@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y : O) (f : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x y) (omon_compose M (omon_id M y) f) f.
Proof.
  exact (omonoid_unit_left M x y (@cpair O (OGraph_unit O) A x y y eq_refl f)).
Qed.

Lemma omon_id_right@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y : O) (f : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x y) (omon_compose M f (omon_id M x)) f.
Proof.
  exact (omonoid_unit_right M x y (@cpair O A (OGraph_unit O) x y x f eq_refl)).
Qed.

Lemma omon_comp_assoc@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y z w : O)
  (f : oedges A z w) (g : oedges A y z) (h : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x w)
    (omon_compose M f (omon_compose M g h))
    (omon_compose M (omon_compose M f g) h).
Proof.
  symmetry.
  exact (omonoid_assoc M x w
           (@cpair O (OGraph_prod A A) A x w y (@cpair O A A y w z f g) h)).
Qed.

Lemma omon_comp_assoc_sym@{o h p hh oo +|+} {O : Type@{o}} {A : OGraph@{o h p} O}
  (M : OMonoid@{o h p hh oo} A) (x y z w : O)
  (f : oedges A z w) (g : oedges A y z) (h : oedges A x y) :
  @equiv@{h p} _ (oedgeset A x w)
    (omon_compose M (omon_compose M f g) h)
    (omon_compose M f (omon_compose M g h)).
Proof. symmetry; apply omon_comp_assoc. Qed.

Definition CategoryOfOMonoid@{o h p hh oo +|+} {O : Type@{o}}
  {A : OGraph@{o h p} O} (M : OMonoid@{o h p hh oo} A) : Category@{o h p} := {|
  obj     := O;
  hom     := oedges A;
  homset  := oedgeset A;
  id      := omon_id M;
  compose := @omon_compose@{o h p hh oo} O A M;

  compose_respects := omon_compose_respects M;

  id_left  := omon_id_left M;
  id_right := omon_id_right M;

  comp_assoc     := omon_comp_assoc M;
  comp_assoc_sym := omon_comp_assoc_sym M
|}.

(** ** The round trips *)

(* Monoid side: the O-graph comes back on the nose, ... *)
Example OGraphOfCat_CategoryOfOMonoid {O : Type} {A : OGraph O} (M : OMonoid A) :
  OGraphOfCat (CategoryOfOMonoid M) = A := eq_refl.

(* ... and so does the multiplication, as a function. *)
Example omul_roundtrip {O : Type} {A : OGraph O} (M : OMonoid A) :
  oemap (omul (MonoidOfCat (CategoryOfOMonoid M)))
    = oemap (omul M) := eq_refl.

(* The unit comes back only after eliminating the identity proof: there is no
   eta rule for [eq], so [match p with eq_refl => ... end] is not the term it
   evaluates to. *)
Lemma ounit_roundtrip {O : Type} {A : OGraph O} (M : OMonoid A) :
  ∀ x z (p : x = z),
    oemap (ounit (MonoidOfCat (CategoryOfOMonoid M))) x z p
      = oemap (ounit M) x z p.
Proof. intros x z p; now destruct p. Qed.

(* Category side: all five data fields are definitional. *)
Example ocat_roundtrip_obj (C : Category) :
  obj[CategoryOfOMonoid (MonoidOfCat C)] = obj[C] := eq_refl.

Example ocat_roundtrip_hom (C : Category) :
  @hom (CategoryOfOMonoid (MonoidOfCat C)) = @hom C := eq_refl.

Example ocat_roundtrip_homset (C : Category) :
  @homset (CategoryOfOMonoid (MonoidOfCat C)) = @homset C := eq_refl.

Example ocat_roundtrip_id (C : Category) :
  @id (CategoryOfOMonoid (MonoidOfCat C)) = @id C := eq_refl.

Example ocat_roundtrip_compose (C : Category) :
  @compose (CategoryOfOMonoid (MonoidOfCat C)) = @compose C := eq_refl.

(*
   本节说明函子、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ograph_iso_id_conj {D : Category} {x y : D} (h : x ~> y) :
  from (@iso_id D y) ∘ h ∘ to (@iso_id D x) ≈ h.
Proof. simpl; now rewrite id_right, id_left. Qed.

Definition ORebuild_to (C : Category) : C ⟶ CategoryOfOMonoid (MonoidOfCat C).
Proof.
  unshelve refine (@Build_Functor C (CategoryOfOMonoid (MonoidOfCat C))
                     (fun x => x) (fun x y f => f) _ _ _).
  - now intros x y f g Hfg.
  - reflexivity.
  - reflexivity.
Defined.

Definition ORebuild_from (C : Category) : CategoryOfOMonoid (MonoidOfCat C) ⟶ C.
Proof.
  unshelve refine (@Build_Functor (CategoryOfOMonoid (MonoidOfCat C)) C
                     (fun x => x) (fun x y f => f) _ _ _).
  - now intros x y f g Hfg.
  - reflexivity.
  - reflexivity.
Defined.

Definition ocat_roundtrip_iso (C : Category) :
  C ≅[Cat] CategoryOfOMonoid (MonoidOfCat C).
Proof.
  unshelve refine (@Build_Isomorphism Cat C (CategoryOfOMonoid (MonoidOfCat C))
                     (ORebuild_to C) (ORebuild_from C) _ _).
  - exists (fun x => iso_id).
    intros x y f.
    rewrite ograph_iso_id_conj.
    reflexivity.
  - exists (fun x => iso_id).
    intros x y f.
    rewrite ograph_iso_id_conj.
    reflexivity.
Defined.

(** ** Mac Lane's remark: a category IS a monoid in O-Grph *)

Theorem category_is_monoid_in_OGrph@{o h p hh oo co ch cp +|+} :
  ((∀ (O : Type@{o}) (A : OGraph@{o h p} O) (M : OMonoid@{o h p hh oo} A),
      (* every monoid in O-Grph is a category on O, and the monoid is
         recovered: its graph on the nose, its multiplication as a function
         on the nose, its unit pointwise *)
      ((OGraphOfCat (CategoryOfOMonoid M) = A) *
       (oemap (omul (MonoidOfCat (CategoryOfOMonoid M))) = oemap (omul M)) *
       (∀ x z (p : x = z),
          oemap (ounit (MonoidOfCat (CategoryOfOMonoid M))) x z p
            = oemap (ounit M) x z p))%type)
   *
   (∀ C : Category@{co ch cp},
      (* and every category is such a monoid, on its own underlying O-graph,
         recovered up to isomorphism in Cat *)
      C ≅[Cat] CategoryOfOMonoid (MonoidOfCat C)))%type.
Proof.
  split.
  - intros O A M.
    split; [ split | ].
    + exact (OGraphOfCat_CategoryOfOMonoid M).
    + exact (omul_roundtrip M).
    + exact (ounit_roundtrip M).
  - exact ocat_roundtrip_iso.
Defined.

(** ** Witness: one node, and monoids *)

Definition OGraph_of_MonObject (M : MonObject) : OGraph poly_unit := {|
  oedges := fun _ _ => carrier M;
  oedgeset := fun _ _ => is_setoid M
|}.

Definition ograph_mon_mu (M : MonObject) :
  OGraphHom (OGraph_prod (OGraph_of_MonObject M) (OGraph_of_MonObject M))
            (OGraph_of_MonObject M).
Proof.
  unshelve refine (@Build_OGraphHom poly_unit
                     (OGraph_prod (OGraph_of_MonObject M)
                                  (OGraph_of_MonObject M))
                     (OGraph_of_MonObject M)
                     (fun x z u => mon_op (cleft u) (cright u)) _).
  intros x z u v.
  destruct u as [y g f], v as [y' g' f']; simpl.
  intros [q [Hg Hf]]; simpl in *.
  destruct q; simpl in *.
  now rewrite Hg, Hf.
Defined.

Definition ograph_mon_eta (M : MonObject) :
  OGraphHom (OGraph_unit poly_unit) (OGraph_of_MonObject M).
Proof.
  unshelve refine (@Build_OGraphHom poly_unit (OGraph_unit poly_unit)
                     (OGraph_of_MonObject M)
                     (fun _ _ _ => mon_unit)
                     (fun x z p p' (Hp : p = p') => _)).
  reflexivity.
Defined.

Definition Monoid_of_MonObject (M : MonObject) : OMonoid (OGraph_of_MonObject M).
Proof.
  unshelve refine (@Build_Monoid (OGrph poly_unit) (OGrph_Monoidal poly_unit)
                     (OGraph_of_MonObject M)
                     (ograph_mon_mu M) (ograph_mon_eta M) _ _ _).
  - intros x w u; simpl.
    destruct u as [y [z f g] h]; simpl.
    now rewrite mon_op_assoc.
  - intros x z u; simpl.
    destruct u as [y p f]; simpl.
    destruct p; simpl.
    now rewrite mon_op_unit_l.
  - intros x z u; simpl.
    destruct u as [y f p]; simpl.
    destruct p; simpl.
    now rewrite mon_op_unit_r.
Defined.

(* The category assembled from that monoid is Mac Lane's B M, on the nose in
   every data field. *)
Example Deloop_of_MonObject_obj (M : MonObject) :
  obj[CategoryOfOMonoid (Monoid_of_MonObject M)] = obj[Deloop M] := eq_refl.

Example Deloop_of_MonObject_hom (M : MonObject) :
  @hom (CategoryOfOMonoid (Monoid_of_MonObject M)) = @hom (Deloop M) := eq_refl.

Example Deloop_of_MonObject_homset (M : MonObject) :
  @homset (CategoryOfOMonoid (Monoid_of_MonObject M)) = @homset (Deloop M)
    := eq_refl.

Example Deloop_of_MonObject_id (M : MonObject) :
  @id (CategoryOfOMonoid (Monoid_of_MonObject M)) = @id (Deloop M) := eq_refl.

Example Deloop_of_MonObject_compose (M : MonObject) :
  @compose (CategoryOfOMonoid (Monoid_of_MonObject M)) = @compose (Deloop M)
    := eq_refl.

(* Conversely, a monoid in poly_unit-Grph is a monoid. *)
Definition MonObject_of_OMonoid {A : OGraph poly_unit} (M : OMonoid A) :
  MonObject := hom_monoid (CategoryOfOMonoid M) ttt.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example MonObject_of_OMonoid_carrier (M : MonObject) :
  carrier (MonObject_of_OMonoid (Monoid_of_MonObject M)) = carrier M := eq_refl.

Example MonObject_of_OMonoid_setoid (M : MonObject) :
  is_setoid (MonObject_of_OMonoid (Monoid_of_MonObject M)) = is_setoid M
    := eq_refl.

Example MonObject_of_OMonoid_unit (M : MonObject) :
  @mon_unit (MonObject_of_OMonoid (Monoid_of_MonObject M)) = @mon_unit M
    := eq_refl.

Example MonObject_of_OMonoid_op (M : MonObject) :
  @mon_op (MonObject_of_OMonoid (Monoid_of_MonObject M)) = @mon_op M
    := eq_refl.

(* And the whole passage computes.  [Nat_Plus] is Construction/Deloop.v's
   monoid (ℕ, +, 0). *)
Example ograph_nat_compose (a b : carrier Nat_Plus) :
  @omon_compose _ _ (Monoid_of_MonObject Nat_Plus) ttt ttt ttt a b
    = (a + b)%nat := eq_refl.

Example ograph_nat_id :
  omon_id (Monoid_of_MonObject Nat_Plus) ttt = 0%nat := eq_refl.

Example ograph_nat_compose_2_3 :
  @omon_compose _ _ (Monoid_of_MonObject Nat_Plus) ttt ttt ttt 2%nat 3%nat
    = 5%nat := eq_refl.

(** ** The unit setoid is load-bearing: coarsening it ENTAILS UIP *)

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition coarse_unit (O : Type) : OGraph O := {|
  oedges := fun x y => x = y;
  oedgeset := fun x y => {| equiv := fun _ _ => True |}
|}.
Next Obligation. constructor; repeat intro; exact Logic.I. Qed.

(* [oul_to]'s underlying map, verbatim, over the coarsened unit. *)
Definition coarse_oul_map {O : Type} (X : OGraph O) (x z : O)
  (u : Composable (coarse_unit O) X x z) : oedges X x z :=
  match cleft u in _ = m return oedges X x m with eq_refl => cright u end.

Lemma coarse_map_on_unit {O : Type} (a : O) (p : a = a) :
  @coarse_oul_map O (OGraph_unit O) a a
    (@cpair O (coarse_unit O) (OGraph_unit O) a a a p eq_refl) = p.
Proof. unfold coarse_oul_map; simpl; now destruct p. Qed.

Theorem coarse_respectfulness_entails_UIP (O : Type)
  (H : ∀ (X : OGraph O) (x z : O),
         Proper (respectful
                   (@equiv _ (oedgeset (OGraph_prod (coarse_unit O) X) x z))
                   (@equiv _ (oedgeset X x z)))
           (@coarse_oul_map O X x z)) :
  NodeUIP O.
Proof.
  intros a p.
  assert (Hequiv : @equiv _ (oedgeset (OGraph_prod (coarse_unit O)
                                         (OGraph_unit O)) a a)
                     (@cpair O (coarse_unit O) (OGraph_unit O) a a a p eq_refl)
                     (@cpair O (coarse_unit O) (OGraph_unit O) a a a eq_refl eq_refl)).
  { exists eq_refl; simpl; split; [ exact Logic.I | reflexivity ]. }
  pose proof (H (OGraph_unit O) a a _ _ Hequiv) as Hr.
  simpl in Hr.
  rewrite <- (coarse_map_on_unit a p).
  exact Hr.
Qed.
