Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Free.Quiver.

From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(* * * Quivers concrete 范畴: multi-sorted case （已译） *)

(*
   nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Quiver_(mathematics)
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出具体范畴相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Existing Instance edgeset.
#[local] Obligation Tactic := idtac.

(* * ** Uniqueness 恒等 proofs nodes （已译） *)

(* The 假设 discussed header: node type `Q` set in
 sense uniqueness 恒等 proofs. （已译） *)
Definition NodeUIP (Q : Quiver) : Type :=
  ∀ (x y : @nodes Q) (p q : x = y), p = q.

(*
   本节说明 Concrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma NodeDecEq_NodeUIP (Q : Quiver)
      (dec : ∀ x y : @nodes Q, {x = y} + {x ≠ y}) : NodeUIP Q.
Proof.
  intros x y p q.
  exact (UIP_dec dec p q).
Qed.

(** ** The vertex functor *)

(* Q ↦ its node type, under Leibniz equality; a homomorphism ↦ its node map.
   Functoriality is immediate: hom-equivalence in `QuiverCategory` carries a
   family of node equalities as its first component. *)
Program Definition QuiverVertices : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier   := @nodes Q
                    ; is_setoid := {| equiv        := @eq (@nodes Q)
                                    ; setoid_equiv := eq_equivalence |} |};
  fmap := fun Q Q' F => {| morphism := @fnodes Q Q' F |}
|}.
Next Obligation. intros Q Q' F a b Hab; simpl in *; subst; exact eq_refl. Qed.
Next Obligation.
  intros Q Q' F G HFG a.
  destruct HFG as [ne _].
  exact (ne a).
Qed.
Next Obligation. intros Q a; reflexivity. Qed.
Next Obligation. intros Q1 Q2 Q3 F G a; reflexivity. Qed.

(** ** The arrow functor *)

(* 相关说明。 （已译） *)
Record QArrow (Q : Quiver) := {
  qsrc  : @nodes Q;
  qtgt  : @nodes Q;
  qedge : edges qsrc qtgt
}.

Arguments qsrc {Q} _.
Arguments qtgt {Q} _.
Arguments qedge {Q} _.

(* Move an edge along equalities of its two endpoints. *)
Definition qmove {Q : Quiver} {a a' b b' : @nodes Q}
           (p : a = a') (q : b = b') (e : edges a b) : edges a' b' :=
  Logic.transport (fun t => edges a' t) q
    (Logic.transport (fun s => edges s b) p e).

(*
   本节说明 Concrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition QArrow_equiv {Q : Quiver} (u v : QArrow Q) : Type :=
  { p : qsrc u = qsrc v &
  { q : qtgt u = qtgt v & qmove p q (qedge u) ≈ qedge v } }.

Lemma QArrow_equiv_refl {Q : Quiver} (u : QArrow Q) : QArrow_equiv u u.
Proof.
  destruct u as [a b e].
  exists eq_refl, eq_refl; simpl.
  reflexivity.
Qed.

Lemma QArrow_equiv_sym {Q : Quiver} (u v : QArrow Q) :
  QArrow_equiv u v → QArrow_equiv v u.
Proof.
  destruct u as [a b e], v as [a' b' e']; intros [p [q Hq]]; simpl in *.
  destruct p, q; simpl in *.
  exists eq_refl, eq_refl; simpl.
  now symmetry.
Qed.

Lemma QArrow_equiv_trans {Q : Quiver} (u v w : QArrow Q) :
  QArrow_equiv u v → QArrow_equiv v w → QArrow_equiv u w.
Proof.
  destruct u as [a b e], v as [a' b' e'], w as [a'' b'' e''].
  intros [p [q Hq]] [p' [q' Hq']]; simpl in *.
  destruct p, q, p', q'; simpl in *.
  exists eq_refl, eq_refl; simpl.
  now transitivity e'.
Qed.

#[export] Program Instance QArrow_Setoid (Q : Quiver) : Setoid (QArrow Q) := {|
  equiv := @QArrow_equiv Q
|}.
Next Obligation.
  intro Q; constructor.
  - exact (@QArrow_equiv_refl Q).
  - exact (@QArrow_equiv_sym Q).
  - exact (@QArrow_equiv_trans Q).
Qed.

(* Introduction forms arrow setoid, so no 证明 below has see
 through `≈` notation reach underlying sigma type. （已译） *)
Lemma QArrow_intro {Q : Quiver} (u v : QArrow Q)
      (p : qsrc u = qsrc v) (q : qtgt u = qtgt v) :
  qmove p q (qedge u) ≈ qedge v → u ≈ v.
Proof. intro H; exact (existT _ p (existT _ q H)). Qed.

(* 相关说明。 （已译） *)
Lemma QArrow_intro_same {Q : Quiver} {a b : @nodes Q} (e e' : edges a b) :
  e ≈ e' →
  {| qsrc := a ; qtgt := b ; qedge := e |} ≈
  {| qsrc := a ; qtgt := b ; qedge := e' |}.
Proof. intro H; exact (existT _ eq_refl (existT _ eq_refl H)). Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma qmove_bridge {Q : Quiver} {a1 a2 b1 b2 : @nodes Q}
      (p : a1 = a2) (q : b1 = b2) (f : edges a1 b1) (g : edges a2 b2) :
  Logic.transport (fun t => edges a1 t) q f ≈
    Logic.transport_r (fun t => edges t b2) p g → qmove p q f ≈ g.
Proof. destruct p, q; unfold qmove, Logic.transport_r; simpl; trivial. Qed.

Lemma qmove_bridge_inv {Q : Quiver} {a1 a2 b1 b2 : @nodes Q}
      (p : a1 = a2) (q : b1 = b2) (f : edges a1 b1) (g : edges a2 b2) :
  qmove p q f ≈ g →
  Logic.transport (fun t => edges a1 t) q f ≈
    Logic.transport_r (fun t => edges t b2) p g.
Proof. destruct p, q; unfold qmove, Logic.transport_r; simpl; trivial. Qed.

(* The action of a homomorphism on arrows. *)
Definition qarrow_map {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
           (u : QArrow Q) : QArrow Q' :=
  {| qsrc  := F (qsrc u)
   ; qtgt  := F (qtgt u)
   ; qedge := @fedgemap _ _ F _ _ (qedge u) |}.

(* 相关说明。 （已译） *)
Lemma qarrow_map_respects {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
      (u v : QArrow Q) : u ≈ v → qarrow_map F u ≈ qarrow_map F v.
Proof.
  destruct u as [a b e], v as [a' b' e']; intros [p [q Hq]]; simpl in *.
  destruct p, q; simpl in *.
  unfold qarrow_map; simpl.
  apply QArrow_intro_same.
  now apply (@fedgemap_respects _ _ F).
Qed.

(* 相关说明。 （已译） *)
Lemma qarrow_map_agrees {Q Q' : Quiver} (F G : Q ~{QuiverCategory}~> Q')
      (HFG : F ≈ G) (u : QArrow Q) : qarrow_map F u ≈ qarrow_map G u.
Proof.
  destruct HFG as [ne coh].
  apply (QArrow_intro (qarrow_map F u) (qarrow_map G u)
                      (ne (qsrc u)) (ne (qtgt u))).
  apply qmove_bridge, coh.
Qed.

Program Definition QuiverArrows : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier := QArrow Q ; is_setoid := QArrow_Setoid Q |};
  fmap := fun Q Q' F => {| morphism := qarrow_map F |}
|}.
Next Obligation. intros Q Q' F u v Huv; now apply qarrow_map_respects. Qed.
Next Obligation. intros Q Q' F G HFG u; now apply qarrow_map_agrees. Qed.
Next Obligation. intros Q u; destruct u as [a b e]; reflexivity. Qed.
Next Obligation.
  intros Q1 Q2 Q3 F G u; destruct u as [a b e]; reflexivity.
Qed.

(** ** The disjoint-union functor *)

(* 相关说明。 （已译） *)
Definition QElt (Q : Quiver) : Type := (@nodes Q + QArrow Q)%type.

Definition QElt_equiv {Q : Quiver} (z w : QElt Q) : Type :=
  match z, w with
  | Datatypes.inl x, Datatypes.inl y => x = y
  | Datatypes.inr u, Datatypes.inr v => QArrow_equiv u v
  | _, _ => False
  end.

#[export] Program Instance QElt_Setoid (Q : Quiver) : Setoid (QElt Q) := {|
  equiv := @QElt_equiv Q
|}.
Next Obligation.
  intro Q; constructor.
  - intros [x|u]; simpl.
    + reflexivity.
    + apply QArrow_equiv_refl.
  - intros [x|u] [y|v]; simpl; try contradiction.
    + intro Hxy; now symmetry.
    + apply QArrow_equiv_sym.
  - intros [x|u] [y|v] [z|w]; simpl; try contradiction.
    + intros H1 H2; now transitivity y.
    + apply QArrow_equiv_trans.
Qed.

Definition qelt_map {Q Q' : Quiver} (F : QuiverHomomorphism Q Q')
           (z : QElt Q) : QElt Q' :=
  match z with
  | Datatypes.inl x => Datatypes.inl (F x)
  | Datatypes.inr u => Datatypes.inr (qarrow_map F u)
  end.

Program Definition QuiverElements : QuiverCategory ⟶ Sets := {|
  fobj := fun Q => {| carrier := QElt Q ; is_setoid := QElt_Setoid Q |};
  fmap := fun Q Q' F => {| morphism := qelt_map F |}
|}.
Next Obligation.
  intros Q Q' F z w Hzw.
  destruct z as [n|u], w as [n'|v]; simpl in *; try contradiction.
  - now subst.
  - now apply qarrow_map_respects.
Qed.
Next Obligation.
  intros Q Q' F G HFG z.
  destruct z as [n|u]; simpl.
  - destruct HFG as [ne _]; exact (ne n).
  - now apply qarrow_map_agrees.
Qed.
Next Obligation.
  intros Q z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; apply QArrow_equiv_refl.
Qed.
Next Obligation.
  intros Q1 Q2 Q3 F G z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; apply QArrow_equiv_refl.
Qed.

(*
   本节说明 Concrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem QuiverElements_faithful_under_NodeUIP
        {Q Q' : QuiverCategory} (uip : NodeUIP Q')
        (F G : Q ~{QuiverCategory}~> Q') :
  fmap[QuiverElements] F ≈ fmap[QuiverElements] G → F ≈ G.
Proof.
  intro H.
  (* 相关说明。 （已译） *)
  unshelve refine (existT _ (fun x => H (Datatypes.inl x)) _).
  intros x y f; simpl.
  (* 相关说明。 （已译） *)
  pose proof (H (Datatypes.inr {| qsrc := x; qtgt := y; qedge := f |})) as Ha.
  simpl in Ha.
  destruct Ha as [ps [pt Hc]].
  (* 相关说明。 （已译） *)
  rewrite (uip _ _ ps (H (Datatypes.inl x))) in Hc.
  rewrite (uip _ _ pt (H (Datatypes.inl y))) in Hc.
  exact (qmove_bridge_inv _ _ _ _ Hc).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition LoopQuiver : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => bool).

(* The loop-swapping endomorphism: 恒等 single node, negation on
 two loops. （已译） *)
Program Definition loop_swap : LoopQuiver ~{QuiverCategory}~> LoopQuiver := {|
  fnodes   := Datatypes.id;
  fedgemap := fun _ _ => negb
|}.

(* Transport along a constant type family is the identity.  The edge family of
   [LoopQuiver] is constant, so every transport appearing in its
   hom-equivalence disappears, whatever equality proof it is taken along. *)
Lemma transport_const {A B : Type} {a a' : A} (p : a = a') (b : B) :
  Logic.transport (fun _ : A => B) p b = b.
Proof. destruct p; reflexivity. Qed.

(* The 恒等 [loop_swap] DISTINCT hom-setoid of
 `QuiverCategory`: whatever node equality offered, coherence
 condition would force `true = negb true`. （已译） *)
Lemma loop_swap_distinct :
  @id QuiverCategory LoopQuiver ≈ loop_swap → False.
Proof.
  intros [ne coh].
  specialize (coh ttt ttt true).
  simpl in coh.
  unfold Logic.transport_r in coh.
  rewrite !transport_const in coh.
  discriminate.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition loop_arrow (b : bool) : QArrow LoopQuiver :=
  Build_QArrow LoopQuiver ttt ttt b.

Lemma LoopQuiver_arrows_distinct :
  QArrow_equiv (loop_arrow true) (loop_arrow false) → False.
Proof.
  intros [p [q Hq]].
  unfold qmove, loop_arrow in Hq; simpl in Hq.
  rewrite !transport_const in Hq.
  discriminate.
Qed.

(* Riehl's first negative: vertex 函子 not faithful. The 恒等
 [loop_swap] have same node map. （已译） *)
Theorem QuiverVertices_not_Faithful : Faithful QuiverVertices → False.
Proof.
  intro HF.
  apply loop_swap_distinct.
  apply (fmap_inj (F:=QuiverVertices)).
  simpl; intro x.
  reflexivity.
Qed.

(* Two nodes no edges. A homomorphism out it pair nodes no
 edge data at all — 这是 what defeats arrow 函子. （已译） *)
Definition DiscQuiver : Quiver :=
  Build_Quiver_Standard_Eq bool (fun _ _ => Empty_set).

(* The node-swapping endomorphism of [DiscQuiver]. *)
Program Definition disc_swap : DiscQuiver ~{QuiverCategory}~> DiscQuiver := {|
  fnodes   := negb;
  fedgemap := fun _ _ => Datatypes.id
|}.

(* The 恒等 [disc_swap] DISTINCT hom-setoid: any node
 family would have prove `true = negb true`. （已译） *)
Lemma disc_swap_distinct :
  @id QuiverCategory DiscQuiver ≈ disc_swap → False.
Proof.
  intros [ne coh].
  pose proof (ne true) as Hne.
  simpl in Hne.
  discriminate.
Qed.

(* Riehl's second negative: arrow 函子 not faithful. The 恒等
 [disc_swap] have same action arrows, [DiscQuiver] having none. （已译） *)
Theorem QuiverArrows_not_Faithful : Faithful QuiverArrows → False.
Proof.
  intro HF.
  apply disc_swap_distinct.
  apply (fmap_inj (F:=QuiverArrows)).
  simpl; intros [a b e].
  destruct e.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition SetQuivers : Subcategory QuiverCategory := {|
  sobj := NodeUIP;
  shom := fun _ _ _ _ _ => poly_unit
|}.
Next Obligation. intros; exact ttt. Qed.
Next Obligation. intros; exact ttt. Qed.

Definition SetQuiverCat : Category := Sub QuiverCategory SetQuivers.

Lemma SetQuivers_Full : Full QuiverCategory SetQuivers.
Proof. intros x y ox oy f; exact ttt. Qed.

(* The three 函子, restricted along 含入. （已译） *)
Definition SetQuiverVertices : SetQuiverCat ⟶ Sets :=
  QuiverVertices ◯ Incl QuiverCategory SetQuivers.

Definition SetQuiverArrows : SetQuiverCat ⟶ Sets :=
  QuiverArrows ◯ Incl QuiverCategory SetQuivers.

Definition SetQuiverElements : SetQuiverCat ⟶ Sets :=
  QuiverElements ◯ Incl QuiverCategory SetQuivers.

(* 相关说明。 （已译） *)
Lemma LoopQuiver_NodeUIP : NodeUIP LoopQuiver.
Proof.
  apply NodeDecEq_NodeUIP.
  intros x y; destruct x, y; left; reflexivity.
Qed.

Lemma DiscQuiver_NodeUIP : NodeUIP DiscQuiver.
Proof.
  apply NodeDecEq_NodeUIP.
  intros x y; destruct x, y;
    solve [ left; reflexivity | right; intro Hxy; discriminate ].
Qed.

Definition LoopSetQuiver : SetQuiverCat := (LoopQuiver; LoopQuiver_NodeUIP).
Definition DiscSetQuiver : SetQuiverCat := (DiscQuiver; DiscQuiver_NodeUIP).

(* 相关说明。 （已译） *)
Theorem SetQuiverVertices_not_Faithful : Faithful SetQuiverVertices → False.
Proof.
  intro HF.
  apply loop_swap_distinct.
  exact (fmap_inj (F:=SetQuiverVertices)
                  (x:=LoopSetQuiver) (y:=LoopSetQuiver)
                  (id; ttt) (loop_swap; ttt) (fun n => eq_refl)).
Qed.

Theorem SetQuiverArrows_not_Faithful : Faithful SetQuiverArrows → False.
Proof.
  intro HF.
  apply disc_swap_distinct.
  unshelve refine (fmap_inj (F:=SetQuiverArrows)
                            (x:=DiscSetQuiver) (y:=DiscSetQuiver)
                            (id; ttt) (disc_swap; ttt) _).
  simpl; intros [a b e]; destruct e.
Qed.

(* The positive half, unconditionally [SetQuiverCat]: [NodeUIP] witness
 定理 needs carried target 对象. （已译） *)
#[export] Instance SetQuiverElements_Faithful : Faithful SetQuiverElements.
Proof.
  constructor; intros x y f g Hfg.
  exact (QuiverElements_faithful_under_NodeUIP `2 y `1 f `1 g Hfg).
Qed.

(* 相关说明。 （已译） *)
#[export] Instance SetQuiver_Concrete : Concrete SetQuiverCat := {|
  underlying          := SetQuiverElements;
  underlying_faithful := SetQuiverElements_Faithful
|}.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma SetQuiverCat_two_arrows :
  @id SetQuiverCat LoopSetQuiver ≈ (loop_swap; ttt) → False.
Proof. exact loop_swap_distinct. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The node-UIP 假设 necessary, not merely convenient （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma uip_transport_id {A} {c a : A} (p : c = a) :
  Logic.transport (fun s => c = s) p eq_refl = p.
Proof. destruct p; reflexivity. Qed.

Lemma uip_transport_l {A} {c : A} {K : Type} {a a2 : A}
      (p : a = a2) (u : c = a) (v : K) :
  Logic.transport (fun s => ((c = s) * K)%type) p (u, v)
  = (Logic.transport (fun s => c = s) p u, v).
Proof. destruct p; reflexivity. Qed.

Lemma uip_transport_r {A} {c : A} {K : Type} {b b2 : A}
      (q : b = b2) (u : K) (v : c = b) :
  Logic.transport (fun t => (K * (c = t))%type) q (u, v)
  = (u, Logic.transport (fun t => c = t) q v).
Proof. destruct q; reflexivity. Qed.

(* 相关说明。 （已译） *)
Lemma uip_key {A} {c : A} (shared loop : c = c) :
  Logic.transport (fun t : A => ((c = c) * (c = t))%type) shared
    (eq_refl, eq_refl)
  = Logic.transport (fun s : A => ((c = s) * (c = c))%type) (eq_sym shared)
      (Logic.transport (fun s : A => ((c = s) * (c = c))%type) loop
         (eq_refl, eq_refl))
  → loop = eq_refl.
Proof.
  rewrite (uip_transport_r (c:=c) (K:=(c=c)) shared eq_refl eq_refl).
  rewrite (uip_transport_l (c:=c) (K:=(c=c)) loop eq_refl eq_refl).
  rewrite (uip_transport_l (c:=c) (K:=(c=c)) (eq_sym shared)
                (Logic.transport (fun s => c = s) loop eq_refl) eq_refl).
  rewrite !uip_transport_id.
  intro H.
  pose proof (f_equal fst H) as H1.
  pose proof (f_equal snd H) as H2.
  simpl in H1, H2.
  rewrite H2 in H1.
  simpl in H1.
  exact (eq_sym H1).
Qed.

Section UIPNecessity.

Context (N : Set) (c : N) (loop : c = c).

(* 相关说明。 （已译） *)
Definition UIPQuiver : Quiver :=
  Build_Quiver_Standard_Eq N (fun x y => ((c = x) * (c = y))%type).

Definition uip_edge_id : @edges UIPQuiver c c := (eq_refl, eq_refl).
Definition uip_edge_moved : @edges UIPQuiver c c :=
  @qmove UIPQuiver c c c c loop eq_refl uip_edge_id.

Program Definition uip_hom_id : UIPQuiver ~{QuiverCategory}~> UIPQuiver :=
  {| fnodes := fun _ => c ; fedgemap := fun _ _ _ => uip_edge_id |}.
Program Definition uip_hom_moved : UIPQuiver ~{QuiverCategory}~> UIPQuiver :=
  {| fnodes := fun _ => c ; fedgemap := fun _ _ _ => uip_edge_moved |}.

(* The disjoint-union functor cannot tell them apart. *)
Lemma uip_homs_agree_on_elements :
  fmap[QuiverElements] uip_hom_id ≈ fmap[QuiverElements] uip_hom_moved.
Proof.
  intro z; destruct z as [n|u]; simpl.
  - reflexivity.
  - destruct u as [a b e]; simpl.
    exact (existT _ loop (existT _ eq_refl eq_refl)).
Qed.

(* But quiver 范畴 equates them loop trivial. （已译） *)
Lemma uip_homs_equal_forces_trivial :
  uip_hom_id ≈ uip_hom_moved → loop = eq_refl.
Proof.
  intros [shared coh].
  specialize (coh c c (eq_refl, eq_refl)).
  simpl in coh.
  unfold Logic.transport_r, uip_edge_moved, qmove, uip_edge_id in coh;
    simpl in coh.
  exact (uip_key (shared c) loop coh).
Qed.

End UIPNecessity.

(* Hence 假设 under [QuiverElements] was proved faithful is
 exactly what faithfulness would give back. （已译） *)
Theorem faithful_QuiverElements_implies_UIP :
  Faithful QuiverElements →
  ∀ (N : Set) (c : N) (loop : c = c), loop = eq_refl.
Proof.
  intros HF N c loop.
  apply (uip_homs_equal_forces_trivial N c loop).
  apply (fmap_inj (F:=QuiverElements)).
  apply uip_homs_agree_on_elements.
Qed.
