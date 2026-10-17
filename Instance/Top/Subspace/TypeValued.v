Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(** * Subspaces and quotients over the Type-valued [Top] *)

(*
 nLab: https://ncatlab.org/nlab/show/subspace+topology
 nLab: https://ncatlab.org/nlab/show/quotient+space

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* Continuity depends on the map only up to pointwise [≈]. *)
Lemma tcont_respects@{o +} {X Y : TopSpace@{o}}
  (f g : SetoidMorphism@{o o o} (top_carrier X) (top_carrier Y)) :
  (∀ x, f x ≈ g x) → Continuous X Y f → Continuous X Y g.
Proof.
  intros Hfg Hf U HU.
  apply (open_respects X (fun x => U (f x))); [|exact (Hf U HU)].
  intro x; split; intro u.
  - exact (open_proper Y U HU (f x) (g x) (Hfg x) u).
  - exact (open_proper Y U HU (g x) (f x) (symmetry (Hfg x)) u).
Qed.

(** ** The quotient topology, at the points' universe *)

Section TopQuotient.

Universe o.

Context (X : TopSpace@{o}) (T : SetoidObject@{o o})
        (q : SetoidMorphism@{o o o} (top_carrier X) T).

(* It fits at [o]: it only APPLIES [IsOpen X]. *)
Definition tquot_open (V : T → Type@{o}) : Type@{o} :=
  ((∀ t t' : T, t ≈ t' → V t → V t') ∧ IsOpen X (fun x => V (q x)))%type.

Lemma tquot_open_respects (U V : T → Type@{o}) :
  (∀ t, U t ↔ V t) → tquot_open U → tquot_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros t t' e v. apply (fst (H t')), (Hp t t' e), (snd (H t)), v.
  - exact (open_respects X _ _ (fun x => H (q x)) Ho).
Qed.

Lemma tquot_open_proper (U : T → Type@{o}) :
  tquot_open U → ∀ t t' : T, t ≈ t' → U t → U t'.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma tquot_open_union (I : Type@{o}) (U : I → T → Type@{o}) :
  (∀ i, tquot_open (U i)) → tquot_open (fun t => { i : I & U i t }).
Proof.
  intro HU; split.
  - intros t t' e [i u]; exact (i; fst (HU i) t t' e u).
  - exact (open_union X I (fun i x => U i (q x)) (fun i => snd (HU i))).
Qed.

Lemma tquot_open_whole : tquot_open (fun _ => poly_unit@{o}).
Proof. split; [intros; exact ttt|exact (open_whole X)]. Qed.

Lemma tquot_open_inter (U V : T → Type@{o}) :
  tquot_open U → tquot_open V → tquot_open (fun t => U t ∧ V t).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros t t' e [u v]; exact (HpU t t' e u, HpV t t' e v).
  - exact (open_inter X _ _ HoU HoV).
Qed.

Definition TQuot : TopSpace@{o} := {|
  top_carrier   := T;
  IsOpen        := tquot_open;
  open_respects := tquot_open_respects;
  open_proper   := tquot_open_proper;
  open_union    := tquot_open_union;
  open_whole    := tquot_open_whole;
  open_inter    := tquot_open_inter
|}.

Example TQuot_carrier : top_carrier TQuot = T := eq_refl.

Example TQuot_open (V : T → Type@{o}) : IsOpen TQuot V = tquot_open V
  := eq_refl.

Lemma tquot_proj_cont : Continuous X TQuot q.
Proof. intros V HV; exact (snd HV). Qed.

Definition tquot_proj : ContinuousMorphism X TQuot :=
  @Build_ContinuousMorphism X TQuot q tquot_proj_cont.

(* The universal property, over ARBITRARY spaces [Z] mapping out. *)
Lemma tquot_universal (Z : TopSpace@{o})
  (k : SetoidMorphism@{o o o} T (top_carrier Z)) :
  Continuous TQuot Z k ↔ Continuous X Z (setoid_morphism_compose k q).
Proof.
  split.
  - intros Hk W HW. exact (snd (Hk W HW)).
  - intros Hc W HW; split.
    + intros t t' e w.
      exact (open_proper Z W HW (k t) (k t') (proper_morphism k t t' e) w).
    + exact (Hc W HW).
Qed.

(* The book's form: a continuous [f : X → Z] whose underlying function
   factors as [k ∘ q] has [k] continuous out of the quotient. *)
Definition tquot_desc (Z : TopSpace@{o}) (f : ContinuousMorphism X Z)
  (k : SetoidMorphism@{o o o} T (top_carrier Z))
  (Hfk : ∀ x, continuous_map f x ≈ k (q x)) : ContinuousMorphism TQuot Z :=
  @Build_ContinuousMorphism TQuot Z k
    (snd (tquot_universal Z k)
       (tcont_respects (continuous_map f) (setoid_morphism_compose k q)
          Hfk (continuity f))).

Example tquot_desc_map (Z : TopSpace@{o}) (f : ContinuousMorphism X Z)
  (k : SetoidMorphism@{o o o} T (top_carrier Z))
  (Hfk : ∀ x, continuous_map f x ≈ k (q x)) :
  continuous_map (tquot_desc Z f k Hfk) = k := eq_refl.

End TopQuotient.

(** ** The subspace topology, one universe up *)

Section TopSubspace.

Universes o o1.
Constraint o < o1.

Context (X : TopSpace@{o}) (S : SetoidObject@{o o})
        (h : SetoidMorphism@{o o o} S (top_carrier X)).

(* Mac Lane's predicate, verbatim: V is open when it is the preimage along
   [h] of an open of X.  It quantifies over the opens of X, so it is valued
   at [o1], one universe above the points. *)
Definition tsub_open (V : S → Type@{o}) : Type@{o1} :=
  { U : top_carrier X → Type@{o} &
    (IsOpen X U ∧ (∀ s : S, V s ↔ U (h s)))%type }.

Lemma tsub_open_respects (U V : S → Type@{o}) :
  (∀ s, U s ↔ V s) → tsub_open U → tsub_open V.
Proof.
  intros HUV [B [HB HUB]].
  exists B; split; [exact HB|].
  intro s; split.
  - intro v; exact (fst (HUB s) (snd (HUV s) v)).
  - intro b; exact (fst (HUV s) (snd (HUB s) b)).
Qed.

Lemma tsub_open_proper (U : S → Type@{o}) :
  tsub_open U → ∀ s t : S, s ≈ t → U s → U t.
Proof.
  intros [B [HB HUB]] s t Hst u.
  apply (snd (HUB t)).
  exact (open_proper X B HB (h s) (h t) (proper_morphism h s t Hst)
           (fst (HUB s) u)).
Qed.

(* Unions indexed at the points' universe, as in [open_union]: the
   witnesses are data, and the union of the witnesses witnesses the
   union. *)
Lemma tsub_open_union (I : Type@{o}) (U : I → S → Type@{o}) :
  (∀ i, tsub_open (U i)) → tsub_open (fun s => { i : I & U i s }).
Proof.
  intro HU.
  exists (fun x => { i : I & `1 (HU i) x }); split.
  - apply (open_union X I (fun i => `1 (HU i))).
    intro i; exact (fst `2 (HU i)).
  - intro s; split.
    + intros [i u]; exact (i; fst (snd `2 (HU i) s) u).
    + intros [i b]; exact (i; snd (snd `2 (HU i) s) b).
Qed.

Lemma tsub_open_whole : tsub_open (fun _ => poly_unit@{o}).
Proof.
  exists (fun _ => poly_unit@{o}); split; [exact (open_whole X)|].
  intro s; split; exact (fun w => w).
Qed.

Lemma tsub_open_inter (U V : S → Type@{o}) :
  tsub_open U → tsub_open V → tsub_open (fun s => U s ∧ V s).
Proof.
  intros [A [HA HUA]] [B [HB HVB]].
  exists (fun x => A x ∧ B x); split.
  - exact (open_inter X A B HA HB).
  - intro s; split.
    + intros [u v]; exact (fst (HUA s) u, fst (HVB s) v).
    + intros [a b]; exact (snd (HUA s) a, snd (HVB s) b).
Qed.

(* [h] is continuous out of the subspace: preimages of opens are open. *)
Lemma tsub_preimage_open (U : top_carrier X → Type@{o}) :
  IsOpen X U → tsub_open (fun s => U (h s)).
Proof.
  intro HU; exists U; split; [exact HU|].
  intro s; split; exact (fun w => w).
Qed.

(* Continuity into the subspace, for a setoid map from a space. *)
Definition tsub_continuous (Z : TopSpace@{o})
  (g : SetoidMorphism@{o o o} (top_carrier Z) S) : Type@{o1} :=
  ∀ V : S → Type@{o}, tsub_open V → IsOpen Z (fun z => V (g z)).

(* The universal property, over ARBITRARY spaces [Z] mapping in. *)
Lemma tsub_universal (Z : TopSpace@{o})
  (g : SetoidMorphism@{o o o} (top_carrier Z) S) :
  tsub_continuous Z g ↔ Continuous Z X (setoid_morphism_compose h g).
Proof.
  split.
  - intros Hc U HU.
    exact (Hc (fun s => U (h s)) (tsub_preimage_open U HU)).
  - intros Hc V [B [HB HVB]].
    apply (open_respects Z (fun z => B (h (g z)))).
    + intro z; split; [exact (snd (HVB (g z))) | exact (fst (HVB (g z)))].
    + exact (Hc B HB).
Qed.

(* The book's form: a continuous [f : Z → X] whose underlying function
   factors as [h ∘ g] has [g] continuous into the subspace. *)
Definition tsub_lift (Z : TopSpace@{o}) (f : ContinuousMorphism Z X)
  (g : SetoidMorphism@{o o o} (top_carrier Z) S)
  (Hfg : ∀ z, continuous_map f z ≈ h (g z)) : tsub_continuous Z g :=
  snd (tsub_universal Z g)
    (tcont_respects (continuous_map f) (setoid_morphism_compose h g)
       Hfg (continuity f)).

End TopSubspace.

(** ** The sliced forgetful functors at [Top_Forget] *)

(* [G ↓ X] and [X ↓ G] at [Top_Forget], into the slices of the LIFTED
   [Sets@{h so}] that [Top_Forget] lands in. *)
Program Definition Top_Forget_over@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :
  @Slice Top@{h o} X ⟶ @Slice Sets@{h so} (Top_Forget@{o h so} X) := {|
  fobj := fun x => (Top_Forget (`1 x); fmap[Top_Forget] (`2 x));
  fmap := fun x y m => (fmap[Top_Forget] (`1 m); _)
|}.
Next Obligation.
  intros X [a f] [b g] [m Hm] t; simpl in *. exact (Hm t).
Qed.
Next Obligation. intros X x y m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros X x t; simpl. apply reflexive_lift. Qed.
Next Obligation. intros X x y z m n t; simpl. apply reflexive_lift. Qed.

Program Definition Top_Forget_under@{o h so +| o < h, h < so +}
  (X : TopSpace@{o}) :
  @Coslice Top@{h o} X ⟶ @Coslice Sets@{h so} (Top_Forget@{o h so} X) := {|
  fobj := fun x => (Top_Forget (`1 x); fmap[Top_Forget] (`2 x));
  fmap := fun x y m => (fmap[Top_Forget] (`1 m); _)
|}.
Next Obligation.
  intros X [a f] [b g] [m Hm] t; simpl in *. exact (Hm t).
Qed.
Next Obligation. intros X x y m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros X x t; simpl. apply reflexive_lift. Qed.
Next Obligation. intros X x y z m n t; simpl. apply reflexive_lift. Qed.

(** ** The quotient functor, out of the UNLIFTED [Sets] *)

Program Definition TQuot_Functor@{o h so +| o < h, o < so +}
  (X : TopSpace@{o}) :
  @Coslice Sets@{o so} (top_carrier X) ⟶ @Coslice Top@{h o} X := {|
  fobj := fun c => (TQuot X (`1 c) (`2 c); tquot_proj X (`1 c) (`2 c));
  fmap := fun c d m =>
    (@Build_ContinuousMorphism (TQuot X (`1 c) (`2 c)) (TQuot X (`1 d) (`2 d))
       (`1 m) _; _)
|}.
Next Obligation.
  intros X [T q] [T' q'] [m Hm]; simpl in *.
  apply (snd (tquot_universal X T q (TQuot X T' q') m)).
  apply (@tcont_respects X (TQuot X T' q') q'); [exact Hm|].
  exact (tquot_proj_cont X T' q').
Qed.
Next Obligation. intros X [T q] [T' q'] [m Hm] x; simpl in *. exact (Hm x). Qed.
Next Obligation. intros X c d m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros X c t; simpl. reflexivity. Qed.
Next Obligation. intros X c d e m n t; simpl. reflexivity. Qed.

(** ** The cross-universe transpositions *)

Section Transpositions.

Universes o h so.
Constraint o < h.
Constraint o < so.

Context (X : TopSpace@{o}).

(* A space under [X], stripped to its points and underlying map in the
   UNLIFTED coslice; [Top_Forget_under] is its lift. *)
Definition tstrip_under (y : @Coslice Top@{h o} X) :
  @Coslice Sets@{o so} (top_carrier X) :=
  (top_carrier (`1 y); continuous_map (`2 y)).

(* The space's image under [Top_Forget_under X] is the lift of its
   stripped reading, on the nose. *)
Example tstrip_under_lift@{so' + | h < so' +} (y : @Coslice Top@{h o} X) :
  Top_Forget_under@{o h so'} X y
  = (Setoid_Lift@{o h} (`1 (tstrip_under y));
     SetoidMorphism_Lift@{o h} (`2 (tstrip_under y))) := eq_refl.

Definition tstrip_under_map {y z : @Coslice Top@{h o} X}
  (f : y ~{@Coslice Top@{h o} X}~> z) :
  tstrip_under y ~{@Coslice Sets@{o so} (top_carrier X)}~> tstrip_under z :=
  (continuous_map (`1 f); `2 f).

(* The transposition of [M ⊣ X ↓ G]: a map under [X] out of the quotient IS
   its underlying map.  The small side is lifted to sit beside [Top]'s large
   hom-setoid in one [Sets], as in Instance/Top/Forgetful.v's
   [discrete_adj]. *)
Program Definition tquot_adj (x : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice Top@{h o} X) (TQuot_Functor X x) y
     ; is_setoid := @homset (@Coslice Top@{h o} X) (TQuot_Functor X x) y |}
    (Setoid_Lift
       {| carrier := @hom (@Coslice Sets@{o so} (top_carrier X)) x
                       (tstrip_under y)
        ; is_setoid := @homset (@Coslice Sets@{o so} (top_carrier X)) x
                         (tstrip_under y) |}) := {|
  to   := {| morphism := fun k => (continuous_map (`1 k); `2 k) |};
  from := {| morphism := fun k =>
    (@Build_ContinuousMorphism (`1 (TQuot_Functor X x)) (`1 y) (`1 k) _;
     `2 k) |}
|}.
Next Obligation. intros x y k k' H t; exact (H t). Qed.
Next Obligation.
  intros [T q] [Y f] [k Hk]; simpl in *.
  apply (snd (tquot_universal X T q Y k)).
  apply (tcont_respects (continuous_map f)); [exact Hk|].
  exact (continuity f).
Qed.
Next Obligation. intros x y k k' H t; exact (H t). Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.

Example tquot_adj_to_map (x : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X)
  (k : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y) :
  `1 (to (tquot_adj x y) k) = continuous_map (`1 k) := eq_refl.

Example tquot_adj_from_map (x : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X)
  (k : x ~{@Coslice Sets@{o so} (top_carrier X)}~> tstrip_under y) :
  continuous_map (`1 (from (tquot_adj x y) k)) = `1 k := eq_refl.

Lemma tquot_adj_nat_l (x x' : @Coslice Sets@{o so} (top_carrier X))
  (y : @Coslice Top@{h o} X)
  (f : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y)
  (g : x' ~{@Coslice Sets@{o so} (top_carrier X)}~> x) :
  to (tquot_adj x' y) (f ∘ fmap[TQuot_Functor X] g)
    ≈ to (tquot_adj x y) f ∘[@Coslice Sets@{o so} (top_carrier X)] g.
Proof. intro t; simpl. reflexivity. Qed.

Lemma tquot_adj_nat_r (x : @Coslice Sets@{o so} (top_carrier X))
  (y z : @Coslice Top@{h o} X) (f : y ~{@Coslice Top@{h o} X}~> z)
  (g : TQuot_Functor X x ~{@Coslice Top@{h o} X}~> y) :
  to (tquot_adj x z) (f ∘ g)
    ≈ tstrip_under_map f ∘[@Coslice Sets@{o so} (top_carrier X)]
        to (tquot_adj x y) g.
Proof. intro t; simpl. reflexivity. Qed.

(* [(X ↓ G) ∘ M = Id], stripped: Leibniz after destructing the pair. *)
Lemma tquot_obj_stripped (c : @Coslice Sets@{o so} (top_carrier X)) :
  tstrip_under (TQuot_Functor X c) = c.
Proof. destruct c; reflexivity. Defined.

Example tquot_obj_stripped_pair (T : SetoidObject@{o o})
  (q : top_carrier X ~{Sets@{o so}}~> T) :
  tstrip_under (TQuot_Functor X (T; q)) = (T; q) := eq_refl.

(* The unit of the transposition is the identity, transported. *)
Lemma tquot_unit_stripped (c : @Coslice Sets@{o so} (top_carrier X)) :
  to (tquot_adj c (TQuot_Functor X c)) id
    ≈[@Coslice Sets@{o so} (top_carrier X)]
  id_cast (eq_sym (tquot_obj_stripped c)).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

End Transpositions.

Section SubspaceTransposition.

Universes o o1 h.
Constraint o < o1.
Constraint o < h.

Context (X : TopSpace@{o}) (S : SetoidObject@{o o})
        (h : SetoidMorphism@{o o o} S (top_carrier X)).

(* Maps over [X] from [(Z, f)] into the (unpackaged) subspace on [(S, h)]:
   setoid maps into [S], continuous into the subspace, over [X]. *)
Definition tsub_hom (Z : TopSpace@{o}) (f : ContinuousMorphism@{h o} Z X) :
  Type@{o1} :=
  { g : SetoidMorphism@{o o o} (top_carrier Z) S &
    (tsub_continuous X S h Z g ∧ (∀ z, continuous_map f z ≈ h (g z)))%type }.

Program Definition tsub_hom_setoid (Z : TopSpace@{o})
  (f : ContinuousMorphism@{h o} Z X) : SetoidObject@{o1 o1} := {|
  carrier := tsub_hom Z f;
  is_setoid := {| equiv := fun g g' => ∀ z, `1 g z ≈ `1 g' z |}
|}.
Next Obligation.
  intros Z f; constructor.
  - intros g z; reflexivity.
  - intros g g' H z; symmetry; exact (H z).
  - intros g g' g'' H1 H2 z; transitivity (`1 g' z);
      [exact (H1 z)|exact (H2 z)].
Qed.

(* The transposition of [G ↓ X ⊣ L]: a map over [X] into the subspace IS
   its underlying map, continuity coming from [tsub_universal]. *)
Program Definition tsub_adj (Z : TopSpace@{o})
  (f : ContinuousMorphism@{h o} Z X) :
  @Isomorphism Sets
    (Setoid_Lift
       {| carrier := @hom (@Slice Sets@{o o1} (top_carrier X))
                       (top_carrier Z; continuous_map f) (S; h)
        ; is_setoid := @homset (@Slice Sets@{o o1} (top_carrier X))
                         (top_carrier Z; continuous_map f) (S; h) |})
    (tsub_hom_setoid Z f) := {|
  to   := {| morphism := fun k => (`1 k; (tsub_lift X S h Z f (`1 k) _, _)) |};
  from := {| morphism := fun g => (`1 g; _) |}
|}.
Next Obligation. intros Z f k z; simpl in *. symmetry; exact (`2 k z). Qed.
Next Obligation. intros Z f k z; simpl in *. symmetry; exact (`2 k z). Qed.
Next Obligation. intros Z f k k' H z; exact (H z). Qed.
Next Obligation.
  intros Z f g z; simpl in *. symmetry; exact (snd `2 g z).
Qed.
Next Obligation. intros Z f g g' H z; exact (H z). Qed.
Next Obligation. intros Z f g z; simpl. reflexivity. Qed.
Next Obligation. intros Z f k z; simpl. reflexivity. Qed.

Example tsub_adj_to_map (Z : TopSpace@{o}) (f : ContinuousMorphism@{h o} Z X)
  (k : @hom (@Slice Sets@{o o1} (top_carrier X))
         (top_carrier Z; continuous_map f) (S; h)) :
  `1 (to (tsub_adj Z f) k) = `1 k := eq_refl.

End SubspaceTransposition.
