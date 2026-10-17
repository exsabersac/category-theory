Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab: https://ncatlab.org/nlab/show/quotient+group
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_group

   本文件给出商相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Subgroups and normal subgroups *)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record Subgroup (G : GrpObject) := {
  sub_mem : carrier G → Type;

  (* (1) ≈-saturation *)
  sub_resp : ∀ a b : carrier G, a ≈ b → sub_mem a → sub_mem b;
  (* (2) the unit *)
  sub_unit : sub_mem (grp_unit G);
  (* (3) closure under product *)
  sub_mul : ∀ a b : carrier G,
    sub_mem a → sub_mem b → sub_mem (grp_mul G a b);
  (* (4) closure under inverse *)
  sub_inv : ∀ a : carrier G, sub_mem a → sub_mem (grp_inv G a)
}.

Arguments sub_mem {G} _ _.
Arguments sub_resp {G} _ _ _ _ _.
Arguments sub_unit {G} _.
Arguments sub_mul {G} _ _ _ _ _.
Arguments sub_inv {G} _ _ _.

(* A normal subgroup adds the fifth fact: closure under conjugation.  The
   five laws are exactly the five that Abelianization.v names. *)
Record NormalSubgroup (G : GrpObject) := {
  ns_sub :> Subgroup G;

  (* (5) normality *)
  ns_conj : ∀ t a : carrier G, sub_mem ns_sub a →
    sub_mem ns_sub (grp_mul G (grp_mul G t a) (grp_inv G t))
}.

Arguments ns_sub {G} _.
Arguments ns_conj {G} _ _ _ _.

(* Saturation in the argument-implicit shape the proofs below want, so
   that they read like Abelianization.v's [inc_resp] applications. *)
Definition sub_at {G : GrpObject} (S : Subgroup G) {a b : carrier G}
  (Hab : a ≈ b) (Ha : sub_mem S a) : sub_mem S b := sub_resp S a b Hab Ha.

(** ** The subgroup as an object of Grp *)

(* The sigma carrier over membership, compared on elements -- the shape
   Instance/Grp.v's [Grp_kernel] and Instance/Grp/Center.v use, so the
   membership witness carries no equational weight. *)
Definition sub_carrier {G : GrpObject} (S : Subgroup G) : Type :=
  { a : carrier G & sub_mem S a }.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition SubgroupGrp {G : GrpObject} (S : Subgroup G) : GrpObject := {|
  grp_setoid := {| carrier := sub_carrier S
                 ; is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |} |};
  grp_unit := existT _ (grp_unit G) (sub_unit S);
  grp_mul := fun p q =>
    existT _ (grp_mul G (`1 p) (`1 q)) (sub_mul S _ _ (`2 p) (`2 q));
  grp_inv := fun p => existT _ (grp_inv G (`1 p)) (sub_inv S _ (`2 p))
|}.
Next Obligation. intros G S; equivalence; now transitivity (`1 y). Qed.
Next Obligation.
  intros G S a a' Ha b b' Hb; simpl in *; now rewrite Ha, Hb.
Qed.
Next Obligation. intros G S a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G S a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G S a; simpl; apply grp_mul_inv_l. Qed.
Next Obligation.
  (*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  intros G S.
  unshelve refine (sigma_first_PropEquiv _ _ _ (grp_prop G)).
  - intros p q Hpq; exact Hpq.
  - intros p q Hpq; exact Hpq.
Defined.

(* The inclusion of a subgroup: the first projection. *)
Program Definition sub_incl {G : GrpObject} (S : Subgroup G) :
  SubgroupGrp S ~{Grp}~> G := {|
  grp_map := {| morphism := fun p : sub_carrier S => `1 p |}
|}.
Next Obligation. intros G S a b Hab; exact Hab. Qed.
Next Obligation. intros G S; simpl; reflexivity. Qed.
Next Obligation. intros G S a b; simpl; reflexivity. Qed.

(* The inclusion is injective, hence monic in [Grp] by
   Instance/Grp.v's biconditional. *)
Lemma sub_incl_injective {G : GrpObject} (S : Subgroup G)
  (a b : carrier (SubgroupGrp S)) :
  grp_map (sub_incl S) a ≈ grp_map (sub_incl S) b → a ≈ b.
Proof. intro Hab; exact Hab. Qed.

Lemma sub_incl_monic {G : GrpObject} (S : Subgroup G) : Monic (sub_incl S).
Proof.
  apply (fst (Grp_injectivity_is_monic (sub_incl S))).
  apply sub_incl_injective.
Qed.

(** ** The quotient relation *)

(* a ~ b when a * b⁻¹ lies in N.  The orientation matches
   Instance/Grp/Abelianization.v's [abel_eq], which this generalizes. *)
Definition quot_rel {G : GrpObject} (N : Subgroup G) (a b : carrier G) : Type :=
  sub_mem N (grp_mul G a (grp_inv G b)).

Section QuotientRelation.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

(* The finer relation implies the coarser one. *)
Lemma quot_rel_of_equiv (a b : carrier G) : a ≈ b → quot_rel N a b.
Proof.
  intro Hab; unfold quot_rel.
  apply (sub_at N (a := grp_unit G)); [| exact (sub_unit N) ].
  rewrite Hab.
  symmetry; apply (grp_mul_inv_r G).
Qed.

Lemma quot_rel_refl (a : carrier G) : quot_rel N a a.
Proof. apply quot_rel_of_equiv; reflexivity. Qed.

Lemma quot_rel_sym (a b : carrier G) : quot_rel N a b → quot_rel N b a.
Proof.
  unfold quot_rel; intro K.
  apply (sub_at N (a := grp_inv G (grp_mul G a (grp_inv G b)))).
  - rewrite (grp_inv_mul G a (grp_inv G b)).
    rewrite (grp_inv_inv G b).
    reflexivity.
  - exact (sub_inv N _ K).
Qed.

Lemma quot_rel_trans (a b c : carrier G) :
  quot_rel N a b → quot_rel N b c → quot_rel N a c.
Proof.
  unfold quot_rel; intros K1 K2.
  apply (sub_at N
           (a := grp_mul G (grp_mul G a (grp_inv G b))
                   (grp_mul G b (grp_inv G c)))).
  - rewrite (grp_mul_assoc G a (grp_inv G b)
               (grp_mul G b (grp_inv G c))).
    rewrite <- (grp_mul_assoc G (grp_inv G b) b (grp_inv G c)).
    rewrite (grp_mul_inv_l G b).
    rewrite (grp_mul_unit_l G (grp_inv G c)).
    reflexivity.
  - exact (sub_mul N _ _ K1 K2).
Qed.

(* Multiplication respects the relation.  This is the first of the two
   places where NORMALITY is spent: the correction term a * (b * b'⁻¹) * a⁻¹
   is a conjugate of a member. *)
Lemma quot_rel_mul (a a' b b' : carrier G) :
  quot_rel N a a' → quot_rel N b b' →
  quot_rel N (grp_mul G a b) (grp_mul G a' b').
Proof.
  unfold quot_rel; intros K1 K2.
  apply (sub_at N
           (a := grp_mul G
                   (grp_mul G (grp_mul G a (grp_mul G b (grp_inv G b')))
                      (grp_inv G a))
                   (grp_mul G a (grp_inv G a')))).
  - rewrite (grp_inv_mul G a' b').
    rewrite (grp_mul_assoc G
               (grp_mul G a (grp_mul G b (grp_inv G b')))
               (grp_inv G a) (grp_mul G a (grp_inv G a'))).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a (grp_inv G a')).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_l G (grp_inv G a')).
    rewrite (grp_mul_assoc G a (grp_mul G b (grp_inv G b'))
               (grp_inv G a')).
    rewrite (grp_mul_assoc G b (grp_inv G b') (grp_inv G a')).
    rewrite (grp_mul_assoc G a b
               (grp_mul G (grp_inv G b') (grp_inv G a'))).
    reflexivity.
  - exact (sub_mul N _ _ (ns_conj N a _ K2) K1).
Qed.

(* Inversion respects the relation; normality again. *)
Lemma quot_rel_inv (a a' : carrier G) :
  quot_rel N a a' → quot_rel N (grp_inv G a) (grp_inv G a').
Proof.
  unfold quot_rel; intros K.
  apply (sub_at N
           (a := grp_mul G
                   (grp_mul G (grp_inv G a)
                      (grp_inv G (grp_mul G a (grp_inv G a'))))
                   (grp_inv G (grp_inv G a)))).
  - rewrite (grp_inv_mul G a (grp_inv G a')).
    rewrite (grp_inv_inv G a').
    rewrite (grp_inv_inv G a).
    rewrite <- (grp_mul_assoc G (grp_inv G a) a' (grp_inv G a)).
    rewrite (grp_mul_assoc G (grp_mul G (grp_inv G a) a')
               (grp_inv G a) a).
    rewrite (grp_mul_inv_l G a).
    rewrite (grp_mul_unit_r G (grp_mul G (grp_inv G a) a')).
    reflexivity.
  - exact (ns_conj N (grp_inv G a) _ (sub_inv N _ K)).
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma quot_rel_unit_iff (a : carrier G) :
  quot_rel N a (grp_unit G) ↔ sub_mem N a.
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at N (a := grp_mul G a (grp_inv G (grp_unit G)))); [| exact K ].
    rewrite (grp_inv_unit G).
    apply (grp_mul_unit_r G).
  - apply (sub_at N (a := a)); [| exact K ].
    rewrite (grp_inv_unit G).
    symmetry; apply (grp_mul_unit_r G).
Qed.

End QuotientRelation.

(** ** The quotient group and its projection *)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition quot_equiv {G : GrpObject} (N : NormalSubgroup G)
  (a b : carrier G) : Prop := inhabited (quot_rel N a b).

(* The setoid is named rather than written inline in the record below: a
   [Program] record literal cannot carry a [PropEquiv] field naming a setoid
   written inline in the same literal. *)
Program Definition quot_setoid {G : GrpObject} (N : NormalSubgroup G) :
  SetoidObject := {|
  carrier := carrier G;
  is_setoid := {| equiv := quot_equiv N |}
|}.
Next Obligation.
  intros G N.
  constructor.
  - intro a; constructor; apply quot_rel_refl.
  - intros a b [Hab]; constructor; now apply quot_rel_sym.
  - intros a b c [Hab] [Hbc]; constructor; now apply (quot_rel_trans N a b).
Qed.

Program Definition QuotientGrp {G : GrpObject} (N : NormalSubgroup G) :
  GrpObject := {|
  grp_setoid := quot_setoid N;
  grp_unit := grp_unit G;
  grp_mul := grp_mul G;
  grp_inv := grp_inv G;
  (* The relation IS a [Prop], so the two implications are the identity. *)
  grp_prop :=
    @PropEquiv_of_relation _ (is_setoid (quot_setoid N)) (@quot_equiv G N)
      (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation.
  (* [@equiv _ S x y] is ascribed sort [Type] even when the underlying
     relation is a [Prop], so the hypotheses and the goal are converted to
     the [inhabited] form before the elimination. *)
  intros G N a a' Ha b b' Hb.
  change (inhabited (quot_rel N a a')) in Ha.
  change (inhabited (quot_rel N b b')) in Hb.
  change (inhabited (quot_rel N (grp_mul G a b) (grp_mul G a' b'))).
  destruct Ha as [Ha], Hb as [Hb]; constructor; now apply quot_rel_mul.
Qed.
Next Obligation.
  intros G N a b c; constructor; apply quot_rel_of_equiv, grp_mul_assoc.
Qed.
Next Obligation.
  intros G N a; constructor; apply quot_rel_of_equiv, grp_mul_unit_l.
Qed.
Next Obligation.
  intros G N a; constructor; apply quot_rel_of_equiv, grp_mul_inv_l.
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The projection: the identity function, read from the fine setoid into
   the coarse one. *)
Program Definition quot_proj {G : GrpObject} (N : NormalSubgroup G) :
  G ~{Grp}~> QuotientGrp N := {|
  grp_map := {| morphism := fun a : carrier G => a |}
|}.
Next Obligation.
  intros G N a b Hab; constructor; apply quot_rel_of_equiv, Hab.
Qed.
Next Obligation. intros G N; simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation. intros G N a b; simpl; constructor; apply quot_rel_refl. Qed.

(* The projection kills N, which is the statement that gives the universal
   element below its element. *)
Lemma quot_proj_kills {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  sub_mem N a → grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N).
Proof.
  intro Ha; simpl.
  constructor.
  exact (snd (quot_rel_unit_iff N a) Ha).
Qed.

(* Conversely, anything the projection kills lies in N: the projection's
   kernel is exactly N, as a biconditional rather than an inclusion. *)
(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma quot_proj_kernel {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  grp_map (quot_proj N) a ≈ grp_unit (QuotientGrp N) ↔ inhabited (sub_mem N a).
Proof.
  split; intro K.
  - change (inhabited (quot_rel N a (grp_unit G))) in K.
    destruct K as [K]; constructor; exact (fst (quot_rel_unit_iff N a) K).
  - change (inhabited (quot_rel N a (grp_unit G))).
    destruct K as [K]; constructor; exact (snd (quot_rel_unit_iff N a) K).
Qed.

(* The projection is surjective on elements -- indeed the identity -- and
   hence epic.  Recorded because the isomorphism-theorem chases in the
   sibling file cancel it on the right. *)
Lemma quot_proj_epic {G : GrpObject} (N : NormalSubgroup G) :
  Epic (quot_proj N).
Proof.
  constructor; intros K g h Hgh a.
  exact (Hgh a).
Qed.

(** ** The functor of homomorphisms killing N *)

(* Kills N K is the set of homomorphisms G -> K that send every member of
   N to the unit.  It is covariant in K by postcomposition, which is what
   makes ⟨G/N, p⟩ a universal element in Mac Lane's covariant sense rather
   than a representing object of a presheaf. *)
Definition Kills {G : GrpObject} (N : NormalSubgroup G) (K : GrpObject) : Type :=
  { h : G ~{Grp}~> K & ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K }.

(* Two members are compared by their underlying homomorphisms; the
   killing witness carries no equational weight, exactly as the membership
   witness does not in [sub_carrier]. *)
Program Definition Kills_Setoid {G : GrpObject} (N : NormalSubgroup G)
  (K : GrpObject) : Setoid (Kills N K) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.
Next Obligation.
  intros G N K.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; now symmetry.
  - intros p q r Hpq Hqr; now transitivity (`1 q).
Qed.

Lemma Kills_post {G : GrpObject} (N : NormalSubgroup G) {K K' : GrpObject}
  (k : K ~{Grp}~> K') (p : Kills N K) (a : carrier G) :
  sub_mem N a → grp_map (k ∘ `1 p) a ≈ grp_unit K'.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  rewrite (`2 p a Ha).
  apply (grp_map_unit k).
Qed.

Program Definition KillsFunctor {G : GrpObject} (N : NormalSubgroup G) :
  Grp ⟶ Sets := {|
  fobj := fun K => {| carrier := Kills N K ; is_setoid := Kills_Setoid N K |};
  fmap := fun K K' k =>
    {| morphism := fun p : Kills N K =>
         existT _ (k ∘ `1 p) (Kills_post N k p) |}
|}.
Next Obligation.
  intros G N K K' k p q Hpq a; simpl in *.
  unfold Basics.compose.
  now rewrite (Hpq a).
Qed.
Next Obligation.
  intros G N K K' k k' Hk p a; simpl.
  unfold Basics.compose.
  exact (Hk _).
Qed.
Next Obligation. intros G N K p a; simpl; reflexivity. Qed.
Next Obligation. intros G N K K' K'' k k' p a; simpl; reflexivity. Qed.

(** ** The mediating homomorphism *)

Section Mediator.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).
Context {K : GrpObject}.
Context (p : Kills N K).

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kills_descends (a b : carrier G) :
  quot_rel N a b → grp_map (`1 p) a ≈ grp_map (`1 p) b.
Proof.
  intro Hab.
  apply (grp_cancel_r K (grp_inv K (grp_map (`1 p) b))).
  rewrite (grp_mul_inv_r K (grp_map (`1 p) b)).
  rewrite <- (grp_map_inv (`1 p) b).
  rewrite <- (grp_map_mul (`1 p)).
  exact (`2 p _ Hab).
Qed.

Program Definition quot_med : QuotientGrp N ~{Grp}~> K := {|
  grp_map := {| morphism := fun a : carrier (QuotientGrp N) =>
                              grp_map (`1 p) a |}
|}.
(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Next Obligation.
  intros a b Hab.
  apply (@pequiv_to _ _ (grp_prop K)).
  change (inhabited (quot_rel N a b)) in Hab.
  destruct Hab as [Hab].
  apply (@pequiv_from _ _ (grp_prop K)).
  exact (kills_descends a b Hab).
Qed.
Next Obligation. simpl; apply (grp_map_unit (`1 p)). Qed.
Next Obligation. intros a b; simpl; apply (grp_map_mul (`1 p)). Qed.

(* The mediator's defining triangle, at the level of the underlying
   homomorphisms: it holds by reflexivity, since the projection is the
   identity function. *)
Lemma quot_med_commutes : quot_med ∘ quot_proj N ≈ `1 p.
Proof. intro a; simpl; reflexivity. Qed.

Lemma quot_med_unique (v : QuotientGrp N ~{Grp}~> K)
  (Hv : v ∘ quot_proj N ≈ `1 p) : quot_med ≈ v.
Proof. intro a; simpl; symmetry; exact (Hv a). Qed.

End Mediator.

Arguments quot_med {G} N {K} p.

(** ** Mac Lane's construction 5: ⟨G/N, p⟩ is a universal element *)

(* The projection, packaged as an element of (Kills N)(G/N). *)
Definition quot_elem {G : GrpObject} (N : NormalSubgroup G) :
  Kills N (QuotientGrp N) :=
  existT _ (quot_proj N) (quot_proj_kills N).

(*
   本节说明Yoneda相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition quot_universal_element {G : GrpObject}
  (N : NormalSubgroup G) : AUniversalElement (KillsFunctor N) (QuotientGrp N) := {|
  aue_elem := quot_elem N
|}.
Next Obligation.
  intros G N K x.
  unshelve refine {| unique_obj := quot_med N x |}.
  - exact (quot_med_commutes N x).
  - intros v Hv; simpl in *.
    exact (quot_med_unique N x v Hv).
Defined.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example quot_universal_elem_is_proj {G : GrpObject} (N : NormalSubgroup G) :
  `1 (@aue_elem _ (KillsFunctor N) (QuotientGrp N) (quot_universal_element N))
    = quot_proj N.
Proof. reflexivity. Qed.

(* And the mediator extracted from the class is the fixpoint-free direct
   one, again by convertibility. *)
Example quot_universal_med_is_quot_med {G : GrpObject} (N : NormalSubgroup G)
  {K : GrpObject} (x : Kills N K) :
  unique_obj (@aue_universal _ (KillsFunctor N) (QuotientGrp N)
                (quot_universal_element N) K x)
    = quot_med N x.
Proof. reflexivity. Qed.

(** ** Awodey Theorem 4.4: the homomorphism theorem, as a biconditional *)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem hom_theorem {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K) :
  (∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K)
    ↔ (∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h).
Proof.
  split.
  - intro Hkill.
    pose (x := existT (fun h : G ~{Grp}~> K =>
                         ∀ a : carrier G, sub_mem N a →
                           grp_map h a ≈ grp_unit K) h Hkill).
    unshelve refine {| unique_obj := quot_med N x |}.
    + exact (quot_med_commutes N x).
    + intros v Hv.
      exact (quot_med_unique N x v Hv).
  - intros [u Hu _] a Ha.
    transitivity (grp_map u (grp_map (quot_proj N) a)).
    + symmetry; exact (Hu a).
    + transitivity (grp_map u (grp_unit (QuotientGrp N))).
      * apply proper_morphism.
        exact (quot_proj_kills N a Ha).
      * exact (grp_map_unit u).
Qed.

(* The two halves separately, in the shape a consumer applies. *)
Definition hom_theorem_factor {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hkill : ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) :
  ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h :=
  fst (hom_theorem N h) Hkill.

Definition hom_theorem_kills {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hfac : ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h) :
  ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K :=
  snd (hom_theorem N h) Hfac.

(*
   本节说明同构、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition KernelNS {G K : GrpObject} (h : G ~{Grp}~> K) :
  NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun a : carrier G => grp_map h a ≈ grp_unit K |}
|}.
Next Obligation.
  intros G K h a b Hab Ha; simpl in *.
  now rewrite <- Hab.
Qed.
Next Obligation. intros G K h; simpl; apply (grp_map_unit h). Qed.
Next Obligation.
  intros G K h a b Ha Hb; simpl in *.
  rewrite (grp_map_mul h), Ha, Hb.
  apply (grp_mul_unit_l K).
Qed.
Next Obligation.
  intros G K h a Ha; simpl in *.
  rewrite (grp_map_inv h), Ha.
  apply (grp_inv_unit K).
Qed.
Next Obligation.
  intros G K h t a Ha; simpl in *.
  rewrite !(grp_map_mul h), (grp_map_inv h), Ha.
  rewrite (grp_mul_unit_r K).
  apply (grp_mul_inv_r K).
Qed.

(* Membership in the kernel subgroup IS the defining equation, by
   convertibility. *)
Example KernelNS_mem {G K : GrpObject} (h : G ~{Grp}~> K) (a : carrier G) :
  sub_mem (KernelNS h) a = (grp_map h a ≈ grp_unit K).
Proof. reflexivity. Qed.

(* The subgroup object of the kernel normal subgroup has the same carrier
   as Instance/Grp.v's [Grp_kernel], by convertibility. *)
Example KernelNS_carrier_is_Grp_kernel {G K : GrpObject} (h : G ~{Grp}~> K) :
  carrier (SubgroupGrp (KernelNS h)) = carrier (Grp_kernel h).
Proof. reflexivity. Qed.

(** ** The degenerate normal subgroups, named and separated *)

(* The trivial normal subgroup {e}. *)
Program Definition TrivialNS (G : GrpObject) : NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun a : carrier G => a ≈ grp_unit G |}
|}.
Next Obligation. intros G a b Hab Ha; simpl in *; now rewrite <- Hab. Qed.
Next Obligation. intros G; simpl; reflexivity. Qed.
Next Obligation.
  intros G a b Ha Hb; simpl in *.
  rewrite Ha, Hb; apply (grp_mul_unit_l G).
Qed.
Next Obligation.
  intros G a Ha; simpl in *.
  rewrite Ha; apply (grp_inv_unit G).
Qed.
Next Obligation.
  intros G t a Ha; simpl in *.
  rewrite Ha, (grp_mul_unit_r G).
  apply (grp_mul_inv_r G).
Qed.

(* The whole group, as a normal subgroup of itself. *)
Program Definition TotalNS (G : GrpObject) : NormalSubgroup G := {|
  ns_sub := {| sub_mem := fun _ : carrier G => poly_unit |}
|}.
Next Obligation. intros G a b Hab Ha; exact ttt. Qed.
Next Obligation. intros G; exact ttt. Qed.
Next Obligation. intros G a b Ha Hb; exact ttt. Qed.
Next Obligation. intros G a Ha; exact ttt. Qed.
Next Obligation. intros G t a Ha; exact ttt. Qed.

(* Quotienting by the trivial subgroup changes nothing: the coarse
   relation coincides with `≈`, in both directions. *)
Lemma quot_trivial_iff (G : GrpObject) (a b : carrier G) :
  quot_rel (TrivialNS G) a b ↔ a ≈ b.
Proof.
  split.
  - intro K; simpl in K.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite K.
    symmetry; apply (grp_mul_inv_r G).
  - intro Hab; simpl.
    rewrite Hab; apply (grp_mul_inv_r G).
Qed.

(* Quotienting by the whole group collapses everything. *)
Lemma quot_total_collapses (G : GrpObject) (a b : carrier G) :
  quot_rel (TotalNS G) a b.
Proof. exact ttt. Qed.

(** ** Quotients by coextensive normal subgroups agree *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition quot_congr {G : GrpObject} (N N' : NormalSubgroup G)
  (H1 : ∀ a : carrier G, sub_mem N a → sub_mem N' a)
  (H2 : ∀ a : carrier G, sub_mem N' a → sub_mem N a) :
  QuotientGrp N ≅[Grp] QuotientGrp N' := {|
  to := {| grp_map := {| morphism := fun a : carrier (QuotientGrp N) => a |} |};
  from := {| grp_map := {| morphism := fun a : carrier (QuotientGrp N') => a |} |}
|}.
(* The two respectfulness obligations are the only places the truncation is
   visible: unwrap the hypothesis, apply the inclusion, wrap again. *)
Next Obligation.
  intros G N N' H1 H2 a b Hab.
  change (inhabited (quot_rel N a b)) in Hab.
  change (inhabited (quot_rel N' a b)).
  destruct Hab as [Hab]; constructor; exact (H1 _ Hab).
Qed.
Next Obligation. intros G N N' H1 H2; simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation.
  intros G N N' H1 H2 a b; simpl; constructor; apply quot_rel_refl.
Qed.
Next Obligation.
  intros G N N' H1 H2 a b Hab.
  change (inhabited (quot_rel N' a b)) in Hab.
  change (inhabited (quot_rel N a b)).
  destruct Hab as [Hab]; constructor; exact (H2 _ Hab).
Qed.
Next Obligation. intros G N N' H1 H2; simpl; constructor; apply quot_rel_refl. Qed.
Next Obligation.
  intros G N N' H1 H2 a b; simpl; constructor; apply quot_rel_refl.
Qed.
Next Obligation.
  intros G N N' H1 H2 a; simpl; constructor; apply quot_rel_refl.
Qed.
Next Obligation.
  intros G N N' H1 H2 a; simpl; constructor; apply quot_rel_refl.
Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* A3, the rotations: the elements whose reflection component is false.
   S3's setoid IS propositional equality
   (Instance/Grp/TwoFunctors.v's [S3_equiv_is_eq]), so saturation is
   substitution and every closure law is a finite check. *)
Program Definition A3 : NormalSubgroup S3 := {|
  ns_sub := {| sub_mem := fun a : carrier S3 => snd a = false |}
|}.
Next Obligation. intros a b Hab Ha; simpl in *; now subst. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hb Hc; simpl in *; subst; reflexivity.
Qed.
Next Obligation. intros [i b] Hb; simpl in *; subst; reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hc; simpl in *; subst.
  destruct i, j, b; reflexivity.
Qed.

(* A3 is PROPER: the reflection is not a rotation. *)
Lemma A3_proper : sub_mem A3 S3_s → False.
Proof. simpl; discriminate. Qed.

(* A3 is NONTRIVIAL: it contains a non-unit element. *)
Lemma A3_nontrivial : sub_mem A3 S3_r * (S3_r ≈ s3_unit → False).
Proof. split; [ reflexivity | discriminate ]. Qed.

(* Normality of A3 is not vacuous: conjugation in S3 genuinely moves
   elements ([S3_conj_s_nontrivial]), so [ns_conj] is doing work here
   rather than holding because conjugation is the identity. *)
Lemma A3_conjugation_nontrivial : Grp_conj S3 S3_s ≈ @id Grp S3 → False.
Proof. exact S3_conj_s_nontrivial. Qed.

(* THE QUOTIENT DOES NOT COLLAPSE: the reflection stays apart from the
   unit in S3/A3. *)
Theorem S3_mod_A3_not_collapsed : quot_rel A3 S3_s s3_unit → False.
Proof. simpl; discriminate. Qed.

(* Nor does the quotient projection identify the two generators, so
   S3/A3 has at least two elements. *)
(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_mod_A3_two_elements :
  grp_map (quot_proj A3) S3_s ≈ grp_map (quot_proj A3) s3_unit → False.
Proof. intros [H]; simpl in H; discriminate. Qed.

(* But it does collapse the rotations, so the projection is not injective
   -- the quotient is a genuine quotient and not a relabelling of S3. *)
Theorem S3_mod_A3_collapses_rotations :
  grp_map (quot_proj A3) S3_r ≈ grp_map (quot_proj A3) s3_unit.
Proof. constructor; reflexivity. Qed.

Theorem quot_proj_A3_not_injective :
  (∀ a b : carrier S3,
     grp_map (quot_proj A3) a ≈ grp_map (quot_proj A3) b → a ≈ b) → False.
Proof.
  intro Hinj.
  pose proof (Hinj S3_r s3_unit S3_mod_A3_collapses_rotations) as E.
  discriminate E.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition S3_refl_sub : Subgroup S3 := {|
  sub_mem := fun a : carrier S3 => fst a = rot0
|}.
Next Obligation. intros a b Hab Ha; simpl in *; now subst. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  intros [i b] [j c] Hb Hc; simpl in *; subst; now destruct b.
Qed.
Next Obligation. intros [i b] Hb; simpl in *; subst; now destruct b. Qed.

Theorem S3_refl_sub_not_normal :
  (∀ t a : carrier S3, sub_mem S3_refl_sub a →
     sub_mem S3_refl_sub (grp_mul S3 (grp_mul S3 t a) (grp_inv S3 t)))
  → False.
Proof.
  intro Hn.
  pose proof (Hn S3_r S3_s (eq_refl : fst S3_s = rot0)) as E.
  simpl in E.
  discriminate E.
Qed.
