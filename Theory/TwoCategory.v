Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Metacategory.General.

Generalizable All Variables.

(** * 严格 2-范畴（Mac Lane 的两种呈现） *)

(* nLab:      https://ncatlab.org/nlab/show/strict+2-category
   nLab:      https://ncatlab.org/nlab/show/2-category

   严格 2-范畴有 0-胞、1-胞与 2-胞，垂直与水平复合严格结合且有单位，并服从交换律
   (interchange)。与弱 2-范畴/双范畴（Theory/Bicategory.v）相对，严格性使重括号与单位调整
   在表面上为恒等。本文件给出严格 2-范畴类与交换律；长历史短文后续可续译。 *)

(*
   nLab:  https://ncatlab.org/nlab/show/2-category
   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   Paper: Bénabou, "Introduction to bicategories", Lecture Notes in
   Paper: Kelly, Street, "Review of the elements of 2-categories", Lecture

   本节说明自然变换、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Class TwoCategory : Type := {
  (* 0-cells and 1-cells, as an ordinary category. *)
  tcat : Category;

  (* 2-cells, indexed by a PARALLEL pair of 1-cells (the globular shape). *)
  tcell {a b : tcat} (f g : a ~{tcat}~> b) : Type;
  tcell_setoid {a b : tcat} {f g : a ~{tcat}~> b} : Setoid (tcell f g);

  (* Vertical composition, making each hom into a category ([thom]). *)
  tid2 {a b : tcat} (f : a ~{tcat}~> b) : tcell f f;

  tvcomp {a b : tcat} {f g h : a ~{tcat}~> b} :
    tcell g h → tcell f g → tcell f h;

  tvcomp_respects {a b : tcat} {f g h : a ~{tcat}~> b} :
    Proper (equiv ==> equiv ==> equiv) (@tvcomp a b f g h);

  tvid_left {a b : tcat} {f g : a ~{tcat}~> b} (α : tcell f g) :
    tvcomp (tid2 g) α ≈ α;

  tvid_right {a b : tcat} {f g : a ~{tcat}~> b} (α : tcell f g) :
    tvcomp α (tid2 f) ≈ α;

  tvassoc {a b : tcat} {f g h k : a ~{tcat}~> b}
    (γ : tcell h k) (β : tcell g h) (α : tcell f g) :
    tvcomp γ (tvcomp β α) ≈ tvcomp (tvcomp γ β) α;

  (* Horizontal 复合, lying over 复合 1-cells. The outer
 factor comes first, matching order `∘`. （已译） *)
  thcomp {a b c : tcat} {f f' : a ~{tcat}~> b} {g g' : b ~{tcat}~> c} :
    tcell g g' → tcell f f' → tcell (g ∘ f) (g' ∘ f');

  thcomp_respects {a b c : tcat} {f f' : a ~{tcat}~> b}
    {g g' : b ~{tcat}~> c} :
    Proper (equiv ==> equiv ==> equiv) (@thcomp a b c f f' g g');

  (* Mac Lane's `1_{g f} = 1_g ∘ 1_f`: horizontal composition preserves the
     vertical identities. *)
  thcomp_id {a b c : tcat} (f : a ~{tcat}~> b) (g : b ~{tcat}~> c) :
    thcomp (tid2 g) (tid2 f) ≈ tid2 (g ∘ f);

  (* The interchange law, Mac Lane §II.5 display (5). *)
  tinterchange {a b c : tcat} {f f' f'' : a ~{tcat}~> b}
    {g g' g'' : b ~{tcat}~> c}
    (δ : tcell g' g'') (γ : tcell g g') (β : tcell f' f'') (α : tcell f f') :
    thcomp (tvcomp δ γ) (tvcomp β α) ≈ tvcomp (thcomp δ β) (thcomp γ α);

  (*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  tassoc_cast {a b c d : tcat} {f f' : a ~{tcat}~> b}
    {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d} :
    tcell (h ∘ (g ∘ f)) (h' ∘ (g' ∘ f')) →
    tcell ((h ∘ g) ∘ f) ((h' ∘ g') ∘ f');

  tunitl_cast {a b : tcat} {f f' : a ~{tcat}~> b} :
    tcell (id ∘ f) (id ∘ f') → tcell f f';

  tunitr_cast {a b : tcat} {f f' : a ~{tcat}~> b} :
    tcell (f ∘ id) (f' ∘ id) → tcell f f';

  tassoc_cast_respects {a b c d : tcat} {f f' : a ~{tcat}~> b}
    {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d} :
    Proper (equiv ==> equiv) (@tassoc_cast a b c d f f' g g' h h');

  tunitl_cast_respects {a b : tcat} {f f' : a ~{tcat}~> b} :
    Proper (equiv ==> equiv) (@tunitl_cast a b f f');

  tunitr_cast_respects {a b : tcat} {f f' : a ~{tcat}~> b} :
    Proper (equiv ==> equiv) (@tunitr_cast a b f f');

  tassoc_cast_vcomp {a b c d : tcat} {f f' f'' : a ~{tcat}~> b}
    {g g' g'' : b ~{tcat}~> c} {h h' h'' : c ~{tcat}~> d}
    (β : tcell (h' ∘ (g' ∘ f')) (h'' ∘ (g'' ∘ f'')))
    (α : tcell (h ∘ (g ∘ f)) (h' ∘ (g' ∘ f'))) :
    tassoc_cast (tvcomp β α) ≈ tvcomp (tassoc_cast β) (tassoc_cast α);

  tunitl_cast_vcomp {a b : tcat} {f f' f'' : a ~{tcat}~> b}
    (β : tcell (id ∘ f') (id ∘ f'')) (α : tcell (id ∘ f) (id ∘ f')) :
    tunitl_cast (tvcomp β α) ≈ tvcomp (tunitl_cast β) (tunitl_cast α);

  tunitr_cast_vcomp {a b : tcat} {f f' f'' : a ~{tcat}~> b}
    (β : tcell (f' ∘ id) (f'' ∘ id)) (α : tcell (f ∘ id) (f' ∘ id)) :
    tunitr_cast (tvcomp β α) ≈ tvcomp (tunitr_cast β) (tunitr_cast α);

  (* Horizontal 复合 associative unital ON THE NOSE, modulo
 boundary identifications. （已译） *)
  thassoc {a b c d : tcat} {f f' : a ~{tcat}~> b} {g g' : b ~{tcat}~> c}
    {h h' : c ~{tcat}~> d}
    (γ : tcell h h') (β : tcell g g') (α : tcell f f') :
    tassoc_cast (thcomp γ (thcomp β α)) ≈ thcomp (thcomp γ β) α;

  thunit_left {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
    tunitl_cast (thcomp (tid2 (@id tcat b)) α) ≈ α;

  thunit_right {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
    tunitr_cast (thcomp α (tid2 (@id tcat a))) ≈ α
}.

#[export] Existing Instance tcell_setoid.
#[export] Existing Instance tvcomp_respects.
#[export] Existing Instance thcomp_respects.
#[export] Existing Instance tassoc_cast_respects.
#[export] Existing Instance tunitl_cast_respects.
#[export] Existing Instance tunitr_cast_respects.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition thom `{K : TwoCategory} (a b : @tcat K) : Category := {|
  obj              := a ~{tcat}~> b;
  hom              := @tcell K a b;
  homset           := @tcell_setoid K a b;
  id               := @tid2 K a b;
  compose          := @tvcomp K a b;
  compose_respects := @tvcomp_respects K a b;
  id_left          := @tvid_left K a b;
  id_right         := @tvid_right K a b;
  comp_assoc       := @tvassoc K a b;
  comp_assoc_sym   := fun f g h k γ β α =>
    symmetry (@tvassoc K a b f g h k γ β α)
|}.

Section TwoCategoryLemmas.

Context {K : TwoCategory}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition twhisker_l {a b c : tcat} (g : b ~{tcat}~> c)
  {f f' : a ~{tcat}~> b} (α : tcell f f') : tcell (g ∘ f) (g ∘ f') :=
  thcomp (tid2 g) α.

Definition twhisker_r {a b c : tcat} {g g' : b ~{tcat}~> c}
  (β : tcell g g') (f : a ~{tcat}~> b) : tcell (g ∘ f) (g' ∘ f) :=
  thcomp β (tid2 f).

#[local] Instance twhisker_l_respects {a b c : tcat} (g : b ~{tcat}~> c)
  (f f' : a ~{tcat}~> b) :
  Proper (equiv ==> equiv) (@twhisker_l a b c g f f').
Proof.
  proper.
  unfold twhisker_l.
  now apply thcomp_respects.
Qed.

#[local] Instance twhisker_r_respects {a b c : tcat}
  (g g' : b ~{tcat}~> c) (f : a ~{tcat}~> b) :
  Proper (equiv ==> equiv) (fun β => @twhisker_r a b c g g' β f).
Proof.
  proper.
  unfold twhisker_r.
  now apply thcomp_respects.
Qed.

(* Whiskering 恒等 1-cell (after boundary identification)
 cell itself: two unit laws restated whiskering form. （已译） *)
Lemma twhisker_l_id {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tunitl_cast (twhisker_l (@id tcat b) α) ≈ α.
Proof. apply thunit_left. Qed.

Lemma twhisker_r_id {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tunitr_cast (twhisker_r α (@id tcat a)) ≈ α.
Proof. apply thunit_right. Qed.

(* Whiskering preserves identities vertical composites: each whiskering
 函子 between hom-范畴, Mac Lane's remark that
 `S' ∘ (-)` `(-) ∘ T` functorial. （已译） *)
Lemma twhisker_l_ident {a b c : tcat} (g : b ~{tcat}~> c)
  (f : a ~{tcat}~> b) : twhisker_l g (tid2 f) ≈ tid2 (g ∘ f).
Proof. apply thcomp_id. Qed.

Lemma twhisker_r_ident {a b c : tcat} (g : b ~{tcat}~> c)
  (f : a ~{tcat}~> b) : twhisker_r (tid2 g) f ≈ tid2 (g ∘ f).
Proof. apply thcomp_id. Qed.

Lemma twhisker_l_vcomp {a b c : tcat} (g : b ~{tcat}~> c)
  {f f' f'' : a ~{tcat}~> b} (β : tcell f' f'') (α : tcell f f') :
  twhisker_l g (tvcomp β α) ≈ tvcomp (twhisker_l g β) (twhisker_l g α).
Proof.
  unfold twhisker_l.
  rewrite <- tinterchange.
  apply thcomp_respects; [| reflexivity ].
  now rewrite tvid_left.
Qed.

Lemma twhisker_r_vcomp {a b c : tcat} {g g' g'' : b ~{tcat}~> c}
  (δ : tcell g' g'') (γ : tcell g g') (f : a ~{tcat}~> b) :
  twhisker_r (tvcomp δ γ) f ≈ tvcomp (twhisker_r δ f) (twhisker_r γ f).
Proof.
  unfold twhisker_r.
  rewrite <- tinterchange.
  apply thcomp_respects; [ reflexivity |].
  now rewrite tvid_left.
Qed.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma thcomp_whisker_left {a b c : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} (β : tcell g g') (α : tcell f f') :
  thcomp β α ≈ tvcomp (twhisker_r β f') (twhisker_l g α).
Proof.
  unfold twhisker_l, twhisker_r.
  rewrite <- tinterchange.
  apply thcomp_respects.
  - now rewrite tvid_right.
  - now rewrite tvid_left.
Qed.

Lemma thcomp_whisker_right {a b c : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} (β : tcell g g') (α : tcell f f') :
  thcomp β α ≈ tvcomp (twhisker_l g' α) (twhisker_r β f).
Proof.
  unfold twhisker_l, twhisker_r.
  rewrite <- tinterchange.
  apply thcomp_respects.
  - now rewrite tvid_left.
  - now rewrite tvid_right.
Qed.

(* Consequently two factorisations agree: Godement square commutes,
 Mac Lane's remark horizontal 复合 diagonal
 交换方块. （已译） *)
Corollary tgodement_square {a b c : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} (β : tcell g g') (α : tcell f f') :
  tvcomp (twhisker_r β f') (twhisker_l g α)
    ≈ tvcomp (twhisker_l g' α) (twhisker_r β f).
Proof.
  rewrite <- thcomp_whisker_left.
  apply thcomp_whisker_right.
Qed.

(* 相关说明。 （已译） *)

Lemma tassoc_cast_id {a b c d : tcat} (f : a ~{tcat}~> b)
  (g : b ~{tcat}~> c) (h : c ~{tcat}~> d) :
  tassoc_cast (tid2 (h ∘ (g ∘ f))) ≈ tid2 ((h ∘ g) ∘ f).
Proof.
  rewrite <- (thcomp_id (g ∘ f) h).
  rewrite <- (thcomp_id f g).
  rewrite thassoc.
  now rewrite thcomp_id, thcomp_id.
Qed.

Lemma tunitl_cast_id {a b : tcat} (f : a ~{tcat}~> b) :
  tunitl_cast (tid2 (@id tcat b ∘ f)) ≈ tid2 f.
Proof.
  rewrite <- (thcomp_id f (@id tcat b)).
  apply thunit_left.
Qed.

Lemma tunitr_cast_id {a b : tcat} (f : a ~{tcat}~> b) :
  tunitr_cast (tid2 (f ∘ @id tcat a)) ≈ tid2 f.
Proof.
  rewrite <- (thcomp_id (@id tcat a) f).
  apply thunit_right.
Qed.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition IsVUnit {a b : tcat} {f : a ~{tcat}~> b} (u : tcell f f) : Type :=
  (∀ (g : a ~{tcat}~> b) (α : tcell f g), tvcomp α u ≈ α) ∧
  (∀ (g : a ~{tcat}~> b) (α : tcell g f), tvcomp u α ≈ α).

Definition IsHUnit {a : tcat} (u : tcell (@id tcat a) (@id tcat a)) : Type :=
  (∀ (b : tcat) (f f' : a ~{tcat}~> b) (α : tcell f f'),
     tunitr_cast (thcomp α u) ≈ α) ∧
  (∀ (b : tcat) (f f' : b ~{tcat}~> a) (α : tcell f f'),
     tunitl_cast (thcomp u α) ≈ α).

(* Mac Lane §II.5 Theorem 1's closing clause, condition his def 3
 abstracts it: 恒等 2-cell 恒等 1-cell unit
 BOTH compositions. （已译） *)
Theorem twocategory_def3 (a : tcat) :
  IsVUnit (tid2 (@id tcat a)) ∧ IsHUnit (tid2 (@id tcat a)).
Proof.
  split.
  - split; intros g α.
    + apply tvid_right.
    + apply tvid_left.
  - split; intros b f f' α.
    + apply thunit_right.
    + apply thunit_left.
Qed.

(* 相关说明。 （已译） *)
Theorem twocategory_tid2_vunit {a b : tcat} (f : a ~{tcat}~> b) :
  IsVUnit (tid2 f).
Proof.
  split; intros g α.
  - apply tvid_right.
  - apply tvid_left.
Qed.

End TwoCategoryLemmas.

Arguments IsVUnit {_ _ _ _} _.
Arguments IsHUnit {_ _} _.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record MetaComp {A : Type} (S : Setoid A) : Type := {
  (* [mccomp g f h] reads "g∙f is defined, and equals h". *)
  mccomp : A → A → A → Type;

  mcdefined (g f : A) := ∃ h, mccomp g f h;

  mccomp_respects {g g' f f' h h'} :
    @equiv _ S g g' → @equiv _ S f f' → @equiv _ S h h' →
    mccomp g f h → mccomp g' f' h';

  mccomp_unique {g f h h'} :
    mccomp g f h → mccomp g f h' → @equiv _ S h h';

  mccomp_assoc_l {k g f kg kgf} :
    mccomp k g kg → mccomp kg f kgf → ∃ gf, mccomp g f gf ∧ mccomp k gf kgf;

  mccomp_assoc_r {k g f gf kgf} :
    mccomp g f gf → mccomp k gf kgf → ∃ kg, mccomp k g kg ∧ mccomp kg f kgf;

  mccomp_match {k g f kg gf} :
    mccomp k g kg → mccomp g f gf → ∃ kgf, mccomp kg f kgf;

  mcident (u : A) :=
    (∀ f, mcdefined f u → mccomp f u f) ∧
    (∀ g, mcdefined u g → mccomp u g g);

  mcident_law (g : A) :
    ∃ u u', (mcident u ∧ mcident u') ∧ (mcdefined g u ∧ mcdefined u' g)
}.

Arguments mccomp {A S} _ _ _ _.
Arguments mcdefined {A S} _ _ _ /.
Arguments mccomp_respects {A S} _ {g g' f f' h h'} _ _ _ _.
Arguments mccomp_unique {A S} _ {g f h h'} _ _.
Arguments mccomp_assoc_l {A S} _ {k g f kg kgf} _ _.
Arguments mccomp_assoc_r {A S} _ {k g f gf kgf} _ _.
Arguments mccomp_match {A S} _ {k g f kg gf} _ _.
Arguments mcident {A S} _ _ /.
Arguments mcident_law {A S} _ _.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Metacategory_of_MetaComp {A : Type} {S : Setoid A}
  (M : MetaComp S) : Metacategory := {|
  marr             := A;
  marr_setoid      := S;
  mcomp            := mccomp M;
  mcomp_respects   := @mccomp_respects _ _ M;
  mcomp_unique     := @mccomp_unique _ _ M;
  mcomp_assoc_l    := @mccomp_assoc_l _ _ M;
  mcomp_assoc_r    := @mccomp_assoc_r _ _ M;
  mcomp_match      := @mccomp_match _ _ M;
  mident_law       := @mcident_law _ _ M
|}.

Definition MetaComp_of_Metacategory (M : Metacategory) :
  MetaComp (marr_setoid M) := {|
  mccomp            := mcomp M;
  mccomp_respects   := @mcomp_respects M;
  mccomp_unique     := @mcomp_unique M;
  mccomp_assoc_l    := @mcomp_assoc_l M;
  mccomp_assoc_r    := @mcomp_assoc_r M;
  mccomp_match      := @mcomp_match M;
  mcident_law       := @mident_law M
|}.

(* * *** Definition 2: double 范畴 （已译） *)

Record StrictDoubleCategory : Type := {
  (* "a set set arrows two different 复合
 operations" — here setoid cells, since every collection this
 library carries own equality. （已译） *)
  dcell : Type;
  dcell_setoid : Setoid dcell;

  dvert  : MetaComp dcell_setoid;       (* the first composition,  `·` *)
  dhoriz : MetaComp dcell_setoid;       (* the second composition, `∘` *)

  (*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  dinterchange {σ τ σ' τ' p q r s x y : dcell} :
    mccomp dvert τ σ p →                (* p = τ · σ *)
    mccomp dvert τ' σ' q →              (* q = τ' · σ' *)
    mccomp dhoriz q p x →               (* x = (τ' · σ') ∘ (τ · σ) *)
    mccomp dhoriz τ' τ r →              (* r = τ' ∘ τ *)
    mccomp dhoriz σ' σ s →              (* s = σ' ∘ σ *)
    mccomp dvert r s y →                (* y = (τ' ∘ τ) · (σ' ∘ σ) *)
    @equiv _ dcell_setoid x y
}.

#[export] Existing Instance dcell_setoid.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dvert_Meta (D : StrictDoubleCategory) : Metacategory :=
  Metacategory_of_MetaComp (dvert D).

Definition dhoriz_Meta (D : StrictDoubleCategory) : Metacategory :=
  Metacategory_of_MetaComp (dhoriz D).

Definition dvert_Category (D : StrictDoubleCategory) : Category :=
  Category_from_Metacategory (dvert_Meta D).

Definition dhoriz_Category (D : StrictDoubleCategory) : Category :=
  Category_from_Metacategory (dhoriz_Meta D).

(* The two 恒等 predicates, Mac Lane's sense arrow a
 unit 复合 wherever 复合 defined. （已译） *)

Definition dvident (D : StrictDoubleCategory) (u : dcell D) : Type :=
  mcident (dvert D) u.

Definition dhident (D : StrictDoubleCategory) (u : dcell D) : Type :=
  mcident (dhoriz D) u.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record StrictTwoCategory : Type := {
  s2double : StrictDoubleCategory;

  s2ident_coincide : ∀ u : dcell s2double,
    dhident s2double u → dvident s2double u
}.

Require Import Coq.micromega.Lia.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record NatSq : Type := {
  nsq_top   : nat;
  nsq_left  : nat;
  nsq_right : nat;
  nsq_bot   : nat;
  nsq_comm  : (nsq_bot + nsq_left = nsq_right + nsq_top)%nat
}.

Definition mkNatSq (t l r b : nat) (H : (b + l = r + t)%nat) : NatSq :=
  {| nsq_top   := t;
     nsq_left  := l;
     nsq_right := r;
     nsq_bot   := b;
     nsq_comm  := H |}.

(* Two squares same four edges are; commuting 证明
 carries no information beyond them. （已译） *)
Definition NatSq_eq (x y : NatSq) : Type :=
  (nsq_top x = nsq_top y) ∧ (nsq_left x = nsq_left y) ∧
  (nsq_right x = nsq_right y) ∧ (nsq_bot x = nsq_bot y).

Program Definition NatSq_Setoid : Setoid NatSq := {|
  equiv := NatSq_eq
|}.
Next Obligation.
  constructor.
  - intros x; now repeat split.
  - intros x y [? [? [? ?]]]; now repeat split.
  - intros x y z [? [? [? ?]]] [? [? [? ?]]]; repeat split;
      etransitivity; eassumption.
Qed.

(* Vertical pasting: [f] on top, [g] below, matching along [f]'s bottom. *)
Definition NatSq_vcomp (g f h : NatSq) : Type :=
  (nsq_top g = nsq_bot f) ∧
  (nsq_top h = nsq_top f) ∧
  (nsq_bot h = nsq_bot g) ∧
  (nsq_left h = (nsq_left g + nsq_left f)%nat) ∧
  (nsq_right h = (nsq_right g + nsq_right f)%nat).

(* 相关说明。 （已译） *)
Definition NatSq_hcomp (g f h : NatSq) : Type :=
  (nsq_left g = nsq_right f) ∧
  (nsq_left h = nsq_left f) ∧
  (nsq_right h = nsq_right g) ∧
  (nsq_top h = (nsq_top g + nsq_top f)%nat) ∧
  (nsq_bot h = (nsq_bot g + nsq_bot f)%nat).

Definition NatSq_vdefined (g f : NatSq) : Type := ∃ h, NatSq_vcomp g f h.
Definition NatSq_hdefined (g f : NatSq) : Type := ∃ h, NatSq_hcomp g f h.

Definition NatSq_vident (u : NatSq) : Type :=
  (∀ f, NatSq_vdefined f u → NatSq_vcomp f u f) ∧
  (∀ g, NatSq_vdefined u g → NatSq_vcomp u g g).

Definition NatSq_hident (u : NatSq) : Type :=
  (∀ f, NatSq_hdefined f u → NatSq_hcomp f u f) ∧
  (∀ g, NatSq_hdefined u g → NatSq_hcomp u g g).

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Ltac nsq_hyps :=
  simpl in *;
  repeat match goal with
  | [ H : NatSq_vcomp _ _ _  |- _ ] => destruct H as [? [? [? [? ?]]]]
  | [ H : NatSq_hcomp _ _ _  |- _ ] => destruct H as [? [? [? [? ?]]]]
  | [ H : NatSq_eq _ _       |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : NatSq_vdefined _ _ |- _ ] => destruct H as [? ?]
  | [ H : NatSq_hdefined _ _ |- _ ] => destruct H as [? ?]
  end; simpl in *.

(* 相关说明。 （已译） *)

Lemma NatSq_vpaste_comm (g f : NatSq) (Hm : nsq_top g = nsq_bot f) :
  (nsq_bot g + (nsq_left g + nsq_left f)
     = (nsq_right g + nsq_right f) + nsq_top f)%nat.
Proof.
  pose proof (nsq_comm f); pose proof (nsq_comm g); lia.
Qed.

Definition NatSq_vpaste (g f : NatSq) (Hm : nsq_top g = nsq_bot f) : NatSq :=
  mkNatSq (nsq_top f) (nsq_left g + nsq_left f)
          (nsq_right g + nsq_right f) (nsq_bot g)
          (NatSq_vpaste_comm g f Hm).

Lemma NatSq_hpaste_comm (g f : NatSq) (Hm : nsq_left g = nsq_right f) :
  ((nsq_bot g + nsq_bot f) + nsq_left f
     = nsq_right g + (nsq_top g + nsq_top f))%nat.
Proof.
  pose proof (nsq_comm f); pose proof (nsq_comm g); lia.
Qed.

Definition NatSq_hpaste (g f : NatSq) (Hm : nsq_left g = nsq_right f)
  : NatSq :=
  mkNatSq (nsq_top g + nsq_top f) (nsq_left f)
          (nsq_right g) (nsq_bot g + nsq_bot f)
          (NatSq_hpaste_comm g f Hm).

Lemma NatSq_vcomp_total (g f : NatSq) (Hm : nsq_top g = nsq_bot f) :
  NatSq_vdefined g f.
Proof. exists (NatSq_vpaste g f Hm); now repeat split. Qed.

Lemma NatSq_hcomp_total (g f : NatSq) (Hm : nsq_left g = nsq_right f) :
  NatSq_hdefined g f.
Proof. exists (NatSq_hpaste g f Hm); now repeat split. Qed.

(* The identity squares of each direction: a vertical identity has trivial
   vertical edges, a horizontal identity trivial horizontal edges. *)

Lemma NatSq_vid_comm (t : nat) : (t + 0 = 0 + t)%nat.
Proof. lia. Qed.

Definition NatSq_vid (t : nat) : NatSq := mkNatSq t 0 0 t (NatSq_vid_comm t).

Lemma NatSq_hid_comm (c : nat) : (0 + c = c + 0)%nat.
Proof. lia. Qed.

Definition NatSq_hid (c : nat) : NatSq := mkNatSq 0 c c 0 (NatSq_hid_comm c).

Lemma NatSq_vid_ident (t : nat) : NatSq_vident (NatSq_vid t).
Proof.
  split; intros f Hd; nsq_hyps; repeat split; simpl; lia.
Qed.

Lemma NatSq_hid_ident (c : nat) : NatSq_hident (NatSq_hid c).
Proof.
  split; intros f Hd; nsq_hyps; repeat split; simpl; lia.
Qed.

(* 相关说明。 （已译） *)

Program Definition NatSq_Vert : MetaComp NatSq_Setoid := {|
  mccomp := NatSq_vcomp
|}.
Next Obligation.                        (* respects *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* single-valued *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* axiom (i), left to right *)
  nsq_hyps.
  assert (Hm : nsq_top g = nsq_bot f) by lia.
  exists (NatSq_vpaste g f Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (i), right to left *)
  nsq_hyps.
  assert (Hm : nsq_top k = nsq_bot g) by lia.
  exists (NatSq_vpaste k g Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (ii) *)
  nsq_hyps.
  apply NatSq_vcomp_total; lia.
Qed.
Next Obligation.                        (* axiom (iii) *)
  exists (NatSq_vid (nsq_top g)), (NatSq_vid (nsq_bot g)).
  split; split.
  - apply NatSq_vid_ident.
  - apply NatSq_vid_ident.
  - apply NatSq_vcomp_total; now simpl.
  - apply NatSq_vcomp_total; now simpl.
Qed.

Program Definition NatSq_Horiz : MetaComp NatSq_Setoid := {|
  mccomp := NatSq_hcomp
|}.
Next Obligation.                        (* respects *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* single-valued *)
  nsq_hyps; repeat split; lia.
Qed.
Next Obligation.                        (* axiom (i), left to right *)
  nsq_hyps.
  assert (Hm : nsq_left g = nsq_right f) by lia.
  exists (NatSq_hpaste g f Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (i), right to left *)
  nsq_hyps.
  assert (Hm : nsq_left k = nsq_right g) by lia.
  exists (NatSq_hpaste k g Hm).
  repeat split; simpl; lia.
Qed.
Next Obligation.                        (* axiom (ii) *)
  nsq_hyps.
  apply NatSq_hcomp_total; lia.
Qed.
Next Obligation.                        (* axiom (iii) *)
  exists (NatSq_hid (nsq_left g)), (NatSq_hid (nsq_right g)).
  split; split.
  - apply NatSq_hid_ident.
  - apply NatSq_hid_ident.
  - apply NatSq_hcomp_total; now simpl.
  - apply NatSq_hcomp_total; now simpl.
Qed.

(* * *** The double 范畴, refutation 定义 3 （已译） *)

Program Definition NatSq_Double : StrictDoubleCategory := {|
  dcell        := NatSq;
  dcell_setoid := NatSq_Setoid;
  dvert        := NatSq_Vert;
  dhoriz       := NatSq_Horiz
|}.
Next Obligation.                        (* the interchange law *)
  nsq_hyps; repeat split; lia.
Qed.

(* The offending cell: horizontal 恒等 vertical arrow 1. （已译） *)
Definition NatSq_bad : NatSq := NatSq_hid 1.

Lemma NatSq_bad_hident : dhident NatSq_Double NatSq_bad.
Proof. apply NatSq_hid_ident. Qed.

Lemma NatSq_bad_not_vident : dvident NatSq_Double NatSq_bad → False.
Proof.
  intros [Hsrc _].
  (* Pasting cell under itself defined, vertical edges being
 composable; were cell vertical 恒等, pasting would
 return it unchanged, forcing 1 = 1 + 1. （已译） *)
  assert (Hd : NatSq_vdefined NatSq_bad NatSq_bad)
    by (apply NatSq_vcomp_total; now simpl).
  destruct (Hsrc NatSq_bad Hd) as [? [? [? [Hl ?]]]].
  simpl in Hl.
  discriminate.
Qed.

(* Mac Lane §II.5: the double category of commuting squares is not a
   2-category.  There is no way to equip [NatSq_Double] with a
   [StrictTwoCategory] structure, its def-3 condition being refutable. *)
Theorem NatSq_not_a_two_category :
  (∀ u : dcell NatSq_Double, dhident NatSq_Double u → dvident NatSq_Double u)
    → False.
Proof.
  intro H.
  exact (NatSq_bad_not_vident (H NatSq_bad NatSq_bad_hident)).
Qed.

Corollary NatSq_no_StrictTwoCategory
  (S : StrictTwoCategory) (H : s2double S = NatSq_Double) : False.
Proof.
  apply NatSq_not_a_two_category.
  rewrite <- H.
  apply s2ident_coincide.
Qed.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example NatSq_vid_is_not_hid (t : nat) :
  NatSq_hident (NatSq_vid (S t)) → False.
Proof.
  intros [Hsrc _].
  assert (Hd : NatSq_hdefined (NatSq_vid (S t)) (NatSq_vid (S t)))
    by (apply NatSq_hcomp_total; now simpl).
  destruct (Hsrc _ Hd) as [? [? [? [Ht ?]]]].
  simpl in Ht.
  lia.
Qed.

Example NatSq_vpaste_computes :
  nsq_left (NatSq_vpaste NatSq_bad NatSq_bad eq_refl) = 2%nat := eq_refl.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

From Coq Require Import Eqdep_dec.

Section ToStrict.

Context {K : TwoCategory}.

(* Transporting a 1-cell along an equality of its source or target, and a
   2-cell along either of those or along an equality of its own boundary
   1-cells.  Each is [ToArrows]'s [tsrc]/[ttgt] one dimension up. *)

Definition tr1_src {x y : tcat} (f : x ~{tcat}~> y) {x'} (p : x = x')
  : x' ~{tcat}~> y := eq_rect x (fun s => s ~{tcat}~> y) f x' p.

Definition tr1_tgt {x y : tcat} (f : x ~{tcat}~> y) {y'} (q : y = y')
  : x ~{tcat}~> y' := eq_rect y (fun t => x ~{tcat}~> t) f y' q.

Definition tr2_src {x y : tcat} {f g : x ~{tcat}~> y} {x'} (p : x = x')
  (α : tcell f g) : tcell (tr1_src f p) (tr1_src g p).
Proof. destruct p; exact α. Defined.

Definition tr2_tgt {x y : tcat} {f g : x ~{tcat}~> y} {y'} (q : y = y')
  (α : tcell f g) : tcell (tr1_tgt f q) (tr1_tgt g q).
Proof. destruct q; exact α. Defined.

Definition tr2_cast {x y : tcat} {f f' g g' : x ~{tcat}~> y}
  (ed : f = f') (ec : g = g') (α : tcell f g) : tcell f' g'.
Proof. destruct ed, ec; exact α. Defined.

Lemma tr2_cast_sym {x y : tcat} {f f' g g' : x ~{tcat}~> y}
  (ed : f = f') (ec : g = g') (α : tcell f g) :
  tr2_cast (eq_sym ed) (eq_sym ec) (tr2_cast ed ec α) = α.
Proof using Type. destruct ed, ec; reflexivity. Qed.

Lemma tr2_cast_respects {x y : tcat} {f f' g g' : x ~{tcat}~> y}
  (ed : f = f') (ec : g = g') (α β : tcell f g) :
  α ≈ β → tr2_cast ed ec α ≈ tr2_cast ed ec β.
Proof using Type. destruct ed, ec; intro H; exact H. Qed.

(* 相关说明。 （已译） *)
Record TwoArr : Type := {
  t0src : tcat;
  t0tgt : tcat;
  t1dom : t0src ~{tcat}~> t0tgt;
  t1cod : t0src ~{tcat}~> t0tgt;
  t2cell : tcell t1dom t1cod
}.

Definition TwoArr_at {x y : tcat} {f g : x ~{tcat}~> y} (α : tcell f g)
  : TwoArr :=
  {| t0src := x; t0tgt := y; t1dom := f; t1cod := g; t2cell := α |}.

Definition TwoArr_eq (a b : TwoArr) : Type :=
  ∃ (p : t0src a = t0src b) (q : t0tgt a = t0tgt b)
    (ed : tr1_tgt (tr1_src (t1dom a) p) q = t1dom b)
    (ec : tr1_tgt (tr1_src (t1cod a) p) q = t1cod b),
    tr2_cast ed ec (tr2_tgt q (tr2_src p (t2cell a))) ≈ t2cell b.

(* The 假设 pack; see discussion above. （已译） *)
Record StrictBase : Type := {
  sb_obj_uip : ∀ (x y : @tcat K) (p q : x = y), p = q;
  sb_hom_uip : ∀ (a b : @tcat K) (f g : a ~{tcat}~> b) (p q : f = g), p = q;

  sb_id_left : ∀ {a b : @tcat K} (f : a ~{tcat}~> b), @id tcat b ∘ f = f;
  sb_id_right : ∀ {a b : @tcat K} (f : a ~{tcat}~> b), f ∘ @id tcat a = f;
  sb_assoc : ∀ {a b c d : @tcat K} (h : c ~{tcat}~> d) (g : b ~{tcat}~> c)
               (f : a ~{tcat}~> b), h ∘ (g ∘ f) = (h ∘ g) ∘ f;

  sb_assoc_cast : ∀ {a b c d : @tcat K} {f f' : a ~{tcat}~> b}
                    {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d}
                    (s : tcell (h ∘ (g ∘ f)) (h' ∘ (g' ∘ f'))),
    tassoc_cast s ≈ tr2_cast (sb_assoc h g f) (sb_assoc h' g' f') s;

  sb_unitl_cast : ∀ {a b : @tcat K} {f f' : a ~{tcat}~> b}
                    (s : tcell (@id tcat b ∘ f) (@id tcat b ∘ f')),
    tunitl_cast s ≈ tr2_cast (sb_id_left f) (sb_id_left f') s;

  sb_unitr_cast : ∀ {a b : @tcat K} {f f' : a ~{tcat}~> b}
                    (s : tcell (f ∘ @id tcat a) (f' ∘ @id tcat a)),
    tunitr_cast s ≈ tr2_cast (sb_id_right f) (sb_id_right f') s
}.

Context (SB : StrictBase).

Definition TwoV (a b c : TwoArr) : Type :=
  ∃ (p : t0src b = t0src a) (q : t0tgt b = t0tgt a)
    (e : tr1_tgt (tr1_src (t1cod b) p) q = t1dom a),
    TwoArr_eq (TwoArr_at (tvcomp (t2cell a)
              (tr2_cast eq_refl e (tr2_tgt q (tr2_src p (t2cell b)))))) c.

Definition TwoH (a b c : TwoArr) : Type :=
  ∃ (p : t0tgt b = t0src a),
    TwoArr_eq (TwoArr_at (thcomp (t2cell a) (tr2_tgt p (t2cell b)))) c.

Definition TwoV_defined (a b : TwoArr) : Type := ∃ c, TwoV a b c.
Definition TwoH_defined (a b : TwoArr) : Type := ∃ c, TwoH a b c.

Definition TwoV_ident (u : TwoArr) : Type :=
  (∀ f, TwoV_defined f u → TwoV f u f) ∧ (∀ g, TwoV_defined u g → TwoV u g g).

Definition TwoH_ident (u : TwoArr) : Type :=
  (∀ f, TwoH_defined f u → TwoH f u f) ∧ (∀ g, TwoH_defined u g → TwoH u g g).

Ltac twoarr_crush :=
  repeat (match goal with
  | [ a : TwoArr |- _ ] => destruct a
  | [ H : TwoV_defined _ _ |- _ ] => destruct H as [? ?]
  | [ H : TwoH_defined _ _ |- _ ] => destruct H as [? ?]
  | [ H : TwoV _ _ _ |- _ ] => destruct H as [? [? [? ?]]]
  | [ H : TwoH _ _ _ |- _ ] => destruct H as [? ?]
  | [ H : TwoArr_eq _ _ |- _ ] => destruct H as [? [? [? [? ?]]]]
  | [ p : @eq (@obj (@tcat K)) ?x ?x |- _ ] =>
    let H := fresh "Huip" in
    assert (H : p = eq_refl) by apply (sb_obj_uip SB); subst p
  | [ p : @eq (@obj (@tcat K)) _ _ |- _ ] => destruct p
  | [ p : @eq (@hom (@tcat K) ?x ?y) ?f ?f |- _ ] =>
    let H := fresh "Huip" in
    assert (H : p = eq_refl) by apply (sb_hom_uip SB); subst p
  | [ p : @eq (@hom (@tcat K) ?x ?y) _ _ |- _ ] => destruct p
  end; simpl in * ).

Lemma TwoArr_eq_equivalence : Equivalence TwoArr_eq.
Proof.
  constructor.
  - intros a; exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
  - intros a b H; twoarr_crush.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; symmetry; assumption.
  - intros a b c H1 H2; twoarr_crush.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    etransitivity; eassumption.
Qed.

Definition TwoArr_Setoid : Setoid TwoArr :=
  {| equiv := TwoArr_eq; setoid_equiv := TwoArr_eq_equivalence |}.

#[local] Existing Instance TwoArr_eq_equivalence.

Ltac twoarr_finish :=
  repeat match goal with
  | [ H : ?x ≈ ?y |- _ ] => is_var x; rewrite H in *; clear H
  end;
  solve [ assumption | reflexivity
        | (symmetry; assumption)
        | (etransitivity; eassumption)
        | (etransitivity; [ symmetry; eassumption | eassumption ])
        | (etransitivity; [ eassumption | symmetry; eassumption ])
        | (symmetry; etransitivity; eassumption)
        | (symmetry; etransitivity;
           [ symmetry; eassumption | eassumption ]) ].

Lemma TwoV_respects {a a' b b' c c'} :
  TwoArr_eq a a' → TwoArr_eq b b' → TwoArr_eq c c' →
  TwoV a b c → TwoV a' b' c'.
Proof using K.
  intros Ha Hb Hc H; twoarr_crush.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma TwoH_respects {a a' b b' c c'} :
  TwoArr_eq a a' → TwoArr_eq b b' → TwoArr_eq c c' →
  TwoH a b c → TwoH a' b' c'.
Proof using K.
  intros Ha Hb Hc H; twoarr_crush.
  exists eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma TwoV_unique {a b c c'} : TwoV a b c → TwoV a b c' → TwoArr_eq c c'.
Proof using K SB.
  intros H1 H2; twoarr_crush.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma TwoH_unique {a b c c'} : TwoH a b c → TwoH a b c' → TwoArr_eq c c'.
Proof using K SB.
  intros H1 H2; twoarr_crush.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  twoarr_finish.
Qed.

Lemma thassoc_sym {a b c d : tcat} {f f' : a ~{tcat}~> b}
  {g g' : b ~{tcat}~> c} {h h' : c ~{tcat}~> d}
  (γ : tcell h h') (β : tcell g g') (α : tcell f f') :
  tr2_cast (eq_sym (sb_assoc SB h g f)) (eq_sym (sb_assoc SB h' g' f'))
         (thcomp (thcomp γ β) α)
    ≈ thcomp γ (thcomp β α).
Proof using K SB.
  etransitivity.
  - apply tr2_cast_respects.
    etransitivity; [ symmetry; apply thassoc |].
    apply (sb_assoc_cast SB).
  - rewrite tr2_cast_sym; reflexivity.
Qed.

Lemma TwoV_assoc_l {k g f kg kgf} :
  TwoV k g kg → TwoV kg f kgf → ∃ gf, TwoV g f gf ∧ TwoV k gf kgf.
Proof using K.
  intros [p1 [q1 [e1 E1]]] [p2 [q2 [e2 E2]]].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (tvcomp _ _)); split.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    rewrite tvassoc, EE1; exact EE2.
Qed.

Lemma TwoV_assoc_r {k g f gf kgf} :
  TwoV g f gf → TwoV k gf kgf → ∃ kg, TwoV k g kg ∧ TwoV kg f kgf.
Proof using K.
  intros [p1 [q1 [e1 E1]]] [p2 [q2 [e2 E2]]].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (tvcomp _ _)); split.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    rewrite <- tvassoc, EE1; exact EE2.
Qed.

Lemma TwoV_match {k g f kg gf} :
  TwoV k g kg → TwoV g f gf → ∃ kgf, TwoV kg f kgf.
Proof using K.
  intros [p1 [q1 [e1 E1]]] [p2 [q2 [e2 E2]]].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (tvcomp _ _)).
  exists eq_refl, eq_refl, eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma TwoH_assoc_l {k g f kg kgf} :
  TwoH k g kg → TwoH kg f kgf → ∃ gf, TwoH g f gf ∧ TwoH k gf kgf.
Proof using K SB.
  intros [p1 E1] [p2 E2].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (thcomp _ _)); split.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, (sb_assoc SB _ _ _), (sb_assoc SB _ _ _); simpl.
    etransitivity; [ symmetry; apply (sb_assoc_cast SB) |].
    rewrite thassoc, EE1; exact EE2.
Qed.

Lemma TwoH_assoc_r {k g f gf kgf} :
  TwoH g f gf → TwoH k gf kgf → ∃ kg, TwoH k g kg ∧ TwoH kg f kgf.
Proof using K SB.
  intros [p1 E1] [p2 E2].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (thcomp _ _)); split.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - exists eq_refl; simpl.
    exists eq_refl, eq_refl, (eq_sym (sb_assoc SB _ _ _)),
           (eq_sym (sb_assoc SB _ _ _)); simpl.
    rewrite thassoc_sym, EE1; exact EE2.
Qed.

Lemma TwoH_match {k g f kg gf} :
  TwoH k g kg → TwoH g f gf → ∃ kgf, TwoH kg f kgf.
Proof using K.
  intros [p1 E1] [p2 E2].
  destruct E1 as [r1 [s1 [d1 [c1 EE1]]]].
  destruct E2 as [r2 [s2 [d2 [c2 EE2]]]].
  twoarr_crush.
  eexists (TwoArr_at (thcomp _ _)).
  exists eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma thunit_right_cast {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tr2_cast (sb_id_right SB f) (sb_id_right SB f')
         (thcomp α (tid2 (@id tcat a))) ≈ α.
Proof using K SB.
  etransitivity; [ symmetry; apply (sb_unitr_cast SB) |].
  apply thunit_right.
Qed.

Lemma thunit_left_cast {a b : tcat} {f f' : a ~{tcat}~> b} (α : tcell f f') :
  tr2_cast (sb_id_left SB f) (sb_id_left SB f')
         (thcomp (tid2 (@id tcat b)) α) ≈ α.
Proof using K SB.
  etransitivity; [ symmetry; apply (sb_unitl_cast SB) |].
  apply thunit_left.
Qed.

Lemma TwoV_ident_id {x y : tcat} (f : x ~{tcat}~> y) :
  TwoV_ident (TwoArr_at (tid2 f)).
Proof using K.
  split; intros a Ha.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p [q [e _]]]; simpl in p, q, e.
    exists p, q, e; destruct p, q; simpl in e; destruct e; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    apply tvid_right.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p [q [e _]]]; simpl in p, q, e.
    exists p, q, e; destruct p, q; simpl in e; destruct e; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
    apply tvid_left.
Qed.

Lemma TwoV_ident_law (a : TwoArr) :
  ∃ u u', (TwoV_ident u ∧ TwoV_ident u')
        ∧ (TwoV_defined a u ∧ TwoV_defined u' a).
Proof using K SB.
  exists (TwoArr_at (tid2 (t1dom a))), (TwoArr_at (tid2 (t1cod a))).
  split; split.
  - apply TwoV_ident_id.
  - apply TwoV_ident_id.
  - eexists; exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - eexists; exists eq_refl, eq_refl, eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma TwoH_ident_id (x : tcat) : TwoH_ident (TwoArr_at (tid2 (@id tcat x))).
Proof using K SB.
  split; intros a Ha.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p _]; simpl in p.
    exists p; destruct p; simpl.
    exists eq_refl, eq_refl, (sb_id_right SB af), (sb_id_right SB ag); simpl.
    apply thunit_right_cast.
  - destruct Ha as [c Hc]; destruct a as [a0 a1 af ag α]; simpl in *.
    destruct Hc as [p _]; simpl in p.
    exists p; destruct p; simpl.
    exists eq_refl, eq_refl, (sb_id_left SB af), (sb_id_left SB ag); simpl.
    apply thunit_left_cast.
Qed.

Lemma TwoH_ident_law (a : TwoArr) :
  ∃ u u', (TwoH_ident u ∧ TwoH_ident u')
        ∧ (TwoH_defined a u ∧ TwoH_defined u' a).
Proof using K SB.
  exists (TwoArr_at (tid2 (@id tcat (t0src a)))),
         (TwoArr_at (tid2 (@id tcat (t0tgt a)))).
  split; split.
  - apply TwoH_ident_id.
  - apply TwoH_ident_id.
  - eexists; exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
  - eexists; exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity.
Qed.

Lemma TwoArr_interchange {σ τ σ' τ' pp qq rr ss xx yy} :
  TwoV τ σ pp → TwoV τ' σ' qq → TwoH qq pp xx →
  TwoH τ' τ rr → TwoH σ' σ ss → TwoV rr ss yy → TwoArr_eq xx yy.
Proof using K SB.
  intros [a1 [a2 [a3 A]]] [b1 [b2 [b3 B]]] [c1 C] [d1 D] [e1 E]
         [f1 [f2 [f3 F]]].
  destruct A as [? [? [? [? AA]]]].
  destruct B as [? [? [? [? BB]]]].
  destruct C as [? [? [? [? CC]]]].
  destruct D as [? [? [? [? DD]]]].
  destruct E as [? [? [? [? EE]]]].
  destruct F as [? [? [? [? FF]]]].
  twoarr_crush.
  exists eq_refl, eq_refl, eq_refl, eq_refl; simpl.
  rewrite <- CC, <- AA, <- BB, tinterchange, DD, EE; exact FF.
Qed.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma TwoV_ident_respects {u u'} :
  TwoArr_eq u u' → TwoV_ident u → TwoV_ident u'.
Proof using K SB.
  intros Hu [H1 H2]; split.
  - intros f Hf.
    assert (Hf' : TwoV_defined f u).
    { destruct Hf as [c Hc]; exists c.
      exact (TwoV_respects (reflexivity f) (symmetry Hu) (reflexivity c) Hc). }
    exact (TwoV_respects (reflexivity f) Hu (reflexivity f) (H1 f Hf')).
  - intros g Hg.
    assert (Hg' : TwoV_defined u g).
    { destruct Hg as [c Hc]; exists c.
      exact (TwoV_respects (symmetry Hu) (reflexivity g) (reflexivity c) Hc). }
    exact (TwoV_respects Hu (reflexivity g) (reflexivity g) (H2 g Hg')).
Qed.

(* Mac Lane's 定义 3, bundled structure: every 恒等 for
 horizontal 复合 恒等 vertical one. （已译） *)
Lemma TwoArr_hident_is_vident (u : TwoArr) : TwoH_ident u → TwoV_ident u.
Proof using K SB.
  intros Hu.
  assert (Hd : TwoH_defined (TwoArr_at (tid2 (@id tcat (t0tgt u)))) u).
  { eexists; exists eq_refl; simpl.
    exists eq_refl, eq_refl, eq_refl, eq_refl; simpl; reflexivity. }
  pose proof (fst Hu _ Hd) as H1.
  pose proof (snd (TwoH_ident_id (t0tgt u)) u Hd) as H2.
  exact (TwoV_ident_respects (TwoH_unique H1 H2)
           (TwoV_ident_id (@id tcat (t0tgt u)))).
Qed.

(** ** The passage *)

Definition TwoArr_Vert : MetaComp TwoArr_Setoid.
Proof using K SB.
  unshelve refine {| mccomp := TwoV |}.
  - exact (@TwoV_respects).
  - exact (@TwoV_unique).
  - exact (@TwoV_assoc_l).
  - exact (@TwoV_assoc_r).
  - exact (@TwoV_match).
  - exact TwoV_ident_law.
Defined.

Definition TwoArr_Horiz : MetaComp TwoArr_Setoid.
Proof using K SB.
  unshelve refine {| mccomp := TwoH |}.
  - exact (@TwoH_respects).
  - exact (@TwoH_unique).
  - exact (@TwoH_assoc_l).
  - exact (@TwoH_assoc_r).
  - exact (@TwoH_match).
  - exact TwoH_ident_law.
Defined.

Definition TwoArr_Double : StrictDoubleCategory := {|
  dcell        := TwoArr;
  dcell_setoid := TwoArr_Setoid;
  dvert        := TwoArr_Vert;
  dhoriz       := TwoArr_Horiz;
  dinterchange := @TwoArr_interchange
|}.

Definition TwoCategory_to_Strict : StrictTwoCategory := {|
  s2double         := TwoArr_Double;
  s2ident_coincide := TwoArr_hident_is_vident
|}.

(** ** What the passage preserves *)

Lemma TwoArr_at_respects {x y : tcat} {f g : x ~{tcat}~> y} (α β : tcell f g) :
  α ≈ β → TwoArr_eq (TwoArr_at α) (TwoArr_at β).
Proof using Type.
  intro H; exists eq_refl, eq_refl, eq_refl, eq_refl; exact H.
Qed.

Lemma TwoArr_at_faithful {x y : tcat} {f g : x ~{tcat}~> y} (α β : tcell f g) :
  TwoArr_eq (TwoArr_at α) (TwoArr_at β) → α ≈ β.
Proof using K SB. intro H; twoarr_crush; assumption. Qed.

Lemma TwoArr_at_surjective (a : TwoArr) : TwoArr_eq (TwoArr_at (t2cell a)) a.
Proof using Type.
  destruct a; exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
Qed.

Lemma TwoV_at {x y : tcat} {f g h : x ~{tcat}~> y}
  (β : tcell g h) (α : tcell f g) :
  TwoV (TwoArr_at β) (TwoArr_at α) (TwoArr_at (tvcomp β α)).
Proof using Type.
  exists eq_refl, eq_refl, eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
Qed.

Lemma TwoH_at {x y z : tcat} {f f' : x ~{tcat}~> y} {g g' : y ~{tcat}~> z}
  (β : tcell g g') (α : tcell f f') :
  TwoH (TwoArr_at β) (TwoArr_at α) (TwoArr_at (thcomp β α)).
Proof using Type.
  exists eq_refl; simpl.
  exists eq_refl, eq_refl, eq_refl, eq_refl; reflexivity.
Qed.

Lemma TwoV_at_unique {x y : tcat} {f g h : x ~{tcat}~> y}
  (β : tcell g h) (α : tcell f g) (c : TwoArr) :
  TwoV (TwoArr_at β) (TwoArr_at α) c → TwoArr_eq (TwoArr_at (tvcomp β α)) c.
Proof using K SB. intro H; exact (TwoV_unique (TwoV_at β α) H). Qed.

Lemma TwoH_at_unique {x y z : tcat} {f f' : x ~{tcat}~> y}
  {g g' : y ~{tcat}~> z} (β : tcell g g') (α : tcell f f') (c : TwoArr) :
  TwoH (TwoArr_at β) (TwoArr_at α) c → TwoArr_eq (TwoArr_at (thcomp β α)) c.
Proof using K SB. intro H; exact (TwoH_unique (TwoH_at β α) H). Qed.

End ToStrict.

(*
   本节说明 TwoCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma dvert_unit_hcomp (D : StrictDoubleCategory) {u v w x y z t : dcell D} :
  mccomp (dvert D) x u x →      (* u is a vertical unit for x *)
  mccomp (dvert D) y v y →      (* v is a vertical unit for y *)
  mccomp (dhoriz D) y x z →     (* z is the horizontal composite of y, x *)
  mccomp (dhoriz D) v u w →     (* w is the horizontal composite of v, u *)
  mccomp (dvert D) z w t →      (* t is the vertical composite of z, w *)
  @equiv _ (dcell_setoid D) z t.
Proof.
  intros H1 H2 H3 H4 H5.
  exact (dinterchange D H1 H2 H3 H3 H4 H5).
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition poly_unit_dec (x y : poly_unit) : {x = y} + {x <> y}.
Proof. left; destruct x, y; reflexivity. Defined.

Program Definition chaotic_setoid (A : Type) : Setoid A := {|
  equiv := fun _ _ => True
|}.

#[local] Obligation Tactic :=
  simpl; intros; try apply eq_equivalence; repeat intro; simpl in *; lia.

Program Definition NatPlusCat : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => nat;
  homset  := fun _ _ => {| equiv := @eq nat |};
  id      := fun _ => 0%nat;
  compose := fun _ _ _ f g => (f + g)%nat
|}.

#[local] Obligation Tactic := simpl; intros; repeat intro; exact I.

Program Definition ChaoticTwoCat : TwoCategory := {|
  tcat         := NatPlusCat;
  tcell        := fun _ _ _ _ => poly_unit;
  tcell_setoid := fun _ _ _ _ => chaotic_setoid poly_unit;
  tid2         := fun _ _ _ => ttt;
  tvcomp       := fun _ _ _ _ _ _ _ => ttt;
  thcomp       := fun _ _ _ _ _ _ _ _ _ => ttt;
  tassoc_cast  := fun _ _ _ _ _ _ _ _ _ _ _ => ttt;
  tunitl_cast  := fun _ _ _ _ _ => ttt;
  tunitr_cast  := fun _ _ _ _ _ => ttt
|}.

#[local] Obligation Tactic := simpl; intros; exact I.

Program Definition NatPlus_StrictBase : @StrictBase ChaoticTwoCat := {|
  sb_obj_uip  := UIP_dec poly_unit_dec;
  sb_hom_uip  := fun a b => UIP_dec PeanoNat.Nat.eq_dec;
  sb_id_left  := fun a b f => eq_refl;
  sb_id_right := fun a b f => PeanoNat.Nat.add_0_r f;
  sb_assoc    := fun a b c d h g f => PeanoNat.Nat.add_assoc h g f
|}.

Definition ChaoticTwoCat_Strict : StrictTwoCategory :=
  TwoCategory_to_Strict NatPlus_StrictBase.

Example ChaoticTwoCat_cells_separate :
  @TwoArr_eq ChaoticTwoCat (@TwoArr_at ChaoticTwoCat ttt ttt 0%nat 0%nat ttt)
                    (@TwoArr_at ChaoticTwoCat ttt ttt 1%nat 1%nat ttt) → False.
Proof.
  intros [p [q [ed [ec _]]]].
  rewrite (UIP_dec poly_unit_dec p eq_refl) in ed.
  rewrite (UIP_dec poly_unit_dec q eq_refl) in ed.
  simpl in ed; discriminate.
Qed.
