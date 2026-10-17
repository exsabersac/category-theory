Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Deloop.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Existing Instance edgeset.

(*
   nLab: https://ncatlab.org/nlab/show/quotient+category
   nLab: https://ncatlab.org/nlab/show/congruence
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   Book: Awodey, Category Theory, §4.4, printed p. 89 (the finitely
   Book: Fong and Spivak, Seven Sketches in Compositionality, CUP 2019,
   Book: Riehl, Category Theory in Context, §1.6 Remark 1.6.7, printed

   本节说明 Presented 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Presentation.

Universes o h p.
Context (G : Quiver@{o h p}).

(*
   本节说明 Presented 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PathRel : Type := HomRelT (FreeOnQuiver G).

(*
   本节说明 Presented 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example PathRel_parallel :
  PathRel = (∀ x y : G, tlist edges x y → tlist edges x y → Type).
Proof. reflexivity. Qed.

(*
   本节说明 Presented 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record FiniteQuiver : Type := {
  fq_nodes : nat;
  fq_node : Fin.t fq_nodes → G;
  fq_index : G → Fin.t fq_nodes;
  fq_node_rt : ∀ x : G, fq_node (fq_index x) = x;
  fq_edges : G → G → nat;
  fq_edge : ∀ x y : G, Fin.t (fq_edges x y) → edges x y;
  fq_eindex : ∀ x y : G, edges x y → Fin.t (fq_edges x y);
  fq_edge_rt : ∀ (x y : G) (e : edges x y),
      fq_edge x y (fq_eindex x y e) ≈ e
}.

(** Finitely many equations, per parallel pair of endpoints. *)
Record FiniteEquations : Type := {
  fe_count : G → G → nat;
  fe_lhs : ∀ x y : G, Fin.t (fe_count x y) → x ~{FreeOnQuiver G}~> y;
  fe_rhs : ∀ x y : G, Fin.t (fe_count x y) → x ~{FreeOnQuiver G}~> y
}.

(** The path 关系 finite equation set names. [∃] [sigT] here, so
 lands [Type], matching [PathRel]. （已译） *)
Definition fe_rel (E : FiniteEquations) : PathRel :=
  fun x y f g => ∃ i : Fin.t (fe_count E x y),
    (f ≈ fe_lhs E x y i) * (g ≈ fe_rhs E x y i).

Context (R : PathRel).

(* * ** The presented 范畴

 Generators [G], relations [R]: free 范畴 [G], quotiented by
 congruence generated [R]. （已译） *)
Definition PresentedQuiver : Category := QuotientCong (FreeOnQuiver G) R.

(** The presenting projection. *)
Definition PresentedQuiverProj : FreeOnQuiver G ⟶ PresentedQuiver :=
  QuotientCongProj R.

(** A generating edge, read as a morphism of the presented category. *)
Definition pgen {x y : G} (e : edges x y) : x ~{PresentedQuiver}~> y :=
  tlist_singleton e.

(** Mac Lane §II.8 Proposition 1, clause (i), specialized: imposed
 equations hold presented 范畴. （已译） *)
Lemma presented_relations_hold {x y : G}
  {p q : x ~{FreeOnQuiver G}~> y} (Hr : R x y p q) :
  fmap[PresentedQuiverProj] p ≈ fmap[PresentedQuiverProj] q.
Proof. exact (cong_identifies R Hr). Qed.

(** The projection 恒等 对象. （已译） *)
Lemma presented_proj_obj (x : G) : fobj[PresentedQuiverProj] x = x.
Proof. reflexivity. Qed.

(** 本节：The hom TYPES untouched: equations merge, never add. （已译） *)
Lemma presented_hom_type (x y : G) :
  (x ~{PresentedQuiver}~> y) = (x ~{FreeOnQuiver G}~> y).
Proof. reflexivity. Qed.

(** Surjectivity on each hom-set, as a CHOSEN section. *)
Definition PresentedQuiverProj_Full : Full PresentedQuiverProj :=
  @QuotientProj_Full (FreeOnQuiver G) (CongClosure R)
    (CongClosure_Congruence R).

(** 本节：The same, restated readers who want existential. （已译） *)
Lemma presented_proj_hom_surjective {x y : G}
  (f : x ~{PresentedQuiver}~> y) :
  { p : x ~{FreeOnQuiver G}~> y & fmap[PresentedQuiverProj] p ≈ f }.
Proof. exists f. reflexivity. Qed.

(* * ** The 普遍性质

 A 函子 out presented 范畴 exactly quiver
 homomorphism whose induced 函子 merges relations. （已译） *)

Section PresentedUMP.

Context {D : Category}.
Context (F : QuiverHomomorphism G (QuiverOfCat D)).
Context (HF : ∀ x y (f g : x ~{FreeOnQuiver G}~> y), R x y f g →
              fmap[InducedFunctor G F] f ≈ fmap[InducedFunctor G F] g).

(** The induced 函子 out presented 范畴. （已译） *)
Definition PresentedFunctor : PresentedQuiver ⟶ D :=
  QuotientCongLift R (InducedFunctor G F) HF.

(** It sends each generator where quiver homomorphism does. (The
 [id_left] path fold's trailing 恒等 singleton path.) （已译） *)
Lemma PresentedFunctor_gen {x y : G} (e : edges x y) :
  fmap[PresentedFunctor] (pgen e) ≈ @fedgemap _ _ F x y e.
Proof. simpl. now rewrite id_left. Qed.

(** 本节：...and each node likewise, nose. （已译） *)
Lemma PresentedFunctor_obj (x : G) :
  fobj[PresentedFunctor] x = @fnodes _ _ F x.
Proof. reflexivity. Qed.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma PresentedFunctor_unique (K : PresentedQuiver ⟶ D)
  (Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x)
  (Hgen : ∀ (x y : G) (e : edges x y),
      hom_cast (Hobj x) (Hobj y) (fmap[K] (pgen e))
        ≈ @fedgemap _ _ F x y e) :
  ∀ (x y : G) (f : x ~{PresentedQuiver}~> y),
    hom_cast (Hobj x) (Hobj y) (fmap[K] f) ≈ fmap[PresentedFunctor] f.
Proof.
  intros x y f.
  induction f.
  - change (@tnil _ _ y) with (@id PresentedQuiver y).
    rewrite fmap_id. simpl. rewrite hom_cast_id. reflexivity.
  - assert (RW : @equiv (@hom PresentedQuiver i y) _ (b ::: f)
                   (@compose PresentedQuiver _ _ _ f (pgen b))).
    { unfold pgen, tlist_singleton. simpl.
      apply cc_equiv. simpl. now rewrite <- tlist_app_cons. }
    rewrite RW, fmap_comp.
    rewrite <- (hom_cast_comp (Hobj i) (Hobj j) (Hobj y)).
    rewrite IHf, Hgen.
    now rewrite fmap_comp, PresentedFunctor_gen.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Restrict.

Context (S : PresentedQuiver ⟶ D).

(** The quiver homomorphism underlying [S]. *)
Definition presented_restrict : QuiverHomomorphism G (QuiverOfCat D) :=
  QuiverComp (UnitQuiverCatAdjunction G)
    (QuiverHomomorphismOfFunctor _ _ (S ◯ PresentedQuiverProj)).

(** On generators the restriction is [S] itself, definitionally — a
    Leibniz equality of morphisms, stated at that strength deliberately,
    in the manner of [QuotientLift_proj] ([Construction/Quotient.v]). *)
Lemma presented_restrict_gen {x y : G} (e : edges x y) :
  @fedgemap _ _ presented_restrict x y e = fmap[S] (pgen e).
Proof. reflexivity. Qed.

(** The 函子 induced restriction agrees [S] every
 path. （已译） *)
Lemma presented_restrict_induced {a b : G}
  (u : a ~{FreeOnQuiver G}~> b) :
  fmap[InducedFunctor G presented_restrict] u ≈ fmap[S] u.
Proof.
  induction u; simpl.
  - now rewrite fmap_id.
  - transitivity (fmap[S] u ∘ fmap[S] (pgen b0)).
    + apply compose_respects; [ exact IHu | reflexivity ].
    + rewrite <- fmap_comp. apply fmap_respects.
      unfold pgen, tlist_singleton; simpl.
      apply cc_equiv; simpl. now rewrite <- tlist_app_cons.
Qed.

(** Every 函子 out presented 范畴 merges [R] automatically —
 converse merging 假设 [HF]. （已译） *)
Lemma presented_restrict_satisfies {x y : G}
  {p q : x ~{FreeOnQuiver G}~> y} (Hr : R x y p q) :
  fmap[InducedFunctor G presented_restrict] p
    ≈ fmap[InducedFunctor G presented_restrict] q.
Proof.
  transitivity (fmap[S] p); [ exact (presented_restrict_induced p) | ].
  transitivity (fmap[S] q);
    [ exact (@fmap_respects _ _ S x y p q (cc_gen Hr))
    | symmetry; exact (presented_restrict_induced q) ].
Qed.

End Restrict.

End PresentedUMP.

End Presentation.

Arguments PathRel G : assert.
Arguments PresentedQuiver G R : assert.
Arguments pgen {G R x y} e.
Arguments fe_rel {G} E.

(* 相关说明。 （已译） *)
Record FinitePresentation : Type := {
  fp_quiver : Quiver;
  fp_finite : FiniteQuiver fp_quiver;
  fp_eqns : FiniteEquations fp_quiver
}.

(** Seven Sketches §3.2.2's finitely presented category, with finiteness
    carried as data throughout. *)
Definition FinitelyPresented (P : FinitePresentation) : Category :=
  PresentedQuiver (fp_quiver P) (fe_rel (fp_eqns P)).

(* * ** The generators-and-relations 普遍性质, bundled （已译） *)

Section PresentedUniversal.

Context (G : Quiver) (R : PathRel G) {D : Category}.

(*
   本节说明函子、hom、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem presented_universal
  (F : QuiverHomomorphism G (QuiverOfCat D))
  (HF : ∀ x y (f g : x ~{FreeOnQuiver G}~> y), R x y f g →
        fmap[InducedFunctor G F] f ≈ fmap[InducedFunctor G F] g) :
  { K : PresentedQuiver G R ⟶ D &
  { Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x &
    ((∀ (x y : G) (e : edges x y),
        hom_cast (Hobj x) (Hobj y) (fmap[K] (pgen e))
          ≈ @fedgemap _ _ F x y e) *
     (∀ (K' : PresentedQuiver G R ⟶ D)
        (Hobj' : ∀ x : G, fobj[K'] x = @fnodes _ _ F x),
        (∀ (x y : G) (e : edges x y),
           hom_cast (Hobj' x) (Hobj' y) (fmap[K'] (pgen e))
             ≈ @fedgemap _ _ F x y e) →
        ∀ (x y : G) (f : x ~{PresentedQuiver G R}~> y),
          hom_cast (Hobj' x) (Hobj' y) (fmap[K'] f)
            ≈ hom_cast (Hobj x) (Hobj y) (fmap[K] f)))%type } }.
Proof.
  exists (@PresentedFunctor G R D F HF), (fun _ => eq_refl).
  split.
  - intros x y e. exact (@PresentedFunctor_gen G R D F HF x y e).
  - intros K' Hobj' Hgen x y f.
    exact (@PresentedFunctor_unique G R D F HF K' Hobj' Hgen x y f).
Qed.

End PresentedUniversal.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The quiver one node one edge set. [poly_unit] keeps the
 对象 universe free rather than pinning it at [Set]. （已译） *)
Definition OneNodeQuiver (A : Type) : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => A).

(** The free 幺半群 [A]: carrier reduces paths the
 single node itself, i.e. [tlist] encoding [list A]. （已译） *)
Definition FreeMonoidOn (A : Type) : MonObject :=
  hom_monoid (FreeOnQuiver (OneNodeQuiver A)) ttt.

(** The 幺半群 presented generators [A] relations [R]. （已译） *)
Definition PresentedMonoidOn (A : Type) (R : PathRel (OneNodeQuiver A)) :
  MonObject :=
  hom_monoid (PresentedQuiver (OneNodeQuiver A) R) ttt.

(*
   本节说明 Presented 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive Ord3Node : Set := Ord3_0 | Ord3_1 | Ord3_2.

Inductive Ord3Edge : Ord3Node → Ord3Node → Set :=
  | Ord3_a : Ord3Edge Ord3_0 Ord3_1
  | Ord3_b : Ord3Edge Ord3_1 Ord3_2
  | Ord3_c : Ord3Edge Ord3_0 Ord3_2.

Definition Ord3Quiver : Quiver := Build_Quiver_Standard_Eq Ord3Node Ord3Edge.

(** The two paths 关系 identifies. （已译） *)
Definition ord3_path_c : Ord3_0 ~{FreeOnQuiver Ord3Quiver}~> Ord3_2 :=
  tlist_singleton (B:=@edges Ord3Quiver) Ord3_c.

Definition ord3_path_ab : Ord3_0 ~{FreeOnQuiver Ord3Quiver}~> Ord3_2 :=
  tcons (B:=@edges Ord3Quiver) _ Ord3_a
    (tlist_singleton (B:=@edges Ord3Quiver) Ord3_b).

(** In FREE 范畴 they distinct. The discriminator the
 intermediate node equality [tlist'_quiver_equiv] exposes the
 first component [sigT]. （已译） *)
Lemma ord3_free_distinct : ord3_path_c ≈ ord3_path_ab → False.
Proof.
  unfold ord3_path_c, ord3_path_ab, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl. intros [q He Ht]. discriminate q.
Qed.

(** The single equation, as finite data. *)
Definition Ord3_count (x y : Ord3Quiver) : nat :=
  match x, y with Ord3_0, Ord3_2 => 1 | _, _ => 0 end.

Definition Ord3_lhs (x y : Ord3Quiver) :
  Fin.t (Ord3_count x y) → x ~{FreeOnQuiver Ord3Quiver}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact ord3_path_c ].
Defined.

Definition Ord3_rhs (x y : Ord3Quiver) :
  Fin.t (Ord3_count x y) → x ~{FreeOnQuiver Ord3Quiver}~> y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i) | exact ord3_path_ab ].
Defined.

Definition Ord3Eqns : FiniteEquations Ord3Quiver := {|
  fe_count := Ord3_count;
  fe_lhs := Ord3_lhs;
  fe_rhs := Ord3_rhs
|}.

(** 本节：The quiver finite, enumeration carried data. （已译） *)
Definition Ord3_node (i : Fin.t 3) : Ord3Node :=
  match i with
  | Fin.F1 => Ord3_0
  | Fin.FS j =>
      match j with
      | Fin.F1 => Ord3_1
      | Fin.FS _ => Ord3_2
      end
  end.

Definition Ord3_index (x : Ord3Node) : Fin.t 3 :=
  match x with
  | Ord3_0 => Fin.F1
  | Ord3_1 => Fin.FS Fin.F1
  | Ord3_2 => Fin.FS (Fin.FS Fin.F1)
  end.

Lemma Ord3_node_rt (x : Ord3Node) : Ord3_node (Ord3_index x) = x.
Proof. destruct x; reflexivity. Qed.

Definition Ord3_ecount (x y : Ord3Node) : nat :=
  match x, y with
  | Ord3_0, Ord3_1 => 1
  | Ord3_1, Ord3_2 => 1
  | Ord3_0, Ord3_2 => 1
  | _, _ => 0
  end.

Definition Ord3_edge (x y : Ord3Node) :
  Fin.t (Ord3_ecount x y) → Ord3Edge x y.
Proof.
  destruct x, y; simpl; intro i;
    solve [ exact (Fin.case0 _ i)
          | exact Ord3_a | exact Ord3_b | exact Ord3_c ].
Defined.

Definition Ord3_eindex (x y : Ord3Node) (e : Ord3Edge x y) :
  Fin.t (Ord3_ecount x y) :=
  match e in Ord3Edge a b return Fin.t (Ord3_ecount a b) with
  | Ord3_a => Fin.F1
  | Ord3_b => Fin.F1
  | Ord3_c => Fin.F1
  end.

Lemma Ord3_edge_rt (x y : Ord3Node) (e : Ord3Edge x y) :
  Ord3_edge x y (Ord3_eindex x y e) = e.
Proof. destruct e; reflexivity. Qed.

Definition Ord3Finite : FiniteQuiver Ord3Quiver :=
  @Build_FiniteQuiver Ord3Quiver 3 Ord3_node Ord3_index Ord3_node_rt
    Ord3_ecount Ord3_edge Ord3_eindex Ord3_edge_rt.

Definition Ord3Presentation : FinitePresentation := {|
  fp_quiver := Ord3Quiver;
  fp_finite := Ord3Finite;
  fp_eqns := Ord3Eqns
|}.

(** The presented category. *)
Definition Ord3 : Category :=
  PresentedQuiver Ord3Quiver (fe_rel Ord3Eqns).

(** 本节：...in two paths ARE identified. （已译） *)
Lemma ord3_relation_holds :
  @equiv _ (@homset Ord3 Ord3_0 Ord3_2) ord3_path_c ord3_path_ab.
Proof. apply cc_gen. exists Fin.F1. split; reflexivity. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Inductive SquareNode : Set := Sq_A | Sq_B | Sq_C | Sq_D.

Inductive SquareEdge : SquareNode → SquareNode → Set :=
  | Sq_f : SquareEdge Sq_A Sq_B
  | Sq_g : SquareEdge Sq_A Sq_C
  | Sq_h : SquareEdge Sq_B Sq_D
  | Sq_k : SquareEdge Sq_C Sq_D.

Definition SquareQuiver : Quiver :=
  Build_Quiver_Standard_Eq SquareNode SquareEdge.

Definition square_diag_fh : Sq_A ~{FreeOnQuiver SquareQuiver}~> Sq_D :=
  tcons (B:=@edges SquareQuiver) _ Sq_f
    (tlist_singleton (B:=@edges SquareQuiver) Sq_h).

Definition square_diag_gk : Sq_A ~{FreeOnQuiver SquareQuiver}~> Sq_D :=
  tcons (B:=@edges SquareQuiver) _ Sq_g
    (tlist_singleton (B:=@edges SquareQuiver) Sq_k).

(* 相关说明。 （已译） *)
Theorem free_square_diagonals_distinct :
  square_diag_fh ≈ square_diag_gk → False.
Proof.
  unfold square_diag_fh, square_diag_gk, tlist_singleton; simpl.
  unfold tlist_quiver_equiv; simpl. intros [q He Ht]. discriminate q.
Qed.

(*
   本节说明 Presented 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AmbientCong (C : Category) : @HomCongruence C (fun x y f g => f ≈ g).
Proof.
  unshelve econstructor.
  - intros x y f g H; exact H.
  - intros x y f g H; symmetry; exact H.
  - intros x y f g h H1 H2; transitivity g; assumption.
  - intros x y z f f' g g' H1 H2; now rewrite H1, H2.
Defined.

Definition SquareNoEqns : FiniteEquations SquareQuiver :=
  {| fe_count := fun _ _ => O;
     fe_lhs := fun x y i => Fin.case0 _ i;
     fe_rhs := fun x y i => Fin.case0 _ i |}.

Definition SquareFree : Category :=
  PresentedQuiver SquareQuiver (fe_rel SquareNoEqns).

Theorem presented_no_eqns_separates :
  @equiv _ (@homset SquareFree Sq_A Sq_D) square_diag_fh square_diag_gk → False.
Proof.
  intro H.
  apply free_square_diagonals_distinct.
  refine (@cc_least (FreeOnQuiver SquareQuiver) (fe_rel SquareNoEqns)
            (fun x y f g => f ≈ g) (AmbientCong _) _ _ _ _ _ H).
  intros x y f g [i _]. exact (Fin.case0 _ i).
Qed.
