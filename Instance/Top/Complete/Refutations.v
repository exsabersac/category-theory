Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Subspace.
Require Import Category.Instance.Top.Complete.

Generalizable All Variables.

(** * Where completeness of spaces stops: [PTopCat], and [Top] below its
      homs *)

(*
 nLab: https://ncatlab.org/nlab/show/complete+small+category
 nLab: https://ncatlab.org/nlab/show/Top

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Evaluation at the point separates the two points of [PBool] *)

Definition pbool_eval_pt@{o so +| o < so +}
  (f : PPoint@{o} ~{PTopCat@{o so}}~> PBool@{o}) : bool :=
  pmap f ttt.

Lemma pbool_eval_pt_resp@{o so +| o < so +}
  (u v : PPoint@{o} ~{PTopCat@{o so}}~> PBool@{o}) :
  u ≈ v → pbool_eval_pt u = pbool_eval_pt v.
Proof. intro H. exact (H ttt). Qed.

(** ** Freyd's core at an arbitrary arrow index *)

Theorem PTop_not_complete_Freyd@{r s o so +| o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (freyd_no_separated_pair AI (ppoint_true@{o}) (ppoint_false@{o}) _ _
           (complete_iprod comp (fun _ : ai_index AI => PBool@{o}))
           pbool_eval_pt pbool_eval_pt_resp eq_refl eq_refl).
Qed.

(* The canonical index of [PTopCat@{o so}] sits at [so]. *)
Theorem PTop_not_complete_IEM_canonical@{e r s o so +| o < so +} (E : IEM@{e})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_Freyd
           (canonical_ArrowIndex (ObjDecEq_of_IEM E PTopCat@{o so})) comp).
Qed.

(* The objects and homs of [PTopCat@{o so1}] and [PTopCat@{o so2}] are the
   same [PTop@{o}] and [PMor@{o}], so an arrow index moves between them. *)
Definition PTop_ArrowIndex_transport@{s o so1 so2 +| o < so1, o < so2 +}
  (AI : ArrowIndex@{s so1 o} PTopCat@{o so1}) :
  ArrowIndex@{s so2 o} PTopCat@{o so2} :=
  @Build_ArrowIndex PTopCat@{o so2} (ai_index AI)
    (fun x y f => @ai_enc PTopCat@{o so1} AI x y f)
    (fun x y m d => @ai_dec PTopCat@{o so1} AI x y m d)
    (fun x y f d => @ai_dec_enc PTopCat@{o so1} AI x y f d).

(* Every shape universe strictly above the points: decidable equality of
   spaces, transported to the canonical index at [s]. *)
Theorem PTop_not_complete_ObjDecEq@{r s o so +| o < so, o < s +}
  (DO : ObjDecEq PTopCat@{o so})
  (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_Freyd
           (PTop_ArrowIndex_transport@{s o s so}
              (canonical_ArrowIndex (DO : ObjDecEq PTopCat@{o s})))
           comp).
Qed.

Theorem PTop_not_complete_IEM@{e r s o so +| o < so, o < s +}
  (E : IEM@{e}) (comp : @Complete@{r s o so} PTopCat@{o so}) : False.
Proof.
  exact (PTop_not_complete_ObjDecEq (ObjDecEq_of_IEM E PTopCat@{o so}) comp).
Qed.

(** ** No arrow index at or below the points, constructively *)

Definition PTop_no_ArrowIndex_at_points@{o so +| o < so +}
  (AI : ArrowIndex@{o so o} PTopCat@{o so}) : False :=
  PTop_not_complete_Freyd AI PTop_Complete_via_products.

Definition PTop_no_ArrowIndex_below@{s o so +| s <= o, o < so +}
  (AI : ArrowIndex@{s so o} PTopCat@{o so}) : False :=
  PTop_not_complete_Freyd AI PTop_Complete.

(** ** Products above the points *)

Theorem PTop_iprod_refuted_IEM@{e s o so +| o < so, o < s +}
  (E : IEM@{e})
  (HP : @HasIndexedProducts@{s s s s so o} PTopCat@{o so}) : False.
Proof.
  pose (AI := PTop_ArrowIndex_transport@{s o s so}
                (canonical_ArrowIndex
                   (ObjDecEq_of_IEM E PTopCat@{o so} : ObjDecEq PTopCat@{o s}))).
  exact (freyd_no_separated_pair AI (ppoint_true@{o}) (ppoint_false@{o}) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => PBool@{o}))
           pbool_eval_pt pbool_eval_pt_resp eq_refl eq_refl).
Qed.

(** ** The Type-valued [Top]: products at and above the hom universe *)

(* The canonical index of [Top@{h o}] sits at its object universe [h], and
   indexes at every [s] with [h <= s]. *)
Theorem Top_iprod_refuted_IEM_canonical@{e s h o +| o < h, h <= s +}
  (E : IEM@{e}) (HP : @HasIndexedProducts@{s s s s h h} Top@{h o}) : False.
Proof.
  pose (AI := canonical_ArrowIndex@{s h h} (ObjDecEq_of_IEM E Top@{h o})).
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(** ** The Type-valued [Top]: an arrow index moves between hom universes *)

(*
   本节说明 Refutations 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition top_rebuild@{o h1 h2 | o < h1, o < h2 +} {X Y : TopSpace@{o}}
  (f : ContinuousMorphism@{h1 o} X Y) : ContinuousMorphism@{h2 o} X Y :=
  {| continuous_map := continuous_map f;
     continuity := fun U HU => continuity f U HU |}.

(* The index never mentions a hom universe: encode and decode through the
   rebuild, both ways; the decoding law is pointwise. *)
Definition Top_ArrowIndex_transport@{s o h1 h2 | o < h1, o < h2 +}
  (AI : ArrowIndex@{s h1 h1} Top@{h1 o}) :
  ArrowIndex@{s h2 h2} Top@{h2 o} :=
  @Build_ArrowIndex Top@{h2 o} (ai_index AI)
    (fun x y f => @ai_enc Top@{h1 o} AI x y (top_rebuild@{o h2 h1} f))
    (fun x y m d => top_rebuild@{o h1 h2}
                      (@ai_dec Top@{h1 o} AI x y m (top_rebuild@{o h2 h1} d)))
    (fun x y f d z => @ai_dec_enc Top@{h1 o} AI x y (top_rebuild@{o h2 h1} f)
                        (top_rebuild@{o h2 h1} d) z).

(* Every shape universe strictly above the points, the shapes below the
   homs included: the canonical index is built at [Top@{s o}] and
   transported to [Top@{h o}]. *)
Theorem Top_not_complete_below_ObjDecEq@{r s h o +| o < h, o < s +}
  (DE : ObjDecEq Top@{h o}) (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete
           (Top_ArrowIndex_transport@{s o s h}
              (canonical_ArrowIndex (DE : ObjDecEq Top@{s o})))
           comp).
Qed.

Theorem Top_not_complete_below_IEM@{e r s h o +| o < h, o < s +}
  (E : IEM@{e}) (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete_below_ObjDecEq (ObjDecEq_of_IEM E Top@{h o}) comp).
Qed.

(* Products indexed strictly above the points and at or below the homs:
   the reading of [HasIndexedProducts] whose fourth slot is the hom
   universe. *)
Theorem Top_iprod_refuted_below_IEM@{e s h o +| o < h, o < s, s <= h +}
  (E : IEM@{e}) (HP : @HasIndexedProducts@{s s s h h h} Top@{h o}) : False.
Proof.
  pose (AI := Top_ArrowIndex_transport@{s o s h}
                (canonical_ArrowIndex
                   (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))).
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (@indexed_product_ump _ HP (ai_index AI) (fun _ => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

(* #455's [CompHaus_ArrowIndex_of_Top] after the transport: [Complete
   CompHaus] refuted under [IEM] at every shape universe strictly above
   the points, the shapes below the homs included. *)
Theorem CompHaus_not_complete_below_IEM@{e r s c h o +| o < h, o < s +}
  (E : IEM@{e})
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h})) : False.
Proof.
  exact (CompHaus_not_complete
           (CompHaus_ArrowIndex_of_Top
              (Top_ArrowIndex_transport@{s o s h}
                 (canonical_ArrowIndex
                    (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))))
           comp).
Qed.
