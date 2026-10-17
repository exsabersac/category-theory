Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Funny.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Seam helpers

 [transport] moves 态射 along equality codomain and
 [transport_r] along equality domain; note orientation
 [transport_r B (p : = b) : B b → B a], matching
 [Functor_StrictEq_Setoid]. Each helper proved path induction, so
 each holds definitionally once equality [eq_refl]. （已译） *)

Lemma transport_id_hom {E : Category} {a b : E} (p : a = b) :
  transport (fun z => a ~{E}~> z) p id
    ≈ transport_r (fun z => z ~{E}~> b) p id.
Proof. destruct p; simpl; reflexivity. Qed.

Lemma transport_cod_comp {E : Category} {x m w w' : E} (p : w = w')
  (u : m ~{E}~> w) (v : x ~{E}~> m) :
  transport (fun z => x ~{E}~> z) p (u ∘ v)
    = transport (fun z => m ~{E}~> z) p u ∘ v.
Proof. destruct p; reflexivity. Qed.

Lemma transport_dom_comp {E : Category} {x x' m w : E} (p : x = x')
  (u : m ~{E}~> w) (v : x' ~{E}~> m) :
  transport_r (fun z => z ~{E}~> w) p (u ∘ v)
    = u ∘ transport_r (fun z => z ~{E}~> m) p v.
Proof. destruct p; reflexivity. Qed.

(* Moving transport across 复合 seam: domain-transport the
 left factor equals codomain-transport right factor. （已译） *)
Lemma transport_seam {E : Category} {x m m' w : E} (p : m = m')
  (u : m' ~{E}~> w) (v : x ~{E}~> m) :
  transport_r (fun z => z ~{E}~> w) p u ∘ v
    = u ∘ transport (fun z => x ~{E}~> z) p v.
Proof. destruct p; reflexivity. Qed.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma transport_cod_respects {E : Category} {x w w' : E} (p : w = w')
  {u v : x ~{E}~> w} :
  u ≈ v →
  transport (fun z => x ~{E}~> z) p u ≈ transport (fun z => x ~{E}~> z) p v.
Proof. intros; destruct p; assumption. Qed.

Lemma transport_dom_respects {E : Category} {x x' w : E} (p : x = x')
  {u v : x' ~{E}~> w} :
  u ≈ v →
  transport_r (fun z => z ~{E}~> w) p u
    ≈ transport_r (fun z => z ~{E}~> w) p v.
Proof. intros; destruct p; assumption. Qed.

(* 相关说明。 （已译） *)

Definition Functor_StrictEq_intro {A B : Category} (F G : A ⟶ B)
  (eo : ∀ x : A, F x = G x)
  (em : ∀ (x y : A) (f : x ~{A}~> y),
      transport (fun z => F x ~{B}~> z) (eo y) (fmap[F] f)
        ≈ transport_r (fun z => z ~{B}~> G y) (eo x) (fmap[G] f)) :
  @equiv _ (@Functor_StrictEq_Setoid A B) F G := (eo; em).

(** ** The master lemma *)

Section FunnyStrictEq.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.
Context (H K : (C □ D) ⟶ E).
Context (eo : ∀ (c : C) (d : D), H (c, d) = K (c, d)).
Context (el : ∀ (c c' : C) (f : c ~{C}~> c') (d : D),
  transport (fun z => H (c, d) ~{E}~> z) (eo c' d)
            (@fmap (C □ D) E H (c, d) (c', d) (lstep f))
    ≈ transport_r (fun z => z ~{E}~> K (c', d)) (eo c d)
                  (@fmap (C □ D) E K (c, d) (c', d) (lstep f))).
Context (er : ∀ (c : C) (d d' : D) (g : d ~{D}~> d'),
  transport (fun z => H (c, d) ~{E}~> z) (eo c d')
            (@fmap (C □ D) E H (c, d) (c, d') (rstep g))
    ≈ transport_r (fun z => z ~{E}~> K (c, d')) (eo c d)
                  (@fmap (C □ D) E K (c, d) (c, d') (rstep g))).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Funny_strict_eq_word {c1 : C} {d1 : D} {c2 : C} {d2 : D}
  (t : FunHom c1 d1 c2 d2) :
  transport (fun z => H (c1, d1) ~{E}~> z) (eo c2 d2)
            (@fmap (C □ D) E H (c1, d1) (c2, d2) t)
    ≈ transport_r (fun z => z ~{E}~> K (c2, d2)) (eo c1 d1)
                  (@fmap (C □ D) E K (c1, d1) (c2, d2) t).
Proof using C D E H K el eo er.
  induction t as [ c d | ca cb da f cc dc t IHt | ca da db g cc dc t IHt ].
  - (* fnil ≡ id *)
    etransitivity.
    { apply transport_cod_respects.
      exact (@fmap_id (C □ D) E H (c, d)). }
    etransitivity.
    { apply transport_id_hom. }
    apply transport_dom_respects.
    symmetry.
    exact (@fmap_id (C □ D) E K (c, d)).
  - (* fconsL f t ≡ t ∘ lstep f *)
    etransitivity.
    { apply transport_cod_respects.
      exact (@fmap_comp (C □ D) E H (ca, da) (cb, da) (cc, dc) t (lstep f)). }
    rewrite transport_cod_comp.
    etransitivity.
    { apply compose_respects; [ exact IHt | reflexivity ]. }
    rewrite transport_seam.
    etransitivity.
    { apply compose_respects; [ reflexivity | exact (el ca cb f da) ]. }
    rewrite <- transport_dom_comp.
    apply transport_dom_respects.
    symmetry.
    exact (@fmap_comp (C □ D) E K (ca, da) (cb, da) (cc, dc) t (lstep f)).
  - (* fconsR g t ≡ t ∘ rstep g *)
    etransitivity.
    { apply transport_cod_respects.
      exact (@fmap_comp (C □ D) E H (ca, da) (ca, db) (cc, dc) t (rstep g)). }
    rewrite transport_cod_comp.
    etransitivity.
    { apply compose_respects; [ exact IHt | reflexivity ]. }
    rewrite transport_seam.
    etransitivity.
    { apply compose_respects; [ reflexivity | exact (er ca da db g) ]. }
    rewrite <- transport_dom_comp.
    apply transport_dom_respects.
    symmetry.
    exact (@fmap_comp (C □ D) E K (ca, da) (ca, db) (cc, dc) t (rstep g)).
Qed.

(* In applications [eo] is typically [fun _ _ => eq_refl] (or a pair/unit
   destruct), making the transports in [el]/[er] vanish definitionally.  The
   object component needs the pair match because [prod] has no definitional
   eta. *)
Theorem Funny_strict_eq : @equiv _ (@Functor_StrictEq_Setoid (C □ D) E) H K.
Proof using C D E H K el eo er.
  refine (Functor_StrictEq_intro H K
            (fun x => match x as p return (H p = K p) with
                      | (c, d) => eo c d
                      end) _).
  intros [c1 d1] [c2 d2] t.
  exact (Funny_strict_eq_word t).
Qed.

End FunnyStrictEq.

(* * ** Eta: 函子 out [C □ D] determined generating steps （已译） *)

Corollary Funny_eta {C D E : Category} (H : (C □ D) ⟶ E) :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) E) H (FunnyUP (toSep H)).
Proof.
  apply (Funny_strict_eq H (FunnyUP (toSep H)) (fun _ _ => eq_refl)).
  - intros c c' f d.
    symmetry.
    exact (id_left (@fmap (C □ D) E H (c, d) (c', d) (lstep f))).
  - intros c d d' g.
    symmetry.
    exact (id_left (@fmap (C □ D) E H (c, d) (c, d') (rstep g))).
Qed.

(* * ** Uniqueness half pushout 普遍性质 （已译） *)

Corollary Funny_UP_unique {C D E : Category} {h : C → D → E}
  (S : SepFunctorial h) (H : (C □ D) ⟶ E)
  (eo : ∀ (c : C) (d : D), H (c, d) = h c d)
  (el : ∀ (c c' : C) (f : c ~{C}~> c') (d : D),
      transport (fun z => H (c, d) ~{E}~> z) (eo c' d)
                (@fmap (C □ D) E H (c, d) (c', d) (lstep f))
        ≈ transport_r (fun z => z ~{E}~> h c' d) (eo c d) (sf_lmap S f d))
  (er : ∀ (c : C) (d d' : D) (g : d ~{D}~> d'),
      transport (fun z => H (c, d) ~{E}~> z) (eo c d')
                (@fmap (C □ D) E H (c, d) (c, d') (rstep g))
        ≈ transport_r (fun z => z ~{E}~> h c d') (eo c d) (sf_rmap S c g)) :
  @equiv _ (@Functor_StrictEq_Setoid (C □ D) E) H (FunnyUP S).
Proof.
  apply (Funny_strict_eq H (FunnyUP S) eo).
  - intros c c' f d.
    etransitivity; [ exact (el c c' f d) |].
    apply transport_dom_respects.
    symmetry.
    exact (FunnyUP_lstep S (d:=d) f).
  - intros c d d' g.
    etransitivity; [ exact (er c d d' g) |].
    apply transport_dom_respects.
    symmetry.
    exact (FunnyUP_rstep S (c:=c) g).
Qed.
