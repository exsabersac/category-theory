Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Iso.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Groupoid.

(* nLab: https://ncatlab.org/nlab/show/representable+functor
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   「普遍性质」在此文件的形式化：谓词 P 可表（representable）——
   存在函子 F 使 P(c) ≅ (Hom(c,─) ≅ F) 的同构见证。
   终/始对象、积、极限等 UMP 都是这种「可表性」的特例。
   A universal property here = representability of a predicate P.
*)

(*
   关于普遍性质 / On universal properties

   Haskell 直觉：API 由「与外界的关系」定义，而非内部实现——
   例如「积」只承诺 fst/snd/&&& 方程，不规定具体表示。
   本文件偏高级（Yoneda）；初学可先跳过，用 Terminal/Cartesian/Limit 的 UMP。
   Haskell intuition: define by external equations, not internals.
   Advanced (Yoneda); beginners may skip and use concrete UMPs first.
*)

(*
   【Class IsUniversalProperty 语法与字段展开】/ Syntax & field walkthrough

   1) 参数：C 范畴，P : C → Type（「c 满足某结构」），eqP 使 P c 成 Setoid。
      Parameters: category C, predicate P, setoid on proofs of P.

   2) 字段 / Fields
      - repr_functor : C ⟶ Sets  —— 被表示的函子 F
      - repr_equivalence c       —— P c ≅ (Hom(c,─) ≅ F) 的 Sets-同构
        / iso between "P holds at c" and "Hom(c,─) ≅ F"

   3) 推论：univ_property_unique —— 满足 P 的对象在唯一同构下唯一。
      Corollary: objects satisfying P are unique up to unique iso.

   阅读：先 Terminal/Cartesian/Limit 的具体 UMP，再回看本文件。
   Read concrete UMPs first, then return here.
*)

Class IsUniversalProperty (C : Category) (P : C → Type) (eqP : forall c, Setoid (P c)) :=
  {
    repr_functor : C ⟶ Sets ;  (* 被表示的函子 F / functor being represented *)
    repr_equivalence : forall c : C,
      (* P c ≅ (Hom(c,─) ≅ F) / proofs of P ≅ representations *)
      @Isomorphism Sets
        (Build_SetoidObject (P c) (eqP c))
        (Build_SetoidObject (Isomorphism [Hom c,─] repr_functor) _)
  }.

(* Yoneda 预引理 / pre-Yoneda *)
Lemma preyoneda {C : Category} {c d: C} {P : C^op ⟶ Sets} (τ : [Hom ─ , c] ⟹ P) :
  forall f : d ~> c,
    transform τ d f ≈ fmap[P] f (transform τ c id{C}).
Proof.
  intro f. rewrite <- (id_left f) at 1.
  exact (symmetry (naturality τ _ d f) id{C}).
Qed.

#[local] Program Instance exists_setoid (A : Type) (B : Setoid A) (C : A -> Type) :
  Setoid { x : A & C x } :=
  { equiv := fun a b => `1 a ≈ `1 b }.
Local Arguments morphism {x H y H0} s.

(* 可表性 ↔ Yoneda / representability via Yoneda *)
Proposition representability_by_yoneda (C : Category) (F : C^op ⟶ Sets) (c : C):
  @Isomorphism Sets
    {| carrier := { x : F c & IsIsomorphism (from (Yoneda_Lemma C F c ) x) } |}

    (Build_SetoidObject (Isomorphism [Hom ─,c] F) _) .
Proof.
  unshelve econstructor.
  - unshelve econstructor.
    + intros [elt yoneda_is_iso]. unshelve econstructor.
      * exact (from (Yoneda_Lemma C F c) elt).
      * exact (from (IsIsoToIso _ yoneda_is_iso)).
      * apply is_right_inverse.
      * apply is_left_inverse.
    + abstract(intros [eltx x_is_iso] [elty y_is_iso] eltx_eq_elty;
      simpl in eltx_eq_elty;
      apply to_equiv_implies_iso_equiv; simpl;
      intros; rewrite eltx_eq_elty; reflexivity).
  - unshelve econstructor.
    + simpl. intro X; simpl in X. destruct X as [Xto Xfrom tofromid fromtoid]; simpl in *.
      exists (morphism (to (Yoneda_Lemma C F c)) Xto).
      simpl.
      unshelve econstructor.
      * exact Xfrom.
      * abstract(simpl; intros; rewrite <- tofromid; symmetry; apply preyoneda).
      * abstract(simpl; intros; rewrite <- preyoneda; apply fromtoid).
    + abstract(intros x y eq; simpl; destruct eq as [e ?]; simpl in e; apply e).
  - abstract(unshelve econstructor; simpl; intros ? ?;
                   [ symmetry; apply preyoneda | reflexivity ]  ).
  - abstract(simpl; intros [x f]; simpl; set (k := @fmap_id _ _ F);
             simpl in k; apply k).
Defined.

Section UniversalProperty.
  Context (C : Category) (P : obj[C] -> Type) (eqP : forall c, Setoid (P c))
    (H : IsUniversalProperty C P eqP).

  (* 满足 P 的对象唯一 / uniqueness for P *)
  Proposition univ_property_unique (c : C) (t : P c) : @Unique obj[C] (ob_setoid) P.
  Proof using eqP H.
    exists c ; [exact t |].
    intros v Pv.
    exact (repr_pair_iso (to (repr_equivalence c) t)
                         (to (repr_equivalence v) Pv)).
  Defined.

  (* P 沿同构搬运 / P respects isomorphism *)
  Proposition univ_property_respects_iso (c d : C) (iso : c ≅ d) : P c -> P d.
  Proof using eqP H.
    intro t.
    rapply (from (repr_equivalence d)).
    apply (Equivalence_Transitive (fobj[C] d) (fobj[C] c)).
    - exact (fobj_iso _ _ _ (iso_sym (Isomorphism_Opposite iso))).
    - apply (to (repr_equivalence c)). exact t.
  Defined.

  (* 满足 P 的两对象间唯一同构 / unique iso between P-objects *)
  Proposition univ_property_unique_up_to_unique_iso
    (c d : C) (t : P c) (s : P d) :
    Unique (fun p : (c ≅ d) => univ_property_respects_iso c d p t ≈ s).
  Proof.
    (* We have already constructed the isomorphism p.*)
    (* 可表性 ↔ Yoneda / representability via Yoneda *)
    exists (uniqueness (univ_property_unique c t) d s).
    - (* 同构为何尊重 P / why iso respects P *)
      abstract(simpl; unfold univ_property_respects_iso; simpl;
      (* P d ↔ Hom(d,─) ≅ F / proofs of P ↔ natural isos *)
      (* 只需证自然同构相同 / enough to equate the natural isos *)
      rapply (snd (injectivity_is_monic _) (iso_to_monic (repr_equivalence d)));
      set (M := (iso_to_from (repr_equivalence d)));
        simpl in M; rewrite M; clear M;
      apply to_equiv_implies_iso_equiv;
      intros j u; simpl in u;
      simpl;
      set (ab :=  (to (repr_equivalence c )) );
      assert (K := @naturality _ _ _ _ (to (ab t)) _ _ u);
      simpl in K;
      rewrite <- K;
      clear K;
      set (A := iso_to_from (ab t) d); simpl in A; unfold op; rewrite A; clear A;
      set (aj := to (repr_equivalence d ));
      set (aj' := to (aj s));
      change (@id C d) with (@id (C^op) d);
      rewrite <- 2 (@preyoneda (C^op) _ _ repr_functor aj');
               reflexivity).
    - (* The isomorphism is unique. *)
      (* The canonical isomorphism c ≌ d "carrying" t to s is defined as follows: *)
      (* rep_c : Hom(c, -) ≌ repr_functor *)
      (* rep_d : Hom(d, -) ≌ repr_functor *)
      (* rep_c ^-1 ∘ rep_d : Hom(d,-) -> repr_functor -> Hom(c, -) *)
      (* " ... " d id_d : Hom(c, d) *)
      (* p := rep_c^-1 ∘ rep_d d id_d. *)
      (* OTOH, by assumption, we have -
         y(v) : Hom(d, -) ≌ Hom(c, -)
         rep_c : Hom(c, -) ≌ repr_functor
         rep_d : Hom(d, -) ≌ repr_functor *)
      (* 以及 Hom(d,─) ≅ F 的自然同构 / and the natural iso *)
      (* rep_c ∘ y(v) : Hom(d, -)  ≌ Hom(c, -) ≌ repr_functor *)
      (* corresonds to s across the bijection. *)
      (* Of couse since by construction, s also corresponds to rep_d, *)
      (* 故 rep_c ∘ y(v) ≈ rep_d / hence the isos agree *)
      (* Thus y(v) ≈ rep_c^-1 ∘ rep_d : Hom(d,-) ≅ Hom(c,-) and in particular
         they agree at (d, id{C} d).  *)
      abstract(intros v respects_iso;
      simpl uniqueness;
      apply to_equiv_implies_iso_equiv; simpl;
      unfold univ_property_respects_iso, Equivalence_Transitive in respects_iso;
        simpl in respects_iso;
      set (v' := iso_sym (Isomorphism_Opposite v)) in *;
      set (yv := fobj_iso C d c v') in *;
      rewrite <- (id_left (to v));
      change (id{C} ∘ to v) with (to yv d id{C});
      change (from (to (repr_equivalence c) t) d (to (to (repr_equivalence d) s) d id)) with
        (((from (to (repr_equivalence c) t)) ∘ (to (to (repr_equivalence d) s))) d id);
      cut ((iso_sym (to (repr_equivalence c) t)) ⊙ ( (to (repr_equivalence d) s)) ≈ yv);
               [ intro a; destruct a as [a _]; simpl in a; apply a |];
      apply (@proper_morphism _ _ _ _ (to (repr_equivalence d))) in respects_iso;
      assert (K := (iso_to_from (repr_equivalence d)));
      simpl in K; rewrite K in respects_iso; clear K;
      apply (@compose_respects (Groupoid (@Fun.Fun C Sets)) _ _ _
               (iso_sym (to (repr_equivalence c) t)) (iso_sym (to (repr_equivalence c) t))
               (Equivalence_Reflexive _ ))
              in respects_iso;
      rewrite comp_assoc in respects_iso; simpl in respects_iso;
      rewrite iso_sym_left_inverse in respects_iso;
      change iso_id with (@id (Groupoid (@Fun.Fun C Sets)) (fobj[C] c)) in respects_iso;
      rewrite (@id_left (Groupoid (@Fun.Fun C Sets))) in respects_iso;
      symmetry in respects_iso;
      exact respects_iso).
  Defined.
End UniversalProperty.
