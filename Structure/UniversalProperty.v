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

(* * * Universal properties as representability / * * 作为可表示性的泛性质 *)

(*
 nLab: https://ncatlab.org/nlab/show/universal+property
 nLab: https://ncatlab.org/nlab/show/representable+functor
 Wikipedia: https://en.wikipedia.org/wiki/Universal_property
 Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

 A predicate P on the objects of C is a "universal property" when satisfying
 the predicate is equivalent to representing a fixed functor.  Concretely, an
 object c "has the property P" exactly when c represents [repr_functor], i.e.
 there is a natural isomorphism of copresheaves

 [Hom c,─] ≅ repr_functor    (Hom(c, ─) ≅ P, naturally in the target)

 in the functor category [C, Sets].  This is the standard equivalence
 "universal property ⟺ representability": following nLab, a representation of
 a functor F : C ⟶ Sets is a natural isomorphism Hom(c, ─) ≅ F, and by the
 Yoneda lemma it is determined by a single universal element (the image of
 id{C} c).  Wikipedia phrases the same fact as: (A, u) is universal from X to
 F iff Hom(A, ─) ≅ Hom(X, F ─), and the representing object is then unique up
 to unique isomorphism (see [univ_property_unique_up_to_unique_iso] below).

 Here [repr_functor] is covariant, [Hom c,─] = Curried_Hom C c is the
 covariant hom-functor Hom(c, ─), and the per-c isomorphism lives in [Sets]
 (setoids), identifying the setoid of proofs [P c] with the setoid of natural
 isomorphisms [Hom c,─] ≅ [repr_functor].  The claim is not that this captures
 *every* conceivable universal construction, only the representable ones,
 which cover the standard examples. 

 --------
 nLab：https://ncatlab.org/nlab/show/universal+property
 nLab：https://ncatlab.org/nlab/show/representable+functor
 Wikipedia：https://en.wikipedia.org/wiki/Universal_property
 Wikipedia：https://en.wikipedia.org/wiki/Representable_functor

 当满足谓词等价于表示固定函子时，对C的对象的谓词P称为“普遍性质”。具体来说，当且仅当对象c表示[repr_functor]时，c“具有性质P”，即存在余预层的自然同构

 [Hom c,─] ≅ repr_functor （Hom(c, ─) ≅ P，对目标自然同构）在函子范畴 [C, Sets] 中。这是标准的等价关系“泛性质 ⟺ 表示性”：根据 nLab，一个函子 F : C ⟶ Sets 的表示是一个自然同构 Hom(c, ─) ≅ F，并且根据 Yoneda 引理，它由一个唯一的泛元素决定（id{C} c 的像）。维基百科将相同的事实表述为：(A, u) 从 X 到 F 是泛的，当且仅当 Hom(A, ─) ≅ Hom(X, F ─)，然后表示对象在唯一同构意义下是唯一的（见下文 [univ_property_unique_up_to_unique_iso]）。这里 [repr_functor] 是协变的，[Hom c,─] = Curried_Hom C c 是协变同态函子 Hom(c, ─)，而 per-c 同构存在于 [Sets]（集类）中，将证明集类 [P c] 与自然同构的集类 [Hom c,─] ≅ [repr_functor] 对应起来。这里的说法并不是指它抓住了*每一个*可想象的泛构造，仅适用于可表示的那些，这些涵盖了标准的例子。
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
    repr_functor : C ⟶ Sets ;                  (* the functor F = P being represented / 函子 F = P 被表示 *)
    repr_equivalence : forall c : C,           (* proofs of [P c] ≅ representations of F by c / [P c] 的证明 ≅ F 的表示通过 c *)
      @Isomorphism Sets
        (Build_SetoidObject (P c) (eqP c))
        (Build_SetoidObject (Isomorphism [Hom c,─] repr_functor) _)
                                               (* natural isos [Hom c,─] ≅ repr_functor / 自然同态 [Hom c,─] ≅ 代表函子 *)
  }.

(*
 A transformation out of a representable presheaf [Hom ─,c] ⟹ P is fixed by
 its value at id{C} c, the universal element: τ_d(f) ≈ P(f)(τ_c id).  This is
 the computational half of the Yoneda lemma used throughout below. 

 --------
 一个从可表示的预层 [Hom ─,c] ⟹ P 的变换是由其在 id{C} c 上的值固定的，即通用元素：τ_d(f) ≈ P(f)(τ_c id)。这是下面使用的约内达引理的计算部分。
*)
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

(*
 The universal-element form of representability: the set of universal elements
 { x : F c & the Yoneda image of x is an isomorphism } is itself isomorphic to
 the set of natural isomorphisms [Hom ─,c] ≅ F.  This is the contravariant
 (presheaf) counterpart of the representation packaged in [IsUniversalProperty]
 and witnesses that a representation is the same data as a universal element. 

 --------
 可表示性的泛元素形式：泛元素集合 { x : F c 且 x 的 Yoneda 像是同构 } 本身同构于自然同构集合 [Hom ─,c] ≅ F。这是表示在 [IsUniversalProperty] 中打包的表示的对变（预层）对应物，并证明一个表示与一个泛元素是相同的数据。
*)
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

  (*
 A representing object is unique up to isomorphism: given t : P c, every
 other v with a proof Pv is isomorphic to c.  The mediating iso is the
 explicit inverse pair of the two representations — evaluation at the
 identity through the Yoneda embedding — packaged once and for all as
 Functor/Hom/Yoneda/Iso.v's [repr_pair_iso], which this proof consumes
 where it previously inlined the construction. 

 --------
 表示对象在同构意义下是唯一的：给定 t : P c，每一个带有证明 Pv 的其他 v 都与 c 同构。中介同构是两个表示的显式逆元对——通过 Yoneda 嵌入在恒等上进行求值——一次性打包为 Functor/Hom/Yoneda/Iso.v 的 [repr_pair_iso]，此证明在先前内联构造的位置使用了它。
*)
  Proposition univ_property_unique (c : C) (t : P c) : @Unique obj[C] (ob_setoid) P.
  Proof using eqP H.
    exists c ; [exact t |].
    intros v Pv.
    exact (repr_pair_iso (to (repr_equivalence c) t)
                         (to (repr_equivalence v) Pv)).
  Defined.

  (*
 P is invariant under isomorphism: an iso c ≅ d transports a proof of P c to
 a proof of P d, by conjugating the representation of c with the induced
 iso of hom-functors [Hom d,─] ≅ [Hom c,─]. 

 --------
 P 在同构下是不变的：一个同构 c ≅ d 会将 P c 的证明转移为 P d 的证明，通过对 c 的表示与诱导的同构同调函子 [Hom d,─] ≅ [Hom c,─] 进行共轭。
*)
  Proposition univ_property_respects_iso (c d : C) (iso : c ≅ d) : P c -> P d.
  Proof using eqP H.
    intro t.
    rapply (from (repr_equivalence d)).
    apply (Equivalence_Transitive (fobj[C] d) (fobj[C] c)).
    - exact (fobj_iso _ _ _ (iso_sym (Isomorphism_Opposite iso))).
    - apply (to (repr_equivalence c)). exact t.
  Defined.

  (*
 Let c, d be objects in C, and t : P c, s : P d.
 Then there is a unique isomorphism p : c ≈ d
 such that the transport of p along t is equivalent to s. 

 --------
 设 c, d 是 C 中的对象，且 t : P c, s : P d。  
 则存在唯一的同构 p : c ≈ d，  
 使得沿着 t 的 p 的迁移与 s 等价。
*)
  Proposition univ_property_unique_up_to_unique_iso
    (c d : C) (t : P c) (s : P d) :
    Unique (fun p : (c ≅ d) => univ_property_respects_iso c d p t ≈ s).
  Proof.
    (* We have already constructed the isomorphism p. / 我们已经构造了同构 p。 *)
    (*
 We have isomorphisms Hom(c, -) ≅ repr_functor ≅ Hom(d,-)
 corresponding to the choice of t and s, and we
 pull back this isomorphism Hom(c,-) ≅ Hom(d,-) along the
 Yoneda embedding. 

 --------
 我们有同构 Hom(c, -) ≅ repr_functor ≅ Hom(d,-)，对应于 t 和 s 的选择，并且我们沿着 Yoneda 嵌入将这个同构 Hom(c,-) ≅ Hom(d,-) 拉回。
*)
    exists (uniqueness (univ_property_unique c t) d s).
    - (* Why does this isomorphism respect the structure of P? / 为什么这个同构尊重 P 的结构？ *)
      abstract(simpl; unfold univ_property_respects_iso; simpl;
      (*
 Proofs of P d are in one to one correspondence
 with natural isomorphisms
 Hom(d, - ) ≅ repr_functor. 

 --------
 P d 的证明与自然同构 Hom(d, -) ≅ repr_functor 存在一一对应关系。
*)
      (* So it suffices to show that these determine the same natural isomorphism. / 因此，足以证明这些确定了相同的自然同构。 *)
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
    - (* The isomorphism is unique. / 同构是唯一的。 *)
      (* The canonical isomorphism c ≌ d "carrying" t to s is defined as follows: / 将 t “携带”到 s 的典范同构 c ≌ d 定义如下： *)
      (* rep_c : Hom(c, -) ≌ repr_functor / rep_c : Hom(c, -) ≌ repr_functor *)
      (* rep_d : Hom(d, -) ≌ repr_functor / rep_d : Hom(d, -) ≌ 表示函子 *)
      (* rep_c ^-1 ∘ rep_d : Hom(d,-) -> repr_functor -> Hom(c, -) / rep_c ^-1 ∘ rep_d : Hom(d,-) -> repr_functor -> Hom(c, -) *)
      (* " ... " d id_d : Hom(c, d) / d id_d : Hom(c, d) *)
      (* p := rep_c^-1 ∘ rep_d d id_d. / p := rep_c^-1 ∘ rep_d d id_d. *)
      (*
 OTOH, by assumption, we have -
 y(v) : Hom(d, -) ≌ Hom(c, -)
 rep_c : Hom(c, -) ≌ repr_functor
 rep_d : Hom(d, -) ≌ repr_functor 

 --------
 另一方面，根据假设，我们有 -
 y(v) : Hom(d, -) ≌ Hom(c, -)
 rep_c : Hom(c, -) ≌ 表示函子
 rep_d : Hom(d, -) ≌ 表示函子
*)
      (* and the natural isomorphism Hom(d, -) ≌ repr_functor given by / 以及由下式给出的自然同构 Hom(d, -) ≌ repr_functor *)
      (* rep_c ∘ y(v) : Hom(d, -) ≌ Hom(c, -) ≌ repr_functor / rep_c ∘ y(v) : Hom(d, -) ≌ Hom(c, -) ≌ 代表函子 *)
      (* corresonds to s across the bijection. / 对应到双射上的 s。 *)
      (* Of couse since by construction, s also corresponds to rep_d, / 当然，由于通过构造，s 也对应于 rep_d， *)
      (* this means that rep_c ∘ y(v) ≈ rep_d as isomorphisms Hom(d,-) ≈ repr_functor. / 这意味着 rep_c ∘ y(v) ≈ rep_d 作为同构 Hom(d,-) ≈ repr_functor。 *)
      (*
 Thus y(v) ≈ rep_c^-1 ∘ rep_d : Hom(d,-) ≅ Hom(c,-) and in particular
 they agree at (d, id{C} d).  

 --------
 因此 y(v) ≈ rep_c^-1 ∘ rep_d : Hom(d,-) ≅ Hom(c,-)，特别是它们在 (d, id{C} d) 上是一致的。
*)
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
