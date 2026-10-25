Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Comma-category characterization of adjunctions (Lawvere) / 结合的逗号范畴刻画（Lawvere） *)

(*
 nLab: https://ncatlab.org/nlab/show/adjoint+functor
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 Lawvere's theorem: F ⊣ G iff the comma categories (F ↓ Id[C]) and
 (Id[D] ↓ G) are isomorphic over the projections to the product category
 D ∏ C; that is, the isomorphism commutes with comma_proj.  Here, with
 F : D ⟶ C and G : C ⟶ D, the record [lawvere_equiv] below packages such an
 iso together with its over-D∏C coherence ([projF], [projG], [σ]) and
 extracts from it the hom-set bijection

 φ' : (F a ~> b) ≅ (a ~> G b)

 natural in both a and b (see [lawvere_to_functorial], [lawvere_from_functorial]),
 recovering the classical hom-set definition of an adjunction. 

 --------
 nLab:  https://ncatlab.org/nlab/show/adjoint+functor 
 维基百科:  https://en.wikipedia.org/wiki/Comma_category 

 洛威尔定理: F ⊣ G 当且仅当逗号范畴 (F ↓ Id [C] ) 和
 (Id [D]  ↓ G) 在投影到积范畴 D ∏ C 上同构；也就是说，同构与 comma_proj 交换。这里，给定
 F : D ⟶ C 和 G : C ⟶ D，下方记录 [lawvere_equiv] 将这样的
 同构与其 D∏C 上的一致性 ( [projF] ,  [projG] ,  [σ] ) 打包在一起，并
 从中提取出态射集合的双射

 φ' : (F a ~> b) ≅ (a ~> G b)

 在 a 和 b 上都是自然的（参见 [lawvere_to_functorial] ,  [lawvere_from_functorial] ），
 恢复了伴随的经典态射集合定义。
*)

(*
 Coherence between an iso φ : C ⟶ D (with inverse ψ) and two projections
 πC, πD : _ ⟶ E that it preserves: the unit/counit η, μ paste together with
 the comparison cells κ, θ.  Whiskered along φ and ψ this says φ, ψ are
 compatible "over the projections", the property that makes the comma-category
 iso below an iso over D ∏ C. 

 --------
 一个同构 φ : C ⟶ D（及其逆 ψ）与两个投影 πC, πD : _ ⟶ E 之间的一致性：它保持的单位/余单位 η, μ 与比较单元 κ, θ 粘合在一起。沿着 φ 和 ψ 拍打，这意味着 φ, ψ 在“投影之上”是兼容的，这一性质使得下面的逗号范畴同构在 D ∏ C 上也是同构。
*)
Definition whisker_equiv
           {C D E : Category}
           (φ  : C ⟶ D)
           (ψ  : D ⟶ C)
           (πC : C ⟶ E)
           (πD : D ⟶ E)
           (η  : Id ⟹ ψ ◯ φ)
           (μ  : Id ⟹ φ ◯ ψ)
           (κ  : πC ⟹ πD ◯ φ)
           (θ  : πD ⟹ πC ◯ ψ) :=
  to (nat_α _ _ _) ∙ πC ⊳ η ∙ from (nat_λ _) ≈ (θ ⊲ φ) ∙ κ ∧
  to (nat_α _ _ _) ∙ πD ⊳ μ ∙ from (nat_λ _) ≈ (κ ⊲ ψ) ∙ θ.

Section AdjunctionComma.

(*
 Wikipedia: "Lawvere showed that the functors F : C → D and G : D → C are
 adjoint if and only if the comma categories (F ↓ Id[D]) and (Id[C] ↓ G) are
 isomorphic, and equivalent elements in the comma category can be projected
 onto the same element of C × D. This allows adjunctions to be described
 without involving sets, and was in fact the original motivation for
 introducing comma categories."

 From ncatlab: "To give an adjunction i ⊣ r it suffices to give, for each k
 : x → pe in B ↓ p, an object rk in E such that prk = x and an arrow irk =
 1x → k in B ↓ p that is universal from i to k."

 Lawvere's own statement of the theorem, from his thesis (page 40):

 "For each functor f : A ⟶ B, there exists a functor g : B ⟶ A such that g
 is adjoint to f iff for every object B ∈ |B| there exists an object A ∈ |A|
 and a map φ : B ~> A in B such that for every object A′ ∈ |A| and every
 map x : B ~> A′ in B, there exists a unique map y : A ~> A′ in A such that
 x = φ(yf) in B." 

 --------
 维基百科：“Lawvere 证明了，当且仅当逗号范畴 (F ↓ Id) 和 (Id ↓ G) 同构时，函子 F : C → D 和 G : D → C 是伴随的，并且逗号范畴中相应的元素可以被投影到 C × D 的同一个元素上。这使得伴随可以在不涉及集合的情况下描述，实际上这也是引入逗号范畴的最初动机。”

 来自 ncatlab：“要给出一个伴随 i ⊣ r，对于 B ↓ p 中的每个 k : x → p e，足以给出 E 中的一个对象 rk，使得 prk = x，并且给出一个箭头 irk = 1x → k 在 B ↓ p 中，这个箭头是从 i 到 k 的通用箭头。”

 Lawvere 在其论文（第 40 页）中对该定理的表述：对于每个函子 f : A ⟶ B，都存在一个函子 g : B ⟶ A，使得 g 是 f 的伴随函子，当且仅当对于每个对象 B ∈ |B|，存在一个对象 A ∈ |A| 以及 B 中的一个映射 φ : B ~> A，使得对于每个对象 A′ ∈ |A| 以及 B 中的每个映射 x : B ~> A′，存在唯一的映射 y : A ~> A′ 在 A 中，使得在 B 中有 x = φ(yf)。
*)

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {G : C ⟶ D}.

Definition πD := comma_proj1.
Definition πC := comma_proj2.

#[local] Notation "⟨πD,πC⟩" := comma_proj (at level 0).

Record lawvere_equiv := {
  lawvere_iso : F ↓ Id[C] ≅[Cat] Id[D] ↓ G;   (* the comma iso (F↓Id) ≅ (Id↓G) / 逗号 iso (F↓Id) ≅ (Id↓G) *)

  φ := to lawvere_iso;                         (* forward functor of the iso / 同构的正向函子 *)
  ψ := from lawvere_iso;                       (* backward functor of the iso / iso 的逆向函子 *)

  η x := from (`1 (iso_from_to lawvere_iso) x);  (* ψ◯φ ≅ Id component, as a mor / ψ◯φ ≅ Id 分量，作为一个 mor *)
  μ x := from (`1 (iso_to_from lawvere_iso) x);  (* φ◯ψ ≅ Id component, as a mor / φ◯ψ ≅ Id 分量，作为一个 mor *)

  projF : ⟨πD,πC⟩ ≈ ⟨πD,πC⟩ ◯ φ;               (* φ is over the D∏C projection / φ 在 D∏C 投影上 *)
  projG : ⟨πD,πC⟩ ≈ ⟨πD,πC⟩ ◯ ψ;               (* ψ is over the D∏C projection / ψ 在 D∏C 投影上 *)

  κ := `1 projF;                               (* nat-iso witnessing projF / nat-iso 目击 projF *)
  θ := `1 projG;                               (* nat-iso witnessing projG / nat-iso 见证 projG *)

  σ : @whisker_equiv                           (* η,μ cohere with κ,θ over D∏C / η,μ 在 D∏C 上与 κ,θ 一致 *)
        (F ↓ Id[C]) (Id[D] ↓ G) (D ∏ C)
        (to lawvere_iso) (from lawvere_iso)
        comma_proj comma_proj
        (from (equiv_iso (iso_from_to lawvere_iso)))
        (from (equiv_iso (iso_to_from lawvere_iso)))
        (to (equiv_iso projF))
        (to (equiv_iso projG));

  (*
 The hom-set bijection extracted from the comma iso: transport
 f : F a ~> b through φ, then re-fasten the endpoints to (a, b) using the
 projection comparison κ, landing on a ~> G b. 

 --------
 从逗号同构中提取的 Hom-集双射：通过 φ 传输 f : F a ~> b，然后使用投影比较 κ 将端点重新固定到 (a, b)，落在 a ~> G b 上。
*)
  lawvere_to {a b} (f : F a ~> b) : a ~> G b :=
    let o := ((a, b); f) in
    fmap[G] (snd (from (κ o))) ∘ `2 (φ o) ∘ fst (to (κ o));

  (*
 Its inverse, transporting g : a ~> G b back through ψ via θ. 

 --------
 它的逆，通过 θ 将传输 g : a ~> G b 回到 ψ。
*)
  lawvere_from {a b} (g : a ~> G b) : F a ~> b :=
    let o := ((a, b); g) in
    snd (from (θ o)) ∘ `2 (ψ o) ∘ fmap[F] (fst (to (θ o)));

  φ' {a b} (f : F a ~> b) := lawvere_to f;     (* the forward adjunct ⌊f⌋ / 前置附加成分 ⌊f⌋ *)
  ψ' {a b} (g : a ~> G b) := lawvere_from g     (* the backward adjunct ⌈g⌉ / 后置附加成分 ⌈g⌉ *)
}.

Context `(E : lawvere_equiv).

(*
 Component form of the first conjunct of σ: the unit η factors through the
 projection comparisons κ and θ. 

 --------
 σ 的第一个合取的分量形式：单位 η 通过投影比较 κ 和 θ 分解。
*)
Lemma η_θ_κ : ∀ x, `1 (η E x) ≈ θ E (φ E x) ∘ κ E x.
Proof.
  intros.
  pose proof (σ E).
  destruct X as [X _].
  specialize (X x); simpl in X.
  unfold equiv_iso, η, κ, θ, φ in *.
  destruct (iso_from_to (lawvere_iso E)), (projG E), (projF E).
  destruct X; split.
  - simpl in e2 |- *.
    rewrite <- e2; cat.
  - simpl in e3 |- *.
    rewrite <- e3; cat.
Qed.

(*
 Component form of the second conjunct of σ: the counit μ factors dually. 

 --------
 σ的第二个连词的分量形式：余单位μ以对偶方式分解。
*)
Lemma μ_κ_θ : ∀ x, `1 (μ E x) ≈ κ E (ψ E x) ∘ θ E x.
Proof.
  intros.
  pose proof (σ E).
  destruct X as [_ X].
  specialize (X x); simpl in X.
  unfold equiv_iso, μ, κ, θ, ψ in *.
  destruct (iso_to_from (lawvere_iso E)), (projG E), (projF E).
  destruct X; split.
  - simpl in e2 |- *.
    rewrite <- e2; cat.
  - simpl in e3 |- *.
    rewrite <- e3; cat.
Qed.

(*
 The composite ψ∘φ acts as the identity on the carrier morphism `2 x, the
 morphism-level half of ψ'(φ' f) ≈ f (cf. lawvere_from_to). 

 --------
 复合 ψ∘φ 在承载态射 `2 x 上表现为恒等态射，即 ψ'(φ' f) 在态射层面上约等于 f（参见 lawvere_from_to）。
*)
Theorem ψ_φ_equiv :
  ∀ x, snd (from (κ E x))
         ∘ snd (from (θ E (φ E x)))
         ∘ `2 (ψ E (φ E x))
         ∘ fmap[F] (fst (to (θ E (φ E x))))
         ∘ fmap[F] (fst (to (κ E x)))
         ≈ `2 x.
Proof.
  intros [[a b] f]; simpl in f |- *.
  rewrite (snd_comp _ _ _ (κ E ((a, b); f))⁻¹ (θ E (φ E _))⁻¹).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite (fst_comp _ _ _ (θ E (φ E _)) (κ E ((a, b); f))).
  rewrite <- η_θ_κ.
  rewrite (`2 (η E ((a, b); f))).
  rewrite η_θ_κ.
  rewrite comp_assoc.
  rewrite (snd_comp _ _ _
             ((κ E _)⁻¹ ∘ (θ E (φ E _))⁻¹)
             (θ E (φ E _) ∘ κ E ((a, b); f))).
  rewrite <- comp_assoc.
  rewrite (comp_assoc (θ E (φ E ((a, b); f)))⁻¹ _).
  rewrite iso_from_to, id_left.
  now rewrite iso_from_to; cat.
Qed.

(*
 Dual: φ∘ψ acts as the identity on the carrier morphism, the morphism-level
 half of φ'(ψ' g) ≈ g (cf. lawvere_to_from). 

 --------
 对偶：φ∘ψ 在载体态射上作用为恒等，态射层面的 φ'(ψ' g) ≈ g（参见 lawvere_to_from）。
*)
Theorem φ_ψ_equiv :
  ∀ x, fmap[G] (snd (from (θ E x)))
         ∘ fmap[G] (snd (from (κ E (ψ E x))))
         ∘ `2 (φ E (ψ E x))
         ∘ fst (to (κ E (ψ E x)))
         ∘ fst (to (θ E x))
         ≈ `2 x.
Proof.
  intros [[a b] f]; simpl in f |- *.
  rewrite <- fmap_comp.
  rewrite (snd_comp _ _ _ (θ E ((a, b); f))⁻¹ (κ E (ψ E _))⁻¹).
  rewrite <- !comp_assoc.
  rewrite (fst_comp _ _ _ (κ E (ψ E _)) (θ E ((a, b); f))).
  rewrite <- μ_κ_θ.
  rewrite (`2 (μ E ((a, b); f))).
  rewrite μ_κ_θ.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (snd_comp _ _ _
             ((θ E _)⁻¹ ∘ (κ E (ψ E _))⁻¹)
             (κ E (ψ E _) ∘ θ E ((a, b); f))).
  rewrite <- comp_assoc.
  rewrite (comp_assoc (κ E (ψ E ((a, b); f)))⁻¹ _).
  rewrite iso_from_to, id_left.
  now rewrite iso_from_to; cat.
Qed.

(*
 φ, being a functor, carries isomorphisms to isomorphisms (via fobj_iso). 

 --------
 φ，作为一个函子，会将同构映射到同构（通过 fobj_iso）。
*)
Program Instance to_lawvere_iso_Proper :
  Proper (Isomorphism ==> Isomorphism) (φ E).
Next Obligation.
  proper.
  construct.
  - exact (fmap[φ E] (to X)).
  - exact (fmap[φ E] (from X)).
  - exact (iso_to_from (@fobj_iso _ _ (φ E) _ _ X)).
  - exact (iso_from_to (@fobj_iso _ _ (φ E) _ _ X)).
Qed.

(* Dually, ψ carries isomorphisms to isomorphisms. / 同样地，ψ 将同构映射到同构。 *)
Program Instance from_lawvere_iso_Proper :
  Proper (Isomorphism ==> Isomorphism) (ψ E).
Next Obligation.
  proper.
  construct.
  - exact (fmap[ψ E] (to X)).
  - exact (fmap[ψ E] (from X)).
  - exact (iso_to_from (@fobj_iso _ _ (ψ E) _ _ X)).
  - exact (iso_from_to (@fobj_iso _ _ (ψ E) _ _ X)).
Qed.

(* The forward adjunct φ' respects ≈ on hom-sets. / 前向附加 φ' 尊重 Hom 集上的 ≈。 *)
Program Instance lawvere_to_Proper {a b} :
  Proper (equiv ==> equiv) (@φ' E a b).
Next Obligation.
  proper.
  unfold φ', lawvere_to.
  given (ff : ((a, b); x) ~{ F ↓ Id[C] }~> ((a, b); y)). {
    now refine ((id, id); _); abstract cat.
  }
  spose (`2 (projF E) ((a, b); x) ((a, b); y) ff) as H0.
  destruct H0 as [H1 H2].
  symmetry.
  rewrite <- id_right.
  rewrite H1; clear H1.
  comp_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fst _) _).
  spose (iso_to_from (κ E ((a, b); y))) as H0.
  destruct H0 as [H3 _].
  unfold κ in H3.
  rewrite H3; clear H3.
  rewrite id_left.
  symmetry.
  rewrite <- (id_left (snd _)).
  rewrite H2; clear H2.
  rewrite !fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap (snd (to (κ E ((a, b); x)))))).
  rewrite <- fmap_comp.
  spose (iso_to_from (κ E ((a, b); x))) as H0.
  destruct H0 as [_ H4].
  rewrite H4; clear H4.
  rewrite fmap_id, id_left.
  remember (fmap[to (lawvere_iso E)] _) as o.
  destruct o.
  symmetry.
  apply e.
Qed.

(* Dually, the backward adjunct ψ' respects ≈. / 同样，后向附加成分 ψ' 遵循 ≈。 *)
Program Instance lawvere_from_Proper {a b} :
  Proper (equiv ==> equiv) (@ψ' E a b).
Next Obligation.
  proper.
  unfold ψ', lawvere_from.
  spose (θ E) as H.
  given (ff : ((a, b); x) ~{ Id[D] ↓ G }~> ((a, b); y)). {
    now refine ((id, id); _); abstract cat.
  }
  spose (`2 (projG E) ((a, b); x) ((a, b); y) ff) as H0.
  destruct H0 as [H1 H2].
  rewrite <- id_left.
  rewrite H2; clear H2.
  comp_left.
  rewrite (comp_assoc (snd (to (θ E ((a, b); x)))) (snd _)).
  spose (iso_to_from (θ E ((a, b); x))) as H0.
  destruct H0 as [_ H3].
  rewrite H3; clear H3.
  rewrite id_left.
  symmetry.
  rewrite <- (id_right (fst _)).
  rewrite H1; clear H1.
  rewrite comp_assoc.
  spose (iso_to_from (θ E ((a, b); y))) as H0.
  destruct H0 as [H4 _].
  rewrite comp_assoc.
  rewrite H4; clear H4.
  rewrite !fmap_comp.
  comp_right.
  rewrite fmap_id, id_right.
  remember (fmap[from (lawvere_iso E)] _) as o.
  destruct o.
  apply e.
Qed.

(*
 Fold a product-category composite of first/second components back into the
 component of the composite (fst_comp / snd_comp). 

 --------
 将一个产品类别复合体的第一个/第二个组件折叠回复合体的组件（fst_comp / snd_comp）。
*)
Ltac pair_comp :=
  match goal with
  | [ |- context[@fst _ _ ?F ∘ @fst _ _ ?G] ] =>
    rewrite (@fst_comp _ _ _ _ _ F G)
  | [ |- context[@snd _ _ ?F ∘ @snd _ _ ?G] ] =>
    rewrite (@snd_comp _ _ _ _ _ F G)
  end.

Arguments φ' l {_ _} _.
Arguments ψ' l {_ _} _.

(*
 φ((a,b);f) is isomorphic in (Id[D] ↓ G) to the normal form ((a,b); φ' f),
 re-fastened to the original endpoints (a, b) via κ. 

 --------
 φ((a,b);f) 在 (Id [D] ↓ G) 中同构于正规形式 ((a,b); φ' f)，通过 κ 重新固定到原始端点 (a, b)。
*)
Lemma lawvere_iso_to {a b} (f : F a ~> b) :
  φ E ((a, b); f) ≅ ((a, b); φ' E f).
Proof.
  construct.
  - exists (from (κ E ((a, b); f))).
    abstract
      (unfold φ', lawvere_to;
       rewrite <- !comp_assoc;
       pair_comp;
       rewrite iso_to_from;
       simpl fst;
       now rewrite id_right).
  - exists (to (κ E ((a, b); f))).
    abstract
      (unfold φ', lawvere_to;
       rewrite !comp_assoc;
       rewrite <- !fmap_comp;
       pair_comp;
       rewrite iso_to_from;
       simpl snd;
       now rewrite fmap_id, id_left).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_from_to).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_to_from).
Defined.

(*
 Dually, ψ((a,b);g) ≅ ((a,b); ψ' g) in (F ↓ Id[C]), via θ. 

 --------
 同样地，在 (F ↓ Id [C] ) 中，通过 θ，有 ψ((a,b);g) ≅ ((a,b); ψ' g)。
*)
Lemma lawvere_iso_from {a b} (g : a ~> G b) :
  ψ E ((a, b); g) ≅ ((a, b); ψ' E g).
Proof.
  construct.
  - exists (from (θ E ((a, b); g))).
    abstract
      (unfold ψ', lawvere_from;
      rewrite <- !comp_assoc;
      rewrite <- !fmap_comp;
      pair_comp;
      rewrite iso_to_from;
      simpl fst;
      now rewrite fmap_id, id_right).
  - exists (to (θ E ((a, b); g))).
    abstract
      (unfold ψ', lawvere_from;
       rewrite !comp_assoc;
       pair_comp;
       rewrite iso_to_from;
       simpl snd;
       now rewrite id_left).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_from_to).
  - abstract
      (simpl;
       split; pair_comp;
       now rewrite iso_to_from).
Defined.

(*
 Compose the two normal-form isos: ψ(φ((a,b);f)) ≅ ((a,b); ψ'(φ' f)). 

 --------
 将两个规范形式的等角合成：ψ(φ((a,b);f)) ≅ ((a,b); ψ'(φ' f))。
*)
Lemma lawvere_iso_from_to {a b} (f : F a ~> b) :
  ψ E (φ E ((a, b); f)) ≅ ((a, b); ψ' E (φ' E f)).
Proof.
  refine (iso_compose (lawvere_iso_from (φ' E f)) _).
  apply fobj_iso.
  now apply lawvere_iso_to.
Qed.

(*
 Dually, φ(ψ((a,b);g)) ≅ ((a,b); φ'(ψ' g)). 

 --------
 同样地，φ(ψ((a,b);g)) ≅ ((a,b); φ'(ψ' g))。
*)
Definition lawvere_iso_to_from {a b} (g : a ~> G b) :
  φ E (ψ E ((a, b); g)) ≅ ((a, b); φ' E (ψ' E g)).
Proof.
  refine (iso_compose (lawvere_iso_to (ψ' E g)) _).
  apply fobj_iso.
  now apply lawvere_iso_from.
Qed.

(*
 Round-trip on the (Id[D] ↓ G) side: ((a,b); φ'(ψ' g)) ≅ ((a,b); g), using
 the comma iso's own iso_to_from.  Underlies φ'(ψ' g) ≈ g. 

 --------
 在 (Id [D]  ↓ G) 侧的往返：((a,b); φ'(ψ' g)) ≅ ((a,b); g)，使用逗号同构自身的 iso_to_from。支撑 φ'(ψ' g) ≈ g。
*)
Definition lawvere_to_from_iso {a b} (g : a ~> G b) :
  ((a, b); φ' E (ψ' E g)) ≅[Id[D] ↓ G] ((a, b); g) :=
  iso_compose (`1 (iso_to_from (lawvere_iso E)) ((a, b); g))
              (iso_sym (@lawvere_iso_to_from _ _ g)).

(*
 Dual round-trip on the (F ↓ Id[C]) side, underlying ψ'(φ' f) ≈ f. 

 --------
 在 (F ↓ Id [C]) 侧的双重往返，底层 ψ'(φ' f) ≈ f。
*)
Definition lawvere_from_to_iso {a b} (f : F a ~> b) :
  ((a, b); ψ' E (φ' E f)) ≅[F ↓ Id[C]] ((a, b); f) :=
  iso_compose (`1 (iso_from_to (lawvere_iso E)) ((a, b); f))
              (iso_sym (@lawvere_iso_from_to _ _ f)).

(*
 Naturality of the forward adjunct in both variables: this is the hom-set
 adjunction naturality square Φ(j ∘ f ∘ F i) = G j ∘ Φ(f) ∘ i
 (Wikipedia: Hom(i, G j) ∘ Φ = Φ ∘ Hom(F i, j)). 

 --------
 两个变量中前附加的自然性：这是同构集伴随的自然性方形 Φ(j ∘ f ∘ F i) = G j ∘ Φ(f) ∘ i （维基百科：Hom(i, G j) ∘ Φ = Φ ∘ Hom(F i, j)）。
*)
Lemma lawvere_to_functorial {a b} (f : F a ~{C}~> b)
      {a' b'} (i : a' ~> a) (j : b ~> b') :
  φ' E (j ∘ f ∘ fmap[F] i) ≈ fmap[G] j ∘ φ' E f ∘ i.
Proof.
  (* φ'(j ∘ f ∘ Fi) = φ'(j ∘ f) ∘ i *)

  given (Fi : ((a', b'); j ∘ f ∘ fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b'); j ∘ f)). {
    now refine ((i, id); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_to (j ∘ f))
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (j ∘ f ∘ fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', b'); j ∘ f ∘ fmap[F] i) ((a, b'); j ∘ f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite fmap_id, id_left in H.
  rewrite <- H.
  clear Fi H.

  (*                = G(j ∘ f) ∘ φ'(Fi) *)

  given (Fi : ((a', F a); fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b'); j ∘ f)). {
    now refine ((i, j ∘ f); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_to (j ∘ f))
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', F a); fmap[F] i) ((a, b'); j ∘ f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite H.
  clear Fi H.

  (*                = Gj ∘ Gf ∘ φ'(Fi) *)

  rewrite fmap_comp.

  (*                = Gj ∘ φ'(f) ∘ i *)

  given (Fi : ((a', F a); fmap[F] i) ~{ F ↓ Id[C] }~> ((a, b); f)). {
    now refine ((i, f); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_to f)
                ∘ fmap[φ E] Fi
                ∘ from (lawvere_iso_to (fmap[F] i)))) as H.
  spose (`2 (projF E) ((a', F a); fmap[F] i) ((a, b); f) Fi) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- comp_assoc.
  rewrite <- H.
  now cat.
Qed.

(*
 Dual naturality of the backward adjunct: j ∘ Φ⁻¹(g) ∘ F i = Φ⁻¹(G j ∘ g ∘ i). 

 --------
 后向附加子的双重自然性：j ∘ Φ⁻¹(g) ∘ F i = Φ⁻¹(G j ∘ g ∘ i)。
*)
Lemma lawvere_from_functorial {a b} (g : a ~{D}~> G b)
      {a' b'} (i : a' ~> a) (j : b ~> b') :
  j ∘ ψ' E g ∘ fmap[F] i ≈ ψ' E (fmap[G] j ∘ g ∘ i).
Proof.
  (* ψ'(Gj ∘ g ∘ i) = j ∘ ψ'(g ∘ i) *)

  given (Gj : ((a', b); g ∘ i) ~{ Id[D] ↓ G }~> ((a', b'); fmap[G] j ∘ g ∘ i)). {
    now refine ((id, j); _); simpl; abstract cat.
  }
  spose (`2 (to (lawvere_iso_from (fmap[G] j ∘ g ∘ i))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g ∘ i)))) as H.
  spose (`2 (projG E) ((a', b); g ∘ i) ((a', b'); fmap[G] j ∘ g ∘ i) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite fmap_id, id_right in H.
  rewrite H.
  clear Gj H.

  (*                = ψ'(Gj) ∘ F(g ∘ i) *)

  given (Gj : ((a', b); g ∘ i) ~{ Id[D] ↓ G }~> ((G b, b'); fmap[G] j)). {
    now refine ((g ∘ i, j); _); simpl; abstract cat.
  }
  spose (`2 (to (lawvere_iso_from (fmap[G] j))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g ∘ i)))) as H.
  spose (`2 (projG E) ((a', b); g ∘ i) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  clear Gj H.

  (*                = ψ'(Gj) ∘ Fg ∘ Fi *)

  rewrite fmap_comp.

  (*                = Gj ∘ ψ'(f) ∘ i *)

  given (Gj : ((a, b); g) ~{ Id[D] ↓ G }~> ((G b, b'); fmap[G] j)). {
    now refine ((g, j); _); abstract cat.
  }
  spose (`2 (to (lawvere_iso_from (fmap[G] j))
                ∘ fmap[ψ E] Gj
                ∘ from (lawvere_iso_from (g)))) as H.
  spose (`2 (projG E) ((a, b); g) ((G b, b'); fmap[G] j) Gj) as H1.
  destruct H1 as [H1 H2].
  rewrite <- H1 in H; clear H1.
  rewrite <- H2 in H; clear H2.
  rewrite <- H.
  now cat.
Qed.

(*
 Surjective pairing for comma objects: a comma object is recovered from its
 two D∏C components and its carrier morphism.  This is a structural identity
 on the underlying sigma (hence Leibniz =, not ≈), used to re-expand objects
 under the projections. 

 --------
 逗号对象的满配对：一个逗号对象可以从它的两个 D∏C 分量以及它的承载态射中恢复。这是在底层 sigma 上的一个结构性恒等式（因此是 Leibniz =，而不是 ≈），用于在投影下重新展开对象。
*)
Lemma surjective_tripleF (p : obj[F ↓ Id[C]]) :
  ((fst `1 p, snd `1 p); `2 p) = p.
Proof.
  destruct p; simpl; simpl_eq.
  destruct x; reflexivity.
Qed.

Lemma surjective_tripleG (p : obj[Id[D] ↓ G]) :
  ((fst `1 p, snd `1 p); `2 p) = p.
Proof.
  destruct p; simpl_eq.
  destruct x; reflexivity.
Qed.

(*
 Auxiliary re-expansion lemmas: under φ (resp. ψ) a comma object may be
 replaced by its surjective-pairing normal form without changing the value.
 Stated for completeness; not used by the development below. 

 --------
 辅助重扩展引理：在 φ（分别为 ψ）下，逗号对象可以被其满射配对标准形式替代而不改变值。为完整性而陈述；下面的推导中未使用。
*)
Lemma expand_φ_ψ {a b} (g : a ~> G b) :
  φ E (ψ E ((a, b); g))
    ≈
  φ E
    ((fst `1 ((lawvere_iso E)⁻¹ ((a, b); g)),
      snd `1 ((lawvere_iso E)⁻¹ ((a, b); g)));
       `2 ((lawvere_iso E)⁻¹ ((a, b); g))).
Proof. now rewrite surjective_tripleF. Qed.

Lemma expand_ψ_φ {a b} (f : F a ~> b) :
  ψ E (φ E ((a, b); f))
    ≈
  ψ E
    ((fst `1 (φ E ((a, b); f)),
      snd `1 (φ E ((a, b); f)));
       `2 (φ E ((a, b); f))).
Proof. now rewrite surjective_tripleG. Qed.

(*
 Given that:

 π₁((A,B);f) = (A,B)
 = π₁(φ((A,B);f)) = π₁(ψ((A,B);f))       [projF, projG]
 φ((A,B);f) ≅ ((A,B);φ'(f))                [lawvere_iso_to]
 ψ((A,B);f) ≅ ((A,B);ψ'(f))                [lawvere_iso_from]
 φ(ψ(f)) ≈ f and ψ(φ(f)) ≈ f               [lawvere_iso]

 it follows that:

 φ'(ψ'(f)) ≈ f and ψ'(φ'(f)) ≈ f 

 --------
 鉴于：

 π₁((A,B);f) = (A,B)
 = π₁(φ((A,B);f)) = π₁(ψ((A,B);f))        [projF, projG] 
 φ((A,B);f) ≅ ((A,B);φ'(f))                 [lawvere_iso_to] 
 ψ((A,B);f) ≅ ((A,B);ψ'(f))                 [lawvere_iso_from] 
 φ(ψ(f)) ≈ f 和 ψ(φ(f)) ≈ f                [lawvere_iso] 

 因此得出：

 φ'(ψ'(f)) ≈ f 和 ψ'(φ'(f)) ≈ f
*)

Lemma lawvere_to_from {a b} (g : a ~> G b) : φ' E (ψ' E g) ≈ g.
Proof.
  intros.
  unfold φ', ψ'.
  pose proof (@lawvere_to_functorial
                _ _ (`2 (fobj[(lawvere_iso E)⁻¹] ((a, b); g)))
                a b
                (fst (to (`1 (projG E) ((a, b); g))))
                (snd (`1 (projG E) ((a, b); g))⁻¹)) as X.
  etransitivity.
  - now apply X.
  - clear X.
    symmetry.
    etransitivity.
    + spose (φ_ψ_equiv ((a, b); g)) as X1.
      symmetry in X1.
      now apply X1.
    + apply compose_respects; [|reflexivity].
      rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      spose (surjective_tripleF (ψ E ((a, b); g))) as X2.
      unfold ψ in *.
      simpl.
      rewrite <- X2.
      solve [ reflexivity           (* works in >=8.12 *)
            | simpl;                (* needed for <8.11 / 需要用于 <8.11 *)
              unfold lawvere_to, θ, κ, ψ;
              rewrite !comp_assoc;
              reflexivity
            ].
Qed.

(*
 Dual round-trip: the backward adjunct inverts the forward one. 

 --------
 双向往返：后向附加成分会颠倒前向附加成分。
*)
Lemma lawvere_from_to {a b} (f : F a ~> b) : ψ' E (φ' E f) ≈ f.
Proof.
  intros.
  unfold φ', ψ'.
  pose proof (@lawvere_from_functorial
                _ _ (`2 (fobj[to (lawvere_iso E)] ((a, b); f)))
                a b
                (fst (to (`1 (projF E) ((a, b); f))))
                (snd (`1 (projF E) ((a, b); f))⁻¹)) as X.
  etransitivity.
  - symmetry.
    now apply X.
  - clear X.
    symmetry.
    etransitivity.
    + spose (ψ_φ_equiv ((a, b); f)) as X1.
      symmetry in X1.
      now apply X1.
    + unfold θ, κ, ψ.
      apply compose_respects; [|reflexivity].
      rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      spose (surjective_tripleG (φ E ((a, b); f))) as X2.
      unfold φ in *.
      simpl.
      rewrite <- X2.
      solve [ reflexivity           (* works in >=8.12 *)
            | simpl;                (* needed for <8.11 / 需要用于 <8.11 *)
              unfold lawvere_to, θ, κ, ψ;
              rewrite !comp_assoc;
              reflexivity
            ].
Qed.

(*
 The extracted hom-set bijection Hom_C(F a, b) ≅ Hom_D(a, G b), packaged as a
 Sets-isomorphism with the two adjuncts φ' and ψ' as its legs.  This is the
 classical hom-set datum of an adjunction. 

 --------
 提取的同集双射 Hom_C(F a, b) ≅ Hom_D(a, G b)，被包装为一个集合同构，其两条支腿是两个伴随 φ' 和 ψ'。这是伴随的经典同集数据。
*)
Program Instance lawvere_morph_iso {a b} : F a ~> b ≊ a ~> G b := {
  to   := {| morphism := φ' E; proper_morphism := lawvere_to_Proper |};
  from := {| morphism := ψ' E; proper_morphism := lawvere_from_Proper |};
  iso_to_from := lawvere_to_from;
  iso_from_to := lawvere_from_to
}.

(*
 Naturality of the bijection in both variables, restated for the packaged
 iso: φ'(j ∘ f ∘ F i) ≈ G j ∘ φ'(f) ∘ i (cf. lawvere_to_functorial). 

 --------
 在两个变量中的双射的自然性，针对封装的同构重述：φ'(j ∘ f ∘ F i) ≈ G j ∘ φ'(f) ∘ i（参见 lawvere_to_functorial）。
*)
Corollary lawvere_to_morph_iso_functorial {a b} (f : F a ~{C}~> b)
          {a' b'} (i : a' ~> a) (j : b ~> b') :
  to lawvere_morph_iso (j ∘ f ∘ fmap[F] i)
    ≈ fmap[G] j ∘ to lawvere_morph_iso f ∘ i.
Proof. now apply lawvere_to_functorial. Qed.

(*
 Dual naturality for the inverse leg (cf. lawvere_from_functorial). 

 --------
 逆腿的双重自然性（参见 lawvere_from_functorial）。
*)
Corollary lawvere_from_morph_iso_functorial {a b} (g : a ~{D}~> G b)
          {a' b'} (i : a' ~> a) (j : b ~> b') :
  j ∘ from lawvere_morph_iso g ∘ fmap[F] i
    ≈ from lawvere_morph_iso (fmap[G] j ∘ g ∘ i).
Proof. now apply lawvere_from_functorial. Qed.

(*
 Diagonal embedding of D into (F ↓ Id[C]) sending a to the object
 (a, F a; id[F a]); its carrier id[F a] is the seed whose forward adjunct is
 the unit (see lawvere_eqv_unit). 

 --------
 将 D 对角嵌入到 (F ↓ Id [C]) 中，发送 a 到对象 (a, F a; id [F a])；其承载者 id [F a] 是种子，其前向伴随是单元（参见 lawvere_eqv_unit）。
*)
Program Definition Left_Functor : D ⟶ (F ↓ Id[C]) := {|
  fobj := fun x : D => ((x, F x); id[F x]);
  fmap := fun _ _ f => ((f, fmap[F] f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. split; [ reflexivity | apply fmap_comp ]. Qed.

(*
 Dually, embedding of C into (Id[D] ↓ G) sending a to (G a, a; id[G a]);
 its carrier id[G a] seeds the counit (see lawvere_eqv_counit). 

 --------
 类似地，将 C 嵌入到 (Id [D]  ↓ G) 中，发送 a 到 (G a, a; id [G a]); 它的承载体 id [G a] 引出余单位（参见 lawvere_eqv_counit）。
*)
Program Definition Right_Functor : C ⟶ (Id[D] ↓ G) := {|
  fobj := fun x : C => ((G x, x); id[G x]);
  fmap := fun _ _ f => ((fmap[G] f, f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation. split; [ apply fmap_comp | reflexivity ]. Qed.

(*
 Unit η_a := φ'(id[F a]), the forward adjunct of the identity; this is the
 universal arrow a ~> G (F a). 

 --------
 单位 η_a := φ'(id [F a])，恒等式的前向伴随；这是从 a 到 G(F a) 的通用箭头。
*)
Definition lawvere_eqv_unit {a} : a ~{ D }~> G (F a) :=
  to lawvere_morph_iso (`2 (Left_Functor a)).

(*
 Counit ε_a := ψ'(id[G a]), the backward adjunct of the identity; the
 universal arrow F (G a) ~> a. 

 --------
 余单位 ε_a := ψ'(id [G a])，恒等映射的后向伴随；从 F(G a) 到 a 的泛箭头。
*)
Definition lawvere_eqv_counit {a} : F (G a) ~{ C }~> a :=
  from lawvere_morph_iso (`2 (Right_Functor a)).

(*
 First triangle (zig-zag) identity: ε_{F a} ∘ F(η_a) ≈ id[F a]. 

 --------
 第一个三角形（之字形）恒等式：ε_{F a} ∘ F(η_a) ≈ id [F a] 。
*)
Lemma lawvere_eqv_counit_fmap_unit {a} :
  lawvere_eqv_counit ∘ fmap[F] lawvere_eqv_unit ≈ id[F a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  rewrite <- id_left.
  rewrite comp_assoc.
  rewrite lawvere_from_morph_iso_functorial.
  simpl (`2 _).
  rewrite fmap_id, !id_left.
  now sapply (iso_from_to (@lawvere_morph_iso a (F a))).
Qed.

(*
 Second triangle (zig-zag) identity: G(ε_a) ∘ η_{G a} ≈ id[G a]. 

 --------
 第二个三角形（之字形）恒等式：G(ε_a) ∘ η_{G a} ≈ id [G a] 。
*)
Lemma lawvere_eqv_fmap_counit_unit {a} :
  fmap[G] lawvere_eqv_counit ∘ lawvere_eqv_unit ≈ id[G a].
Proof.
  simpl; intros.
  unfold lawvere_eqv_counit, lawvere_eqv_unit.
  rewrite <- (id_right (to lawvere_morph_iso _)).
  rewrite comp_assoc.
  rewrite <- lawvere_to_morph_iso_functorial.
  simpl (`2 _).
  rewrite fmap_id, !id_right.
  now sapply (iso_to_from (@lawvere_morph_iso (G a) a)).
Qed.

(*
 Naturality of the unit: the underlying square for η as a transformation
 Id ⟹ G ◯ F, obtained by transporting f through the comma projection. 

 --------
 单位的自然性：η 作为一个变换的基础方形 Id ⟹ G ◯ F，是通过逗号投射传递 f 得到的。
*)
Lemma Left_Functoriality
      x y (f : comma_proj (Left_Functor x) ~> comma_proj (Left_Functor y)) :
  fmap[G] (fmap[F] (fst f))
    ∘ (fmap[G] (snd (κ E (Left_Functor x))⁻¹)
         ∘ `2 (φ E (Left_Functor x))
         ∘ fst (to (κ E (Left_Functor x))))
    ≈ fmap[G] (snd (κ E (Left_Functor y))⁻¹)
        ∘ `2 (φ E (Left_Functor y))
        ∘ fst (to (κ E (Left_Functor y)))
        ∘ fst f.
Proof.
  Opaque Left_Functor.
  given (ff : (Left_Functor x) ~{ F ↓ Id[C] }~> (Left_Functor y)). {
    exists (fst f, fmap[F] (fst f)).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  }
  destruct (`2 (projF E) (Left_Functor x) (Left_Functor y) ff).
  srewrite e0.
  do 2 rewrite fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap[G] (snd (to (κ E (Left_Functor x)))))).
  rewrite <- fmap_comp.
  rewrite (snd (iso_to_from (κ E (Left_Functor x)))).
  simpl snd.
  rewrite fmap_id.
  rewrite id_left.
  symmetry.
  spose (`2 (fmap[φ E] ff)) as X.
  rewrite !comp_assoc.
  rewrite <- X.
  comp_left.
  srewrite e.
  comp_right.
  rewrite (fst (iso_to_from (κ E (Left_Functor y)))).
  rewrite id_left.
  reflexivity.
Qed.

(*
 Dually, naturality of the counit ε as a transformation F ◯ G ⟹ Id. 

 --------
 同样，余单位 ε 作为变换 F ◯ G ⟹ Id 的自然性。
*)
Lemma Right_Functoriality
      x y (f : comma_proj (Right_Functor x) ~> comma_proj (Right_Functor y)) :
  snd f ∘ (snd (θ E (Right_Functor x))⁻¹
        ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor x))
        ∘ fmap[F] (fst (to (θ E (Right_Functor x)))))
  ≈ snd (θ E (Right_Functor y))⁻¹
      ∘ `2 ((lawvere_iso E)⁻¹ (Right_Functor y))
      ∘ fmap[F] (fst (to (θ E (Right_Functor y))))
      ∘ fmap[F] (fmap[G] (snd f)).
Proof.
  Opaque Right_Functor.
  given (ff : (Right_Functor x) ~{ Id[D] ↓ G }~> (Right_Functor y)). {
    exists (fmap[G] (snd f), snd f).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  }
  destruct (`2 (projG E) (Right_Functor x) (Right_Functor y) ff).
  symmetry.
  srewrite e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite (fst (iso_to_from (θ E (Right_Functor y)))).
  rewrite id_left.
  symmetry.
  srewrite e0.
  comp_left.
  rewrite (comp_assoc (snd (to (θ E (Right_Functor x))))).
  rewrite (snd (iso_to_from (θ E (Right_Functor x)))).
  rewrite id_left.
  rewrite fmap_comp.
  comp_right.
  symmetry.
  apply (`2 (fmap[ψ E] ff)).
Qed.

(*
 The unit assembled as a natural transformation Id ⟹ G ◯ F. 

 --------
 该单位组装为一个自然变换 Id ⟹ G ◯ F。
*)
Program Definition lawvere_eqv_unit_transform : Id ⟹ G ◯ F := {|
  transform := @lawvere_eqv_unit;
  naturality := fun x y f =>
    Left_Functoriality x y (f, fmap[F] f);
  naturality_sym := fun x y f =>
    symmetry (Left_Functoriality x y (f, fmap[F] f))
|}.

(*
 The counit assembled as a natural transformation F ◯ G ⟹ Id. 

 --------
 余单位组装为一个自然变换 F ◯ G ⟹ Id。
*)
Program Definition lawvere_eqv_counit_transform : F ◯ G ⟹ Id := {|
  transform := @lawvere_eqv_counit;
  naturality := fun x y f =>
    Right_Functoriality x y (fmap[G] f, f);
  naturality_sym := fun x y f =>
    symmetry (Right_Functoriality x y (fmap[G] f, f))
|}.

(*
 The forward direction of Lawvere's theorem: a genuine adjunction H : F ⊣ G
 induces the comma iso, sending ((d,c); f : F d ~> c) to ((d,c); ⌊f⌋), the
 square condition following from naturality of the transpose. 

 --------
 Lawvere 定理的正向方向：一个真正的伴随 H : F ⊣ G 引入了逗号范畴同构，将 ((d,c); f : F d ~> c) 发送为 ((d,c); ⌊f⌋)，方形条件由换位的自然性得出。
*)
Program Definition Comma_Functor_F_Id_Id_G (H : F ⊣ G) :
  (F ↓ Id[C]) ⟶ (Id[D] ↓ G) := {|
  fobj := fun x => (``x; to adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- to_adj_nat_r;
  rewrite <- X;
  rewrite <- to_adj_nat_l;
  reflexivity.
Qed.

(*
 Its inverse functor, sending ((d,c); g : d ~> G c) to ((d,c); ⌈g⌉). 

 --------
 它的逆函子，将 ((d,c); g : d ~> G c) 发送到 ((d,c); ⌈g⌉)。
*)
Program Definition Comma_Functor_Id_G_F_Id (H : F ⊣ G) :
  (Id[D] ↓ G) ⟶ (F ↓ Id[C]) := {|
  fobj := fun x => (``x; from adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- from_adj_nat_r;
  rewrite <- X;
  rewrite <- from_adj_nat_l;
  reflexivity.
Qed.

(*
 The two functors are mutually inverse (via iso_to_from / iso_from_to of the
 adjunction's hom-set iso), giving the comma-category isomorphism that
 Lawvere's theorem asserts in the forward direction. 

 --------
 这两个函子是相互逆的（通过伴随的 Hom-集同构的 iso_to_from / iso_from_to），从而给出了 Lawvere 定理在正向方向断言的逗号范畴同构。
*)
Program Instance Comma_F_Id_Id_G_Iso (H : F ⊣ G) :
  (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G) := {
  to   := Comma_Functor_F_Id_Id_G H;
  from := Comma_Functor_Id_G_F_Id H
}.
Next Obligation.
  constructive.
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity).
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
Defined.
Next Obligation.
  constructive.
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity).
  - exists (id, id).
    abstract
      (destruct x as [[x y] f]; cat;
       srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
  - abstract (clear; simpl; split; cat).
Defined.

End AdjunctionComma.

(*
 Lawvere's characterization, both directions: F ⊣ G holds iff the comma
 categories (F ↓ Id[C]) and (Id[D] ↓ G) are isomorphic over D ∏ C.  Forward:
 package Comma_F_Id_Id_G_Iso with its projection coherence.  Backward: read
 off the unit, counit and triangle identities and build the adjunction from
 them via Adjunction_from_Transform. 

 --------
 Lawvere 的刻画，双向：F ⊣ G 当且仅当逗号范畴 (F ↓ Id [C]) 和 (Id [D] ↓ G) 在 D ∏ C 上同构。正向：打包 Comma_F_Id_Id_G_Iso 及其投影一致性。反向：读出单位、余单位及三角形恒等式，并通过 Adjunction_from_Transform 从它们构建伴随。
*)
Theorem Adjunction_Comma `{F : D ⟶ C} `{G : C ⟶ D} :
  F ⊣ G  ↔  @lawvere_equiv _ _ F G.
Proof.
  split; intros H. {
    unshelve refine {| lawvere_iso := Comma_F_Id_Id_G_Iso H |}.
    - unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - unfold whisker_equiv.
      split; intros; simpl; intros; cat.
  }

  apply Adjunction_from_Transform.

  exact (Build_Adjunction_Transform
           (@lawvere_eqv_unit_transform _ _ _ _ H)
           (@lawvere_eqv_counit_transform _ _ _ _ H)
           (@lawvere_eqv_counit_fmap_unit _ _ _ _ H)
           (@lawvere_eqv_fmap_counit_unit _ _ _ _ H)).
Qed.
