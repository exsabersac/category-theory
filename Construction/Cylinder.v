(*
   * * The cylinder C ∏ 2 and the universal natural transformation 

   --------
   * * 圆柱 C ∏ 2 和普遍自然变换
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §II.3, printed p. 39 (PDF 49), display (6), and §II.4
 Exercise 8, printed p. 42 (PDF 52) —
 maclane:II.3:construction5, maclane:II.4:ex8
 Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.7,
 Example 7.16, printed p. 171 (PDF pp. 180–181) —
 awodey:7.7:example16
 Book:      Riehl, "Category Theory in Context" (Dover, 2016), §1.5,
 Lemma 1.5.1 (printed p. 31) and Exercise 1.5.i (printed
 p. 38) — riehl:1.5:lem1, riehl:1.5:exi
 nLab:      https://ncatlab.org/nlab/show/natural+transformation

 The cylinder on a category C is the product C ∏ 2 with the walking
 arrow: two copies of C joined by connecting arrows, a directed
 homotopy cylinder.  It carries a transformation μ between the two
 inclusion functors that is UNIVERSAL: every natural transformation
 τ : S ⟹ T between functors out of C is obtained from μ by a
 functor on the cylinder, uniquely so among functors restricting to
 S and T on the two ends AND carrying μ to τ (the third condition
 is load-bearing: functors merely restricting to two constants are
 the arrows between them).  This is Mac Lane's construction 5
 (display (6) of §II.3), Riehl's Lemma 1.5.1 with Exercise 1.5.i
 its deferred proof, and — under the exponential transpose of Cat —
 Awodey's "transcendental deduction" of the arrows of a functor
 category, connecting to the arrow-category encoding of Exercise
 II.4.8.

 - [Cyl_incl0]/[Cyl_incl1]: the two inclusions C ⟶ C ∏ 2, as
 named functors, with [Cyl_restrict0]/[Cyl_restrict1] the
 restriction-along-them operations (so the bijection reads
 "restricts to S and T", per Riehl's phrasing)
 - [Cyl_mu]: the universal transformation μ : Cyl_incl0 ⟹
 Cyl_incl1, component (id[c], the walking arrow)
 - [Cyl_functor τ]: the classifying functor of τ on the cylinder,
 with [Cyl_restrict0_eq]/[Cyl_restrict1_eq] (it restricts to S
 and T, with definitional components) and [Cyl_functor_mu] (it
 carries μ to τ)
 - [Cyl_functor_unique]: any functor restricting to S and T and
 carrying μ to τ (through the chosen restriction isomorphisms)
 is ≈ [Cyl_functor τ]
 - [cylinder_universal]: the universal property bundled as a
 unique existence statement
 - [Cyl_extract]/[Cyl_functor_Cyl_extract]: the inverse leg of
 Riehl's bijection — every functor on the cylinder IS the
 classifier of the transformation it carries (its whiskering
 of μ), closing the correspondence in both directions
 - [cylinder_arrow_agree] (in Construction/Cylinder/Arrow.v —
 see note 4): the exponential transpose carries the cylinder
 encoding to the arrow-category encoding

 Design:

 1. THE CLASSIFYING FUNCTOR IS A DEPENDENT MATCH ON THE WALKING
 ARROW.  [Cyl_functor τ] sends (c, TwoX) to S c and (c, TwoY) to
 T c, and a morphism (f, g) by cases on g: the two identity ends
 act by S and T, and the crossing arrow acts by the composite
 τ ∘ S f — equal to T f ∘ τ by naturality, which is exactly what
 makes the functor laws close (the mixed composition case IS the
 naturality square).

 2. THE WHISKER CONDITION IS STATED THROUGH THE RESTRICTION
 ISOMORPHISMS.  For the chosen [Cyl_functor τ] the restrictions
 are definitional and [Cyl_functor_mu] reads literally; for an
 arbitrary competitor F' the condition must be transported
 along the given [Functor_Setoid] witnesses σ0, σ1, in the same
 intertwining form Construction/Arrow/Functor.v uses for its
 triple setoid: to (σ1 c) ∘ F'(μ c) ≈ τ c ∘ to (σ0 c).  The
 hom-equivalence is written with an explicit [@equiv]/[@homset]
 to fix the intended hom-setoid in the statement itself.

 3. UNIQUENESS DERIVES THE CROSSING CASE FROM THE ENDS.  A
 competitor agrees with [Cyl_functor τ] on the ends by σ0/σ1's
 own conjugate naturality; on the crossing morphisms it is
 forced because (f, TwoXY) factors as μ c' ∘ (f, TwoIdX) in the
 cylinder, so the whisker condition plus the σ0-naturality
 determine it.  No condition beyond the three stated is needed.

 4. THE EXERCISE-8 / AWODEY COMPARISON LIVES ONE FILE OVER.
 Relating this encoding to functors into the arrow category
 goes through [Cat_Closed]'s exponential transpose at exponent
 [_2]; the composite there measures at [Category@{Set Set Set}]
 — object universe included — so it cannot be applied above
 [Set].  This file is free of any Set-level pin — the cylinder
 itself never mentions [Fun] — so the comparison is quarantined
 in Construction/Cylinder/Arrow.v, keeping the universal
 property here at the library's general levels (with only the
 ambient h = p constraint every [Functor] statement carries;
 verified by instantiation strictly above [Set]). 

 --------
 书籍：      Mac Lane，《为在职数学家准备的范畴论》，第2版，第II.3节，印刷页39（PDF第49页），公式(6)，以及第II.4节练习8，印刷页42（PDF第52页）— maclane:II.3:construction5, maclane:II.4:ex8
 书籍：      Awodey，《范畴论》（第一版，2005年预印本），第7.7节，例7.16，印刷页171（PDF第180–181页）— awodey:7.7:example16
 书籍：      Riehl，《范畴论的语境》（Dover, 2016），第1.5节，引理1.5.1（印刷页31）以及练习1.5.i（印刷页38）— riehl:1.5:lem1, riehl:1.5:exi
 nLab:       https://ncatlab.org/nlab/show/natural+transformation类别 C 上的圆柱体是使用行箭头的积 C ∏ 2：两个 C 的副本通过连接箭头连接，形成一个有向同伦圆柱体。它携带一个 μ 变换，位于两个包含函子之间，这是普遍的：每一个从 C 出发的函子之间的自然变换 τ : S ⟹ T 都可以通过圆柱体上的一个函子从 μ 得到，并且在两个端点上限制到 S 和 T 且将 μ 对应到 τ 的函子是唯一的（第三个条件是承重条件：仅在两个常量上限制的函子只是它们之间的箭头）。这是 Mac Lane 的构造 5（§II.3 的展示 (6)），Riehl 的引理 1.5.1 及习题 1.5.i 的推迟证明，以及——在 Cat 的指数换位下——Awodey 关于函子范畴箭头的“先验演绎”，与习题 II.4.8 的箭头范畴编码相连接。- [Cyl_incl0] / [Cyl_incl1]：两个包含 C ⟶ C ∏ 2，作为命名函子，其中 [Cyl_restrict0] / [Cyl_restrict1] 是沿它们的限制操作（因此双射表示为“限制到 S 和 T”，按照 Riehl 的表述）
 - [Cyl_mu]：普遍变换 μ : Cyl_incl0 ⟹ Cyl_incl1，分量为 (id [c], 行箭头)
 - [Cyl_functor τ]：在圆柱体上 τ 的分类函子，其中 [Cyl_restrict0_eq] / [Cyl_restrict1_eq]（它限制到 S 和 T，具有定义分量）和 [Cyl_functor_mu]（它将 μ 映射为 τ）
 - [Cyl_functor_unique]：任何限制到 S 和 T 并将 μ 映射为 τ 的函子（通过选择的限制同构）约等于 [Cyl_functor τ]
 - [cylinder_universal]：将普遍性质捆绑为唯一存在性声明
 - [Cyl_extract] / [Cyl_functor_Cyl_extract]：逆向部分Riehl 的双射——圆柱上的每个函子都是它所携带的变换的分类器（它对 μ 的鞭毛作用），在两个方向上闭合对应关系 - [cylinder_arrow_agree]（在 Construction/Cylinder/Arrow.v 中——见注 4）：指数转置将圆柱编码传递到箭头范畴编码设计：

 1. 分类函子是对行箭头的依赖匹配。[Cyl_functor τ] 将 (c, TwoX) 发送到 S c，将 (c, TwoY) 发送到 T c，而对态射 (f, g) 则根据 g 的情况处理：两个恒等端由 S 和 T 作用，交叉箭头由复合 τ ∘ S f 作用——根据自然性等于 T f ∘ τ，这正是使函子定律闭合的原因（混合复合情况就是自然性平方）。2. 触须条件是通过限制同构来说明的。对于所选的 [Cyl_functor τ]，这些限制是定义性的，并且 [Cyl_functor_mu] 是按字面意思读取的；对于任意竞争者 F'，该条件必须沿给定的 [Functor_Setoid] 见证 σ0、σ1 传递，以与 Construction/Arrow/Functor.v 用于其三重集同态的交织形式相同：to (σ1 c) ∘ F'(μ c) ≈ τ c ∘ to (σ0 c)。同态等价通过显式的 [@equiv] / [@homset] 写出，以在语句中固定所需的同态集同态。3. 唯一性由端点推导交叉情况。竞争者通过 σ0/σ1 自身的共轭自然性，在端点上与 [Cyl_functor τ] 一致；在交叉态射上，它是被迫的，因为 (f, TwoXY) 在圆柱中分解为 μ c' ∘ (f, TwoIdX)，因此通过闪络条件加上 σ0-自然性可以确定它。除了陈述的这三个条件之外，不需要其他条件。4. EXERCISE-8 / AWODEY 比较文件在上一个文件中。
 将此编码与箭头范畴中的函子联系起来，通过指数转置 [Cat_Closed] 在指数 [_2] 下完成；那里复合在 [Category@{Set Set Set}] 处测量——包括对象宇宙——所以它不能在 [Set] 之上应用。这个文件没有任何 Set 级别的限制——圆柱体本身从未提到 [Fun]——因此比较被隔离在 Construction/Cylinder/Arrow.v 中，在库的一般层次保持普遍性质（只有每个 [Functor] 语句携带的环境 h = p 约束；通过严格高于 [Set] 的实例化验证）。
*)

(* * ** The two inclusions and the universal transformation / * ** 两个包含和通用变换 *)

Program Definition Cyl_incl0 {C : Category} : C ⟶ C ∏ _2 := {|
  fobj := fun c => (c, TwoX);
  fmap := fun _ _ f => (f, TwoIdX)
|}.
Next Obligation.
  intros C x y f g Hfg; split; simpl; [ exact Hfg | reflexivity ].
Qed.
Next Obligation.
  intros C x; split; simpl; reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; split; simpl; reflexivity.
Qed.

Program Definition Cyl_incl1 {C : Category} : C ⟶ C ∏ _2 := {|
  fobj := fun c => (c, TwoY);
  fmap := fun _ _ f => (f, TwoIdY)
|}.
Next Obligation.
  intros C x y f g Hfg; split; simpl; [ exact Hfg | reflexivity ].
Qed.
Next Obligation.
  intros C x; split; simpl; reflexivity.
Qed.
Next Obligation.
  intros C x y z f g; split; simpl; reflexivity.
Qed.

(*
 Restriction along the inclusions: the two ends of a functor on the
 cylinder. 

 --------
 沿包含的限制：圆柱上函子两端。
*)
Definition Cyl_restrict0 {C B : Category} (F : C ∏ _2 ⟶ B) : C ⟶ B :=
  F ◯ Cyl_incl0.
Definition Cyl_restrict1 {C B : Category} (F : C ∏ _2 ⟶ B) : C ⟶ B :=
  F ◯ Cyl_incl1.

(*
 The universal natural transformation: at each c, the connecting
 arrow of the cylinder. 

 --------
 普遍自然变换：在每个 c 处，圆筒的连接箭头。
*)
Program Definition Cyl_mu {C : Category} :
  @Cyl_incl0 C ⟹ @Cyl_incl1 C := {|
  transform := fun c => (id[c], TwoXY)
|}.
Next Obligation.
  intros C x y f; split; simpl; [ cat | reflexivity ].
Qed.
Next Obligation.
  intros C x y f; split; simpl; [ cat | reflexivity ].
Qed.

(* * ** The classifying functor of a transformation / * ** 变换的分类函子 *)

Program Definition Cyl_functor {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : C ∏ _2 ⟶ B := {|
  fobj := fun p => match snd p with
                   | TwoX => S (fst p)
                   | TwoY => T (fst p)
                   end;
  fmap := fun p q fg =>
    match snd fg in TwoHom t t'
      return (match t with TwoX => S (fst p) | TwoY => T (fst p) end
                ~{B}~>
              match t' with TwoX => S (fst q) | TwoY => T (fst q) end)
    with
    | TwoIdX => fmap[S] (fst fg)
    | TwoIdY => fmap[T] (fst fg)
    | TwoXY  => τ (fst q) ∘ fmap[S] (fst fg)
    end
|}.
Next Obligation.
  intros C B S T τ [c t] [c' t'] [f g] [f' g'] [Hf Hg]; simpl in *.
  subst g'.
  destruct g; simpl; now rewrite Hf.
Qed.
Next Obligation.
  intros C B S T τ [c t]; simpl.
  destruct t; simpl; apply fmap_id.
Qed.
Next Obligation.
  (*
 destruct the walking-arrow OBJECTS first, so _2's composition — a
 match on objects — reduces before the homs are inverted 

 --------
 首先破坏 walking-arrow 对象，这样 _2 的组成——对象上的匹配——在同类被反转之前就会减少
*)
  intros C B S T τ [c t] [c' t'] [c'' t''] [f g] [f' g']; simpl in *.
  destruct t, t', t'';
  try contradiction (TwoHom_Y_X_absurd g);
  try contradiction (TwoHom_Y_X_absurd g');
  pose proof (TwoHom_inv _ _ g) as Hg; simpl in Hg; subst g;
  pose proof (TwoHom_inv _ _ g') as Hg'; simpl in Hg'; subst g'; simpl.
  - apply fmap_comp.
  - (* crossing after an X-endomorphism / 在 X-自同态后的交叉 *)
    rewrite fmap_comp.
    rewrite !comp_assoc.
    reflexivity.
  - (* Y-endomorphism after the crossing: the naturality square / 交叉后的Y-自同态：自然性方格 *)
    rewrite fmap_comp.
    rewrite comp_assoc.
    rewrite <- (naturality[τ]).
    rewrite <- !comp_assoc.
    reflexivity.
  - apply fmap_comp.
Qed.

(** ** The three defining properties / ** 三个定义性特征 *)

(*
 Restricting the classifying functor to either end recovers the given
 functor, with definitional components. 

 --------
 将分类函子限制到任一端会恢复给定的函子，并带有定义性组成部分。
*)
Program Definition Cyl_restrict0_eq {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : Cyl_restrict0 (Cyl_functor τ) ≈ S :=
  existT _ (fun c => iso_id) _.
Next Obligation.
  intros C B S T τ x y f; simpl; cat.
Qed.

Program Definition Cyl_restrict1_eq {C B : Category} {S T : C ⟶ B}
        (τ : S ⟹ T) : Cyl_restrict1 (Cyl_functor τ) ≈ T :=
  existT _ (fun c => iso_id) _.
Next Obligation.
  intros C B S T τ x y f; simpl; cat.
Qed.

(*
 The classifying functor carries the universal transformation to the
 given one. 

 --------
 分类函子将通用变换携带到给定的变换。
*)
Lemma Cyl_functor_mu {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ c : C, fmap[Cyl_functor τ] (Cyl_mu c) ≈ τ c.
Proof.
  intro c; simpl; cat.
Qed.

(** ** Uniqueness / ** 独特性 *)

(*
 Any functor on the cylinder restricting to S and T and carrying μ to
 τ — through the chosen restriction isomorphisms, in the intertwining
 form — is equivalent to the classifying functor. 

 --------
 任何在圆柱上限制到 S 和 T 并通过所选择的限制同构将 μ 映射到 τ 的函子——以交错形式——都等价于分类函子。
*)
Theorem Cyl_functor_unique {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T)
        (F' : C ∏ _2 ⟶ B)
        (σ0 : Cyl_restrict0 F' ≈ S) (σ1 : Cyl_restrict1 F' ≈ T)
        (Hμ : ∀ c, @equiv _ (@homset B (F' (c, TwoX)) (T c))
                 (to (`1 σ1 c) ∘ fmap[F'] (Cyl_mu c))
                 (τ c ∘ to (`1 σ0 c))) :
  F' ≈ Cyl_functor τ.
Proof.
  unshelve eexists.
  - intros [c t]; destruct t; simpl.
    + exact (`1 σ0 c).
    + exact (`1 σ1 c).
  - intros [c t] [c' t'] [f g]; simpl.
    destruct t, t';
    try contradiction (TwoHom_Y_X_absurd g);
    pose proof (TwoHom_inv _ _ g) as Hg; simpl in Hg; subst g; simpl.
    + exact (`2 σ0 c c' f).
    + (* the crossing case: factor (f, TwoXY) ≈ μ c' ∘ (f, TwoIdX) / 交叉情况：因子 （f， TwoXY） ≈ μ c' ∘ （f， TwoIdX） *)
      assert (Hfact : fmap[F'] ((f, TwoXY) : (c, TwoX) ~{C ∏ _2}~> (c', TwoY))
                        ≈ fmap[F'] (Cyl_mu c')
                            ∘ fmap[F'] ((f, TwoIdX) :
                                (c, TwoX) ~{C ∏ _2}~> (c', TwoX))). {
        rewrite <- fmap_comp.
        apply fmap_respects; split; simpl; cat.
      }
      rewrite Hfact.
      (*
 express F'(μ c') via Hμ and F'(f, TwoIdX) via σ0's naturality 

 --------
 通过 Hμ 表示 F'(μ c')，通过 σ0 的自然性表示 F'(f, TwoIdX)
*)
      assert (Hmu : fmap[F'] (Cyl_mu c')
                      ≈ from (`1 σ1 c') ∘ (τ c' ∘ to (`1 σ0 c'))). {
        rewrite <- (Hμ c').
        rewrite comp_assoc.
        rewrite iso_from_to, id_left.
        reflexivity.
      }
      rewrite Hmu.
      rewrite (`2 σ0 c c' f); simpl.
      rewrite !comp_assoc.
      rewrite <- (comp_assoc _ (to (`1 σ0 c'))).
      rewrite iso_to_from, id_right.
      reflexivity.
    + exact (`2 σ1 c c' f).
Qed.

(*
 The universal property, bundled: τ is classified by a functor on the
 cylinder restricting to S and T and carrying μ to τ, uniquely up to
 the ambient functor equivalence. 

 --------
 通用性质，捆绑：τ 由柱面上的一个函子分类，该函子限制在 S 和 T 上，并将 μ 映射到 τ，在环境函子等价下唯一。
*)
Theorem cylinder_universal {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  { F : C ∏ _2 ⟶ B
  & { σ0 : Cyl_restrict0 F ≈ S
    & { σ1 : Cyl_restrict1 F ≈ T
      & (∀ c, @equiv _ (@homset B (F (c, TwoX)) (T c))
            (to (`1 σ1 c) ∘ fmap[F] (Cyl_mu c))
            (τ c ∘ to (`1 σ0 c)))
        * (∀ F' (σ0' : Cyl_restrict0 F' ≈ S) (σ1' : Cyl_restrict1 F' ≈ T),
             (∀ c, @equiv _ (@homset B (F' (c, TwoX)) (T c))
                 (to (`1 σ1' c) ∘ fmap[F'] (Cyl_mu c))
                 (τ c ∘ to (`1 σ0' c))) →
             F' ≈ F) } } }.
Proof.
  exists (Cyl_functor τ), (Cyl_restrict0_eq τ), (Cyl_restrict1_eq τ); split.
  - intro c; simpl; cat.
  - intros F' σ0' σ1' Hμ'.
    exact (Cyl_functor_unique τ F' σ0' σ1' Hμ').
Qed.

(*
   * ** The inverse leg: every cylinder functor classifies its own
   transformation 

   --------
   * ** 逆边：每个圆柱函子分类其自身的变换
*)

(*
 Reading the transformation off a functor on the cylinder: whisker
 the universal transformation.  Its component at c is
 [fmap[F] (Cyl_mu c)]. 

 --------
 从圆柱上的函子读取变换：将其与通用变换“搅拌”。它在 c 处的分量是 [fmap[F] (Cyl_mu c)].
*)
Definition Cyl_extract {C B : Category} (F : C ∏ _2 ⟶ B) :
  Cyl_restrict0 F ⟹ Cyl_restrict1 F :=
  F ⊳ @Cyl_mu C.

(*
 The round trip: F is the classifier of the transformation it
 carries, through transparent reflexivity witnesses (Construction/
 Arrow/Functor.v's [fs_refl]).  With [cylinder_universal] this
 closes Riehl's bijection in both directions. 

 --------
 往返旅行：F 是它所承载的变换的分类器，通过透明的自反性见证（Construction/Arrow/Functor.v 的 [fs_refl]）。使用 [cylinder_universal]，这在两个方向上闭合了 Riehl 的双射。
*)
Theorem Cyl_functor_Cyl_extract {C B : Category} (F : C ∏ _2 ⟶ B) :
  F ≈ Cyl_functor (Cyl_extract F).
Proof.
  apply (Cyl_functor_unique (Cyl_extract F) F (fs_refl _) (fs_refl _)).
  intro c; simpl; cat.
Qed.
