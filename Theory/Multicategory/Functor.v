Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Multicategory.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Multifunctors / * 多函子 *)

(*
nLab: https://ncatlab.org/nlab/show/multicategory
   Wikipedia: https://en.wikipedia.org/wiki/Multicategory

   A multifunctor [F : M ⟶ N] between multicategories sends objects to
   objects and a multimorphism [f : mhom Γ c] to
   [mf_map f : mhom (map mf_obj Γ) (mf_obj c)], preserving identities,
   single-slot composition, and the symmetric-group action.

   BOUNDARY CASTS.  As in Theory/Multicategory.v, the preservation laws
   relate multimorphisms whose source lists are PROPOSITIONALLY but not
   definitionally equal: [map φ (Γ1 ++ b :: Γ2)] versus
   [map φ Γ1 ++ φ b :: map φ Γ2], and [map φ Γ1 ++ map φ Δ ++ map φ Γ2]
   versus [map φ (Γ1 ++ Δ ++ Γ2)].  Lists of objects are Type-level
   object data, so [=] on them is sanctioned; the laws recast along
   [mcast] and are quantified over ANY proofs of their boundary
   equations (the [_any] style of Theory/Multicategory.v), with the
   transparent [mf_eq_*] kit below providing canonical witnesses.

   TRANSPARENT LIST KIT.  The stdlib proofs [map_id]/[map_app]/[map_map]
   are opaque; the instance proofs below (identity and composite
   multifunctors) need the boundary equations to COMPUTE on list
   constructors, so transparent Fixpoint versions [map_id_t]/[map_app_t]
   /[map_map_t]/[map_ext_t] are defined here.

   PERMUTATION ACTION.  The symmetry-preservation law is
   witness-relevant in the permutation, and the class action is indexed
   by the Type-valued [tperm] of Theory/Multicategory.v, so the image of
   a witness under the object map is the structural [perm_map], a
   Fixpoint that computes on each constructor.  Comparing the witnesses
   that arise for the identity and composite multifunctors requires
   transporting a witness along list equalities ([pcast]) and the
   commutation lemmas [pcast_skip]/[pcast_swap]/[pcast_ptrans]; the
   equalities proven between witnesses are [=] on Type-level witness
   data, never on multimorphisms.

--------
nLab：https://ncatlab.org/nlab/show/multicategory
维基百科：https://en.wikipedia.org/wiki/Multicategory

多重范畴之间的多函子 [F : M ⟶ N] 将对象映射到对象，将多态射 [f : mhom Γ c] 映射到 [mf_map f : mhom (map mf_obj Γ) (mf_obj c)]，同时保持恒等映射、单槽组合以及对称群作用。

边界转换。在 Theory/Multicategory.v 中，保持律关联的是源列表在命题上相等但定义上不相等的多态映射：[map φ (Γ1 ++ b :: Γ2)] 与 [map φ Γ1 ++ φ b :: map φ Γ2]，以及 [map φ Γ1 ++ map φ Δ ++ map φ Γ2] 与 [map φ (Γ1 ++ Δ ++ Γ2)]。对象列表是类型级对象数据，因此在它们上应用 [=] 是允许的；律沿 [mcast] 重写，并在它们边界方程的任何证明上进行量化（Theory/Multicategory.v 中的 [_any] 风格），下面的透明 [mf_eq_*] 工具包提供了规范的见证。

透明列表工具包。stdlib 证明 [map_id]/[map_app]/[map_map] 是不透明的；下面的实例证明（恒等和复合多函子）需要边界方程在列表构造上进行计算，因此这里定义了透明的 Fixpoint 版本 [map_id_t]/[map_app_t]/[map_map_t]/[map_ext_t]。

排列作用。对称保持定律在排列中与见证相关，而类作用由 Theory/Multicategory.v 的类型值 [tperm] 索引，因此对象映射下见证的像是结构性 [perm_map]，这是一个在每个构造器上进行计算的 Fixpoint。比较恒等和复合多函子产生的见证需要沿列表等式（[pcast]）以及交换引理 [pcast_skip]/[pcast_swap]/[pcast_ptrans] 传输见证；在见证之间证明的等式是类型级见证数据上的 [=]，从不在多态态射上。
*)

(** ** The transparent list kit / ** 透明列表套件 *)

Section ListKit.

Context {A B C : Type}.

Fixpoint map_id_t (l : list A) : map (fun x => x) l = l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal (cons x) (map_id_t t)
  end.

Fixpoint map_app_t (f : A → B) (l l' : list A) :
  map f (l ++ l') = map f l ++ map f l' :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal (cons (f x)) (map_app_t f t l')
  end.

Fixpoint map_map_t (f : A → B) (g : B → C) (l : list A) :
  map g (map f l) = map (fun x => g (f x)) l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal (cons (g (f x))) (map_map_t f g t)
  end.

Fixpoint map_ext_t (f g : A → B) (H : ∀ a, f a = g a) (l : list A) :
  map f l = map g l :=
  match l with
  | [] => eq_refl
  | x :: t => f_equal2 cons (H x) (map_ext_t f g H t)
  end.

End ListKit.

(** ** The multifunctor boundary-equation kit / ** 多函子边界方程套件 *)

Section BoundaryKit.

Context {A B : Type}.
Context (φ : A → B).

(**
The image of a slot zipper is a slot zipper: [map φ (b :: Γ2)]
    computes, so this is [map_app_t] up to conversion.

--------
插槽拉链的图像就是插槽拉链：[map φ (b :: Γ2)] 进行计算，所以这是 [map_app_t] 直到转换。
*)
Definition mf_eq_slot (Γ1 Γ2 : list A) (b : A) :
  map φ (Γ1 ++ b :: Γ2) = map φ Γ1 ++ φ b :: map φ Γ2 :=
  map_app_t φ Γ1 (b :: Γ2).

(** The image of a spliced context, reassembled blockwise. / 拼接上下文的图像，按块重新组合。 *)
Definition mf_eq_splice (Γ1 Δ Γ2 : list A) :
  map φ Γ1 ++ map φ Δ ++ map φ Γ2 = map φ (Γ1 ++ Δ ++ Γ2) :=
  eq_sym (eq_trans (map_app_t φ Γ1 (Δ ++ Γ2))
                   (f_equal (app (map φ Γ1)) (map_app_t φ Δ Γ2))).

End BoundaryKit.

(** ** The transparent permutation image and its transport calculus / ** 透明排列图像及其传递演算 *)

(**
The structural image of a permutation witness under a function.
    Being a Fixpoint, it computes on each constructor, which the
    identity/composite multifunctor proofs below rely on.

--------
在一个函数下置换证明的结构图像。作为一个不动点，它对每个构造器进行计算，而下面的恒等/复合多函子证明依赖于此。
*)
Fixpoint perm_map {A B : Type} (φ : A → B) {Γ Δ : list A}
  (p : tperm Γ Δ) : tperm (map φ Γ) (map φ Δ) :=
  match p in tperm Γ0 Δ0
        return tperm (map φ Γ0) (map φ Δ0) with
  | tperm_nil => tperm_nil
  | tperm_skip x q => tperm_skip (φ x) (perm_map φ q)
  | tperm_swap x y l => tperm_swap (φ x) (φ y) (map φ l)
  | tperm_trans q r => tperm_trans (perm_map φ q) (perm_map φ r)
  end.

(**
Transport of a permutation witness along equalities of its endpoint
    lists (Type-level object data).

--------
沿其端点列表的相等性传输排列证据（类型级对象数据）。
*)
Definition pcast {A : Type} {Γ Γ' Δ Δ' : list A}
  (e1 : Γ = Γ') (e2 : Δ = Δ') (p : tperm Γ Δ) :
  tperm Γ' Δ' :=
  match e2 with
  | eq_refl => match e1 with eq_refl => p end
  end.

(** [pcast] commutes with [tperm_skip]. / [pcast] 与 [tperm_skip] 可交换。 *)
Lemma pcast_skip {A : Type} {a b c d : list A} (e1 : a = b) (e2 : c = d)
  (x : A) (p : tperm a c) :
  pcast (f_equal (cons x) e1) (f_equal (cons x) e2) (tperm_skip x p)
    = tperm_skip x (pcast e1 e2 p).
Proof. destruct e1, e2; reflexivity. Qed.

(** [pcast] commutes with [tperm_swap]. / [pcast] 与 [tperm_swap] 可交换。 *)
Lemma pcast_swap {A : Type} {a b : list A} (e : a = b) (x y : A) :
  pcast (f_equal (cons y) (f_equal (cons x) e))
        (f_equal (cons x) (f_equal (cons y) e)) (tperm_swap x y a)
    = tperm_swap x y b.
Proof. destruct e; reflexivity. Qed.

(** [pcast] commutes with [tperm_trans]. / [pcast] 与 [tperm_trans] 可交换。 *)
Lemma pcast_ptrans {A : Type} {a a' b b' c c' : list A}
  (e1 : a = a') (e2 : b = b') (e3 : c = c')
  (p : tperm a b) (q : tperm b c) :
  pcast e1 e3 (tperm_trans p q)
    = tperm_trans (pcast e1 e2 p) (pcast e2 e3 q).
Proof. destruct e1, e2, e3; reflexivity. Qed.

(** [eq_sym] slides under [f_equal]. / [eq_sym] 滑到 [f_equal] 下方。 *)
Lemma eq_sym_f_equal {A B : Type} (h : A → B) {a b : A} (e : a = b) :
  eq_sym (f_equal h e) = f_equal h (eq_sym e).
Proof. destruct e; reflexivity. Qed.

(**
The identity function's permutation image is the original witness,
    transported along [map_id_t].  Everything on both sides computes on
    list/permutation constructors, so the induction goes through with
    no identification of equality proofs.  [tperm] lives in [Type], so
    its dependent induction principle [tperm_rect] comes for free.

--------
恒等函数的置换像是原始的证人，沿着 [map_id_t] 传输。两边的所有内容都在列表/置换构造子上进行计算，因此归纳法可以顺利进行，而无需识别等式证明。[tperm] 位于 [Type] 中，因此它的依赖归纳原理 [tperm_rect] 是自然获得的。
*)
Lemma perm_map_id {A : Type} {Γ Δ : list A} (p : tperm Γ Δ) :
  pcast (map_id_t Γ) (map_id_t Δ) (perm_map (fun x => x) p) = p.
Proof.
  induction p as [| x l l' p IH | x y l | l l' l'' p IHp q IHq]; simpl.
  - reflexivity.
  - now rewrite pcast_skip, IH.
  - now rewrite pcast_swap.
  - now rewrite (pcast_ptrans _ (map_id_t l') _), IHp, IHq.
Qed.

(**
The permutation image of a composite function is the composite of
    the images, transported along [map_map_t].

--------
复合函数的排列像是像的复合，通过 [map_map_t] 进行传输。
*)
Lemma perm_map_comp {A B C : Type} (f : A → B) (g : B → C)
  {Γ Δ : list A} (p : tperm Γ Δ) :
  pcast (map_map_t f g Γ) (map_map_t f g Δ) (perm_map g (perm_map f p))
    = perm_map (fun x => g (f x)) p.
Proof.
  induction p as [| x l l' p IH | x y l | l l' l'' p IHp q IHq]; simpl.
  - reflexivity.
  - now rewrite pcast_skip, IH.
  - now rewrite pcast_swap.
  - now rewrite (pcast_ptrans _ (map_map_t f g l') _), IHp, IHq.
Qed.

(**
** Transport lemmas in a multicategory

    Boundary casts commute with everything in sight.  Each lemma is
    quantified over equalities with variable endpoints, so the proof is
    a [destruct] of the equality followed by [mcast_id] — no UIP
    anywhere.

--------
** 多重范畴中的传输引理

边界转换与所见的一切交换。每个引理都在变量端点的等式上量化，因此证明是先进行等式的[destruct]，然后是[mcast_id] —— 任何地方都没有UIP。
*)

Section MulticategoryTransport.

Context {M : Multicategory}.

(**
Recasting the TARGET object of a multimorphism along a
    propositional equality of objects (Type-level object data).  Unlike
    [mcast] this needs no groupoid-law fields: every use below carries
    its equality proof as data, so only functoriality along
    [eq_refl]/[eq_sym]/[eq_trans] is ever needed, and those hold by
    [destruct].

--------
沿着对象的命题等式（类型级对象数据）重新构造多态映射的目标对象。与 [mcast] 不同，这不需要群对象律字段：下面的每次使用都将其等式证明作为数据携带，因此只需要沿 [eq_refl]/[eq_sym]/[eq_trans] 的函子性，并且这些都由 [destruct] 保证。
*)
Definition mtarget_cast {Γ : list mobj} {c c' : mobj} (e : c = c') :
  mhom Γ c → mhom Γ c' :=
  match e with eq_refl => fun f => f end.

#[export] Instance mtarget_cast_respects {Γ c c'} (e : c = c') :
  Proper (equiv ==> equiv) (@mtarget_cast Γ c c' e).
Proof. destruct e; repeat intro; assumption. Qed.

Lemma mtarget_cast_trans {Γ : list mobj} {c c' c'' : mobj}
  (e : c = c') (e' : c' = c'') (f : mhom Γ c) :
  mtarget_cast e' (mtarget_cast e f) ≈ mtarget_cast (eq_trans e e') f.
Proof. destruct e, e'; reflexivity. Qed.

Lemma mtarget_cast_symm {Γ : list mobj} {c c' : mobj}
  (e : c = c') (f : mhom Γ c) :
  mtarget_cast (eq_sym e) (mtarget_cast e f) ≈ f.
Proof. destruct e; reflexivity. Qed.

(** Source and target casts commute. / 源类型转换和目标类型转换是可交换的。 *)
Lemma mcast_mtarget_cast {Γ Γ' : list mobj} {c c' : mobj}
  (e : Γ = Γ') (e' : c = c') (f : mhom Γ c) :
  mcast e (mtarget_cast e' f) ≈ mtarget_cast e' (mcast e f).
Proof. destruct e'; reflexivity. Qed.

(**
Splicing commutes with blockwise recasting of the boundary: casts
    on both arguments of [mcomp] fuse into one cast on the composite.
    The zipper/splice equalities [ez]/[es] are ANY proofs; the blockwise
    equalities [e1]/[e2]/[ed] guarantee they exist.

--------
拼接与边界的块状重铸是可交换的：对 [mcomp] 的两个参数的转换会融合为对组合的一个转换。拉链/拼接等式 [ez]/[es] 是任何证明；块状等式 [e1]/[e2]/[ed] 保证它们存在。
*)
Lemma mcomp_cast_zipper {Γ1 Γ1' Γ2 Γ2' Δ Δ' : list mobj} {b c : mobj}
  (e1 : Γ1 = Γ1') (e2 : Γ2 = Γ2') (ed : Δ = Δ')
  (ez : Γ1 ++ b :: Γ2 = Γ1' ++ b :: Γ2')
  (es : Γ1 ++ Δ ++ Γ2 = Γ1' ++ Δ' ++ Γ2')
  (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b) :
  mcomp (mcast ez f) (mcast ed g) ≈ mcast es (mcomp f g).
Proof.
  destruct e1, e2, ed.
  now rewrite !mcast_id.
Qed.

(**
The symmetric-group action commutes with boundary casts: acting by
    a transported permutation on a recast multimorphism is the recast of
    the original action.

--------
对称群作用与边界投射可交换：在重投射多态射上作用一个平移的置换，是原作用的重投射。
*)
Lemma msym_pcast {Γ Γ' Δ Δ' : list mobj} {c : mobj}
  (e1 : Γ = Γ') (e2 : Δ = Δ') (p : tperm Γ Δ) (f : mhom Γ c) :
  msym (pcast e1 e2 p) (mcast e1 f) ≈ mcast e2 (msym p f).
Proof.
  destruct e1, e2; simpl.
  now rewrite !mcast_id.
Qed.

End MulticategoryTransport.

(** ** The class / ** 那堂课 *)

Class MultiFunctor (M N : Multicategory) : Type := {
  (* The object map. / 对象映射。 *)
  mf_obj : @mobj M → @mobj N;

  (* The multimorphism map: sources go through [map mf_obj]. / 多态映射：源通过 [map mf_obj]。 *)
  mf_map {Γ : list (@mobj M)} {c : @mobj M} :
    mhom Γ c → mhom (map mf_obj Γ) (mf_obj c);

  mf_map_respects {Γ c} : Proper (equiv ==> equiv) (@mf_map Γ c);

  (*
Identities are preserved on the nose: [map mf_obj [a]] computes to
     [[mf_obj a]], so no cast is needed.

--------
恒等在细节上得以保留：[map mf_obj [a]] 计算为 [[mf_obj a]]，因此不需要强制类型转换。
*)
  mf_id (a : @mobj M) : mf_map (mid a) ≈ mid (mf_obj a);

  (*
Splicing is preserved, up to the boundary casts putting the image
     of the zipper in zipper form ([ez]) and reassembling the image of
     the spliced context ([es]).  Quantified over ANY proofs of the two
     boundary equations (witnesses: [mf_eq_slot], [mf_eq_splice]),
     following the [_any] law style of Theory/Multicategory.v.

--------
拼接得以保留，直到边界操作将拉链的图像呈拉链形式（[ez]）并重新组装拼接上下文的图像（[es]）。 对两个边界方程的任何证明进行量化（见证者：[mf_eq_slot]，[mf_eq_splice]），遵循 Theory/Multicategory.v 的 [_any] 法律风格。
*)
  mf_comp {Γ1 Γ2 Δ : list (@mobj M)} {b c : @mobj M}
    (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b)
    (ez : map mf_obj (Γ1 ++ b :: Γ2)
            = map mf_obj Γ1 ++ mf_obj b :: map mf_obj Γ2)
    (es : map mf_obj Γ1 ++ map mf_obj Δ ++ map mf_obj Γ2
            = map mf_obj (Γ1 ++ Δ ++ Γ2)) :
    mf_map (mcomp f g) ≈ mcast es (mcomp (mcast ez (mf_map f)) (mf_map g));

  (*
The symmetric-group action is preserved along the transparent
     permutation image [perm_map].

--------
沿着透明置换像 [perm_map]，对称群作用得以保持。
*)
  mf_sym {Γ Δ : list (@mobj M)} {c : @mobj M}
    (p : tperm Γ Δ) (f : mhom Γ c) :
    mf_map (msym p f) ≈ msym (perm_map mf_obj p) (mf_map f)
}.

#[export] Existing Instance mf_map_respects.

Arguments mf_obj {M N} _ _.
Arguments mf_map {M N} _ {Γ c} _.
Arguments mf_id {M N} _ a.
Arguments mf_comp {M N} _ {Γ1 Γ2 Δ b c} f g ez es.
Arguments mf_sym {M N} _ {Γ Δ c} p f.

(** The composition law at the canonical kit witnesses. / 在规范工具包中，组合律是显而易见的。 *)
Corollary mf_comp_kit {M N : Multicategory} (F : MultiFunctor M N)
  {Γ1 Γ2 Δ : list (@mobj M)} {b c : @mobj M}
  (f : mhom (Γ1 ++ b :: Γ2) c) (g : mhom Δ b) :
  mf_map F (mcomp f g)
    ≈ mcast (mf_eq_splice (mf_obj F) Γ1 Δ Γ2)
        (mcomp (mcast (mf_eq_slot (mf_obj F) Γ1 Γ2 b) (mf_map F f))
               (mf_map F g)).
Proof. apply mf_comp. Qed.

(**
A multifunctor commutes with boundary casts: the image of a recast
    multimorphism is the recast image, along the [f_equal] image of the
    boundary equality.

--------
多函子与边界转换可交换：重转换多态映射的像是沿边界等式的 [f_equal] 映像的重转换像。
*)
Lemma mf_map_cast {M N : Multicategory} (F : MultiFunctor M N)
  {Γ Γ' : list (@mobj M)} {c : @mobj M} (e : Γ = Γ') (f : mhom Γ c) :
  mf_map F (mcast e f) ≈ mcast (f_equal (map (mf_obj F)) e) (mf_map F f).
Proof.
  destruct e; simpl.
  now rewrite !mcast_id.
Qed.

(**
** The setoid of multifunctors

    Two parallel multifunctors are equivalent when their object maps
    agree pointwise (Type-level object data, so [=] is sanctioned) and,
    modulo the source/target recasting that this agreement induces,
    their multimorphism maps agree up to [≈].  The witness [eobj] is
    carried as DATA in a sigma — the pattern of the [Hobj]-conjugated
    uniqueness statements of Construction/ColouredPROP/Universal.v —
    so the equivalence laws never compare equality proofs, only
    compose them.

--------
** 多函子集合的等价类

当两个平行多函子在其对象映射上逐点一致（类型级对象数据，因此 [=] 被允许）时，它们是等价的，并且在模仿这种一致性所引起的源/目标重定义后，它们的多态映射在 [≈] 下是一致的。见证 [eobj] 作为 DATA 携带在 sigma 中——即 Construction/ColouredPROP/Universal.v 中 [Hobj] 共轭的唯一性陈述的模式——因此等价定律从不比较等式证明，只是组合它们。
*)

Definition mf_equiv {M N : Multicategory} (F G : MultiFunctor M N) : Type :=
  { eobj : ∀ a : @mobj M, mf_obj F a = mf_obj G a
  & ∀ (Γ : list (@mobj M)) (c : @mobj M) (f : mhom Γ c),
      mcast (map_ext_t _ _ eobj Γ)
        (mtarget_cast (eobj c) (mf_map F f)) ≈ mf_map G f }.

Lemma mf_equiv_refl {M N : Multicategory} (F : MultiFunctor M N) :
  mf_equiv F F.
Proof.
  exists (fun _ => eq_refl); intros; simpl.
  apply mcast_id.
Qed.

Lemma mf_equiv_sym {M N : Multicategory} (F G : MultiFunctor M N) :
  mf_equiv F G → mf_equiv G F.
Proof.
  intros [eobj eh].
  exists (fun a => eq_sym (eobj a)); intros Γ c f.
  rewrite <- (eh Γ c f).
  rewrite !mcast_mtarget_cast.
  rewrite mtarget_cast_trans.
  rewrite (eq_trans_sym_inv_r (eobj c)); simpl.
  rewrite mcast_trans.
  apply mcast_id.
Qed.

Lemma mf_equiv_trans {M N : Multicategory} (F G H : MultiFunctor M N) :
  mf_equiv F G → mf_equiv G H → mf_equiv F H.
Proof.
  intros [e1 h1] [e2 h2].
  exists (fun a => eq_trans (e1 a) (e2 a)); intros Γ c f.
  rewrite <- (h2 Γ c f).
  rewrite <- (h1 Γ c f).
  rewrite !mcast_mtarget_cast.
  rewrite mtarget_cast_trans.
  rewrite mcast_trans.
  now rewrite (mcast_proof_irrel
                 (map_ext_t _ _ (fun a => eq_trans (e1 a) (e2 a)) Γ)
                 (eq_trans (map_ext_t _ _ e1 Γ) (map_ext_t _ _ e2 Γ))).
Qed.

#[export] Program Instance MultiFunctor_Setoid {M N : Multicategory} :
  Setoid (MultiFunctor M N) := {|
  equiv := mf_equiv
|}.
Next Obligation.
  equivalence.
  - apply mf_equiv_refl.
  - now apply mf_equiv_sym.
  - now apply mf_equiv_trans with y.
Qed.

(**
** The identity multifunctor

    The object map is the identity, but [map (fun a => a) Γ] is only
    propositionally equal to [Γ], so the multimorphism map recasts along
    the transparent [map_id_t].

--------
** 恒等多函子

    对象映射是恒等的，但 [map (fun a => a) Γ] 仅在命题上等于 [Γ]，因此多态映射沿透明的 [map_id_t] 重新构造。
*)

Local Obligation Tactic := intros; cbv beta.

Program Definition MultiId (M : Multicategory) : MultiFunctor M M := {|
  mf_obj := fun a => a;
  mf_map := fun Γ c f => mcast (eq_sym (map_id_t Γ)) f
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  apply mcast_id.
Qed.
Next Obligation.
  rewrite mcast_trans.
  rewrite (mcomp_cast_zipper
             (eq_sym (map_id_t Γ1)) (eq_sym (map_id_t Γ2))
             (eq_sym (map_id_t Δ)) _
             (f_equal2 (@app _) (eq_sym (map_id_t Γ1))
                (f_equal2 (@app _) (eq_sym (map_id_t Δ))
                   (eq_sym (map_id_t Γ2))))).
  rewrite mcast_trans.
  apply mcast_proof_irrel.
Qed.
Next Obligation.
  assert (Hq : msym (pcast (map_id_t Γ) (map_id_t Δ) (perm_map (fun a => a) p))
                 (mcast (map_id_t Γ) (mcast (eq_sym (map_id_t Γ)) f))
               ≈ mcast (map_id_t Δ)
                   (msym (perm_map (fun a => a) p)
                      (mcast (eq_sym (map_id_t Γ)) f)))
    by apply msym_pcast.
  rewrite perm_map_id in Hq.
  rewrite mcast_symm_r in Hq.
  rewrite Hq.
  apply mcast_symm_l.
Qed.

(**
** Composition of multifunctors

    Objects compose on the nose; the multimorphism map recasts along the
    transparent [map_map_t] to move between [map (mf_obj G) (map
    (mf_obj F) Γ)] and [map (fun a => mf_obj G (mf_obj F a)) Γ].

--------
** 多函子组合

    对象是按字面组合的；多态射映射沿透明 [map_map_t] 重新构造，以在 [map (mf_obj G) (map (mf_obj F) Γ)] 和 [map (fun a => mf_obj G (mf_obj F a)) Γ] 之间移动。
*)

Program Definition MultiCompose {M N O : Multicategory}
  (G : MultiFunctor N O) (F : MultiFunctor M N) : MultiFunctor M O := {|
  mf_obj := fun a => mf_obj G (mf_obj F a);
  mf_map := fun Γ c f =>
    mcast (map_map_t (mf_obj F) (mf_obj G) Γ) (mf_map G (mf_map F f))
|}.
Next Obligation.
  proper.
  now rewrite X.
Qed.
Next Obligation.
  rewrite (mf_id F a).
  rewrite (mf_id G (mf_obj F a)).
  apply mcast_id.
Qed.
Next Obligation.
  (*
Normalize the left-hand side: push the image of the splice through
     [G], collecting all boundary casts.

--------
规范化左侧：将拼接的图像通过 [G] 推送，收集所有边界投影。
*)
  rewrite (mf_comp_kit F f g).
  rewrite (mf_map_cast G).
  rewrite (mf_comp_kit G).
  rewrite (mf_map_cast G).
  rewrite !mcast_trans.
  (*
Split the right-hand side's inner cast at the [G ∘ F]-image zipper
     and commute the blockwise casts out of the splice.

--------
在 [G ∘ F] 图像拉链处拆分右侧的内部类型转换，并将块状类型转换移出拼接。
*)
  rewrite <- (mcast_trans_any
                (eq_trans
                   (f_equal (map (mf_obj G)) (mf_eq_slot (mf_obj F) Γ1 Γ2 b))
                   (mf_eq_slot (mf_obj G)
                      (map (mf_obj F) Γ1) (map (mf_obj F) Γ2) (mf_obj F b)))
                (f_equal2 (@app _) (map_map_t (mf_obj F) (mf_obj G) Γ1)
                   (f_equal (cons (mf_obj G (mf_obj F b)))
                      (map_map_t (mf_obj F) (mf_obj G) Γ2)))).
  rewrite (mcomp_cast_zipper
             (map_map_t (mf_obj F) (mf_obj G) Γ1)
             (map_map_t (mf_obj F) (mf_obj G) Γ2)
             (map_map_t (mf_obj F) (mf_obj G) Δ) _
             (f_equal2 (@app _) (map_map_t (mf_obj F) (mf_obj G) Γ1)
                (f_equal2 (@app _) (map_map_t (mf_obj F) (mf_obj G) Δ)
                   (map_map_t (mf_obj F) (mf_obj G) Γ2)))).
  rewrite !mcast_trans.
  apply mcast_proof_irrel.
Qed.
Next Obligation.
  rewrite (mf_sym F p f).
  rewrite (mf_sym G).
  rewrite <- (perm_map_comp (mf_obj F) (mf_obj G) p).
  symmetry; apply msym_pcast.
Qed.

(** ** The evident laws, up to the multifunctor setoid / ** 明显的定律，直到多函数集合点 *)

Lemma MultiCompose_id_left {M N : Multicategory} (F : MultiFunctor M N) :
  MultiCompose (MultiId N) F ≈ F.
Proof.
  exists (fun _ => eq_refl); intros Γ c f; simpl.
  rewrite !mcast_trans.
  apply mcast_id.
Qed.

Lemma MultiCompose_id_right {M N : Multicategory} (F : MultiFunctor M N) :
  MultiCompose F (MultiId M) ≈ F.
Proof.
  exists (fun _ => eq_refl); intros Γ c f; simpl.
  rewrite (mf_map_cast F).
  rewrite !mcast_trans.
  apply mcast_id.
Qed.

Lemma MultiCompose_assoc {M N O P : Multicategory}
  (H : MultiFunctor O P) (G : MultiFunctor N O) (F : MultiFunctor M N) :
  MultiCompose H (MultiCompose G F) ≈ MultiCompose (MultiCompose H G) F.
Proof.
  exists (fun _ => eq_refl); intros Γ c f; simpl.
  rewrite (mf_map_cast H).
  rewrite !mcast_trans.
  apply mcast_proof_irrel.
Qed.
