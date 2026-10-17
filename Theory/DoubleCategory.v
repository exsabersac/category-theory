Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** * Pseudo double categories *)

(* nLab: https://ncatlab.org/nlab/show/double+category
   Wikipedia: https://en.wikipedia.org/wiki/Double_category

   双重范畴 (double category) 有对象、水平 1-胞、垂直 1-胞，以及填入方块的 2-胞
   （四方格），水平与垂直方向各有范畴结构，且两方向的复合经交换律 (interchange)
   相容。本库的伪双重范畴变体允许水平复合仅在连贯同构下结合/有单位（类比双范畴），
   垂直方向通常更严格。companions 与 conjoints 是连接两方向的特殊方块，支撑 mates
   对应。本文件给出核心类与边界连贯；历史与用途见下一块注释（后续波次可续译）。 *)

(*
   nLab:  https://ncatlab.org/nlab/show/double+category
   nLab:  https://ncatlab.org/nlab/show/proarrow+equipment
   Paper: Ehresmann, "Catégories doubles et catégories structurées",

   双全盘分类展示了什么

nL 小号: 你干嘛不说?
nLab敷:ZWP便是Z所审议的
论文:埃赫被认定,"纽带双对各国和 我们都认为 session  那么你后才富有成效的"
ử鳏三晴三三快点三三三和各三 大家都三三三三三准时三 我以为与土著人民丫三三三三三戊三对发展坚定地致力于三三三三三三将负责三三这方面的工作昼三觅三业经三三 他们会三三三三三三三三三三 这位三 但这三三翎三三三表达了三三 我自己三三三三三三 Motor三三蛊三三 上帝三 可是三三三三促成了三的结论三三三三三三三三三四三三三三三 别这样 我以前三三三三三三三三三三三三三三劳力三三三三三三三三三三三挚三三三昼三三萌三三三三三和三三三,三三三三三三三三三三三所确认的三三三三三三三 等一下三三三三三 你为什么要三三崭所发挥的实际上是三展开了配套三三三三三三三三作了规定为实施三三三三三表达了发三三炖 恩辅之以三三三三三声明三三三四俏 如果你不三三三三三审查工作 秘书处的说明三三三三三 还有无误三三三三三三三 của三 救命三造福于三单边三三三
大大评共同大大大大大大萃大大 你有什么之间在大大大大列述大 各位大大见上文均有
40有助于提高 这一部分
....配套.理论
第20(2008) 是呀,对发展

竿子既然是 这方面所给予的二
1细胞是可以同时出现的不同种类.

   （原英文长文首已压缩为中文导言；标识符未改。）
*)

Class DoubleCategory : Type := {
  (* Objects together with their STRICT vertical morphisms. *)
  dcat : Category;

  (* Horizontal 1-cells. *)
  dhor : dcat → dcat → Type;

  (* A square with horizontal top [h], bottom [k], left vertical [u], and
     right vertical [v]. *)
  dsq {a b c d : dcat} :
    dhor a b → (a ~{dcat}~> c) → (b ~{dcat}~> d) → dhor c d → Type;

  dsq_setoid {a b c d} {h u v k} : Setoid (@dsq a b c d h u v k);

  (*( - 奕 -适合于 -就此 -日在 提倡 - 所有成员国 -   这只是曝 - 的例子   我保证  一般 未婚  - 有望 的 - 佑  - 与 天呐真高兴 - 的 已经有了  和工作人员便于 ...   - 的 -  即使  -  知道了 -  与   这次 的可以作为 - 
(潇洒:方块是命题还参加了 以下是身份图 快走
科 咱们的顶部图或其记录: 顶部跨国界图没有并作为肇事遵照. )ất.*)
  dsq_coerce {a b c d} {h} {u u' : a ~{dcat}~> c} {v v' : b ~{dcat}~> d} {k}
    (eu : u ≈ u') (ev : v ≈ v') : dsq h u v k → dsq h u' v' k;

  dsq_coerce_respects {a b c d} {h} {u u' : a ~{dcat}~> c}
    {v v' : b ~{dcat}~> d} {k} (eu : u ≈ u') (ev : v ≈ v') :
    Proper (equiv ==> equiv) (@dsq_coerce a b c d h u u' v v' k eu ev);

  (* Proof-irrelevance of the boundary: coercing along a loop is the identity
     (Phase 10 [dtransport_id] style, stated with [≈] on squares). *)
  dsq_coerce_id {a b c d} {h} {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k}
    (eu : u ≈ u) (ev : v ≈ v) (s : dsq h u v k) :
    dsq_coerce eu ev s ≈ s;

  (* Coercions compose. *)
  dsq_coerce_trans {a b c d} {h}
    {u u' u'' : a ~{dcat}~> c} {v v' v'' : b ~{dcat}~> d} {k}
    (eu : u ≈ u') (eu' : u' ≈ u'') (ev : v ≈ v') (ev' : v' ≈ v'')
    (s : dsq h u v k) :
    dsq_coerce eu' ev' (dsq_coerce eu ev s)
      ≈ dsq_coerce (Equivalence_Transitive _ _ _ eu eu')
                   (Equivalence_Transitive _ _ _ ev ev') s;

  (* Vertical identity square on a horizontal 1-cell. *)
  dsq_vid {a b} (h : dhor a b) : dsq h id id h;

  (* Vertical pasting of squares. *)
  dsq_vcomp {a0 b0 a1 b1 a2 b2}
    {h : dhor a0 b0} {u : a0 ~{dcat}~> a1} {v : b0 ~{dcat}~> b1}
    {k : dhor a1 b1} {u' : a1 ~{dcat}~> a2} {v' : b1 ~{dcat}~> b2}
    {l : dhor a2 b2} :
    dsq h u v k → dsq k u' v' l → dsq h (u' ∘ u) (v' ∘ v) l;

  dsq_vcomp_respects {a0 b0 a1 b1 a2 b2}
    {h u v k u' v' l} :
    Proper (equiv ==> equiv ==> equiv)
      (@dsq_vcomp a0 b0 a1 b1 a2 b2 h u v k u' v' l);

  (* STRICT vertical unit laws, through [dsq_coerce] to absorb [id ∘ u] / u. *)
  dsq_vid_left {a b c d} {h : dhor a b}
    {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k} (s : dsq h u v k) :
    dsq_coerce (id_left u) (id_left v) (dsq_vcomp s (dsq_vid k)) ≈ s;

  dsq_vid_right {a b c d} {h : dhor a b}
    {u : a ~{dcat}~> c} {v : b ~{dcat}~> d} {k} (s : dsq h u v k) :
    dsq_coerce (id_right u) (id_right v) (dsq_vcomp (dsq_vid h) s) ≈ s;

  (* STRICT vertical associativity, through [dsq_coerce]. *)
  dsq_vassoc {a0 b0 a1 b1 a2 b2 a3 b3}
    {h : dhor a0 b0} {u : a0 ~{dcat}~> a1} {v : b0 ~{dcat}~> b1}
    {k : dhor a1 b1} {u' : a1 ~{dcat}~> a2} {v' : b1 ~{dcat}~> b2}
    {l : dhor a2 b2} {u'' : a2 ~{dcat}~> a3} {v'' : b2 ~{dcat}~> b3}
    {m : dhor a3 b3}
    (s : dsq h u v k) (t : dsq k u' v' l) (r : dsq l u'' v'' m) :
    dsq_coerce (comp_assoc u'' u' u) (comp_assoc v'' v' v)
      (dsq_vcomp (dsq_vcomp s t) r)
      ≈ dsq_vcomp s (dsq_vcomp t r);

  (* Horizontal identity 1-cell. *)
  dhid (a : dcat) : dhor a a;

  (* Horizontal composition of 1-cells (outer then inner, like [∘]). *)
  dhcomp {a b c : dcat} : dhor b c → dhor a b → dhor a c;

  (* Horizontal pasting of squares (sharing the middle vertical edge). *)
  dsq_hcomp {a b c a' b' c'}
    {h : dhor a b} {h' : dhor b c}
    {u : a ~{dcat}~> a'} {v : b ~{dcat}~> b'} {w : c ~{dcat}~> c'}
    {k : dhor a' b'} {k' : dhor b' c'} :
    dsq h u v k → dsq h' v w k' → dsq (dhcomp h' h) u w (dhcomp k' k);

  dsq_hcomp_respects {a b c a' b' c'} {h h' u v w k k'} :
    Proper (equiv ==> equiv ==> equiv)
      (@dsq_hcomp a b c a' b' c' h h' u v w k k');

  (*
   本节说明 DoubleCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  dinterchange {a b c a' b' c' a'' b'' c''}
    {h1 : dhor a b} {h2 : dhor b c}
    {u1 : a ~{dcat}~> a'} {u2 : b ~{dcat}~> b'} {u3 : c ~{dcat}~> c'}
    {j1 : dhor a' b'} {j2 : dhor b' c'}
    {w1 : a' ~{dcat}~> a''} {w2 : b' ~{dcat}~> b''} {w3 : c' ~{dcat}~> c''}
    {k1 : dhor a'' b''} {k2 : dhor b'' c''}
    (s11 : dsq h1 u1 u2 j1) (s12 : dsq h2 u2 u3 j2)
    (s21 : dsq j1 w1 w2 k1) (s22 : dsq j2 w2 w3 k2) :
    dsq_vcomp (dsq_hcomp s11 s12) (dsq_hcomp s21 s22)
      ≈ dsq_hcomp (dsq_vcomp s11 s21) (dsq_vcomp s12 s22);

  (* Weak associator: an invertible globular square between the two
     bracketings of a horizontal composite (forward square, backward square,
     two round-trip identities normalised through [dsq_coerce]). *)
  dassoc {a b c d} (f : dhor a b) (g : dhor b c) (h : dhor c d) :
    { fwd : dsq (dhcomp h (dhcomp g f)) id id (dhcomp (dhcomp h g) f) &
    { bwd : dsq (dhcomp (dhcomp h g) f) id id (dhcomp h (dhcomp g f)) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp h (dhcomp g f)))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid (dhcomp (dhcomp h g) f)) } };

  (* Weak left unitor: [dhid b · h ≅ h] as an invertible globular square. *)
  dunit_left {a b} (h : dhor a b) :
    { fwd : dsq (dhcomp (dhid b) h) id id h &
    { bwd : dsq h id id (dhcomp (dhid b) h) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp (dhid b) h))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid h) } };

  (* Weak right unitor: [h · dhid a ≅ h] as an invertible globular square. *)
  dunit_right {a b} (h : dhor a b) :
    { fwd : dsq (dhcomp h (dhid a)) id id h &
    { bwd : dsq h id id (dhcomp h (dhid a)) &
      prod (dsq_coerce (id_left id) (id_left id) (dsq_vcomp fwd bwd)
              ≈ dsq_vid (dhcomp h (dhid a)))
           (dsq_coerce (id_left id) (id_left id) (dsq_vcomp bwd fwd)
              ≈ dsq_vid h) } };

  (* Triangle coherence (square level): whiskering the left unitor equals the
     associator followed by whiskering the right unitor. *)
  dcoherence_triangle {a b c} (f : dhor a b) (k : dhor b c) :
    dsq_coerce (id_left id) (id_left id)
      (dsq_vcomp (projT1 (dassoc f (dhid b) k))
                 (dsq_hcomp (dsq_vid f) (projT1 (dunit_right k))))
      ≈ dsq_hcomp (projT1 (dunit_left f)) (dsq_vid k);

  (* Pentagon coherence (square level): the two globular paths from
     [k · (h · (g · f))] to [((k · h) · g) · f] agree, their [id]-boundaries
     normalised through [dsq_coerce]. *)
  dcoherence_pentagon {a b c d e}
    (f : dhor a b) (g : dhor b c) (h : dhor c d) (k : dhor d e) :
    dsq_coerce (id_left (id ∘ id)) (id_left (id ∘ id))
      (dsq_vcomp (dsq_vcomp
          (dsq_hcomp (projT1 (dassoc f g h)) (dsq_vid k))
          (projT1 (dassoc f (dhcomp h g) k)))
        (dsq_hcomp (dsq_vid f) (projT1 (dassoc g h k))))
      ≈ dsq_vcomp (projT1 (dassoc (dhcomp g f) h k))
                  (projT1 (dassoc f g (dhcomp k h)))
}.

#[export] Existing Instance dsq_setoid.
#[export] Existing Instance dsq_coerce_respects.
#[export] Existing Instance dsq_vcomp_respects.
#[export] Existing Instance dsq_hcomp_respects.

(** ** Named accessors for the invertible globular squares. *)

Definition dassoc_to `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d)
  : dsq (dhcomp h (dhcomp g f)) id id (dhcomp (dhcomp h g) f)
  := projT1 (dassoc f g h).

Definition dassoc_from `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d)
  : dsq (dhcomp (dhcomp h g) f) id id (dhcomp h (dhcomp g f))
  := projT1 (projT2 (dassoc f g h)).

Definition dunit_left_to `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq (dhcomp (dhid b) h) id id h
  := projT1 (dunit_left h).

Definition dunit_left_from `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq h id id (dhcomp (dhid b) h)
  := projT1 (projT2 (dunit_left h)).

Definition dunit_right_to `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq (dhcomp h (dhid a)) id id h
  := projT1 (dunit_right h).

Definition dunit_right_from `{D : DoubleCategory} {a b} (h : dhor a b)
  : dsq h id id (dhcomp h (dhid a))
  := projT1 (projT2 (dunit_right h)).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition dassoc_from_to `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dassoc_to f g h) (dassoc_from f g h))
    ≈ dsq_vid (dhcomp h (dhcomp g f))
  := fst (projT2 (projT2 (dassoc f g h))).

Definition dassoc_to_from `{D : DoubleCategory} {a b c d}
  (f : dhor a b) (g : dhor b c) (h : dhor c d) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dassoc_from f g h) (dassoc_to f g h))
    ≈ dsq_vid (dhcomp (dhcomp h g) f)
  := snd (projT2 (projT2 (dassoc f g h))).

Definition dunit_left_from_to `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_left_to h) (dunit_left_from h))
    ≈ dsq_vid (dhcomp (dhid b) h)
  := fst (projT2 (projT2 (dunit_left h))).

Definition dunit_left_to_from `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_left_from h) (dunit_left_to h))
    ≈ dsq_vid h
  := snd (projT2 (projT2 (dunit_left h))).

Definition dunit_right_from_to `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_right_to h) (dunit_right_from h))
    ≈ dsq_vid (dhcomp h (dhid a))
  := fst (projT2 (projT2 (dunit_right h))).

Definition dunit_right_to_from `{D : DoubleCategory} {a b} (h : dhor a b) :
  dsq_coerce (id_left id) (id_left id)
    (dsq_vcomp (dunit_right_from h) (dunit_right_to h))
    ≈ dsq_vid h
  := snd (projT2 (projT2 (dunit_right h))).

(*
   本节说明 DoubleCategory 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DoubleCategoryLemmas.

Context {D : DoubleCategory}.

(* Coercing there and back again cancels (left orientation). *)
Lemma dsq_coerce_symm_l {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (s : dsq h u v k) :
  dsq_coerce (symmetry eu) (symmetry ev) (dsq_coerce eu ev s) ≈ s.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(* Coercing back and there again cancels (right orientation). *)
Lemma dsq_coerce_symm_r {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (t : dsq h u' v' k) :
  dsq_coerce eu ev (dsq_coerce (symmetry eu) (symmetry ev) t) ≈ t.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(* Reorienting a coercion equation: a coercion may be moved to the other
   side of [≈] by inverting the proofs it rides on. *)
Lemma dsq_coerce_flip {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu : u ≈ u') (ev : v ≈ v') (s : dsq h u v k) (t : dsq h u' v' k) :
  dsq_coerce eu ev s ≈ t ↔ s ≈ dsq_coerce (symmetry eu) (symmetry ev) t.
Proof.
  split; intros H.
  - rewrite <- H.
    symmetry; apply dsq_coerce_symm_l.
  - rewrite H.
    apply dsq_coerce_symm_r.
Qed.

(* Coercion does not depend on the proofs coerced along: the groupoid laws
   [dsq_coerce_id]/[dsq_coerce_trans] force any two parallel proof pairs to
   coerce identically. *)
Lemma dsq_coerce_proof_irrel {a b c d : dcat} {h : dhor a b}
  {u u' : a ~> c} {v v' : b ~> d} {k : dhor c d}
  (eu eu' : u ≈ u') (ev ev' : v ≈ v') (s : dsq h u v k) :
  dsq_coerce eu ev s ≈ dsq_coerce eu' ev' s.
Proof.
  apply (snd (dsq_coerce_flip eu ev s (dsq_coerce eu' ev' s))).
  symmetry; rewrite dsq_coerce_trans; apply dsq_coerce_id.
Qed.

(* [dsq_coerce_trans] with the composite proofs replaced by any proofs of
   the endpoints' relations. *)
Lemma dsq_coerce_trans_any {a b c d : dcat} {h : dhor a b}
  {u u' u'' : a ~> c} {v v' v'' : b ~> d} {k : dhor c d}
  (eu1 : u ≈ u') (eu2 : u' ≈ u'') (eu3 : u ≈ u'')
  (ev1 : v ≈ v') (ev2 : v' ≈ v'') (ev3 : v ≈ v'')
  (s : dsq h u v k) :
  dsq_coerce eu2 ev2 (dsq_coerce eu1 ev1 s) ≈ dsq_coerce eu3 ev3 s.
Proof.
  rewrite dsq_coerce_trans; apply dsq_coerce_proof_irrel.
Qed.

(* The strict vertical laws along any proofs of the base laws: exactly the
   shape of the unit/associativity obligations of categories built from
   squares. *)
Lemma dsq_vid_left_any {a b c d : dcat} {h : dhor a b}
  {u : a ~> c} {v : b ~> d} {k : dhor c d}
  (eu : id ∘ u ≈ u) (ev : id ∘ v ≈ v) (s : dsq h u v k) :
  dsq_coerce eu ev (dsq_vcomp s (dsq_vid k)) ≈ s.
Proof.
  transitivity
    (dsq_coerce (id_left u) (id_left v) (dsq_vcomp s (dsq_vid k))).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vid_left.
Qed.

Lemma dsq_vid_right_any {a b c d : dcat} {h : dhor a b}
  {u : a ~> c} {v : b ~> d} {k : dhor c d}
  (eu : u ∘ id ≈ u) (ev : v ∘ id ≈ v) (s : dsq h u v k) :
  dsq_coerce eu ev (dsq_vcomp (dsq_vid h) s) ≈ s.
Proof.
  transitivity
    (dsq_coerce (id_right u) (id_right v) (dsq_vcomp (dsq_vid h) s)).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vid_right.
Qed.

Lemma dsq_vassoc_any {a0 b0 a1 b1 a2 b2 a3 b3 : dcat}
  {h : dhor a0 b0} {u : a0 ~> a1} {v : b0 ~> b1}
  {k : dhor a1 b1} {u' : a1 ~> a2} {v' : b1 ~> b2}
  {l : dhor a2 b2} {u'' : a2 ~> a3} {v'' : b2 ~> b3}
  {m : dhor a3 b3}
  (eu : u'' ∘ (u' ∘ u) ≈ (u'' ∘ u') ∘ u)
  (ev : v'' ∘ (v' ∘ v) ≈ (v'' ∘ v') ∘ v)
  (s : dsq h u v k) (t : dsq k u' v' l) (r : dsq l u'' v'' m) :
  dsq_coerce eu ev (dsq_vcomp (dsq_vcomp s t) r)
    ≈ dsq_vcomp s (dsq_vcomp t r).
Proof.
  transitivity
    (dsq_coerce (comp_assoc u'' u' u) (comp_assoc v'' v' v)
                (dsq_vcomp (dsq_vcomp s t) r)).
  - apply dsq_coerce_proof_irrel.
  - apply dsq_vassoc.
Qed.

End DoubleCategoryLemmas.
