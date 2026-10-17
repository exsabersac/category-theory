Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.

Generalizable All Variables.

Reserved Infix "~~>" (at level 90, right associativity).
Reserved Infix "~~~>" (at level 90, right associativity).
Reserved Infix "∘∘" (at level 40, left associativity).
Reserved Infix "∘∘∘" (at level 40, left associativity).

(** Bicategory *)

(* nLab: https://ncatlab.org/nlab/show/bicategory
   Wikipedia: https://en.wikipedia.org/wiki/Bicategory

   双范畴 (bicategory)（弱 2-范畴）有 0-胞（对象）、0-胞之间的 1-胞、以及平行 1-胞
   之间的 2-胞。对每对 0-胞，1-胞与 2-胞形成 hom-范畴 `bicat x y`（对象是 1-胞，
   态射是 2-胞，`∘∘` 是垂直复合）。水平复合 `hcompose` 是这些 hom-范畴的函子，
   仅在连贯 2-同构下结合与有单位：结合子 α 与左/右单位子 λ、ρ，服从五边形与三角形
   连贯定律。

   记号对照：下文 verbatim nLab 定义中，→ 是 `~>`（1-胞），⇒ 是 `~~>`（2-胞）；
   此处 `~~~>` 也是 2-胞，`∘∘` 是垂直 2-胞复合，`∘∘∘` 是水平 1-胞复合。

   状态：本开发提供完整双范畴。除 hom-范畴 `bicat x y` 与水平复合函子 `hcompose` 外，
   类现携带结合子 `hassoc`、左/右单位子 `hunit_left`/`hunit_right`（作为 hom-范畴中的
   2-同构）、其自然性方块，以及三角形与五边形连贯定律——恰是在词典
   tensor ↔ hcompose、I ↔ bi1id、λ ↔ hunit_left、ρ ↔ hunit_right、α ↔ hassoc 下镜像
   `Structure/Monoidal.v` 的字段。派生的水平 2-胞运算 `hcomp2`（Godement whiskering）
   是 `hcompose` 对一对 2-胞的函子作用，连贯定律经其陈述。 *)

(*
   Why weaken a 2-范畴: examples, coherence, and the 单子 slogan

   本节：nLab: https://ncatlab.org/nlab/show/双范畴 Wikipedia: https://en.wikipedia.org/wiki/双范畴 Paper: Bénabou, J., "Introduction bicategories", Reports Midwest 范畴 Seminar, LNM 47, Springer 1967, pp.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   From https://ncatlab.org/nlab/show/双范畴#detailedDefn :

   本节：{In 下述 text, → matches ~> this library, ⇒ matches ~~>} A 双范畴 B consists - collection Ob[B] 对象 0-cells, - each 对象 对象 b, collection B(a,b) Hom[B](a,b) 态射 1-cells → b, - each 对象 a, 对象 b, m

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class Bicategory := {
  bi0cell : Type;                       (* collection of 0-cells (objects) *)

  bi1uhom := Type : Type;               (* universe of 1-cell collections *)
  bi1cell : bi0cell → bi0cell → bi1uhom (* 1-cells a ~~> b *)
    where "a ~~> b" := (bi1cell a b);

  bi2uhom := Type : Type;               (* universe of 2-cell collections *)
  bi2cell {x y : bi0cell} (f g : bi1cell x y) : bi2uhom  (* 2-cells f ~~~> g *)
    where "f ~~~> g" := (bi2cell f g);

  bi1id {x : bi0cell} : x ~~> x;        (* identity 1-cell on a 0-cell *)

  bi2homset {x y : bi0cell} : ∀ X Y : bi1cell x y, Setoid (@bi2cell x y X Y);
                                        (* 2-cells form a hom-setoid (≈) *)

  bi2id {x y : bi0cell} {a : bi1cell x y} : a ~~~> a;  (* identity 2-cell on a 1-cell *)

  vcompose {x y : bi0cell} {a b c : bi1cell x y}      (* vertical 2-cell composition *)
           (f : b ~~~> c) (g : a ~~~> b) : a ~~~> c
    where "f ∘∘ g" := (vcompose f g);

  vcompose_respects x y a b c :         (* vertical composition respects ≈ *)
    Proper (equiv ==> equiv ==> equiv) (@vcompose x y a b c);

  bi2id_left  {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : bi2id ∘∘ f ≈ f;
                                        (* left unit law for vertical composition *)
  bi2id_right {x y : bi0cell} {a b : bi1cell x y} (f : a ~~~> b) : f ∘∘ bi2id ≈ f;
                                        (* right unit law for vertical composition *)

  vcompose_assoc {x y : bi0cell} {a b c d : bi1cell x y}  (* associativity of vertical comp. *)
                 (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    f ∘∘ (g ∘∘ h) ≈ (f ∘∘ g) ∘∘ h;
  vcompose_assoc_sym {x y : bi0cell} {a b c d : bi1cell x y}  (* dual form (built-in duality) *)
                     (f : c ~~~> d) (g : b ~~~> c) (h : a ~~~> b) :
    (f ∘∘ g) ∘∘ h ≈ f ∘∘ (g ∘∘ h);

  bicat (x y : bi0cell) : Category := {|  (* hom-category B(x,y): 1-cells / 2-cells *)
    obj              := @bi1cell x y;
    hom              := @bi2cell x y;
    homset           := @bi2homset x y;
    id               := @bi2id x y;
    compose          := @vcompose x y;
    compose_respects := @vcompose_respects x y;
    id_left          := @bi2id_left x y;
    id_right         := @bi2id_right x y;
    comp_assoc       := @vcompose_assoc x y;
    comp_assoc_sym   := @vcompose_assoc_sym x y;
  |};

  hcompose {x y z : bi0cell} : bicat y z ∏ bicat x y ⟶ bicat x z
    where "f ∘∘∘ g" := (hcompose (f, g));  (* horizontal composition functor *)

  (*
   The horizontal 复合 of two 2-cells (Godement whiskering), obtained as

   本节说明相关定义、性质与动机。 the functorial action `hcompose` pair. This is manifest field: it is 定义, not new data, so it computes underlying bifunctor's `fmap`.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  hcomp2 {x y z : bi0cell} {g g' : bicat y z} {f f' : bicat x y}
         (θ : g ~{bicat y z}~> g') (η : f ~{bicat x y}~> f') :
    (g ∘∘∘ f) ~{bicat x z}~> (g' ∘∘∘ f')
    := @fmap _ _ (@hcompose x y z) (g, f) (g', f') (θ, η);

  (*
   The coherence 2-isomorphisms of a 双范畴, living in the hom-范畴

   `bicat _ _` mirroring 单位子 结合子 幺半范畴 (`Structure/幺半.v`), tensor ↔ hcompose, I ↔ bi1id.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  hunit_left  {x y : bi0cell} (f : bicat x y) :   (* left  unitor λ[f] *)
    (bi1id ∘∘∘ f) ≅[bicat x y] f;
  hunit_right {x y : bi0cell} (f : bicat x y) :   (* right unitor ρ[f] *)
    (f ∘∘∘ bi1id) ≅[bicat x y] f;
  hassoc {w x y z : bi0cell}                      (* associator α[h,g,f] *)
         (h : bicat y z) (g : bicat x y) (f : bicat w x) :
    ((h ∘∘∘ g) ∘∘∘ f) ≅[bicat w z] (h ∘∘∘ (g ∘∘∘ f));

  (*
   The 单位子 and the 结合子 are 自然 in their 1-cell arguments; each

   本节说明相关定义、性质与动机。 square is horizontal-复合 analogue 幺半 naturality λ, ρ α (the `to`-direction;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  hunit_left_natural {x y : bi0cell} {f f' : bicat x y}
                     (η : f ~{bicat x y}~> f') :
    η ∘∘ to (hunit_left f) ≈ to (hunit_left f') ∘∘ hcomp2 (bi2id (a:=bi1id)) η;
  hunit_right_natural {x y : bi0cell} {f f' : bicat x y}
                      (η : f ~{bicat x y}~> f') :
    η ∘∘ to (hunit_right f) ≈ to (hunit_right f') ∘∘ hcomp2 η (bi2id (a:=bi1id));
  hassoc_natural {w x y z : bi0cell}
      {h h' : bicat y z} {g g' : bicat x y} {f f' : bicat w x}
      (θ : h ~{bicat y z}~> h') (γ : g ~{bicat x y}~> g') (η : f ~{bicat w x}~> f') :
    hcomp2 θ (hcomp2 γ η) ∘∘ to (hassoc h g f)
      ≈ to (hassoc h' g' f') ∘∘ hcomp2 (hcomp2 θ γ) η;

  (*
   The two coherence laws: the triangle relates the 单位子 to the 结合子

   本节说明相关定义、性质与动机。 across `bi1id`, pentagon makes two reassociations fourfold horizontal 复合 agree.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

  hcoherence_triangle {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
    hcomp2 (to (hunit_right g)) (bi2id (a:=f))
      ≈ hcomp2 (bi2id (a:=g)) (to (hunit_left f)) ∘∘ to (hassoc g bi1id f);
  hcoherence_pentagon {v w x y z : bi0cell}
      (k : bicat y z) (h : bicat x y) (g : bicat w x) (f : bicat v w) :
    hcomp2 (bi2id (a:=k)) (to (hassoc h g f))
      ∘∘ to (hassoc k (h ∘∘∘ g) f)
      ∘∘ hcomp2 (to (hassoc k h g)) (bi2id (a:=f))
      ≈ to (hassoc k h (g ∘∘∘ f)) ∘∘ to (hassoc (k ∘∘∘ h) g f)
}.
#[export] Existing Instance bi2homset.
#[export] Existing Instance vcompose_respects.

(*
   Smart constructor for [双范畴], mirroring [Build_范畴']: it takes

   本节说明相关定义、性质与动机。 every field except `vcompose_assoc_sym` supplies that 对称 form automatically `symmetry (vcompose_assoc …)`.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Build_Bicategory'
    bi0cell bi1cell bi2cell bi1id bi2homset bi2id
    vcompose vcompose_respects bi2id_left bi2id_right vcompose_assoc
    hcompose hunit_left hunit_right hassoc
    hunit_left_natural hunit_right_natural hassoc_natural
    hcoherence_triangle hcoherence_pentagon :=
  @Build_Bicategory bi0cell bi1cell bi2cell bi1id bi2homset bi2id
    vcompose vcompose_respects bi2id_left bi2id_right vcompose_assoc
    (fun x y a b c d f g h => symmetry (vcompose_assoc x y a b c d f g h))
    hcompose hunit_left hunit_right hassoc
    hunit_left_natural hunit_right_natural hassoc_natural
    hcoherence_triangle hcoherence_pentagon.
