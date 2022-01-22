---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-foundations.W-types where

open import univalent-foundations.18-set-quotients public

--------------------------------------------------------------------------------

-- Appendix B W-types

--------------------------------------------------------------------------------

-- Section B.1 W-types

data 𝕎 {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  tree-𝕎 : (x : A) (α : B x → 𝕎 A B) → 𝕎 A B

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  symbol-𝕎 : 𝕎 A B → A
  symbol-𝕎 (tree-𝕎 x α) = x
  
  component-𝕎 : (x : 𝕎 A B) → B (symbol-𝕎 x) → 𝕎 A B
  component-𝕎 (tree-𝕎 x α) = α

  η-𝕎 : (x : 𝕎 A B) → Id (tree-𝕎 (symbol-𝕎 x) (component-𝕎 x)) x
  η-𝕎 (tree-𝕎 x α) = refl

-- Example B.1.3

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  constant-𝕎 : (x : A) → is-empty (B x) → 𝕎 A B
  constant-𝕎 x h = tree-𝕎 x (ex-falso ∘ h)

  is-constant-𝕎 : 𝕎 A B → UU l2
  is-constant-𝕎 x = is-empty (B (symbol-𝕎 x))

-- Proposition B.1.4

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-empty-𝕎 : ((x : A) → type-trunc-Prop (B x)) → is-empty (𝕎 A B)
  is-empty-𝕎 H (tree-𝕎 x α) =
    apply-universal-property-trunc-Prop
      ( H x)
      ( empty-Prop)
      ( λ y → is-empty-𝕎 H (α y))

-- Example B.1.5

Nat-𝕎 : UU lzero
Nat-𝕎 = 𝕎 bool (Eq-bool true)

zero-Nat-𝕎 : Nat-𝕎
zero-Nat-𝕎 = constant-𝕎 false id

succ-Nat-𝕎 : Nat-𝕎 → Nat-𝕎
succ-Nat-𝕎 x = tree-𝕎 true (λ y → x)

Nat-𝕎-ℕ : ℕ → Nat-𝕎
Nat-𝕎-ℕ zero-ℕ = zero-Nat-𝕎
Nat-𝕎-ℕ (succ-ℕ x) = succ-Nat-𝕎 (Nat-𝕎-ℕ x)

ℕ-Nat-𝕎 : Nat-𝕎 → ℕ
ℕ-Nat-𝕎 (tree-𝕎 true α) = succ-ℕ (ℕ-Nat-𝕎 (α star))
ℕ-Nat-𝕎 (tree-𝕎 false α) = zero-ℕ

issec-ℕ-Nat-𝕎 : (Nat-𝕎-ℕ ∘ ℕ-Nat-𝕎) ~ id
issec-ℕ-Nat-𝕎 (tree-𝕎 true α) =
  ap ( tree-𝕎 true)
     ( eq-htpy H)
  where
  H : (z : unit) → Id (Nat-𝕎-ℕ (ℕ-Nat-𝕎 (α star))) (α z)
  H star = issec-ℕ-Nat-𝕎 (α star)
issec-ℕ-Nat-𝕎 (tree-𝕎 false α) =
  ap (tree-𝕎 false) (eq-is-contr (universal-property-empty' Nat-𝕎))

isretr-ℕ-Nat-𝕎 : (ℕ-Nat-𝕎 ∘ Nat-𝕎-ℕ) ~ id
isretr-ℕ-Nat-𝕎 zero-ℕ = refl
isretr-ℕ-Nat-𝕎 (succ-ℕ x) = ap succ-ℕ (isretr-ℕ-Nat-𝕎 x)

is-equiv-Nat-𝕎-ℕ : is-equiv Nat-𝕎-ℕ
is-equiv-Nat-𝕎-ℕ =
  is-equiv-has-inverse
    ℕ-Nat-𝕎
    issec-ℕ-Nat-𝕎
    isretr-ℕ-Nat-𝕎

equiv-Nat-𝕎-ℕ : ℕ ≃ Nat-𝕎
equiv-Nat-𝕎-ℕ = pair Nat-𝕎-ℕ is-equiv-Nat-𝕎-ℕ

is-equiv-ℕ-Nat-𝕎 : is-equiv ℕ-Nat-𝕎
is-equiv-ℕ-Nat-𝕎 =
  is-equiv-has-inverse
    Nat-𝕎-ℕ
    isretr-ℕ-Nat-𝕎
    issec-ℕ-Nat-𝕎

equiv-ℕ-Nat-𝕎 : Nat-𝕎 ≃ ℕ
equiv-ℕ-Nat-𝕎 = pair ℕ-Nat-𝕎 is-equiv-ℕ-Nat-𝕎

-- Example B.1.6

data Planar-Bin-Tree : UU lzero where
  root-PBT : Planar-Bin-Tree
  join-PBT : (x y : Planar-Bin-Tree) → Planar-Bin-Tree

PBT-𝕎 : UU lzero
PBT-𝕎 = 𝕎 bool P
  where
  P : bool → UU lzero
  P true = bool
  P false = empty

root-PBT-𝕎 : PBT-𝕎
root-PBT-𝕎 = constant-𝕎 false id

join-PBT-𝕎 : (x y : PBT-𝕎) → PBT-𝕎
join-PBT-𝕎 x y = tree-𝕎 true α
  where
  α : bool → PBT-𝕎
  α true = x
  α false = y

{-
Planar-Bin-Tree-PBT-𝕎 : PBT-𝕎 → Planar-Bin-Tree
Planar-Bin-Tree-PBT-𝕎 (tree-𝕎 true α) =
  join-PBT
    ( Planar-Bin-Tree-PBT-𝕎 (α true))
    ( Planar-Bin-Tree-PBT-𝕎 (α false))
Planar-Bin-Tree-PBT-𝕎 (tree-𝕎 false α) = {!!}
-}

--------------------------------------------------------------------------------

-- Section B.2 Observational equality of W-types

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  Eq-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-𝕎 (tree-𝕎 x α) (tree-𝕎 y β) =
    Σ (Id x y) (λ p → (z : B x) → Eq-𝕎 (α z) (β (tr B p z))) 

  refl-Eq-𝕎 : (w : 𝕎 A B) → Eq-𝕎 w w
  refl-Eq-𝕎 (tree-𝕎 x α) = pair refl (λ z → refl-Eq-𝕎 (α z))

  center-total-Eq-𝕎 : (w : 𝕎 A B) → Σ (𝕎 A B) (Eq-𝕎 w)
  center-total-Eq-𝕎 w = pair w (refl-Eq-𝕎 w)

  aux-total-Eq-𝕎 :
    (x : A) (α : B x → 𝕎 A B) →
    Σ (B x → 𝕎 A B) (λ β → (y : B x) → Eq-𝕎 (α y) (β y)) →
    Σ (𝕎 A B) (Eq-𝕎 (tree-𝕎 x α))
  aux-total-Eq-𝕎 x α (pair β e) = pair (tree-𝕎 x β) (pair refl e)

  contraction-total-Eq-𝕎 :
    (w : 𝕎 A B) (t : Σ (𝕎 A B) (Eq-𝕎 w)) → Id (center-total-Eq-𝕎 w) t
  contraction-total-Eq-𝕎
    ( tree-𝕎 x α) (pair (tree-𝕎 .x β) (pair refl e)) =
    ap ( ( aux-total-Eq-𝕎 x α) ∘
         ( choice-∞ {A = B x} {B = λ y → 𝕎 A B} {C = λ y → Eq-𝕎 (α y)}))
       { x = λ y → pair (α y) (refl-Eq-𝕎 (α y))}
       { y = λ y → pair (β y) (e y)}
       ( eq-htpy (λ y → contraction-total-Eq-𝕎 (α y) (pair (β y) (e y))))

  is-contr-total-Eq-𝕎 : (w : 𝕎 A B) → is-contr (Σ (𝕎 A B) (Eq-𝕎 w))
  is-contr-total-Eq-𝕎 w =
    pair (center-total-Eq-𝕎 w) (contraction-total-Eq-𝕎 w)

  Eq-𝕎-eq : (v w : 𝕎 A B) → Id v w → Eq-𝕎 v w
  Eq-𝕎-eq v .v refl = refl-Eq-𝕎 v

  is-equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → is-equiv (Eq-𝕎-eq v w)
  is-equiv-Eq-𝕎-eq v =
    fundamental-theorem-id v
      ( refl-Eq-𝕎 v)
      ( is-contr-total-Eq-𝕎 v)
      ( Eq-𝕎-eq v)

  eq-Eq-𝕎 : (v w : 𝕎 A B) → Eq-𝕎 v w → Id v w
  eq-Eq-𝕎 v w = map-inv-is-equiv (is-equiv-Eq-𝕎-eq v w)

  equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → Id v w ≃ Eq-𝕎 v w
  equiv-Eq-𝕎-eq v w = pair (Eq-𝕎-eq v w) (is-equiv-Eq-𝕎-eq v w)
  
  is-trunc-𝕎 : (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (𝕎 A B)
  is-trunc-𝕎 k is-trunc-A (tree-𝕎 x α) (tree-𝕎 y β) =
    is-trunc-is-equiv k
      ( Eq-𝕎 (tree-𝕎 x α) (tree-𝕎 y β))
      ( Eq-𝕎-eq (tree-𝕎 x α) (tree-𝕎 y β))
      ( is-equiv-Eq-𝕎-eq (tree-𝕎 x α) (tree-𝕎 y β))
      ( is-trunc-Σ
        ( is-trunc-A x y)
        ( λ p → is-trunc-Π k
          ( λ z →
            is-trunc-is-equiv' k
            ( Id (α z) (β (tr B p z)))
            ( Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-equiv-Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-trunc-𝕎 k is-trunc-A (α z) (β (tr B p z))))))
  
--------------------------------------------------------------------------------
  
-- Section B.3 W-types as initial algebras

-- The polynomial endofunctor associated to a container
                                              
type-polynomial-endofunctor :
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (X : UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
type-polynomial-endofunctor A B X = Σ A (λ x → B x → X)

-- We characterize the identity type of type-polynomial-endofunctor

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {X : UU l3}
  where

  Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor A B X) → UU (l1 ⊔ l2 ⊔ l3)
  Eq-type-polynomial-endofunctor x y =
    Σ (Id (pr1 x) (pr1 y)) (λ p → (pr2 x) ~ ((pr2 y) ∘ (tr B p)))

  refl-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor A B X) →
    Eq-type-polynomial-endofunctor x x
  refl-Eq-type-polynomial-endofunctor (pair x α) = pair refl refl-htpy

  is-contr-total-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor A B X) →
    is-contr
      ( Σ ( type-polynomial-endofunctor A B X)
          ( Eq-type-polynomial-endofunctor x))
  is-contr-total-Eq-type-polynomial-endofunctor (pair x α) =
    is-contr-total-Eq-structure
      ( ( λ (y : A) (β : B y → X) (p : Id x y) → α ~ (β ∘ tr B p)))
      ( is-contr-total-path x)
      ( pair x refl)
      ( is-contr-total-htpy α)

  Eq-type-polynomial-endofunctor-eq :
    (x y : type-polynomial-endofunctor A B X) →
    Id x y → Eq-type-polynomial-endofunctor x y
  Eq-type-polynomial-endofunctor-eq x .x refl =
    refl-Eq-type-polynomial-endofunctor x

  is-equiv-Eq-type-polynomial-endofunctor-eq :
    (x y : type-polynomial-endofunctor A B X) →
    is-equiv (Eq-type-polynomial-endofunctor-eq x y)
  is-equiv-Eq-type-polynomial-endofunctor-eq x =
    fundamental-theorem-id x
      ( refl-Eq-type-polynomial-endofunctor x)
      ( is-contr-total-Eq-type-polynomial-endofunctor x)
      ( Eq-type-polynomial-endofunctor-eq x)

  eq-Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor A B X) →
    Eq-type-polynomial-endofunctor x y → Id x y
  eq-Eq-type-polynomial-endofunctor x y =
    map-inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq x y)

  isretr-eq-Eq-type-polynomial-endofunctor :
    (x y : type-polynomial-endofunctor A B X) →
    ( ( eq-Eq-type-polynomial-endofunctor x y) ∘
      ( Eq-type-polynomial-endofunctor-eq x y)) ~ id
  isretr-eq-Eq-type-polynomial-endofunctor x y =
    isretr-map-inv-is-equiv (is-equiv-Eq-type-polynomial-endofunctor-eq x y)

  coh-refl-eq-Eq-type-polynomial-endofunctor :
    (x : type-polynomial-endofunctor A B X) →
    Id ( eq-Eq-type-polynomial-endofunctor x x
       ( refl-Eq-type-polynomial-endofunctor x)) refl
  coh-refl-eq-Eq-type-polynomial-endofunctor x =
    isretr-eq-Eq-type-polynomial-endofunctor x x refl
  
--------------------------------------------------------------------------------

-- The action on morphisms of the polynomial endofunctor

map-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  type-polynomial-endofunctor A B X → type-polynomial-endofunctor A B Y
map-polynomial-endofunctor A B f = tot (λ x α → f ∘ α)

-- The action on homotopies of the polynomial endofunctor

htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  {f g : X → Y} →
  f ~ g → map-polynomial-endofunctor A B f ~ map-polynomial-endofunctor A B g
htpy-polynomial-endofunctor A B {X = X} {Y} {f} {g} H (pair x α) =
  eq-Eq-type-polynomial-endofunctor
    ( map-polynomial-endofunctor A B f (pair x α))
    ( map-polynomial-endofunctor A B g (pair x α))
    ( pair refl (H ·r α))

coh-refl-htpy-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} (A : UU l1) (B : A → UU l2) {X : UU l3} {Y : UU l4}
  (f : X → Y) →
  htpy-polynomial-endofunctor A B (refl-htpy {f = f}) ~ refl-htpy
coh-refl-htpy-polynomial-endofunctor A B {X = X} {Y} f (pair x α) =
  coh-refl-eq-Eq-type-polynomial-endofunctor
    ( map-polynomial-endofunctor A B f (pair x α)) 
                                           
-- algebras for the polynomial endofunctors

algebra-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UU (lsuc l ⊔ l1 ⊔ l2)
algebra-polynomial-endofunctor-UU l A B =
  Σ (UU l) (λ X → type-polynomial-endofunctor A B X → X)
                                                  
type-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  algebra-polynomial-endofunctor-UU l A B → UU l
type-algebra-polynomial-endofunctor X = pr1 X
                                            
structure-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l A B) →
  type-polynomial-endofunctor A B (type-algebra-polynomial-endofunctor X) →
  type-algebra-polynomial-endofunctor X
structure-algebra-polynomial-endofunctor X = pr2 X

-- W-types are algebras for polynomial endofunctors

structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor A B (𝕎 A B) → 𝕎 A B
structure-𝕎-Alg (pair x α) = tree-𝕎 x α

𝕎-Alg :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  algebra-polynomial-endofunctor-UU (l1 ⊔ l2) A B
𝕎-Alg A B = pair (𝕎 A B) structure-𝕎-Alg

map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B → type-polynomial-endofunctor A B (𝕎 A B)
map-inv-structure-𝕎-Alg (tree-𝕎 x α) = pair x α

issec-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (structure-𝕎-Alg {B = B} ∘ map-inv-structure-𝕎-Alg {B = B}) ~ id
issec-map-inv-structure-𝕎-Alg (tree-𝕎 x α) = refl

isretr-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (map-inv-structure-𝕎-Alg {B = B} ∘ structure-𝕎-Alg {B = B}) ~ id
isretr-map-inv-structure-𝕎-Alg (pair x α) = refl

is-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (structure-𝕎-Alg {B = B})
is-equiv-structure-𝕎-Alg =
  is-equiv-has-inverse
    map-inv-structure-𝕎-Alg
    issec-map-inv-structure-𝕎-Alg
    isretr-map-inv-structure-𝕎-Alg

equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor A B (𝕎 A B) ≃ 𝕎 A B
equiv-structure-𝕎-Alg =
  pair structure-𝕎-Alg is-equiv-structure-𝕎-Alg

is-equiv-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (map-inv-structure-𝕎-Alg {B = B})
is-equiv-map-inv-structure-𝕎-Alg =
  is-equiv-has-inverse
    structure-𝕎-Alg
    isretr-map-inv-structure-𝕎-Alg
    issec-map-inv-structure-𝕎-Alg

inv-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B ≃ type-polynomial-endofunctor A B (𝕎 A B)
inv-equiv-structure-𝕎-Alg =
  pair map-inv-structure-𝕎-Alg is-equiv-map-inv-structure-𝕎-Alg

-- Morphisms of algebras for polynomial endofunctors
  
hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-algebra-polynomial-endofunctor {A = A} {B} X Y =
  Σ ( type-algebra-polynomial-endofunctor X →
      type-algebra-polynomial-endofunctor Y)
    ( λ f →
      ( f ∘ (structure-algebra-polynomial-endofunctor X)) ~
      ( ( structure-algebra-polynomial-endofunctor Y) ∘
        ( map-polynomial-endofunctor A B f)))

map-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) →
  hom-algebra-polynomial-endofunctor X Y →
  type-algebra-polynomial-endofunctor X →
  type-algebra-polynomial-endofunctor Y
map-hom-algebra-polynomial-endofunctor X Y f = pr1 f

structure-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (Y : algebra-polynomial-endofunctor-UU l4 A B) →
  (f : hom-algebra-polynomial-endofunctor X Y) →
  ( ( map-hom-algebra-polynomial-endofunctor X Y f) ∘
    ( structure-algebra-polynomial-endofunctor X)) ~
  ( ( structure-algebra-polynomial-endofunctor Y) ∘
    ( map-polynomial-endofunctor A B
      ( map-hom-algebra-polynomial-endofunctor X Y f)))
structure-hom-algebra-polynomial-endofunctor X Y f = pr2 f

--------------------------------------------------------------------------------

-- We characterize the identity type of the type of morphisms of algebras
                                                                 
htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y)
  (g : hom-algebra-polynomial-endofunctor X Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
htpy-hom-algebra-polynomial-endofunctor {A = A} {B} X Y f g =
  Σ ( map-hom-algebra-polynomial-endofunctor X Y f ~
      map-hom-algebra-polynomial-endofunctor X Y g)
    ( λ H →
      ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
        ( ( structure-algebra-polynomial-endofunctor Y) ·l
          ( htpy-polynomial-endofunctor A B H))) ~
      ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h
        ( structure-hom-algebra-polynomial-endofunctor X Y g)))

refl-htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  htpy-hom-algebra-polynomial-endofunctor X Y f f
refl-htpy-hom-algebra-polynomial-endofunctor {A = A} {B} X Y f =
  pair refl-htpy
    ( λ z →
      ( ap ( λ t →
             concat
               ( structure-hom-algebra-polynomial-endofunctor X Y f z)
               ( structure-algebra-polynomial-endofunctor Y
                 ( map-polynomial-endofunctor A B
                   ( map-hom-algebra-polynomial-endofunctor X Y f) z) )
               ( ap (structure-algebra-polynomial-endofunctor Y ) t))
           ( coh-refl-htpy-polynomial-endofunctor A B
             ( map-hom-algebra-polynomial-endofunctor X Y f) z)) ∙
      ( right-unit))
  
htpy-hom-algebra-polynomial-endofunctor-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  (g : hom-algebra-polynomial-endofunctor X Y) →
  Id f g → htpy-hom-algebra-polynomial-endofunctor X Y f g
htpy-hom-algebra-polynomial-endofunctor-eq X Y f .f refl =
  refl-htpy-hom-algebra-polynomial-endofunctor X Y f

is-contr-total-htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  is-contr
    ( Σ ( hom-algebra-polynomial-endofunctor X Y)
        ( htpy-hom-algebra-polynomial-endofunctor X Y f))
is-contr-total-htpy-hom-algebra-polynomial-endofunctor {A = A} {B} X Y f =
  is-contr-total-Eq-structure
    ( λ ( g : pr1 X → pr1 Y)
        ( G : (g ∘ pr2 X) ~ ((pr2 Y) ∘ (map-polynomial-endofunctor A B g)))
        ( H : map-hom-algebra-polynomial-endofunctor X Y f ~ g) →
        ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
          ( ( structure-algebra-polynomial-endofunctor Y) ·l
            ( htpy-polynomial-endofunctor A B H))) ~
        ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h G))
    ( is-contr-total-htpy (map-hom-algebra-polynomial-endofunctor X Y f))
    ( pair (map-hom-algebra-polynomial-endofunctor X Y f) refl-htpy)
    ( is-contr-equiv'
      ( Σ ( ( (pr1 f) ∘ pr2 X) ~
            ( pr2 Y ∘ map-polynomial-endofunctor A B (pr1 f)))
          ( λ H → (pr2 f) ~ H))
      ( equiv-tot
        ( λ H →
          ( equiv-concat-htpy
            ( λ x →
              ap ( concat
                   ( pr2 f x)
                   ( structure-algebra-polynomial-endofunctor Y
                     ( map-polynomial-endofunctor A B (pr1 f) x)))
                 ( ap ( ap (pr2 Y))
                      ( coh-refl-htpy-polynomial-endofunctor A B (pr1 f) x)))
            ( H)) ∘e
          ( equiv-concat-htpy right-unit-htpy H)))
      ( is-contr-total-htpy (pr2 f)))

is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  (g : hom-algebra-polynomial-endofunctor X Y) →
  is-equiv (htpy-hom-algebra-polynomial-endofunctor-eq X Y f g)
is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq X Y f =
  fundamental-theorem-id f
    ( refl-htpy-hom-algebra-polynomial-endofunctor X Y f)
    ( is-contr-total-htpy-hom-algebra-polynomial-endofunctor X Y f)
    ( htpy-hom-algebra-polynomial-endofunctor-eq X Y f)
        
eq-htpy-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B)
  (Y : algebra-polynomial-endofunctor-UU l4 A B)
  (f : hom-algebra-polynomial-endofunctor X Y) →
  (g : hom-algebra-polynomial-endofunctor X Y) →
  htpy-hom-algebra-polynomial-endofunctor X Y f g → Id f g
eq-htpy-hom-algebra-polynomial-endofunctor X Y f g =
  map-inv-is-equiv (is-equiv-htpy-hom-algebra-polynomial-endofunctor-eq X Y f g)
                                                                          
--------------------------------------------------------------------------------

-- We show that 𝕎 A B is an initial algebra
  
map-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  𝕎 A B → type-algebra-polynomial-endofunctor X
map-hom-𝕎-Alg X (tree-𝕎 x α) =
  structure-algebra-polynomial-endofunctor X
    ( pair x (λ y → map-hom-𝕎-Alg X (α y)))

structure-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  ( (map-hom-𝕎-Alg X) ∘ structure-𝕎-Alg) ~
  ( ( structure-algebra-polynomial-endofunctor X) ∘
    ( map-polynomial-endofunctor A B (map-hom-𝕎-Alg X)))
structure-hom-𝕎-Alg X (pair x α) = refl

hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X
hom-𝕎-Alg X = pair (map-hom-𝕎-Alg X) (structure-hom-𝕎-Alg X)

htpy-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  map-hom-𝕎-Alg X ~
  map-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f
htpy-htpy-hom-𝕎-Alg {A = A} {B} X f (tree-𝕎 x α) =
  ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
       ( eq-htpy (λ z → htpy-htpy-hom-𝕎-Alg X f (α z)))) ∙
  ( inv
    ( structure-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f
      ( pair x α)))
                 
compute-structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) (x : A) (α : B x → 𝕎 A B)
  {f : 𝕎 A B → type-algebra-polynomial-endofunctor X} →
  (H : map-hom-𝕎-Alg X ~ f) →
  Id ( ap ( structure-algebra-polynomial-endofunctor X)
          ( htpy-polynomial-endofunctor A B H (pair x α)))
     ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
          ( eq-htpy (H ·r α)))
compute-structure-htpy-hom-𝕎-Alg {A = A} {B} X x α = 
  ind-htpy
    ( map-hom-𝕎-Alg X)
    ( λ f H →
      Id ( ap ( structure-algebra-polynomial-endofunctor X)
              ( htpy-polynomial-endofunctor A B H (pair x α)))
         ( ap ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
              ( eq-htpy (H ·r α))))
    ( ap ( ap (pr2 X))
         ( coh-refl-htpy-polynomial-endofunctor A B
           ( map-hom-𝕎-Alg X)
           ( pair x α)) ∙
    ( inv
      ( ap ( ap (λ t → pr2 X (pair x t)))
           ( eq-htpy-refl-htpy (map-hom-𝕎-Alg X ∘ α)))))

structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  ( structure-hom-𝕎-Alg X ∙h
    ( ( structure-algebra-polynomial-endofunctor X) ·l
      ( htpy-polynomial-endofunctor A B (htpy-htpy-hom-𝕎-Alg X f)))) ~
  ( ( (htpy-htpy-hom-𝕎-Alg X f) ·r structure-𝕎-Alg {B = B}) ∙h
    ( structure-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f))
structure-htpy-hom-𝕎-Alg {A = A} {B} X (pair f μ-f) (pair x α) =
  ( ( ( compute-structure-htpy-hom-𝕎-Alg X x α
        ( htpy-htpy-hom-𝕎-Alg X (pair f μ-f)))  ∙
      ( inv right-unit)) ∙
    ( ap ( concat
           ( ap
             ( λ t → pr2 X (pair x t))
             ( eq-htpy (htpy-htpy-hom-𝕎-Alg X (pair f μ-f) ·r α)))
         ( pr2 X (map-polynomial-endofunctor A B f (pair x α))))
         ( inv (left-inv ( μ-f (pair x α)))))) ∙
  ( inv
    ( assoc
      ( ap ( λ t → pr2 X (pair x t))
           ( eq-htpy (htpy-htpy-hom-𝕎-Alg X (pair f μ-f) ·r α)))
      ( inv (μ-f (pair x α)))
      ( μ-f (pair x α))))

htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  htpy-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X (hom-𝕎-Alg X) f
htpy-hom-𝕎-Alg X f =
  pair (htpy-htpy-hom-𝕎-Alg X f) (structure-htpy-hom-𝕎-Alg X f)

is-initial-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor-UU l3 A B) →
  is-contr (hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X)
is-initial-𝕎-Alg {A = A} {B} X =
  pair
    ( hom-𝕎-Alg X)
    ( λ f →
      eq-htpy-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X (hom-𝕎-Alg X) f
        ( htpy-hom-𝕎-Alg X f))

--------------------------------------------------------------------------------

-- Section B.4 Functoriality of 𝕎

map-𝕎' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (g : (x : A) → D (f x) → B x) →
  𝕎 A B → 𝕎 C D
map-𝕎' D f g (tree-𝕎 a α) = tree-𝕎 (f a) (λ d → map-𝕎' D f g (α (g a d)))

map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 A B → 𝕎 C D
map-𝕎 D f e = map-𝕎' D f (λ x → map-inv-equiv (e x))

fib-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  𝕎 C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
fib-map-𝕎 D f e (tree-𝕎 c γ) =
  (fib f c) × ((d : D c) → fib (map-𝕎 D f e) (γ d))

abstract
  equiv-fib-map-𝕎 :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3}
    (D : C → UU l4) (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
    (y : 𝕎 C D) → fib (map-𝕎 D f e) y ≃ fib-map-𝕎 D f e y
  equiv-fib-map-𝕎 {A = A} {B} {C} D f e (tree-𝕎 c γ) =
    ( ( ( inv-equiv
          ( assoc-Σ A
            ( λ a → Id (f a) c)
            ( λ t → (d : D c) → fib (map-𝕎 D f e) (γ d)))) ∘e
        ( equiv-tot
          ( λ a →
            ( ( equiv-tot
                ( λ p →
                  ( ( equiv-Π
                      ( λ (d : D c) → fib (map-𝕎 D f e) (γ d))
                      ( (equiv-tr D p) ∘e (e a))
                      ( λ b → id-equiv)) ∘e
                    ( equiv-inv-choice-∞
                      ( λ b w →
                        Id ( map-𝕎 D f e w)
                           ( γ (tr D p (map-equiv (e a) b)))))) ∘e 
                  ( equiv-tot
                    ( λ α →
                      equiv-Π
                        ( λ (b : B a) →
                          Id ( map-𝕎 D f e (α b))
                             ( γ (tr D p (map-equiv (e a) b))))
                        ( inv-equiv (e a))
                        ( λ d →
                          ( equiv-concat'
                            ( map-𝕎 D f e
                              ( α (map-inv-equiv (e a) d)))
                            ( ap ( γ ∘ (tr D p))
                                 ( inv (issec-map-inv-equiv (e a) d)))) ∘e
                          ( inv-equiv
                            ( equiv-Eq-𝕎-eq
                              ( map-𝕎 D f e
                                ( α (map-inv-equiv (e a) d)))
                              ( γ (tr D p d))))))))) ∘e
              ( equiv-left-swap-Σ)) ∘e
            ( equiv-tot
              ( λ α →
                equiv-Eq-𝕎-eq
                  ( tree-𝕎
                    ( f a)
                    ( ( map-𝕎 D f e) ∘
                      ( α ∘ map-inv-equiv (e a)))) (tree-𝕎 c γ)))))) ∘e
      ( assoc-Σ A
        ( λ a → B a → 𝕎 A B)
        ( λ t →
          Id (map-𝕎 D f e (structure-𝕎-Alg t)) (tree-𝕎 c γ)))) ∘e
    ( equiv-Σ
      ( λ t → Id (map-𝕎 D f e (structure-𝕎-Alg t)) (tree-𝕎 c γ))
      ( inv-equiv-structure-𝕎-Alg)
      ( λ x →
        equiv-concat
          ( ap (map-𝕎 D f e) (issec-map-inv-structure-𝕎-Alg x))
          ( tree-𝕎 c γ)))

is-trunc-map-map-𝕎 :
  {l1 l2 l3 l4 : Level} (k : 𝕋)
  {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-trunc-map k f → is-trunc-map k (map-𝕎 D f e)
is-trunc-map-map-𝕎 k D f e H (tree-𝕎 c γ) =
  is-trunc-equiv k
    ( fib-map-𝕎 D f e (tree-𝕎 c γ))
    ( equiv-fib-map-𝕎 D f e (tree-𝕎 c γ))
    ( is-trunc-Σ
      ( H c)
      ( λ t → is-trunc-Π k (λ d → is-trunc-map-map-𝕎 k D f e H (γ d))))

is-equiv-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-equiv f → is-equiv (map-𝕎 D f e)
is-equiv-map-𝕎 D f e H =
  is-equiv-is-contr-map
    ( is-trunc-map-map-𝕎 neg-two-𝕋 D f e (is-contr-map-is-equiv H))

equiv-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ≃ C) (e : (x : A) → B x ≃ D (map-equiv f x)) →
  𝕎 A B ≃ 𝕎 C D
equiv-𝕎 D f e =
  pair
    ( map-𝕎 D (map-equiv f) e)
    ( is-equiv-map-𝕎 D (map-equiv f) e (is-equiv-map-equiv f))

is-emb-map-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A → C) (e : (x : A) → B x ≃ D (f x)) →
  is-emb f → is-emb (map-𝕎 D f e)
is-emb-map-𝕎 D f e H =
  is-emb-is-prop-map
    (is-trunc-map-map-𝕎 neg-one-𝕋 D f e (is-prop-map-is-emb H))

emb-𝕎 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} (D : C → UU l4)
  (f : A ↪ C) (e : (x : A) → B x ≃ D (map-emb f x)) → 𝕎 A B ↪ 𝕎 C D
emb-𝕎 D f e =
  pair
    ( map-𝕎 D (map-emb f) e)
    ( is-emb-map-𝕎 D (map-emb f) e (is-emb-map-emb f))

--------------------------------------------------------------------------------

-- Section B.5 Indexed W-types

data i𝕎 {l1 l2 l3 : Level} (I : UU l1) (A : I → UU l2) (B : (i : I) → A i → UU l3) (f : (i : I) (x : A i) → B i x → I) (i : I) : UU (l2 ⊔ l3) where
  sup-i𝕎 : (x : A i) (α : (y : B i x) → i𝕎 I A B f (f i x y)) → i𝕎 I A B f i

--------------------------------------------------------------------------------

-- Section B.4 Extensional W-types

-- Definition B.6.1

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _∈-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ∈-𝕎 y = fib (component-𝕎 y) x
  
  extensional-Eq-eq-𝕎 : 
    {x y : 𝕎 A B} → Id x y → (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)
  extensional-Eq-eq-𝕎 refl z = id-equiv

is-extensional-𝕎 :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) → UU (l1 ⊔ l2)
is-extensional-𝕎 A B =
  (x y : 𝕎 A B) → is-equiv (extensional-Eq-eq-𝕎 {x = x} {y})

-- Theorem B.6.2

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  □-∈-𝕎 : (𝕎 A B → UU l3) → (𝕎 A B → UU (l1 ⊔ l2 ⊔ l3))
  □-∈-𝕎 P x = (y : 𝕎 A B) → (y ∈-𝕎 x) → P y

  η-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) → ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-∈-𝕎 P x)
  η-□-∈-𝕎 P f x y e = f y

  ε-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    ((x : 𝕎 A B) → □-∈-𝕎 P x) → (x : 𝕎 A B) → P x
  ε-□-∈-𝕎 P h f x = h x (f x)

  ind-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → □-∈-𝕎 P x
  ind-□-∈-𝕎 P h (tree-𝕎 x α) .(α b) (pair b refl) =
    h (α b) (ind-□-∈-𝕎 P h (α b))

  comp-□-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x y : 𝕎 A B) (e : y ∈-𝕎 x) →
    Id (ind-□-∈-𝕎 P h x y e) (h y (ind-□-∈-𝕎 P h y))
  comp-□-∈-𝕎 P h (tree-𝕎 x α) .(α b) (pair b refl) = refl
  
  ind-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → P x
  ind-∈-𝕎 P h = ε-□-∈-𝕎 P h (ind-□-∈-𝕎 P h)

  comp-∈-𝕎 :
    (P : 𝕎 A B → UU l3) (h : (y : 𝕎 A B) → □-∈-𝕎 P y → P y) →
    (x : 𝕎 A B) → Id (ind-∈-𝕎 P h x) (h x (λ y e → ind-∈-𝕎 P h y))
  comp-∈-𝕎 P h x =
    ap (h x) (eq-htpy (λ y → eq-htpy (λ e → comp-□-∈-𝕎 P h x y e)))

-- Theorem B.6.3

is-univalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-univalent {A = A} B = (x y : A) → is-equiv (λ (p : Id x y) → equiv-tr B p)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-ext-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-ext-𝕎 x y = (z : 𝕎 A B) → (z ∈-𝕎 x) ≃ (z ∈-𝕎 y)

  refl-Eq-ext-𝕎 : (x : 𝕎 A B) → Eq-ext-𝕎 x x
  refl-Eq-ext-𝕎 x z = id-equiv

  Eq-ext-eq-𝕎 : {x y : 𝕎 A B} → Id x y → Eq-ext-𝕎 x y
  Eq-ext-eq-𝕎 {x} refl = refl-Eq-ext-𝕎 x

  Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → UU (l1 ⊔ l2)
  Eq-Eq-ext-𝕎 x y u v =
    (z : 𝕎 A B) → map-equiv (u z) ~ map-equiv (v z)

  refl-Eq-Eq-ext-𝕎 : (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) → Eq-Eq-ext-𝕎 x y u u
  refl-Eq-Eq-ext-𝕎 x y u z = refl-htpy

  is-contr-total-Eq-Eq-ext-𝕎 :
    (x y : 𝕎 A B) (u : Eq-ext-𝕎 x y) →
    is-contr (Σ (Eq-ext-𝕎 x y) (Eq-Eq-ext-𝕎 x y u))
  is-contr-total-Eq-Eq-ext-𝕎 x y u =
    is-contr-total-Eq-Π
      ( λ z e → map-equiv (u z) ~ map-equiv e)
      ( λ z → is-contr-total-htpy-equiv (u z))

  Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → Id u v → Eq-Eq-ext-𝕎 x y u v
  Eq-Eq-ext-eq-𝕎 x y u .u refl = refl-Eq-Eq-ext-𝕎 x y u

  is-equiv-Eq-Eq-ext-eq-𝕎 :
    (x y : 𝕎 A B) (u v : Eq-ext-𝕎 x y) → is-equiv (Eq-Eq-ext-eq-𝕎 x y u v)
  is-equiv-Eq-Eq-ext-eq-𝕎 x y u =
    fundamental-theorem-id u
      ( refl-Eq-Eq-ext-𝕎 x y u)
      ( is-contr-total-Eq-Eq-ext-𝕎 x y u)
      ( Eq-Eq-ext-eq-𝕎 x y u)

  eq-Eq-Eq-ext-𝕎 :
    {x y : 𝕎 A B} {u v : Eq-ext-𝕎 x y} → Eq-Eq-ext-𝕎 x y u v → Id u v
  eq-Eq-Eq-ext-𝕎 {x} {y} {u} {v} =
    map-inv-is-equiv (is-equiv-Eq-Eq-ext-eq-𝕎 x y u v)

  equiv-total-Eq-ext-𝕎 :
    (x : 𝕎 A B) → Σ (𝕎 A B) (Eq-ext-𝕎 x) ≃ Σ A (λ a → B (symbol-𝕎 x) ≃ B a)
  equiv-total-Eq-ext-𝕎 (tree-𝕎 a f) =
    ( ( equiv-tot
            ( λ x →
              ( ( right-unit-law-Σ-is-contr
                  ( λ e → is-contr-total-htpy (f ∘ map-inv-equiv e))) ∘e
                ( equiv-tot
                  ( λ e →
                    equiv-tot
                      ( λ g →
                        equiv-Π
                          ( λ y → Id (f (map-inv-equiv e y)) (g y))
                          ( e)
                          ( λ y →
                            equiv-concat
                              ( ap f (isretr-map-inv-equiv e y))
                              ( g (map-equiv e y))))))) ∘e
              ( ( equiv-left-swap-Σ) ∘e 
                ( equiv-tot
                  ( λ g →
                    inv-equiv (equiv-fam-equiv-equiv-slice f g)))))) ∘e
          ( assoc-Σ
            ( A)
            ( λ x → B x → 𝕎 A B)
            ( λ t → Eq-ext-𝕎 (tree-𝕎 a f) (tree-𝕎 (pr1 t) (pr2 t))))) ∘e
        ( equiv-Σ
          ( λ (t : Σ A (λ x → B x → 𝕎 A B)) →
            Eq-ext-𝕎 (tree-𝕎 a f) (tree-𝕎 (pr1 t) (pr2 t)))
          ( inv-equiv-structure-𝕎-Alg)
          ( H))
    where
    H : (z : 𝕎 A (λ x → B x)) →
        Eq-ext-𝕎 ( tree-𝕎 a f) z ≃
        Eq-ext-𝕎
          ( tree-𝕎 a f)
          ( tree-𝕎
            ( pr1 (map-equiv inv-equiv-structure-𝕎-Alg z))
            ( pr2 (map-equiv inv-equiv-structure-𝕎-Alg z)))
    H (tree-𝕎 b g) = id-equiv

  is-contr-total-Eq-ext-is-univalent-𝕎 :
    is-univalent B → (x : 𝕎 A B) → is-contr (Σ (𝕎 A B) (Eq-ext-𝕎 x))
  is-contr-total-Eq-ext-is-univalent-𝕎 H (tree-𝕎 a f) =
    is-contr-equiv
      ( Σ A (λ x → B a ≃ B x))
      ( equiv-total-Eq-ext-𝕎 (tree-𝕎 a f))
      ( fundamental-theorem-id' a id-equiv (λ x → equiv-tr B) (H a))

  is-extensional-is-univalent-𝕎 :
    is-univalent B → is-extensional-𝕎 A B
  is-extensional-is-univalent-𝕎 H x =
    fundamental-theorem-id x
      ( λ z → id-equiv)
      ( is-contr-total-Eq-ext-is-univalent-𝕎 H x)
      ( λ y → extensional-Eq-eq-𝕎 {y = y})

  is-univalent-is-extensional-𝕎 :
    type-trunc-Prop (𝕎 A B) → is-extensional-𝕎 A B → is-univalent B
  is-univalent-is-extensional-𝕎 p H x =
    apply-universal-property-trunc-Prop p
      ( Π-Prop A (λ y → is-equiv-Prop (λ (γ : Id x y) → equiv-tr B γ)))
      ( λ w →
        fundamental-theorem-id x
          ( id-equiv)
          ( is-contr-equiv'
            ( Σ (𝕎 A B) (Eq-ext-𝕎 (tree-𝕎 x (λ y → w))))
            ( equiv-total-Eq-ext-𝕎 (tree-𝕎 x (λ y → w)))
            ( fundamental-theorem-id'
              ( tree-𝕎 x (λ y → w))
              ( λ z → id-equiv)
              ( λ z → extensional-Eq-eq-𝕎)
              ( H (tree-𝕎 x (λ y → w)))))
          ( λ y →  equiv-tr B {y = y}))

--------------------------------------------------------------------------------

-- Section B.5 Russel's paradox in type theory

-- Definition B.5.1

𝕍 : (l : Level) → UU (lsuc l)
𝕍 l = 𝕎 (UU l) (λ X → X)

-- Definition B.5.2

is-small-𝕍 :
  (l : Level) {l1 : Level} → 𝕍 l1 → UU (l1 ⊔ lsuc l)
is-small-𝕍 l (tree-𝕎 A α) =
  is-small l A × ((x : A) → is-small-𝕍 l (α x))

is-prop-is-small-𝕍 :
  {l l1 : Level} (X : 𝕍 l1) → is-prop (is-small-𝕍 l X)
is-prop-is-small-𝕍 {l} (tree-𝕎 A α) =
  is-prop-prod
    ( is-prop-is-small l A)
    ( is-prop-Π (λ x → is-prop-is-small-𝕍 (α x)))

-- Lemma B.5.3

comprehension-𝕍 :
  {l : Level} (X : 𝕍 l) (P : symbol-𝕎 X → UU l) → 𝕍 l
comprehension-𝕍 X P =
  tree-𝕎 (Σ (symbol-𝕎 X) P) (component-𝕎 X ∘ pr1)

is-small-comprehension-𝕍 :
  (l : Level) {l1 : Level} {X : 𝕍 l1} {P : symbol-𝕎 X → UU l1} →
  is-small-𝕍 l X → ((x : symbol-𝕎 X) → is-small l (P x)) →
  is-small-𝕍 l (comprehension-𝕍 X P)
is-small-comprehension-𝕍 l {l1} {tree-𝕎 A α} {P} (pair (pair X e) H) K =
  pair
    ( is-small-Σ l (pair X e) K)
    ( λ t → H (pr1 t))

-- Proposition B.5.4

_∈-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∈-𝕍 Y = X ∈-𝕎 Y

_∉-𝕍_ : {l : Level} → 𝕍 l → 𝕍 l → UU (lsuc l)
X ∉-𝕍 Y = is-empty (X ∈-𝕍 Y)

is-small-eq-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (Id X Y)
is-small-eq-𝕍 l {l1} {tree-𝕎 A α} {tree-𝕎 B β} (pair (pair X e) H) (pair (pair Y f) K) =
  is-small-equiv l
    ( Eq-𝕎 (tree-𝕎 A α) (tree-𝕎 B β))
    ( equiv-Eq-𝕎-eq (tree-𝕎 A α) (tree-𝕎 B β))
    ( is-small-Σ l
      ( is-small-equiv l
        ( A ≃ B)
        ( equiv-univalence)
        ( pair
          ( X ≃ Y)
          ( equiv-precomp-equiv (inv-equiv e) Y ∘e equiv-postcomp-equiv f A)))
      ( σ))
  where
  σ : (x : Id A B) → is-small l ((z : A) → Eq-𝕎 (α z) (β (tr id x z)))
  σ refl =
    is-small-Π l
      ( pair X e)
      ( λ x →
        is-small-equiv l
          ( Id (α x) (β x))
          ( inv-equiv (equiv-Eq-𝕎-eq (α x) (β x)))
          ( is-small-eq-𝕍 l (H x) (K x)))
  
is-small-∈-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∈-𝕍 Y)
is-small-∈-𝕍 l {l1} {tree-𝕎 A α} {tree-𝕎 B β} H (pair (pair Y f) K) =
  is-small-Σ l
    ( pair Y f)
    ( λ b → is-small-eq-𝕍 l (K b) H)

is-small-∉-𝕍 :
  (l : Level) {l1 : Level} {X Y : 𝕍 l1} →
  is-small-𝕍 l X → is-small-𝕍 l Y → is-small l (X ∉-𝕍 Y)
is-small-∉-𝕍 l H K =
  is-small-Π l
    ( is-small-∈-𝕍 l H K)
    ( λ x → pair (raise-empty l) (equiv-raise-empty l))

-- Definition B.5.3

resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) → is-small-𝕍 l2 X → 𝕍 l2
resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) =
  tree-𝕎 A'
    ( λ x' → resize-𝕍 (α (map-inv-equiv e x')) (H2 (map-inv-equiv e x')))

-- Proposition B.5.6

-- Proposition B.5.6 (i)

is-small-resize-𝕍 :
  {l1 l2 : Level} (X : 𝕍 l1) (H : is-small-𝕍 l2 X) →
  is-small-𝕍 l1 (resize-𝕍 X H)
is-small-resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H2) =
  pair
    ( pair A (inv-equiv e))
    ( λ a' →
      is-small-resize-𝕍
        ( α (map-inv-equiv e a'))
        ( H2 (map-inv-equiv e a')))

-- Proposition B.5.6 (ii)

resize-𝕍' :
  {l1 l2 : Level} →
  Σ (𝕍 l1) (is-small-𝕍 l2) → Σ (𝕍 l2) (is-small-𝕍 l1)
resize-𝕍' (pair X H) = pair (resize-𝕍 X H) (is-small-resize-𝕍 X H)


abstract
  resize-resize-𝕍 :
    {l1 l2 : Level} {x : 𝕍 l1} (H : is-small-𝕍 l2 x) → 
    Id (resize-𝕍 (resize-𝕍 x H) (is-small-resize-𝕍 x H)) x
  resize-resize-𝕍 {x = tree-𝕎 A α} (pair (pair A' e) H) =
    eq-Eq-𝕎
      ( resize-𝕍
        ( resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H))
        ( is-small-resize-𝕍 (tree-𝕎 A α) (pair (pair A' e) H)))
      ( tree-𝕎 A α)
      ( pair
        ( refl)
        ( λ z →
          Eq-𝕎-eq
            ( resize-𝕍
              ( resize-𝕍
                ( α (map-inv-equiv e (map-inv-equiv (inv-equiv e) z)))
                ( H (map-inv-equiv e (map-inv-equiv (inv-equiv e) z))))
              ( is-small-resize-𝕍
                ( α (map-inv-equiv e (map-inv-equiv (inv-equiv e) z)))
                ( H (map-inv-equiv e (map-inv-equiv (inv-equiv e) z)))))
            ( α z)
            ( ( ap
                ( λ t →
                  resize-𝕍
                    ( resize-𝕍 (α t) (H t))
                    ( is-small-resize-𝕍 (α t) (H t)))
                ( isretr-map-inv-equiv e z)) ∙
              ( resize-resize-𝕍 (H z)))))

abstract
  resize-resize-𝕍' :
    {l1 l2 : Level} → (resize-𝕍' {l2} {l1} ∘ resize-𝕍' {l1} {l2}) ~ id
  resize-resize-𝕍' (pair X H) =
    eq-subtype
      ( is-prop-is-small-𝕍)
      ( resize-resize-𝕍 H)

is-equiv-resize-𝕍' :
  {l1 l2 : Level} → is-equiv (resize-𝕍' {l1} {l2})
is-equiv-resize-𝕍' {l1} {l2} =
  is-equiv-has-inverse
    ( resize-𝕍' {l2} {l1})
    ( resize-resize-𝕍')
    ( resize-resize-𝕍')

equiv-resize-𝕍' :
  {l1 l2 : Level} → Σ (𝕍 l1) (is-small-𝕍 l2) ≃ Σ (𝕍 l2) (is-small-𝕍 l1)
equiv-resize-𝕍' {l1} {l2} = pair resize-𝕍' is-equiv-resize-𝕍'

eq-resize-𝕍 :
  {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
  Id x y ≃ Id (resize-𝕍 x H) (resize-𝕍 y K)
eq-resize-𝕍 H K =
  ( equiv-Eq-eq-total-subtype
    ( is-prop-is-small-𝕍)
    ( resize-𝕍' (pair _ H))
    ( resize-𝕍' (pair _ K))) ∘e
  ( ( equiv-ap (equiv-resize-𝕍') (pair _ H) (pair _ K)) ∘e
    ( inv-equiv
      ( equiv-Eq-eq-total-subtype
        ( is-prop-is-small-𝕍)
        ( pair _ H)
        ( pair _ K))))

-- Proposition B.5.7

abstract
  equiv-elementhood-resize-𝕍 :
    {l1 l2 : Level} {x y : 𝕍 l1} (H : is-small-𝕍 l2 x) (K : is-small-𝕍 l2 y) →
    (x ∈-𝕍 y) ≃ (resize-𝕍 x H ∈-𝕍 resize-𝕍 y K)
  equiv-elementhood-resize-𝕍 {x = X} {tree-𝕎 B β} H (pair (pair B' e) K) =
    equiv-Σ
      ( λ y' →
        Id ( component-𝕎 (resize-𝕍 (tree-𝕎 B β) (pair (pair B' e) K)) y')
           ( resize-𝕍 X H))
      ( e)
      ( λ b →
        ( equiv-concat
          ( ap
            ( λ t → resize-𝕍 (β t) (K t))
            ( isretr-map-inv-equiv e b))
          ( resize-𝕍 X H)) ∘e
        ( eq-resize-𝕍 (K b) H))

-- Definition B.5.8

is-small-multiset-𝕍 :
  {l1 l2 : Level} →
  ((A : UU l1) → is-small l2 A) → (X : 𝕍 l1) → is-small-𝕍 l2 X
is-small-multiset-𝕍 {l1} {l2} H (tree-𝕎 A α) =
  pair (H A) (λ x → is-small-multiset-𝕍 H (α x))

is-small-lsuc : {l : Level} (X : UU l) → is-small (lsuc l) X
is-small-lsuc X = pair (raise _ X) (equiv-raise _ X)

universal-tree-𝕍 : (l : Level) → 𝕍 (lsuc l)
universal-tree-𝕍 l =
  tree-𝕎
    ( 𝕍 l)
    ( λ X → resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))

-- Proposition B.5.9

is-small-universe :
  (l l1 : Level) → UU (lsuc l1 ⊔ lsuc l)
is-small-universe l l1 = is-small l (UU l1) × ((X : UU l1) → is-small l X)

is-small-universal-tree-𝕍 :
  (l : Level) {l1 : Level} →
  is-small-universe l l1 → is-small-𝕍 l (universal-tree-𝕍 l1)
is-small-universal-tree-𝕍 l {l1} (pair (pair U e) H) =
  pair
    ( pair
      ( 𝕎 U (λ x → pr1 (H (map-inv-equiv e x))))
      ( equiv-𝕎
        ( λ u → type-is-small (H (map-inv-equiv e u)))
        ( e)
        ( λ X →
          tr ( λ t → X ≃ pr1 (H t))
             ( inv (isretr-map-inv-equiv e X))
             ( pr2 (H X)))))
    ( f)
    where
    f : (X : 𝕍 l1) →
        is-small-𝕍 l
          ( resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))
    f (tree-𝕎 A α) =
      pair
        ( pair
          ( type-is-small (H A))
          ( equiv-is-small (H A) ∘e inv-equiv (equiv-raise (lsuc l1) A)))
        ( λ x → f (α (map-inv-raise x)))

-- Theorem B.5.10

Russell : (l : Level) → 𝕍 (lsuc l)
Russell l =
  comprehension-𝕍
    ( universal-tree-𝕍 l)
    ( λ X → X ∉-𝕍 X)

is-small-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → is-small-𝕍 l2 (Russell l1)
is-small-Russell {l1} {l2} H =
  is-small-comprehension-𝕍 l2
    ( is-small-universal-tree-𝕍 l2 H)
    ( λ X → is-small-∉-𝕍 l2 (K X) (K X))
  where
  K = is-small-multiset-𝕍 (λ A → pr2 H A)

resize-Russell :
  {l1 l2 : Level} → is-small-universe l2 l1 → 𝕍 l2
resize-Russell {l1} {l2} H =
  resize-𝕍 (Russell l1) (is-small-Russell H)

is-small-resize-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  is-small-𝕍 (lsuc l1) (resize-Russell H)
is-small-resize-Russell {l1} {l2} H =
  is-small-resize-𝕍 (Russell l1) (is-small-Russell H)

equiv-Russell-in-Russell :
  {l1 l2 : Level} (H : is-small-universe l2 l1) →
  (Russell l1 ∈-𝕍 Russell l1) ≃ (resize-Russell H ∈-𝕍 resize-Russell H)
equiv-Russell-in-Russell H =
  equiv-elementhood-resize-𝕍 (is-small-Russell H) (is-small-Russell H)

paradox-Russell : {l : Level} → ¬ (is-small l (UU l))
paradox-Russell {l} H =
  no-fixed-points-neg
    ( R ∈-𝕍 R)
    ( pair (map-equiv β) (map-inv-equiv β))

  where
  
  K : is-small-universe l l
  K = pair H (λ X → pair X id-equiv)

  R : 𝕍 (lsuc l)
  R = Russell l
  
  is-small-R : is-small-𝕍 l R
  is-small-R = is-small-Russell K

  R' : 𝕍 l
  R' = resize-Russell K

  is-small-R' : is-small-𝕍 (lsuc l) R'
  is-small-R' = is-small-resize-Russell K

  abstract
    p : Id (resize-𝕍 R' is-small-R') R
    p = resize-resize-𝕍 is-small-R

  α : (R ∈-𝕍 R) ≃ (R' ∈-𝕍 R')
  α = equiv-Russell-in-Russell K

  abstract
    β : (R ∈-𝕍 R) ≃ (R ∉-𝕍 R)
    β = ( equiv-precomp α empty) ∘e
        ( ( left-unit-law-Σ-is-contr
            { B = λ t → (pr1 t) ∉-𝕍 (pr1 t)}
            ( is-contr-total-path' R')
            ( pair R' refl)) ∘e
          ( ( inv-assoc-Σ (𝕍 l) (λ t → Id t R') (λ t → (pr1 t) ∉-𝕍 (pr1 t))) ∘e
            ( ( equiv-tot
                ( λ t →
                  ( commutative-prod) ∘e
                  ( equiv-prod
                    ( id-equiv)
                    ( inv-equiv
                      ( ( equiv-concat'
                          _ ( p)) ∘e
                        ( eq-resize-𝕍
                          ( is-small-multiset-𝕍 is-small-lsuc t)
                          ( is-small-R'))))))) ∘e
              ( assoc-Σ
                ( 𝕍 l)
                ( λ t → t ∉-𝕍 t)
                ( λ t → Id ( resize-𝕍
                             ( pr1 t)
                             ( is-small-multiset-𝕍 is-small-lsuc (pr1 t)))
                           ( R))))))

--------------------------------------------------------------------------------

-- Exercises

_∉-𝕎_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
x ∉-𝕎 y = is-empty (x ∈-𝕎 y)

irreflexive-∈-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (x : 𝕎 A B) → x ∉-𝕎 x
irreflexive-∈-𝕎 {A = A} {B = B} (tree-𝕎 x α) (pair y p) =
  irreflexive-∈-𝕎 (α y) (tr (λ z → (α y) ∈-𝕎 z) (inv p) (pair y refl))

-- Exercise B.5

-- Exercise B.5 (a)

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  -- We define the strict ordering on 𝕎 A B
  
  data _le-𝕎_ (x : 𝕎 A B) : 𝕎 A B → UU (l1 ⊔ l2) where
    le-∈-𝕎 : {y : 𝕎 A B} → x ∈-𝕎 y → x le-𝕎 y
    propagate-le-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x le-𝕎 y → x le-𝕎 z

  -- The strict ordering is transitive, irreflexive, and asymmetric
  
  transitive-le-𝕎 : {x y z : 𝕎 A B} → y le-𝕎 z → x le-𝕎 y → x le-𝕎 z
  transitive-le-𝕎 {x = x} {y} {z} (le-∈-𝕎 H) K =
    propagate-le-𝕎 H K
  transitive-le-𝕎 {x = x} {y} {z} (propagate-le-𝕎 L H) K =
    propagate-le-𝕎 L (transitive-le-𝕎 H K)

  irreflexive-le-𝕎 :
    {x : 𝕎 A B} → ¬ (x le-𝕎 x)
  irreflexive-le-𝕎 {x = x} (le-∈-𝕎 H) = irreflexive-∈-𝕎 x H
  irreflexive-le-𝕎 {x = tree-𝕎 x α} (propagate-le-𝕎 (pair b refl) H) =
    irreflexive-le-𝕎 {x = α b} (transitive-le-𝕎 H (le-∈-𝕎 (pair b refl)))

  asymmetric-le-𝕎 :
    {x y : 𝕎 A B} → x le-𝕎 y → y le-𝕎 x → empty
  asymmetric-le-𝕎 H K = irreflexive-le-𝕎 (transitive-le-𝕎 H K)

-- Exercise B.5 (b)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3)
  where
  
  -- We define an operation □-𝕎 that acts on families over 𝕎 A B.

  □-𝕎 : 𝕎 A B → UU (l1 ⊔ l2 ⊔ l3)
  □-𝕎 x = (y : 𝕎 A B) → (y le-𝕎 x) → P y

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : 𝕎 A B → UU l3}
  where

  -- The unit of □-𝕎 takes sections of P to sections of □-𝕎 P

  unit-□-𝕎 :
    ((x : 𝕎 A B) → P x) → ((x : 𝕎 A B) → □-𝕎 P x)
  unit-□-𝕎 f x y p = f y

  -- The reflector (counit) of □-𝕎 is dual, with an extra hypothesis

  reflect-□-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) →
    ((x : 𝕎 A B) → □-𝕎 P x) → ((x : 𝕎 A B) → P x)
  reflect-□-𝕎 h f x = h x (f x)

  {- We first prove an intermediate induction principle with computation rule,
     where we obtain sections of □-𝕎 P. -}

  □-strong-ind-𝕎 :
    ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → □-𝕎 P x
  □-strong-ind-𝕎 h (tree-𝕎 x α) .(α b) (le-∈-𝕎 (pair b refl)) =
    h (α b) (□-strong-ind-𝕎 h (α b))
  □-strong-ind-𝕎 h (tree-𝕎 x α) y (propagate-le-𝕎 (pair b refl) K) =
    □-strong-ind-𝕎 h (α b) y K

  □-strong-comp-𝕎 :
    (h : (x : 𝕎 A B) → □-𝕎 P x → P x)
    (x : 𝕎 A B) (y : 𝕎 A B) (p : y le-𝕎 x) →
    Id (□-strong-ind-𝕎 h x y p) (h y (□-strong-ind-𝕎 h y))
  □-strong-comp-𝕎 h (tree-𝕎 x α) .(α b) (le-∈-𝕎 (pair b refl)) =
    refl
  □-strong-comp-𝕎 h (tree-𝕎 x α) y (propagate-le-𝕎 (pair b refl) K) =
    □-strong-comp-𝕎 h (α b) y K

{- Now we prove the actual induction principle with computation rule, where we
   obtain sections of P. -}

strong-ind-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) → 
  ((x : 𝕎 A B) → □-𝕎 P x → P x) → (x : 𝕎 A B) → P x
strong-ind-𝕎 P h = reflect-□-𝕎 h (□-strong-ind-𝕎 h)
                                               
strong-comp-𝕎 :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (P : 𝕎 A B → UU l3) →
  (h : (x : 𝕎 A B) → □-𝕎 P x → P x) (x : 𝕎 A B) →
  Id (strong-ind-𝕎 P h x) (h x (unit-□-𝕎 (strong-ind-𝕎 P h) x))
strong-comp-𝕎 P h x =
  ap (h x) (eq-htpy (λ y → eq-htpy (λ p → □-strong-comp-𝕎 h x y p)))

-- Exercise B.5 (c)

no-infinite-descent-𝕎 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (f : ℕ → 𝕎 A B) → ¬ ((n : ℕ) → (f (succ-ℕ n) le-𝕎 (f n)))
no-infinite-descent-𝕎 {A = A} {B} f =
  strong-ind-𝕎
    ( λ x → (f : ℕ → 𝕎 A B) (p : Id (f zero-ℕ) x) →
            ¬ ((n : ℕ) → (f (succ-ℕ n)) le-𝕎 (f n)))
    ( λ x IH f p H →
      IH ( f one-ℕ)
         ( tr (λ t → (f one-ℕ) le-𝕎 t) p (H zero-ℕ))
         ( f ∘ succ-ℕ)
         ( refl)
         ( λ n → H (succ-ℕ n)))
    ( f zero-ℕ)
    ( f)
    ( refl)

-- Exercise B.6

-- Exercise B.7

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _≼-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  (tree-𝕎 x α) ≼-𝕎-Prop (tree-𝕎 y β) =
    Π-Prop (B x) (λ b → exists-Prop (λ c → (α b) ≼-𝕎-Prop (β c)))

  _≼-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≼-𝕎 y = type-Prop (x ≼-𝕎-Prop y)

  _≺-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  x ≺-𝕎-Prop y =
    exists-Prop (λ (t : Σ (𝕎 A B) (λ w → w ∈-𝕎 y)) → x ≼-𝕎-Prop (pr1 t))

  _≺-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x ≺-𝕎 y = type-Prop (x ≺-𝕎-Prop y)

  -- Exercise B.7 (a)

  refl-≼-𝕎 : (x : 𝕎 A B) → x ≼-𝕎 x
  refl-≼-𝕎 (tree-𝕎 x α) b = unit-trunc-Prop (pair b (refl-≼-𝕎 (α b)))

  transitive-≼-𝕎 : {x y z : 𝕎 A B} → (x ≼-𝕎 y) → (y ≼-𝕎 z) → (x ≼-𝕎 z)
  transitive-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} {tree-𝕎 z γ} H K a =
    apply-universal-property-trunc-Prop
      ( H a)
      ( exists-Prop (λ c → (α a) ≼-𝕎-Prop (γ c)))
      ( λ t →
        apply-universal-property-trunc-Prop
          ( K (pr1 t))
          ( exists-Prop (λ c → (α a) ≼-𝕎-Prop (γ c)))
          ( λ s →
            unit-trunc-Prop
              ( pair
                ( pr1 s)
                ( transitive-≼-𝕎
                  { α a}
                  { β (pr1 t)}
                  { γ (pr1 s)}
                  ( pr2 t)
                  ( pr2 s)))))

  -- Exercise B.7 (a) (i)

  _strong-≼-𝕎-Prop_ : 𝕎 A B → 𝕎 A B → UU-Prop (l1 ⊔ l2)
  x strong-≼-𝕎-Prop y =
    Π-Prop
      ( 𝕎 A B)
      ( λ u →
        Π-Prop
          ( u ∈-𝕎 x)
          ( λ H →
            exists-Prop
              ( λ (v : 𝕎 A B) →
                exists-Prop (λ (K : v ∈-𝕎 y) → u ≼-𝕎-Prop v))))

  _strong-≼-𝕎_ : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  x strong-≼-𝕎 y = type-Prop (x strong-≼-𝕎-Prop y)

  strong-≼-≼-𝕎 : {x y : 𝕎 A B} → (x ≼-𝕎 y) → (x strong-≼-𝕎 y)
  strong-≼-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} H .(α b) (pair b refl) =
    apply-universal-property-trunc-Prop (H b)
      ( exists-Prop ((λ v → exists-Prop (λ hv → (α b) ≼-𝕎-Prop v))))
      ( f)
      where
      f : Σ (B y) (λ c → pr1 (α b ≼-𝕎-Prop β c)) →
          exists (λ v → exists-Prop (λ hv → α b ≼-𝕎-Prop v))
      f (pair c K) =
        intro-exists
          ( λ v → exists-Prop (λ hv → α b ≼-𝕎-Prop v))
          ( β c)
          ( intro-exists
            ( λ hβc → α b ≼-𝕎-Prop β c)
            ( pair c refl)
            ( K))

  ≼-strong-≼-𝕎 : {x y : 𝕎 A B} → (x strong-≼-𝕎 y) → (x ≼-𝕎 y)
  ≼-strong-≼-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} H b =
    apply-universal-property-trunc-Prop
      ( H (α b) (pair b refl))
      ( exists-Prop (λ c → α b ≼-𝕎-Prop β c))
      ( f)
    where
    f : Σ ( 𝕎 A B) (λ v → exists (λ K → α b ≼-𝕎-Prop v)) →
        exists (λ c → α b ≼-𝕎-Prop β c)
    f (pair v K) =
        apply-universal-property-trunc-Prop K
          ( exists-Prop (λ c → α b ≼-𝕎-Prop β c))
          ( g)
      where
      g : (v ∈-𝕎 tree-𝕎 y β) × (α b ≼-𝕎 v) → ∃ (λ c → α b ≼-𝕎 β c)
      g (pair (pair c p) M) = intro-∃ c (tr (λ t → α b ≼-𝕎 t) (inv p) M)

  -- Exercise B.7 (a) (ii)

  ≼-∈-𝕎 : {x y : 𝕎 A B} → (x ∈-𝕎 y) → (x ≼-𝕎 y)
  ≼-∈-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} (pair v p) u =
    intro-exists
      ( λ z → α u ≼-𝕎-Prop β z)
      ( v)
      ( tr ( λ t → α u ≼-𝕎 t)
           ( inv p)
           ( ≼-∈-𝕎 {α u} {tree-𝕎 x α} (pair u refl)))

  ≼-le-𝕎 : {x y : 𝕎 A B} → (x le-𝕎 y) → (x ≼-𝕎 y)
  ≼-le-𝕎 {x} {y} (le-∈-𝕎 H) = ≼-∈-𝕎 H
  ≼-le-𝕎 {x} {y} (propagate-le-𝕎 {y = y'} K H) =
    transitive-≼-𝕎 {x} {y = y'} {y} (≼-le-𝕎 H) (≼-∈-𝕎 K)

  -- Exercise B.7 (a) (iii)

  not-≼-∈-𝕎 : {x y : 𝕎 A B} → (x ∈-𝕎 y) → ¬ (y ≼-𝕎 x)
  not-≼-∈-𝕎 {tree-𝕎 x α} {tree-𝕎 y β} (pair b p) K =
    apply-universal-property-trunc-Prop (K b) (empty-Prop) f
    where
    f : Σ (B x) (λ c → β b ≼-𝕎 α c) → empty
    f (pair c L) =
      not-≼-∈-𝕎 {α c} {β b} (tr (λ t → α c ∈-𝕎 t) (inv p) (pair c refl)) L

  not-≼-le-𝕎 : {x y : 𝕎 A B} → (x le-𝕎 y) → ¬ (y ≼-𝕎 x)
  not-≼-le-𝕎 {x} {y} (le-∈-𝕎 H) = not-≼-∈-𝕎 {x} {y} H
  not-≼-le-𝕎 {x} {y} (propagate-le-𝕎 {y = y'} H K) L =
    not-≼-∈-𝕎 {y'} {y} H (transitive-≼-𝕎 {y} {x} {y'} L (≼-le-𝕎 K))

  -- Exercise B.7 (a) (iv)

  is-least-≼-constant-𝕎 :
    {x : A} (h : is-empty (B x)) (w : 𝕎 A B) → constant-𝕎 x h ≼-𝕎 w
  is-least-≼-constant-𝕎 h (tree-𝕎 y β) x = ex-falso (h x)

  is-least-≼-is-constant-𝕎 :
    {x : 𝕎 A B} → is-constant-𝕎 x → (y : 𝕎 A B) → x ≼-𝕎 y
  is-least-≼-is-constant-𝕎 {tree-𝕎 x α} H (tree-𝕎 y β) z =
    ex-falso (H z)

  is-constant-is-least-≼-𝕎 :
    {x : 𝕎 A B} → ((y : 𝕎 A B) → x ≼-𝕎 y) → is-constant-𝕎 x
  is-constant-is-least-≼-𝕎 {tree-𝕎 x α} H b =
    not-≼-∈-𝕎 {α b} {tree-𝕎 x α} (pair b refl) (H (α b))

  -- Exercise B.7 (b)

  ≼-≺-𝕎 : {x y : 𝕎 A B} → (x ≺-𝕎 y) → (x ≼-𝕎 y)
  ≼-≺-𝕎 {x} {y} H =
    apply-universal-property-trunc-Prop H (x ≼-𝕎-Prop y) f
    where
    f : Σ (Σ (𝕎 A B) (λ w → w ∈-𝕎 y)) (λ t → x ≼-𝕎 pr1 t) → (x ≼-𝕎 y)
    f (pair (pair w K) L) = transitive-≼-𝕎 {x} {w} {y} L (≼-∈-𝕎 K)

  transitive-≺-𝕎 : {x y z : 𝕎 A B} → (x ≺-𝕎 y) → (y ≺-𝕎 z) → (x ≺-𝕎 z)
  transitive-≺-𝕎 {x} {y} {z} H K =
    apply-universal-property-trunc-Prop H (x ≺-𝕎-Prop z) f
    where
    f : Σ (Σ (𝕎 A B) (λ w → w ∈-𝕎 y)) (λ t → x ≼-𝕎 pr1 t) → x ≺-𝕎 z
    f (pair (pair w L) M) =
      apply-universal-property-trunc-Prop K (x ≺-𝕎-Prop z) g
      where
      g : Σ (Σ (𝕎 A B) (λ w → w ∈-𝕎 z)) (λ t → y ≼-𝕎 pr1 t) → x ≺-𝕎 z
      g (pair (pair v P) Q) =
        intro-exists
          ( λ (t : Σ (𝕎 A B) (λ s → s ∈-𝕎 z)) → x ≼-𝕎-Prop (pr1 t))
          ( pair v P)
          ( transitive-≼-𝕎 {x} {w} {v} M
            ( transitive-≼-𝕎 {w} {y} {v} (≼-∈-𝕎 L) Q))

  irreflexive-≺-𝕎 : {x : 𝕎 A B} → ¬ (x ≺-𝕎 x)
  irreflexive-≺-𝕎 {tree-𝕎 x α} H =
    apply-universal-property-trunc-Prop H empty-Prop f
    where
    f : ¬ ( Σ ( Σ (𝕎 A B) (λ w → w ∈-𝕎 tree-𝕎 x α))
              ( λ t → tree-𝕎 x α ≼-𝕎 pr1 t))
    f (pair (pair w K) L) = not-≼-∈-𝕎 {w} {tree-𝕎 x α} K L

  in-lower-set-≺-𝕎-Prop : (x y : 𝕎 A B) → UU-Prop (l1 ⊔ l2)
  in-lower-set-≺-𝕎-Prop x y = y ≺-𝕎-Prop x

  in-lower-set-≺-𝕎 : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  in-lower-set-≺-𝕎 x y = y ≺-𝕎 x

  has-same-lower-set-≺-𝕎 : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  has-same-lower-set-≺-𝕎 x y = (z : 𝕎 A B) → (z ≺-𝕎 x) × (z ≺-𝕎 y)

  _≈-𝕎-Prop_ : (x y : 𝕎 A B) → UU-Prop (l1 ⊔ l2)
  x ≈-𝕎-Prop y = prod-Prop (x ≼-𝕎-Prop y) (y ≼-𝕎-Prop x)

  _≈-𝕎_ : (x y : 𝕎 A B) → UU (l1 ⊔ l2)
  x ≈-𝕎 y = type-Prop (x ≈-𝕎-Prop y)

{-
  ≈-has-same-lower-set-≺-𝕎 :
    {x y : 𝕎 A B} → has-same-lower-set-≺-𝕎 x y → x ≈-𝕎 y
  ≈-has-same-lower-set-≺-𝕎 {x} {y} H = {!!}
-}

--------------------------------------------------------------------------------

data _leq-𝕎_ {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (x : 𝕎 A B) :
  𝕎 A B → UU (l1 ⊔ l2) where
  refl-leq-𝕎 : x leq-𝕎 x
  propagate-leq-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x leq-𝕎 y → x leq-𝕎 z

--------------------------------------------------------------------------------

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data Path-𝕎 : 𝕎 A B → UU (l1 ⊔ l2) where
    root : (w : 𝕎 A B) → Path-𝕎 w
    cons : (a : A) (f : B a → 𝕎 A B) (b : B a) → Path-𝕎 (f b) → Path-𝕎 (tree-𝕎 a f)

  length-Path-𝕎 : (w : 𝕎 A B) → Path-𝕎 w → ℕ
  length-Path-𝕎 w (root .w) = zero-ℕ
  length-Path-𝕎 .(tree-𝕎 a f) (cons a f b p) = succ-ℕ (length-Path-𝕎 (f b) p)
```
