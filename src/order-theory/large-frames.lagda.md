# Large frames

```agda
module order-theory.large-frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.preorders
open import order-theory.suplattices
open import order-theory.top-elements-large-posets
open import order-theory.upper-bounds-large-posets
```

</details>

## Idea

A **large frame** is a large [meet-suplattice](order-theory.meet-suplattices.md)
satisfying the distributive law for meets over suprema.

## Definitions

### Large frames

```agda
record
  Large-Frame (α : Level → Level) (β : Level → Level → Level) (γ : Level) : UUω
  where
  constructor
    make-Large-Frame
  field
    large-poset-Large-Frame :
      Large-Poset α β
    is-large-meet-semilattice-Large-Frame :
      is-large-meet-semilattice-Large-Poset large-poset-Large-Frame
    is-large-suplattice-Large-Frame :
      is-large-suplattice-Large-Poset γ large-poset-Large-Frame
    distributive-meet-sup-Large-Frame :
      {l1 l2 l3 : Level}
      (x : type-Large-Poset large-poset-Large-Frame l1)
      {I : UU l2} (y : I → type-Large-Poset large-poset-Large-Frame l3) →
      meet-is-large-meet-semilattice-Large-Poset
        ( large-poset-Large-Frame)
        ( is-large-meet-semilattice-Large-Frame)
        ( x)
        ( sup-has-least-upper-bound-family-of-elements-Large-Poset
          ( is-large-suplattice-Large-Frame y)) ＝
      sup-has-least-upper-bound-family-of-elements-Large-Poset
        ( is-large-suplattice-Large-Frame
          ( λ i →
            meet-is-large-meet-semilattice-Large-Poset
              ( large-poset-Large-Frame)
              ( is-large-meet-semilattice-Large-Frame)
              ( x)
              ( y i)))

open Large-Frame public

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Frame α β γ)
  where

  large-preorder-Large-Frame : Large-Preorder α β
  large-preorder-Large-Frame =
    large-preorder-Large-Poset (large-poset-Large-Frame L)

  set-Large-Frame : (l : Level) → Set (α l)
  set-Large-Frame = set-Large-Poset (large-poset-Large-Frame L)

  type-Large-Frame : (l : Level) → UU (α l)
  type-Large-Frame = type-Large-Poset (large-poset-Large-Frame L)

  is-set-type-Large-Frame : {l : Level} → is-set (type-Large-Frame l)
  is-set-type-Large-Frame =
    is-set-type-Large-Poset (large-poset-Large-Frame L)

  leq-Large-Frame-Prop : Large-Relation-Prop α β type-Large-Frame
  leq-Large-Frame-Prop = leq-Large-Poset-Prop (large-poset-Large-Frame L)

  leq-Large-Frame : Large-Relation α β type-Large-Frame
  leq-Large-Frame = leq-Large-Poset (large-poset-Large-Frame L)

  is-prop-leq-Large-Frame :
    is-prop-Large-Relation type-Large-Frame leq-Large-Frame
  is-prop-leq-Large-Frame =
    is-prop-leq-Large-Poset (large-poset-Large-Frame L)

  leq-eq-Large-Frame :
    {l1 : Level} {x y : type-Large-Frame l1} →
    (x ＝ y) → leq-Large-Frame x y
  leq-eq-Large-Frame =
    leq-eq-Large-Poset (large-poset-Large-Frame L)

  refl-leq-Large-Frame : is-large-reflexive type-Large-Frame leq-Large-Frame
  refl-leq-Large-Frame = refl-leq-Large-Poset (large-poset-Large-Frame L)

  antisymmetric-leq-Large-Frame :
    is-large-antisymmetric type-Large-Frame leq-Large-Frame
  antisymmetric-leq-Large-Frame =
    antisymmetric-leq-Large-Poset (large-poset-Large-Frame L)

  transitive-leq-Large-Frame :
    is-large-transitive type-Large-Frame leq-Large-Frame
  transitive-leq-Large-Frame =
    transitive-leq-Large-Poset (large-poset-Large-Frame L)

  large-meet-semilattice-Large-Frame :
    Large-Meet-Semilattice α β
  large-poset-Large-Meet-Semilattice large-meet-semilattice-Large-Frame =
    large-poset-Large-Frame L
  is-large-meet-semilattice-Large-Meet-Semilattice
    large-meet-semilattice-Large-Frame =
    is-large-meet-semilattice-Large-Frame L

  has-meets-Large-Frame :
    has-meets-Large-Poset (large-poset-Large-Frame L)
  has-meets-Large-Frame =
    has-meets-Large-Meet-Semilattice large-meet-semilattice-Large-Frame

  meet-Large-Frame :
    {l1 l2 : Level} →
    type-Large-Frame l1 → type-Large-Frame l2 → type-Large-Frame (l1 ⊔ l2)
  meet-Large-Frame =
    meet-is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Frame L)
      ( is-large-meet-semilattice-Large-Frame L)

  is-greatest-binary-lower-bound-meet-Large-Frame :
    {l1 l2 : Level} →
    (x : type-Large-Frame l1) (y : type-Large-Frame l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Frame L)
      ( x)
      ( y)
      ( meet-Large-Frame x y)
  is-greatest-binary-lower-bound-meet-Large-Frame =
    is-greatest-binary-lower-bound-meet-is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Frame L)
      ( is-large-meet-semilattice-Large-Frame L)

  ap-meet-Large-Frame :
    {l1 l2 : Level}
    {x x' : type-Large-Frame l1} {y y' : type-Large-Frame l2} →
    (x ＝ x') → (y ＝ y') → (meet-Large-Frame x y ＝ meet-Large-Frame x' y')
  ap-meet-Large-Frame =
    ap-meet-Large-Meet-Semilattice large-meet-semilattice-Large-Frame

  has-top-element-Large-Frame :
    has-top-element-Large-Poset (large-poset-Large-Frame L)
  has-top-element-Large-Frame =
    has-top-element-Large-Meet-Semilattice
      large-meet-semilattice-Large-Frame

  top-Large-Frame : type-Large-Frame lzero
  top-Large-Frame =
    top-Large-Meet-Semilattice large-meet-semilattice-Large-Frame

  is-top-element-top-Large-Frame :
    {l1 : Level} (x : type-Large-Frame l1) →
    leq-Large-Frame x top-Large-Frame
  is-top-element-top-Large-Frame =
    is-top-element-top-Large-Meet-Semilattice
      large-meet-semilattice-Large-Frame

  sup-Large-Frame :
    {l1 l2 : Level} {I : UU l1} →
    (I → type-Large-Frame l2) → type-Large-Frame (γ ⊔ l1 ⊔ l2)
  sup-Large-Frame =
    sup-is-large-suplattice-Large-Poset γ
      ( large-poset-Large-Frame L)
      ( is-large-suplattice-Large-Frame L)

  is-least-upper-bound-sup-Large-Frame :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Frame l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Frame L)
      ( x)
      ( sup-Large-Frame x)
  is-least-upper-bound-sup-Large-Frame =
    is-least-upper-bound-sup-is-large-suplattice-Large-Poset γ
      ( large-poset-Large-Frame L)
      ( is-large-suplattice-Large-Frame L)

  large-suplattice-Large-Frame : Large-Suplattice α β γ
  large-poset-Large-Suplattice large-suplattice-Large-Frame =
    large-poset-Large-Frame L
  is-large-suplattice-Large-Suplattice large-suplattice-Large-Frame =
    is-large-suplattice-Large-Frame L

  is-upper-bound-sup-Large-Frame :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Frame l2) →
    is-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Frame L)
      ( x)
      ( sup-Large-Frame x)
  is-upper-bound-sup-Large-Frame =
    is-upper-bound-sup-Large-Suplattice large-suplattice-Large-Frame
```

## Properties

### Small constructions from large frames

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Frame α β γ)
  where

  preorder-Large-Frame : (l : Level) → Preorder (α l) (β l l)
  preorder-Large-Frame = preorder-Large-Preorder (large-preorder-Large-Frame L)

  poset-Large-Frame : (l : Level) → Poset (α l) (β l l)
  poset-Large-Frame = poset-Large-Poset (large-poset-Large-Frame L)

  is-suplattice-poset-Large-Frame :
    (l1 l2 : Level) → is-suplattice-Poset l1 (poset-Large-Frame (γ ⊔ l1 ⊔ l2))
  pr1 (is-suplattice-poset-Large-Frame l1 l2 I y) =
    sup-Large-Frame L y
  pr2 (is-suplattice-poset-Large-Frame l1 l2 I y) =
    is-least-upper-bound-sup-Large-Frame L y

  suplattice-Large-Frame :
    (l1 l2 : Level) →
    Suplattice (α (γ ⊔ l1 ⊔ l2)) (β (γ ⊔ l1 ⊔ l2) (γ ⊔ l1 ⊔ l2)) l1
  pr1 (suplattice-Large-Frame l1 l2) = poset-Large-Frame (γ ⊔ l1 ⊔ l2)
  pr2 (suplattice-Large-Frame l1 l2) = is-suplattice-poset-Large-Frame l1 l2

  is-meet-semilattice-poset-Large-Frame :
    (l : Level) → is-meet-semilattice-Poset (poset-Large-Frame l)
  pr1 (is-meet-semilattice-poset-Large-Frame l x y) =
    meet-Large-Frame L x y
  pr2 (is-meet-semilattice-poset-Large-Frame l x y) =
    is-greatest-binary-lower-bound-meet-Large-Frame L x y

  order-theoretic-meet-semilattice-Large-Frame :
    (l : Level) → Order-Theoretic-Meet-Semilattice (α l) (β l l)
  pr1 (order-theoretic-meet-semilattice-Large-Frame l) =
    poset-Large-Frame l
  pr2 (order-theoretic-meet-semilattice-Large-Frame l) =
    is-meet-semilattice-poset-Large-Frame l

  meet-semilattice-Large-Frame : (l : Level) → Meet-Semilattice (α l)
  meet-semilattice-Large-Frame =
    meet-semilattice-Large-Meet-Semilattice
      ( large-meet-semilattice-Large-Frame L)
```
