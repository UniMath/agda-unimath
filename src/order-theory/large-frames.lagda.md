# Large frames

```agda
module order-theory.large-frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.top-elements-large-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets
```

</details>

## Idea

A **large frame** is a large meet-suplattice satisfying the distributive law
for meets over suprema.

## Definitions

### Large frames

```agda
record
  Large-Frame (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Frame
  field
    large-poset-Large-Frame :
      Large-Poset α β
    is-large-meet-semilattice-Large-Frame :
      is-large-meet-semilattice-Large-Poset large-poset-Large-Frame
    is-large-suplattice-Large-Frame :
      is-large-suplattice-Large-Poset large-poset-Large-Frame
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
  {α : Level → Level} {β : Level → Level → Level} (L : Large-Frame α β)
  where

  set-Large-Frame : (l : Level) → Set (α l)
  set-Large-Frame = set-Large-Poset (large-poset-Large-Frame L)

  type-Large-Frame : (l : Level) → UU (α l)
  type-Large-Frame = type-Large-Poset (large-poset-Large-Frame L)

  is-set-type-Large-Frame : {l : Level} → is-set (type-Large-Frame l)
  is-set-type-Large-Frame =
    is-set-type-Large-Poset (large-poset-Large-Frame L)

  leq-Large-Frame-Prop :
    {l1 l2 : Level} →
    type-Large-Frame l1 → type-Large-Frame l2 → Prop (β l1 l2)
  leq-Large-Frame-Prop = leq-Large-Poset-Prop (large-poset-Large-Frame L)

  leq-Large-Frame :
    {l1 l2 : Level} → type-Large-Frame l1 → type-Large-Frame l2 → UU (β l1 l2)
  leq-Large-Frame = leq-Large-Poset (large-poset-Large-Frame L)

  is-prop-leq-Large-Frame :
    {l1 l2 : Level} (x : type-Large-Frame l1) (y : type-Large-Frame l2) →
    is-prop (leq-Large-Frame x y)
  is-prop-leq-Large-Frame =
    is-prop-leq-Large-Poset (large-poset-Large-Frame L)

  refl-leq-Large-Frame :
    {l1 : Level} (x : type-Large-Frame l1) → leq-Large-Frame x x
  refl-leq-Large-Frame = refl-leq-Large-Poset (large-poset-Large-Frame L)

  antisymmetric-leq-Large-Frame :
    {l1 : Level} (x y : type-Large-Frame l1) →
    leq-Large-Frame x y → leq-Large-Frame y x → x ＝ y
  antisymmetric-leq-Large-Frame =
    antisymmetric-leq-Large-Poset (large-poset-Large-Frame L)

  transitive-leq-Large-Frame :
    {l1 l2 l3 : Level}
    (x : type-Large-Frame l1) (y : type-Large-Frame l2)
    (z : type-Large-Frame l3) →
    leq-Large-Frame y z → leq-Large-Frame x y → leq-Large-Frame x z
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
    (I → type-Large-Frame l2) → type-Large-Frame (l1 ⊔ l2)
  sup-Large-Frame =
    sup-is-large-suplattice-Large-Poset
      ( large-poset-Large-Frame L)
      ( is-large-suplattice-Large-Frame L)

  is-least-upper-bound-sup-Large-Frame :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Frame l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Frame L)
      ( x)
      ( sup-Large-Frame x)
  is-least-upper-bound-sup-Large-Frame =
    is-least-upper-bound-sup-is-large-suplattice-Large-Poset
      ( large-poset-Large-Frame L)
      ( is-large-suplattice-Large-Frame L)

  large-suplattice-Large-Frame : Large-Suplattice α β
  large-poset-Large-Suplattice large-suplattice-Large-Frame =
    large-poset-Large-Frame L
  is-large-suplattice-Large-Suplattice large-suplattice-Large-Frame =
    is-large-suplattice-Large-Frame L
```
