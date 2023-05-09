# Large locales

```agda
module order-theory.large-locales where
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
open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets
```

</details>

## Idea

A **large locale** is a large meet-suplattice satisfying the distributive law
for meets over suprema.

## Definitions

### Large locales

```agda
record
  Large-Locale (α : Level → Level) (β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Locale
  field
    large-poset-Large-Locale :
      Large-Poset α β
    has-meets-Large-Locale :
      has-meets-Large-Poset large-poset-Large-Locale
    is-large-suplattice-Large-Locale :
      is-large-suplattice-Large-Poset large-poset-Large-Locale
    distributive-meet-sup-Large-Locale :
      {l1 l2 l3 : Level}
      (x : type-Large-Poset large-poset-Large-Locale l1)
      {I : UU l2} (y : I → type-Large-Poset large-poset-Large-Locale l3) →
      meet-has-meets-Large-Poset has-meets-Large-Locale
        ( x)
        ( sup-has-least-upper-bound-family-of-elements-Large-Poset
          ( is-large-suplattice-Large-Locale y)) ＝
      sup-has-least-upper-bound-family-of-elements-Large-Poset
        ( is-large-suplattice-Large-Locale
          ( λ i → meet-has-meets-Large-Poset has-meets-Large-Locale x (y i)))

open Large-Locale public

module _
  {α : Level → Level} {β : Level → Level → Level} (L : Large-Locale α β)
  where

  set-Large-Locale : (l : Level) → Set (α l)
  set-Large-Locale = set-Large-Poset (large-poset-Large-Locale L)

  type-Large-Locale : (l : Level) → UU (α l)
  type-Large-Locale = type-Large-Poset (large-poset-Large-Locale L)

  is-set-type-Large-Locale : {l : Level} → is-set (type-Large-Locale l)
  is-set-type-Large-Locale =
    is-set-type-Large-Poset (large-poset-Large-Locale L)

  leq-Large-Locale-Prop :
    {l1 l2 : Level} →
    type-Large-Locale l1 → type-Large-Locale l2 → Prop (β l1 l2)
  leq-Large-Locale-Prop = leq-Large-Poset-Prop (large-poset-Large-Locale L)

  leq-Large-Locale :
    {l1 l2 : Level} → type-Large-Locale l1 → type-Large-Locale l2 → UU (β l1 l2)
  leq-Large-Locale = leq-Large-Poset (large-poset-Large-Locale L)

  is-prop-leq-Large-Locale :
    {l1 l2 : Level} (x : type-Large-Locale l1) (y : type-Large-Locale l2) →
    is-prop (leq-Large-Locale x y)
  is-prop-leq-Large-Locale =
    is-prop-leq-Large-Poset (large-poset-Large-Locale L)

  refl-leq-Large-Locale :
    {l1 : Level} (x : type-Large-Locale l1) → leq-Large-Locale x x
  refl-leq-Large-Locale = refl-leq-Large-Poset (large-poset-Large-Locale L)

  antisymmetric-leq-Large-Locale :
    {l1 : Level} (x y : type-Large-Locale l1) →
    leq-Large-Locale x y → leq-Large-Locale y x → x ＝ y
  antisymmetric-leq-Large-Locale =
    antisymmetric-leq-Large-Poset (large-poset-Large-Locale L)

  transitive-leq-Large-Locale :
    {l1 l2 l3 : Level}
    (x : type-Large-Locale l1) (y : type-Large-Locale l2)
    (z : type-Large-Locale l3) →
    leq-Large-Locale y z → leq-Large-Locale x y → leq-Large-Locale x z
  transitive-leq-Large-Locale =
    transitive-leq-Large-Poset (large-poset-Large-Locale L)

  meet-Large-Locale :
    {l1 l2 : Level} →
    type-Large-Locale l1 → type-Large-Locale l2 → type-Large-Locale (l1 ⊔ l2)
  meet-Large-Locale =
    meet-has-meets-Large-Poset (has-meets-Large-Locale L)

  is-greatest-binary-lower-bound-meet-Large-Locale :
    {l1 l2 : Level} →
    (x : type-Large-Locale l1) (y : type-Large-Locale l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Locale L)
      ( x)
      ( y)
      ( meet-Large-Locale x y)
  is-greatest-binary-lower-bound-meet-Large-Locale =
    is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
      ( has-meets-Large-Locale L)

  large-meet-semilattice-Large-Locale :
    Large-Meet-Semilattice α β
  large-poset-Large-Meet-Semilattice large-meet-semilattice-Large-Locale =
    large-poset-Large-Locale L
  has-meets-Large-Meet-Semilattice large-meet-semilattice-Large-Locale =
    has-meets-Large-Locale L

  sup-Large-Locale :
    {l1 l2 : Level} {I : UU l1} →
    (I → type-Large-Locale l2) → type-Large-Locale (l1 ⊔ l2)
  sup-Large-Locale =
    sup-is-large-suplattice-Large-Poset
      ( large-poset-Large-Locale L)
      ( is-large-suplattice-Large-Locale L)

  is-least-upper-bound-sup-Large-Locale :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Locale l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Locale L)
      ( x)
      ( sup-Large-Locale x)
  is-least-upper-bound-sup-Large-Locale =
    is-least-upper-bound-sup-is-large-suplattice-Large-Poset
      ( large-poset-Large-Locale L)
      ( is-large-suplattice-Large-Locale L)

  large-suplattice-Large-Locale : Large-Suplattice α β
  large-poset-Large-Suplattice large-suplattice-Large-Locale =
    large-poset-Large-Locale L
  is-large-suplattice-Large-Suplattice large-suplattice-Large-Locale =
    is-large-suplattice-Large-Locale L
```
