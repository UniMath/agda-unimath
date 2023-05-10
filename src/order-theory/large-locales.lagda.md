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
open import order-theory.large-frames
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.top-elements-large-posets
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
Large-Locale :
  (α : Level → Level) (β : Level → Level → Level) → UUω
Large-Locale α β = Large-Frame α β

module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Locale α β)
  where

  large-poset-Large-Locale : Large-Poset α β
  large-poset-Large-Locale = large-poset-Large-Frame L

  set-Large-Locale : (l : Level) → Set (α l)
  set-Large-Locale = set-Large-Frame L

  type-Large-Locale : (l : Level) → UU (α l)
  type-Large-Locale = type-Large-Frame L

  is-set-type-Large-Locale : {l : Level} → is-set (type-Large-Locale l)
  is-set-type-Large-Locale = is-set-type-Large-Frame L

  leq-Large-Locale-Prop :
    {l1 l2 : Level} →
    type-Large-Locale l1 → type-Large-Locale l2 → Prop (β l1 l2)
  leq-Large-Locale-Prop = leq-Large-Frame-Prop L

  leq-Large-Locale :
    {l1 l2 : Level} → type-Large-Locale l1 → type-Large-Locale l2 → UU (β l1 l2)
  leq-Large-Locale = leq-Large-Frame L

  is-prop-leq-Large-Locale :
    {l1 l2 : Level} (x : type-Large-Locale l1) (y : type-Large-Locale l2) →
    is-prop (leq-Large-Locale x y)
  is-prop-leq-Large-Locale = is-prop-leq-Large-Frame L

  refl-leq-Large-Locale :
    {l1 : Level} (x : type-Large-Locale l1) → leq-Large-Locale x x
  refl-leq-Large-Locale = refl-leq-Large-Frame L

  antisymmetric-leq-Large-Locale :
    {l1 : Level} (x y : type-Large-Locale l1) →
    leq-Large-Locale x y → leq-Large-Locale y x → x ＝ y
  antisymmetric-leq-Large-Locale =
    antisymmetric-leq-Large-Frame L

  transitive-leq-Large-Locale :
    {l1 l2 l3 : Level}
    (x : type-Large-Locale l1) (y : type-Large-Locale l2)
    (z : type-Large-Locale l3) →
    leq-Large-Locale y z → leq-Large-Locale x y → leq-Large-Locale x z
  transitive-leq-Large-Locale =
    transitive-leq-Large-Frame L

  is-large-meet-semilattice-Large-Locale :
    is-large-meet-semilattice-Large-Poset large-poset-Large-Locale
  is-large-meet-semilattice-Large-Locale =
    is-large-meet-semilattice-Large-Frame L

  large-meet-semilattice-Large-Locale : Large-Meet-Semilattice α β
  large-meet-semilattice-Large-Locale =
    large-meet-semilattice-Large-Frame L

  has-meets-Large-Locale : has-meets-Large-Poset large-poset-Large-Locale
  has-meets-Large-Locale =
    has-meets-Large-Meet-Semilattice large-meet-semilattice-Large-Locale

  meet-Large-Locale :
    {l1 l2 : Level} →
    type-Large-Locale l1 → type-Large-Locale l2 → type-Large-Locale (l1 ⊔ l2)
  meet-Large-Locale = meet-Large-Frame L

  is-greatest-binary-lower-bound-meet-Large-Locale :
    {l1 l2 : Level} →
    (x : type-Large-Locale l1) (y : type-Large-Locale l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Locale)
      ( x)
      ( y)
      ( meet-Large-Locale x y)
  is-greatest-binary-lower-bound-meet-Large-Locale =
    is-greatest-binary-lower-bound-meet-Large-Frame L

  has-top-element-Large-Locale :
    has-top-element-Large-Poset large-poset-Large-Locale
  has-top-element-Large-Locale =
    has-top-element-Large-Frame L

  top-Large-Locale : type-Large-Locale lzero
  top-Large-Locale = top-Large-Frame L

  is-top-element-top-Large-Locale :
    {l1 : Level} (x : type-Large-Locale l1) →
    leq-Large-Locale x top-Large-Locale
  is-top-element-top-Large-Locale =
    is-top-element-top-Large-Frame L

  large-suplattice-Large-Locale : Large-Suplattice α β
  large-suplattice-Large-Locale = large-suplattice-Large-Frame L

  is-large-suplattice-Large-Locale :
    is-large-suplattice-Large-Poset large-poset-Large-Locale
  is-large-suplattice-Large-Locale = is-large-suplattice-Large-Frame L

  sup-Large-Locale :
    {l1 l2 : Level} {I : UU l1} →
    (I → type-Large-Locale l2) → type-Large-Locale (l1 ⊔ l2)
  sup-Large-Locale = sup-Large-Frame L

  is-least-upper-bound-sup-Large-Locale :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Locale l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Locale)
      ( x)
      ( sup-Large-Locale x)
  is-least-upper-bound-sup-Large-Locale =
    is-least-upper-bound-sup-Large-Frame L

  distributive-meet-sup-Large-Locale :
    {l1 l2 l3 : Level}
    (x : type-Large-Poset large-poset-Large-Locale l1)
    {I : UU l2} (y : I → type-Large-Poset large-poset-Large-Locale l3) →
    meet-Large-Locale x (sup-Large-Locale y) ＝
    sup-Large-Locale (λ i → meet-Large-Locale x (y i))
  distributive-meet-sup-Large-Locale =
    distributive-meet-sup-Large-Frame L
```
