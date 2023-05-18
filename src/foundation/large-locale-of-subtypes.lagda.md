# The large locale of subtypes

```agda
module foundation.large-locale-of-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-locale-of-propositions

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.powers-of-large-locales
```

</details>

## Idea

The **large locale of subtypes** of a type `A` is the
[power locale](order-theory.powers-of-large-locales.md) `A → Prop-Large-Locale`.

## Definition

```agda
module _
  {l1 : Level} (A : UU l1)
  where

  power-set-Large-Locale :
    Large-Locale (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3))
  power-set-Large-Locale = power-Large-Locale A Prop-Large-Locale

  large-poset-power-set-Large-Locale :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3))
  large-poset-power-set-Large-Locale =
    large-poset-Large-Locale power-set-Large-Locale

  set-power-set-Large-Locale : (l : Level) → Set (l1 ⊔ lsuc l)
  set-power-set-Large-Locale =
    set-Large-Locale power-set-Large-Locale

  type-power-set-Large-Locale : (l : Level) → UU (l1 ⊔ lsuc l)
  type-power-set-Large-Locale =
    type-Large-Locale power-set-Large-Locale

  is-set-type-power-set-Large-Locale :
    {l : Level} → is-set (type-power-set-Large-Locale l)
  is-set-type-power-set-Large-Locale =
    is-set-type-Large-Locale power-set-Large-Locale

  large-meet-semilattice-power-set-Large-Locale :
    Large-Meet-Semilattice (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3))
  large-meet-semilattice-power-set-Large-Locale =
    large-meet-semilattice-Large-Locale power-set-Large-Locale

  large-suplattice-power-set-Large-Locale :
    Large-Suplattice (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3))
  large-suplattice-power-set-Large-Locale =
    large-suplattice-Large-Locale power-set-Large-Locale

module _
  {l1 : Level} {A : UU l1}
  where

  leq-power-set-Large-Locale-Prop :
    {l2 l3 : Level} →
    type-power-set-Large-Locale A l2 → type-power-set-Large-Locale A l3 →
    Prop (l1 ⊔ l2 ⊔ l3)
  leq-power-set-Large-Locale-Prop =
    leq-Large-Locale-Prop (power-set-Large-Locale A)

  leq-power-set-Large-Locale :
    {l2 l3 : Level} →
    type-power-set-Large-Locale A l2 → type-power-set-Large-Locale A l3 →
    UU (l1 ⊔ l2 ⊔ l3)
  leq-power-set-Large-Locale =
    leq-Large-Locale (power-set-Large-Locale A)

  is-prop-leq-power-set-Large-Locale :
    {l2 l3 : Level}
    (x : type-power-set-Large-Locale A l2)
    (y : type-power-set-Large-Locale A l3) →
    is-prop (leq-power-set-Large-Locale x y)
  is-prop-leq-power-set-Large-Locale =
    is-prop-leq-Large-Locale (power-set-Large-Locale A)

  refl-leq-power-set-Large-Locale :
    {l2 : Level} (x : type-power-set-Large-Locale A l2) →
    leq-power-set-Large-Locale x x
  refl-leq-power-set-Large-Locale =
    refl-leq-Large-Locale (power-set-Large-Locale A)

  antisymmetric-leq-power-set-Large-Locale :
    {l2 : Level} (x y : type-power-set-Large-Locale A l2) →
    leq-power-set-Large-Locale x y → leq-power-set-Large-Locale y x → x ＝ y
  antisymmetric-leq-power-set-Large-Locale =
    antisymmetric-leq-Large-Locale (power-set-Large-Locale A)

  transitive-leq-power-set-Large-Locale :
    {l2 l3 l4 : Level}
    (x : type-power-set-Large-Locale A l2)
    (y : type-power-set-Large-Locale A l3)
    (z : type-power-set-Large-Locale A l4) →
    leq-power-set-Large-Locale y z → leq-power-set-Large-Locale x y →
    leq-power-set-Large-Locale x z
  transitive-leq-power-set-Large-Locale =
    transitive-leq-Large-Locale (power-set-Large-Locale A)

  has-meets-power-set-Large-Locale :
    has-meets-Large-Poset (large-poset-power-set-Large-Locale A)
  has-meets-power-set-Large-Locale =
    has-meets-Large-Locale (power-set-Large-Locale A)

  meet-power-set-Large-Locale :
    {l2 l3 : Level} →
    type-power-set-Large-Locale A l2 →
    type-power-set-Large-Locale A l3 →
    type-power-set-Large-Locale A (l2 ⊔ l3)
  meet-power-set-Large-Locale =
    meet-Large-Locale (power-set-Large-Locale A)

  is-greatest-binary-lower-bound-meet-power-set-Large-Locale :
    {l2 l3 : Level}
    (x : type-power-set-Large-Locale A l2)
    (y : type-power-set-Large-Locale A l3) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-power-set-Large-Locale A)
      ( x)
      ( y)
      ( meet-power-set-Large-Locale x y)
  is-greatest-binary-lower-bound-meet-power-set-Large-Locale =
    is-greatest-binary-lower-bound-meet-Large-Locale (power-set-Large-Locale A)

  is-large-suplattice-power-set-Large-Locale :
    is-large-suplattice-Large-Poset (large-poset-power-set-Large-Locale A)
  is-large-suplattice-power-set-Large-Locale =
    is-large-suplattice-Large-Locale (power-set-Large-Locale A)

  sup-power-set-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-power-set-Large-Locale A l3) →
    type-power-set-Large-Locale A (l2 ⊔ l3)
  sup-power-set-Large-Locale =
    sup-Large-Locale (power-set-Large-Locale A)

  is-least-upper-bound-sup-power-set-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-power-set-Large-Locale A l3) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-power-set-Large-Locale A)
      ( x)
      ( sup-power-set-Large-Locale x)
  is-least-upper-bound-sup-power-set-Large-Locale =
    is-least-upper-bound-sup-Large-Locale (power-set-Large-Locale A)

  distributive-meet-sup-power-set-Large-Locale :
    {l2 l3 l4 : Level}
    (x : type-power-set-Large-Locale A l2)
    {J : UU l3} (y : J → type-power-set-Large-Locale A l4) →
    meet-power-set-Large-Locale x (sup-power-set-Large-Locale y) ＝
    sup-power-set-Large-Locale (λ j → meet-power-set-Large-Locale x (y j))
  distributive-meet-sup-power-set-Large-Locale =
    distributive-meet-sup-Large-Locale (power-set-Large-Locale A)
```
