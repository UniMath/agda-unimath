# The large locale of subtypes

```agda
module foundation.large-locale-of-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.large-binary-relations
open import foundation.large-locale-of-propositions
open import foundation.large-reflexive-relations
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.sets

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

  powerset-Large-Locale :
    Large-Locale (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3)) lzero
  powerset-Large-Locale = power-Large-Locale A Prop-Large-Locale

  large-poset-powerset-Large-Locale :
    Large-Poset (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3))
  large-poset-powerset-Large-Locale =
    large-poset-Large-Locale powerset-Large-Locale

  set-powerset-Large-Locale : (l : Level) → Set (l1 ⊔ lsuc l)
  set-powerset-Large-Locale =
    set-Large-Locale powerset-Large-Locale

  type-powerset-Large-Locale : (l : Level) → UU (l1 ⊔ lsuc l)
  type-powerset-Large-Locale =
    type-Large-Locale powerset-Large-Locale

  is-set-type-powerset-Large-Locale :
    {l : Level} → is-set (type-powerset-Large-Locale l)
  is-set-type-powerset-Large-Locale =
    is-set-type-Large-Locale powerset-Large-Locale

  large-meet-semilattice-powerset-Large-Locale :
    Large-Meet-Semilattice (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3))
  large-meet-semilattice-powerset-Large-Locale =
    large-meet-semilattice-Large-Locale powerset-Large-Locale

  large-suplattice-powerset-Large-Locale :
    Large-Suplattice (λ l2 → l1 ⊔ lsuc l2) (λ l2 l3 → l1 ⊔ (l2 ⊔ l3)) lzero
  large-suplattice-powerset-Large-Locale =
    large-suplattice-Large-Locale powerset-Large-Locale

module _
  {l1 : Level} {A : UU l1}
  where

  leq-prop-powerset-Large-Locale :
    Large-Relation-Prop
      ( λ l2 l3 → l1 ⊔ l2 ⊔ l3)
      ( type-powerset-Large-Locale A)
  leq-prop-powerset-Large-Locale =
    leq-prop-Large-Locale (powerset-Large-Locale A)

  leq-powerset-Large-Locale :
    Large-Relation
      ( λ l2 l3 → l1 ⊔ l2 ⊔ l3)
      ( type-powerset-Large-Locale A)
  leq-powerset-Large-Locale =
    leq-Large-Locale (powerset-Large-Locale A)

  is-prop-leq-powerset-Large-Locale :
    is-prop-Large-Relation
      ( type-powerset-Large-Locale A)
      ( leq-powerset-Large-Locale)
  is-prop-leq-powerset-Large-Locale =
    is-prop-leq-Large-Locale (powerset-Large-Locale A)

  refl-leq-powerset-Large-Locale :
    is-reflexive-Large-Relation
      ( type-powerset-Large-Locale A)
      ( leq-powerset-Large-Locale)
  refl-leq-powerset-Large-Locale =
    refl-leq-Large-Locale (powerset-Large-Locale A)

  antisymmetric-leq-powerset-Large-Locale :
    is-antisymmetric-Large-Relation
      ( type-powerset-Large-Locale A)
      ( leq-powerset-Large-Locale)
  antisymmetric-leq-powerset-Large-Locale =
    antisymmetric-leq-Large-Locale (powerset-Large-Locale A)

  transitive-leq-powerset-Large-Locale :
    is-transitive-Large-Relation
      ( type-powerset-Large-Locale A)
      ( leq-powerset-Large-Locale)
  transitive-leq-powerset-Large-Locale =
    transitive-leq-Large-Locale (powerset-Large-Locale A)

  has-meets-powerset-Large-Locale :
    has-meets-Large-Poset (large-poset-powerset-Large-Locale A)
  has-meets-powerset-Large-Locale =
    has-meets-Large-Locale (powerset-Large-Locale A)

  meet-powerset-Large-Locale :
    {l2 l3 : Level} →
    type-powerset-Large-Locale A l2 →
    type-powerset-Large-Locale A l3 →
    type-powerset-Large-Locale A (l2 ⊔ l3)
  meet-powerset-Large-Locale =
    meet-Large-Locale (powerset-Large-Locale A)

  is-greatest-binary-lower-bound-meet-powerset-Large-Locale :
    {l2 l3 : Level}
    (x : type-powerset-Large-Locale A l2)
    (y : type-powerset-Large-Locale A l3) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-powerset-Large-Locale A)
      ( x)
      ( y)
      ( meet-powerset-Large-Locale x y)
  is-greatest-binary-lower-bound-meet-powerset-Large-Locale =
    is-greatest-binary-lower-bound-meet-Large-Locale (powerset-Large-Locale A)

  is-large-suplattice-powerset-Large-Locale :
    is-large-suplattice-Large-Poset lzero (large-poset-powerset-Large-Locale A)
  is-large-suplattice-powerset-Large-Locale =
    is-large-suplattice-Large-Locale (powerset-Large-Locale A)

  sup-powerset-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-powerset-Large-Locale A l3) →
    type-powerset-Large-Locale A (l2 ⊔ l3)
  sup-powerset-Large-Locale =
    sup-Large-Locale (powerset-Large-Locale A)

  is-least-upper-bound-sup-powerset-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-powerset-Large-Locale A l3) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-powerset-Large-Locale A)
      ( x)
      ( sup-powerset-Large-Locale x)
  is-least-upper-bound-sup-powerset-Large-Locale =
    is-least-upper-bound-sup-Large-Locale (powerset-Large-Locale A)

  distributive-meet-sup-powerset-Large-Locale :
    {l2 l3 l4 : Level}
    (x : type-powerset-Large-Locale A l2)
    {J : UU l3} (y : J → type-powerset-Large-Locale A l4) →
    meet-powerset-Large-Locale x (sup-powerset-Large-Locale y) ＝
    sup-powerset-Large-Locale (λ j → meet-powerset-Large-Locale x (y j))
  distributive-meet-sup-powerset-Large-Locale =
    distributive-meet-sup-Large-Locale (powerset-Large-Locale A)
```
