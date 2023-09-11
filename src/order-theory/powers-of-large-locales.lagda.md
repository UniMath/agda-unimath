# Powers of large locales

```agda
module order-theory.powers-of-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.dependent-products-large-locales
open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.top-elements-large-posets
```

</details>

## Idea

Given a large locale `L` and a type `X : UU l`, the **large power locale** is
the locale `X → L` of functions from `X` to `L`.

## Definitions

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level} {l1 : Level}
  (X : UU l1) (L : Large-Locale α β γ)
  where

  power-Large-Locale :
    Large-Locale (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  power-Large-Locale = Π-Large-Locale (λ (x : X) → L)

  large-poset-power-Large-Locale :
    Large-Poset (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-poset-power-Large-Locale =
    large-poset-Large-Locale power-Large-Locale

  set-power-Large-Locale : (l : Level) → Set (α l ⊔ l1)
  set-power-Large-Locale =
    set-Large-Locale power-Large-Locale

  type-power-Large-Locale : (l : Level) → UU (α l ⊔ l1)
  type-power-Large-Locale =
    type-Large-Locale power-Large-Locale

  is-set-type-power-Large-Locale :
    {l : Level} → is-set (type-power-Large-Locale l)
  is-set-type-power-Large-Locale =
    is-set-type-Large-Locale power-Large-Locale

  leq-power-Large-Locale-Prop :
    Large-Relation-Prop
      ( λ l2 → α l2 ⊔ l1)
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-power-Large-Locale)
  leq-power-Large-Locale-Prop =
    leq-Large-Locale-Prop power-Large-Locale

  leq-power-Large-Locale :
    Large-Relation
      ( λ l2 → α l2 ⊔ l1)
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-power-Large-Locale)
  leq-power-Large-Locale =
    leq-Large-Locale power-Large-Locale

  is-prop-leq-power-Large-Locale :
    is-prop-Large-Relation (type-power-Large-Locale) (leq-power-Large-Locale)
  is-prop-leq-power-Large-Locale =
    is-prop-leq-Large-Locale power-Large-Locale

  refl-leq-power-Large-Locale :
    is-large-reflexive type-power-Large-Locale leq-power-Large-Locale
  refl-leq-power-Large-Locale =
    refl-leq-Large-Locale power-Large-Locale

  antisymmetric-leq-power-Large-Locale :
    is-large-antisymmetric type-power-Large-Locale leq-power-Large-Locale
  antisymmetric-leq-power-Large-Locale =
    antisymmetric-leq-Large-Locale power-Large-Locale

  transitive-leq-power-Large-Locale :
    is-large-transitive type-power-Large-Locale leq-power-Large-Locale
  transitive-leq-power-Large-Locale =
    transitive-leq-Large-Locale power-Large-Locale

  large-meet-semilattice-power-Large-Locale :
    Large-Meet-Semilattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-meet-semilattice-power-Large-Locale =
    large-meet-semilattice-Large-Locale power-Large-Locale

  has-meets-power-Large-Locale :
    has-meets-Large-Poset large-poset-power-Large-Locale
  has-meets-power-Large-Locale =
    has-meets-Large-Locale power-Large-Locale

  meet-power-Large-Locale :
    {l2 l3 : Level} →
    type-power-Large-Locale l2 → type-power-Large-Locale l3 →
    type-power-Large-Locale (l2 ⊔ l3)
  meet-power-Large-Locale =
    meet-Large-Locale power-Large-Locale

  is-greatest-binary-lower-bound-meet-power-Large-Locale :
    {l2 l3 : Level}
    (x : type-power-Large-Locale l2)
    (y : type-power-Large-Locale l3) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-power-Large-Locale)
      ( x)
      ( y)
      ( meet-power-Large-Locale x y)
  is-greatest-binary-lower-bound-meet-power-Large-Locale =
    is-greatest-binary-lower-bound-meet-Large-Locale power-Large-Locale

  has-top-element-power-Large-Locale :
    has-top-element-Large-Poset large-poset-power-Large-Locale
  has-top-element-power-Large-Locale =
    has-top-element-Large-Locale power-Large-Locale

  top-power-Large-Locale : type-power-Large-Locale lzero
  top-power-Large-Locale = top-Large-Locale power-Large-Locale

  is-top-element-top-power-Large-Locale :
    {l1 : Level} (x : type-power-Large-Locale l1) →
    leq-power-Large-Locale x top-power-Large-Locale
  is-top-element-top-power-Large-Locale =
    is-top-element-top-Large-Locale power-Large-Locale

  large-suplattice-power-Large-Locale :
    Large-Suplattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  large-suplattice-power-Large-Locale =
    large-suplattice-Large-Locale power-Large-Locale

  is-large-suplattice-power-Large-Locale :
    is-large-suplattice-Large-Poset γ large-poset-power-Large-Locale
  is-large-suplattice-power-Large-Locale =
    is-large-suplattice-Large-Locale power-Large-Locale

  sup-power-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-power-Large-Locale l3) →
    type-power-Large-Locale (γ ⊔ l2 ⊔ l3)
  sup-power-Large-Locale =
    sup-Large-Locale power-Large-Locale

  is-least-upper-bound-sup-power-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-power-Large-Locale l3) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-power-Large-Locale)
      ( x)
      ( sup-power-Large-Locale x)
  is-least-upper-bound-sup-power-Large-Locale =
    is-least-upper-bound-sup-Large-Locale power-Large-Locale

  distributive-meet-sup-power-Large-Locale :
    {l2 l3 l4 : Level}
    (x : type-power-Large-Locale l2)
    {J : UU l3} (y : J → type-power-Large-Locale l4) →
    meet-power-Large-Locale x (sup-power-Large-Locale y) ＝
    sup-power-Large-Locale (λ j → meet-power-Large-Locale x (y j))
  distributive-meet-sup-power-Large-Locale =
    distributive-meet-sup-Large-Locale power-Large-Locale
```
