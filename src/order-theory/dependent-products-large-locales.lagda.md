# Dependent products of large locales

```agda
module order-theory.dependent-products-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.dependent-products-large-frames
open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
open import order-theory.top-elements-large-posets
```

</details>

Given a family `L : I → Large-Locale α β` of large locales indexed by a type
`I : UU l`, the product of the large locales `L i` is again a large locale.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  {l1 : Level} {I : UU l1} (L : I → Large-Locale α β γ)
  where

  Π-Large-Locale : Large-Locale (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  Π-Large-Locale = Π-Large-Frame L

  large-poset-Π-Large-Locale :
    Large-Poset (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-poset-Π-Large-Locale = large-poset-Π-Large-Frame L

  large-meet-semilattice-Π-Large-Locale :
    Large-Meet-Semilattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-meet-semilattice-Π-Large-Locale =
    large-meet-semilattice-Π-Large-Frame L

  has-meets-Π-Large-Locale :
    has-meets-Large-Poset large-poset-Π-Large-Locale
  has-meets-Π-Large-Locale = has-meets-Π-Large-Frame L

  large-suplattice-Π-Large-Locale :
    Large-Suplattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1) γ
  large-suplattice-Π-Large-Locale = large-suplattice-Π-Large-Frame L

  is-large-suplattice-Π-Large-Locale :
    is-large-suplattice-Large-Poset γ large-poset-Π-Large-Locale
  is-large-suplattice-Π-Large-Locale =
    is-large-suplattice-Π-Large-Frame L

  set-Π-Large-Locale : (l : Level) → Set (α l ⊔ l1)
  set-Π-Large-Locale = set-Π-Large-Frame L

  type-Π-Large-Locale : (l : Level) → UU (α l ⊔ l1)
  type-Π-Large-Locale = type-Π-Large-Frame L

  is-set-type-Π-Large-Locale : {l : Level} → is-set (type-Π-Large-Locale l)
  is-set-type-Π-Large-Locale = is-set-type-Π-Large-Frame L

  leq-Π-Large-Locale-Prop :
    Large-Relation-Prop
      ( λ l2 → α l2 ⊔ l1)
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-Π-Large-Locale)
  leq-Π-Large-Locale-Prop = leq-Π-Large-Frame-Prop L

  leq-Π-Large-Locale :
    Large-Relation
      ( λ l2 → α l2 ⊔ l1)
      ( λ l2 l3 → β l2 l3 ⊔ l1)
      ( type-Π-Large-Locale)
  leq-Π-Large-Locale = leq-Π-Large-Frame L

  is-prop-leq-Π-Large-Locale :
    is-prop-Large-Relation type-Π-Large-Locale leq-Π-Large-Locale
  is-prop-leq-Π-Large-Locale = is-prop-leq-Π-Large-Frame L

  refl-leq-Π-Large-Locale :
    is-large-reflexive type-Π-Large-Locale leq-Π-Large-Locale
  refl-leq-Π-Large-Locale = refl-leq-Π-Large-Frame L

  antisymmetric-leq-Π-Large-Locale :
    is-large-antisymmetric type-Π-Large-Locale leq-Π-Large-Locale
  antisymmetric-leq-Π-Large-Locale = antisymmetric-leq-Π-Large-Frame L

  transitive-leq-Π-Large-Locale :
    is-large-transitive type-Π-Large-Locale leq-Π-Large-Locale
  transitive-leq-Π-Large-Locale = transitive-leq-Π-Large-Frame L

  meet-Π-Large-Locale :
    {l2 l3 : Level} →
    type-Π-Large-Locale l2 → type-Π-Large-Locale l3 →
    type-Π-Large-Locale (l2 ⊔ l3)
  meet-Π-Large-Locale = meet-Π-Large-Frame L

  is-greatest-binary-lower-bound-meet-Π-Large-Locale :
    {l2 l3 : Level}
    (x : type-Π-Large-Locale l2)
    (y : type-Π-Large-Locale l3) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Π-Large-Locale)
      ( x)
      ( y)
      ( meet-Π-Large-Locale x y)
  is-greatest-binary-lower-bound-meet-Π-Large-Locale =
    is-greatest-binary-lower-bound-meet-Π-Large-Frame L

  top-Π-Large-Locale : type-Π-Large-Locale lzero
  top-Π-Large-Locale = top-Π-Large-Frame L

  is-top-element-top-Π-Large-Locale :
    {l1 : Level} (x : type-Π-Large-Locale l1) →
    leq-Π-Large-Locale x top-Π-Large-Locale
  is-top-element-top-Π-Large-Locale =
    is-top-element-top-Π-Large-Frame L

  has-top-element-Π-Large-Locale :
    has-top-element-Large-Poset large-poset-Π-Large-Locale
  has-top-element-Π-Large-Locale =
    has-top-element-Π-Large-Frame L

  is-large-meet-semilattice-Π-Large-Locale :
    is-large-meet-semilattice-Large-Poset large-poset-Π-Large-Locale
  is-large-meet-semilattice-Π-Large-Locale =
    is-large-meet-semilattice-Π-Large-Frame L

  sup-Π-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Locale l3) →
    type-Π-Large-Locale (γ ⊔ l2 ⊔ l3)
  sup-Π-Large-Locale = sup-Π-Large-Frame L

  is-least-upper-bound-sup-Π-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Locale l3) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Π-Large-Locale)
      ( x)
      ( sup-Π-Large-Locale x)
  is-least-upper-bound-sup-Π-Large-Locale =
    is-least-upper-bound-sup-Π-Large-Frame L

  distributive-meet-sup-Π-Large-Locale :
    {l2 l3 l4 : Level}
    (x : type-Π-Large-Locale l2)
    {J : UU l3} (y : J → type-Π-Large-Locale l4) →
    meet-Π-Large-Locale x (sup-Π-Large-Locale y) ＝
    sup-Π-Large-Locale (λ j → meet-Π-Large-Locale x (y j))
  distributive-meet-sup-Π-Large-Locale =
    distributive-meet-sup-Π-Large-Frame L
```
