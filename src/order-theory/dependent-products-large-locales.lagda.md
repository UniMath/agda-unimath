# Dependent products of large locales

```agda
module order-theory.dependent-products-large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.dependent-products-large-meet-semilattices
open import order-theory.dependent-products-large-posets
open import order-theory.dependent-products-large-suplattices
open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-locales
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-suplattices
open import order-theory.least-upper-bounds-large-posets
```

</details>

Given a family `L : I → Large-Locale α β` of large locales indexed by a type
`I : UU l`, the product of the large locales `L i` is again a large locale.

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (L : I → Large-Locale α β)
  where

  large-poset-Π-Large-Locale :
    Large-Poset (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-poset-Π-Large-Locale =
    Π-Large-Poset (λ i → large-poset-Large-Locale (L i))

  large-meet-semilattice-Π-Large-Locale :
    Large-Meet-Semilattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-meet-semilattice-Π-Large-Locale =
    Π-Large-Meet-Semilattice (λ i → large-meet-semilattice-Large-Locale (L i))

  has-meets-Π-Large-Locale :
    has-meets-Large-Poset large-poset-Π-Large-Locale
  has-meets-Π-Large-Locale =
    has-meets-Π-Large-Poset
      ( λ i → large-poset-Large-Locale (L i))
      ( λ i → has-meets-Large-Locale (L i))

  large-suplattice-Π-Large-Locale :
    Large-Suplattice (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-suplattice-Π-Large-Locale =
    Π-Large-Suplattice (λ i → large-suplattice-Large-Locale (L i))

  is-large-suplattice-Π-Large-Locale :
    is-large-suplattice-Large-Poset large-poset-Π-Large-Locale
  is-large-suplattice-Π-Large-Locale =
    is-large-suplattice-Π-Large-Suplattice
      ( λ i → large-suplattice-Large-Locale (L i))

  set-Π-Large-Locale : (l : Level) → Set (α l ⊔ l1)
  set-Π-Large-Locale = set-Large-Poset large-poset-Π-Large-Locale

  type-Π-Large-Locale : (l : Level) → UU (α l ⊔ l1)
  type-Π-Large-Locale = type-Large-Poset large-poset-Π-Large-Locale

  is-set-type-Π-Large-Locale : {l : Level} → is-set (type-Π-Large-Locale l)
  is-set-type-Π-Large-Locale =
    is-set-type-Large-Poset large-poset-Π-Large-Locale

  leq-Π-Large-Locale-Prop :
    {l2 l3 : Level} → type-Π-Large-Locale l2 → type-Π-Large-Locale l3 →
    Prop (β l2 l3 ⊔ l1)
  leq-Π-Large-Locale-Prop =
    leq-Large-Poset-Prop large-poset-Π-Large-Locale

  leq-Π-Large-Locale :
    {l2 l3 : Level} →
    type-Π-Large-Locale l2 → type-Π-Large-Locale l3 → UU (β l2 l3 ⊔ l1)
  leq-Π-Large-Locale = leq-Large-Poset large-poset-Π-Large-Locale

  is-prop-leq-Π-Large-Locale :
    {l2 l3 : Level} (x : type-Π-Large-Locale l2) (y : type-Π-Large-Locale l3) →
    is-prop (leq-Π-Large-Locale x y)
  is-prop-leq-Π-Large-Locale =
    is-prop-leq-Large-Poset large-poset-Π-Large-Locale

  refl-leq-Π-Large-Locale :
    {l2 : Level} (x : type-Π-Large-Locale l2) → leq-Π-Large-Locale x x
  refl-leq-Π-Large-Locale = refl-leq-Large-Poset large-poset-Π-Large-Locale

  antisymmetric-leq-Π-Large-Locale :
    {l2 : Level} (x y : type-Π-Large-Locale l2) →
    leq-Π-Large-Locale x y → leq-Π-Large-Locale y x → x ＝ y
  antisymmetric-leq-Π-Large-Locale =
    antisymmetric-leq-Large-Poset large-poset-Π-Large-Locale

  transitive-leq-Π-Large-Locale :
    {l2 l3 l4 : Level}
    (x : type-Π-Large-Locale l2)
    (y : type-Π-Large-Locale l3)
    (z : type-Π-Large-Locale l4) →
    leq-Π-Large-Locale y z → leq-Π-Large-Locale x y → leq-Π-Large-Locale x z
  transitive-leq-Π-Large-Locale =
    transitive-leq-Large-Poset large-poset-Π-Large-Locale

  meet-Π-Large-Locale :
    {l2 l3 : Level} →
    type-Π-Large-Locale l2 → type-Π-Large-Locale l3 →
    type-Π-Large-Locale (l2 ⊔ l3)
  meet-Π-Large-Locale =
    meet-has-meets-Large-Poset has-meets-Π-Large-Locale

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
    is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
      has-meets-Π-Large-Locale

  sup-Π-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Locale l3) →
    type-Π-Large-Locale (l2 ⊔ l3)
  sup-Π-Large-Locale =
    sup-is-large-suplattice-Large-Poset
      ( large-poset-Π-Large-Locale)
      ( is-large-suplattice-Π-Large-Locale)

  is-least-upper-bound-sup-Π-Large-Locale :
    {l2 l3 : Level} {J : UU l2} (x : J → type-Π-Large-Locale l3) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Π-Large-Locale)
      ( x)
      ( sup-Π-Large-Locale x)
  is-least-upper-bound-sup-Π-Large-Locale =
    is-least-upper-bound-sup-is-large-suplattice-Large-Poset
      ( large-poset-Π-Large-Locale)
      ( is-large-suplattice-Π-Large-Locale)

  distributive-meet-sup-Π-Large-Locale :
    {l2 l3 l4 : Level}
    (x : type-Π-Large-Locale l2)
    {J : UU l3} (y : J → type-Π-Large-Locale l4) →
    meet-Π-Large-Locale x (sup-Π-Large-Locale y) ＝
    sup-Π-Large-Locale (λ j → meet-Π-Large-Locale x (y j))
  distributive-meet-sup-Π-Large-Locale x y =
    eq-htpy
      ( λ i → distributive-meet-sup-Large-Locale (L i) (x i) (λ j → y j i))

  Π-Large-Locale : Large-Locale (λ l2 → α l2 ⊔ l1) (λ l2 l3 → β l2 l3 ⊔ l1)
  large-poset-Large-Locale Π-Large-Locale =
    large-poset-Π-Large-Locale
  has-meets-Large-Locale Π-Large-Locale =
    has-meets-Π-Large-Locale
  is-large-suplattice-Large-Locale Π-Large-Locale =
    is-large-suplattice-Π-Large-Locale
  distributive-meet-sup-Large-Locale Π-Large-Locale =
    distributive-meet-sup-Π-Large-Locale
```
