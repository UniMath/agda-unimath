# Large locales

```agda
module order-theory.large-locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-reflexive-relations
open import foundation.large-transitive-binary-relations
open import foundation.sets
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-frames
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

A **large locale** is a large
[meet-suplattice](order-theory.meet-suplattices.md) satisfying the distributive
law for meets over suprema.

## Definitions

### Large locales

```agda
Large-Locale :
  (α : Level → Level) (β : Level → Level → Level) (γ : Level) → UUω
Large-Locale = Large-Frame

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ)
  where

  large-poset-Large-Locale : Large-Poset α β
  large-poset-Large-Locale = large-poset-Large-Frame L

  large-preorder-Large-Locale : Large-Preorder α β
  large-preorder-Large-Locale =
    large-preorder-Large-Poset large-poset-Large-Locale

  set-Large-Locale : (l : Level) → Set (α l)
  set-Large-Locale = set-Large-Frame L

  type-Large-Locale : (l : Level) → UU (α l)
  type-Large-Locale = type-Large-Frame L

  is-set-type-Large-Locale : {l : Level} → is-set (type-Large-Locale l)
  is-set-type-Large-Locale = is-set-type-Large-Frame L

  leq-prop-Large-Locale : Large-Relation-Prop β type-Large-Locale
  leq-prop-Large-Locale = leq-prop-Large-Frame L

  leq-Large-Locale : Large-Relation β type-Large-Locale
  leq-Large-Locale = leq-Large-Frame L

  is-prop-leq-Large-Locale :
    is-prop-Large-Relation type-Large-Locale leq-Large-Locale
  is-prop-leq-Large-Locale = is-prop-leq-Large-Frame L

  leq-eq-Large-Locale :
    {l1 : Level} {x y : type-Large-Locale l1} →
    (x ＝ y) → leq-Large-Locale x y
  leq-eq-Large-Locale = leq-eq-Large-Frame L

  refl-leq-Large-Locale :
    is-reflexive-Large-Relation type-Large-Locale leq-Large-Locale
  refl-leq-Large-Locale = refl-leq-Large-Frame L

  antisymmetric-leq-Large-Locale :
    is-antisymmetric-Large-Relation type-Large-Locale leq-Large-Locale
  antisymmetric-leq-Large-Locale =
    antisymmetric-leq-Large-Frame L

  transitive-leq-Large-Locale :
    is-transitive-Large-Relation type-Large-Locale leq-Large-Locale
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

  ap-meet-Large-Locale :
    {l1 l2 : Level} →
    {x x' : type-Large-Locale l1} {y y' : type-Large-Locale l2} →
    (x ＝ x') → (y ＝ y') → (meet-Large-Locale x y ＝ meet-Large-Locale x' y')
  ap-meet-Large-Locale = ap-meet-Large-Frame L

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

  large-suplattice-Large-Locale : Large-Suplattice α β γ
  large-suplattice-Large-Locale = large-suplattice-Large-Frame L

  is-large-suplattice-Large-Locale :
    is-large-suplattice-Large-Poset γ large-poset-Large-Locale
  is-large-suplattice-Large-Locale = is-large-suplattice-Large-Frame L

  sup-Large-Locale :
    {l1 l2 : Level} {I : UU l1} →
    (I → type-Large-Locale l2) → type-Large-Locale (γ ⊔ l1 ⊔ l2)
  sup-Large-Locale = sup-Large-Frame L

  is-least-upper-bound-sup-Large-Locale :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Locale l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Locale)
      ( x)
      ( sup-Large-Locale x)
  is-least-upper-bound-sup-Large-Locale =
    is-least-upper-bound-sup-Large-Frame L

  is-upper-bound-sup-Large-Locale :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Locale l2) →
    is-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Locale)
      ( x)
      ( sup-Large-Locale x)
  is-upper-bound-sup-Large-Locale =
    is-upper-bound-sup-Large-Frame L

  distributive-meet-sup-Large-Locale :
    {l1 l2 l3 : Level}
    (x : type-Large-Poset large-poset-Large-Locale l1)
    {I : UU l2} (y : I → type-Large-Poset large-poset-Large-Locale l3) →
    meet-Large-Locale x (sup-Large-Locale y) ＝
    sup-Large-Locale (λ i → meet-Large-Locale x (y i))
  distributive-meet-sup-Large-Locale =
    distributive-meet-sup-Large-Frame L
```

## Properties

### Small constructions from large locales

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (L : Large-Locale α β γ)
  where

  preorder-Large-Locale : (l : Level) → Preorder (α l) (β l l)
  preorder-Large-Locale = preorder-Large-Frame L

  poset-Large-Locale : (l : Level) → Poset (α l) (β l l)
  poset-Large-Locale = poset-Large-Frame L

  is-suplattice-poset-Large-Locale :
    (l1 l2 : Level) → is-suplattice-Poset l1 (poset-Large-Locale (γ ⊔ l1 ⊔ l2))
  is-suplattice-poset-Large-Locale = is-suplattice-poset-Large-Frame L

  suplattice-Large-Locale :
    (l1 l2 : Level) →
    Suplattice (α (γ ⊔ l1 ⊔ l2)) (β (γ ⊔ l1 ⊔ l2) (γ ⊔ l1 ⊔ l2)) l1
  suplattice-Large-Locale = suplattice-Large-Frame L

  is-meet-semilattice-poset-Large-Locale :
    (l : Level) → is-meet-semilattice-Poset (poset-Large-Locale l)
  is-meet-semilattice-poset-Large-Locale =
    is-meet-semilattice-poset-Large-Frame L

  order-theoretic-meet-semilattice-Large-Locale :
    (l : Level) → Order-Theoretic-Meet-Semilattice (α l) (β l l)
  order-theoretic-meet-semilattice-Large-Locale =
    order-theoretic-meet-semilattice-Large-Frame L

  meet-semilattice-Large-Locale : (l : Level) → Meet-Semilattice (α l)
  meet-semilattice-Large-Locale = meet-semilattice-Large-Frame L
```
