# Large quotient locales

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.large-quotient-locales
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types funext
open import foundation.large-binary-relations funext
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets funext
open import order-theory.large-locales funext
open import order-theory.large-meet-semilattices funext
open import order-theory.large-meet-subsemilattices funext
open import order-theory.large-posets funext
open import order-theory.large-preorders funext
open import order-theory.large-subframes funext
open import order-theory.large-subposets funext
open import order-theory.large-subpreorders funext
open import order-theory.large-subsuplattices funext
open import order-theory.large-suplattices funext
open import order-theory.least-upper-bounds-large-posets funext
open import order-theory.top-elements-large-posets funext
```

</details>

## Idea

A **large quotient locale** of a [large locale](order-theory.large-locales.md)
`L` is by duality just a [large subframe](order-theory.large-subframes.md) of
`L`.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  (δ : Level → Level)
  (L : Large-Locale α β γ)
  where

  Large-Quotient-Locale : UUω
  Large-Quotient-Locale = Large-Subframe δ L

module _
  {α : Level → Level} {β : Level → Level → Level} {γ : Level}
  {δ : Level → Level}
  (L : Large-Locale α β γ) (Q : Large-Quotient-Locale δ L)
  where

  large-subposet-Large-Quotient-Locale :
    Large-Subposet δ (large-poset-Large-Locale L)
  large-subposet-Large-Quotient-Locale =
    large-subposet-Large-Subframe Q

  is-closed-under-meets-Large-Quotient-Locale :
    is-closed-under-meets-Large-Subposet
      ( large-meet-semilattice-Large-Locale L)
      ( large-subposet-Large-Quotient-Locale)
  is-closed-under-meets-Large-Quotient-Locale =
    is-closed-under-meets-Large-Subframe Q

  contains-top-Large-Quotient-Locale :
    contains-top-Large-Subposet
      ( large-meet-semilattice-Large-Locale L)
      ( large-subposet-Large-Quotient-Locale)
  contains-top-Large-Quotient-Locale =
    contains-top-Large-Subframe Q

  is-closed-under-sup-Large-Quotient-Locale :
    is-closed-under-sup-Large-Subposet
      ( large-suplattice-Large-Locale L)
      ( large-subposet-Large-Quotient-Locale)
  is-closed-under-sup-Large-Quotient-Locale =
    is-closed-under-sup-Large-Subframe Q

  large-poset-Large-Quotient-Locale :
    Large-Poset (λ l → α l ⊔ δ l) β
  large-poset-Large-Quotient-Locale =
    large-poset-Large-Subframe L Q

  large-subpreorder-Large-Quotient-Locale :
    Large-Subpreorder δ (large-preorder-Large-Locale L)
  large-subpreorder-Large-Quotient-Locale =
    large-subpreorder-Large-Subframe L Q

  large-preorder-Large-Quotient-Locale :
    Large-Preorder (λ l → α l ⊔ δ l) (λ l1 l2 → β l1 l2)
  large-preorder-Large-Quotient-Locale =
    large-preorder-Large-Subframe L Q

  is-in-Large-Quotient-Locale :
    {l1 : Level} → type-Large-Locale L l1 → UU (δ l1)
  is-in-Large-Quotient-Locale =
    is-in-Large-Subframe L Q

  type-Large-Quotient-Locale : (l1 : Level) → UU (α l1 ⊔ δ l1)
  type-Large-Quotient-Locale =
    type-Large-Subframe L Q

  leq-prop-Large-Quotient-Locale :
    Large-Relation-Prop β type-Large-Quotient-Locale
  leq-prop-Large-Quotient-Locale =
    leq-prop-Large-Subframe L Q

  leq-Large-Quotient-Locale :
    Large-Relation β type-Large-Quotient-Locale
  leq-Large-Quotient-Locale =
    leq-Large-Subframe L Q

  is-prop-leq-Large-Quotient-Locale :
    is-prop-Large-Relation type-Large-Quotient-Locale leq-Large-Quotient-Locale
  is-prop-leq-Large-Quotient-Locale =
    is-prop-leq-Large-Subframe L Q

  refl-leq-Large-Quotient-Locale :
    is-reflexive-Large-Relation
      ( type-Large-Quotient-Locale)
      ( leq-Large-Quotient-Locale)
  refl-leq-Large-Quotient-Locale =
    refl-leq-Large-Subframe L Q

  transitive-leq-Large-Quotient-Locale :
    is-transitive-Large-Relation
      ( type-Large-Quotient-Locale)
      ( leq-Large-Quotient-Locale)
  transitive-leq-Large-Quotient-Locale =
    transitive-leq-Large-Subframe L Q

  antisymmetric-leq-Large-Quotient-Locale :
    is-antisymmetric-Large-Relation
      ( type-Large-Quotient-Locale)
      ( leq-Large-Quotient-Locale)
  antisymmetric-leq-Large-Quotient-Locale =
    antisymmetric-leq-Large-Subframe L Q

  is-closed-under-sim-Large-Quotient-Locale :
    {l1 l2 : Level}
    (x : type-Large-Locale L l1)
    (y : type-Large-Locale L l2) →
    leq-Large-Locale L x y →
    leq-Large-Locale L y x →
    is-in-Large-Quotient-Locale x →
    is-in-Large-Quotient-Locale y
  is-closed-under-sim-Large-Quotient-Locale =
    is-closed-under-sim-Large-Subframe L Q

  meet-Large-Quotient-Locale :
    {l1 l2 : Level}
    (x : type-Large-Quotient-Locale l1)
    (y : type-Large-Quotient-Locale l2) →
    type-Large-Quotient-Locale (l1 ⊔ l2)
  meet-Large-Quotient-Locale =
    meet-Large-Subframe L Q

  is-greatest-binary-lower-bound-meet-Large-Quotient-Locale :
    {l1 l2 : Level}
    (x : type-Large-Quotient-Locale l1)
    (y : type-Large-Quotient-Locale l2) →
    is-greatest-binary-lower-bound-Large-Poset
      ( large-poset-Large-Quotient-Locale)
      ( x)
      ( y)
      ( meet-Large-Quotient-Locale x y)
  is-greatest-binary-lower-bound-meet-Large-Quotient-Locale =
    is-greatest-binary-lower-bound-meet-Large-Subframe L Q

  has-meets-Large-Quotient-Locale :
    has-meets-Large-Poset
      ( large-poset-Large-Quotient-Locale)
  has-meets-Large-Quotient-Locale =
    has-meets-Large-Subframe L Q

  top-Large-Quotient-Locale :
    type-Large-Quotient-Locale lzero
  top-Large-Quotient-Locale =
    top-Large-Subframe L Q

  is-top-element-top-Large-Quotient-Locale :
    {l1 : Level} (x : type-Large-Quotient-Locale l1) →
    leq-Large-Quotient-Locale x top-Large-Quotient-Locale
  is-top-element-top-Large-Quotient-Locale =
    is-top-element-top-Large-Subframe L Q

  has-top-element-Large-Quotient-Locale :
    has-top-element-Large-Poset
      ( large-poset-Large-Quotient-Locale)
  has-top-element-Large-Quotient-Locale =
    has-top-element-Large-Subframe L Q

  is-large-meet-semilattice-Large-Quotient-Locale :
    is-large-meet-semilattice-Large-Poset
      ( large-poset-Large-Quotient-Locale)
  is-large-meet-semilattice-Large-Quotient-Locale =
    is-large-meet-semilattice-Large-Subframe L Q

  large-meet-semilattice-Large-Quotient-Locale :
    Large-Meet-Semilattice (λ l → α l ⊔ δ l) β
  large-meet-semilattice-Large-Quotient-Locale =
    large-meet-semilattice-Large-Subframe L Q

  sup-Large-Quotient-Locale :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Quotient-Locale l2) →
    type-Large-Quotient-Locale (γ ⊔ l1 ⊔ l2)
  sup-Large-Quotient-Locale =
    sup-Large-Subframe L Q

  is-least-upper-bound-sup-Large-Quotient-Locale :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Quotient-Locale l2) →
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Quotient-Locale)
      ( x)
      ( sup-Large-Quotient-Locale x)
  is-least-upper-bound-sup-Large-Quotient-Locale =
    is-least-upper-bound-sup-Large-Subframe L Q

  is-large-suplattice-Large-Quotient-Locale :
    is-large-suplattice-Large-Poset γ (large-poset-Large-Quotient-Locale)
  is-large-suplattice-Large-Quotient-Locale =
    is-large-suplattice-Large-Subframe L Q

  large-suplattice-Large-Quotient-Locale :
    Large-Suplattice (λ l → α l ⊔ δ l) β γ
  large-suplattice-Large-Quotient-Locale =
    large-suplattice-Large-Subframe L Q

  distributive-meet-sup-Large-Quotient-Locale :
    {l1 l2 l3 : Level} (x : type-Large-Quotient-Locale l1)
    {I : UU l2} (y : I → type-Large-Quotient-Locale l3) →
    meet-Large-Quotient-Locale x (sup-Large-Quotient-Locale y) ＝
    sup-Large-Quotient-Locale (λ i → meet-Large-Quotient-Locale x (y i))
  distributive-meet-sup-Large-Quotient-Locale =
    distributive-meet-sup-Large-Subframe L Q

  large-locale-Large-Quotient-Locale :
    Large-Locale (λ l → α l ⊔ δ l) β γ
  large-locale-Large-Quotient-Locale =
    large-frame-Large-Subframe L Q
```
