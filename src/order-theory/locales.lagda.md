# Locales

```agda
module order-theory.locales where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.frames
open import order-theory.greatest-lower-bounds-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.meet-suplattices
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

A **locale** is an object in the opposite of the category of
[frames](order-theory.frames.md). In other words, a locale is just a frame.

## Definition

```agda
Locale : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Locale l1 l2 = Frame l1 l2

module _
  {l1 l2 : Level} (L : Locale l1 l2)
  where

  meet-suplattice-Locale : Meet-Suplattice l1 l2
  meet-suplattice-Locale = meet-suplattice-Frame L

  meet-semilattice-Locale : Meet-Semilattice l1
  meet-semilattice-Locale = meet-semilattice-Frame L

  suplattice-Locale : Suplattice l1 l1 l2
  suplattice-Locale = suplattice-Frame L

  poset-Locale : Poset l1 l1
  poset-Locale = poset-Frame L

  set-Locale : Set l1
  set-Locale = set-Frame L

  type-Locale : UU l1
  type-Locale = type-Frame L

  is-set-type-Locale : is-set type-Locale
  is-set-type-Locale = is-set-type-Frame L

  leq-Locale-Prop : (x y : type-Locale) → Prop l1
  leq-Locale-Prop = leq-Frame-Prop L

  leq-Locale : (x y : type-Locale) → UU l1
  leq-Locale = leq-Frame L

  is-prop-leq-Locale : (x y : type-Locale) → is-prop (leq-Locale x y)
  is-prop-leq-Locale = is-prop-leq-Frame L

  refl-leq-Locale : is-reflexive leq-Locale
  refl-leq-Locale = refl-leq-Frame L

  antisymmetric-leq-Locale : is-antisymmetric leq-Locale
  antisymmetric-leq-Locale = antisymmetric-leq-Frame L

  transitive-leq-Locale : is-transitive leq-Locale
  transitive-leq-Locale = transitive-leq-Frame L

  meet-Locale : type-Locale → type-Locale → type-Locale
  meet-Locale = meet-Frame L

  is-greatest-binary-lower-bound-meet-Locale :
    (x y : type-Locale) →
    is-greatest-binary-lower-bound-Poset poset-Locale x y (meet-Locale x y)
  is-greatest-binary-lower-bound-meet-Locale =
    is-greatest-binary-lower-bound-meet-Frame L

  associative-meet-Locale :
    (x y z : type-Locale) →
    meet-Locale (meet-Locale x y) z ＝ meet-Locale x (meet-Locale y z)
  associative-meet-Locale = associative-meet-Frame L

  commutative-meet-Locale :
    (x y : type-Locale) → meet-Locale x y ＝ meet-Locale y x
  commutative-meet-Locale = commutative-meet-Frame L

  idempotent-meet-Locale :
    (x : type-Locale) → meet-Locale x x ＝ x
  idempotent-meet-Locale = idempotent-meet-Frame L

  is-suplattice-Locale :
    is-suplattice-Poset l2 poset-Locale
  is-suplattice-Locale = is-suplattice-Frame L

  sup-Locale : {I : UU l2} → (I → type-Locale) → type-Locale
  sup-Locale = sup-Frame L

  is-least-upper-bound-sup-Locale :
    {I : UU l2} (x : I → type-Locale) →
    is-least-upper-bound-family-of-elements-Poset poset-Locale x (sup-Locale x)
  is-least-upper-bound-sup-Locale = is-least-upper-bound-sup-Frame L

  distributive-meet-sup-Locale :
    distributive-law-Meet-Suplattice meet-suplattice-Locale
  distributive-meet-sup-Locale = distributive-meet-sup-Frame L
```
