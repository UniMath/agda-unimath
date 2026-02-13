# Least upper bounds on postfixpoints of endomaps on posets

```agda
module order-theory.least-upper-bounds-postfixpoints-endomaps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
open import order-theory.postfixpoints-endomaps-posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

Given an endomap on a [poset](order-theory.posets.md) `f : P → P`, we consider
the family of all [postfixpoints](order-theory.postfixpoints-endomaps-posets.md)
of `f`. A
{{#concept "least upper bound of postfixpoints" Disambiguation="of an endomap on a poset" Agda=is-least-upper-bound-postfixpoints-endomap-Poset}}
is a least upper bound of this family.

## Definitions

```agda
indexing-type-postfixpoints-endomap-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) →
  (type-Poset P → type-Poset P) → UU (l1 ⊔ l2)
indexing-type-postfixpoints-endomap-Poset P f =
  Σ (type-Poset P) (is-postfixpoint-endomap-Poset P f)

family-of-elements-postfixpoints-endomap-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) →
  (f : type-Poset P → type-Poset P) →
  indexing-type-postfixpoints-endomap-Poset P f →
  type-Poset P
family-of-elements-postfixpoints-endomap-Poset P _ = pr1

is-least-upper-bound-postfixpoints-endomap-Poset :
  {l1 l2 : Level} (P : Poset l1 l2) →
  (f : type-Poset P → type-Poset P) →
  type-Poset P → UU (l1 ⊔ l2)
is-least-upper-bound-postfixpoints-endomap-Poset P f x0 =
  (z : type-Poset P) →
  is-upper-bound-family-of-elements-Poset
    ( P)
    ( family-of-elements-postfixpoints-endomap-Poset P f)
    ( z) ↔
  leq-Poset P x0 z
```
