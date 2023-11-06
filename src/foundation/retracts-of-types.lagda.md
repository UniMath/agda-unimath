# Retracts of types

```agda
module foundation.retracts-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
```

</details>

## Idea

We say that a type `A` is a **retract of** a type `B` if the types `A` and `B`
come equipped with **retract data**, i.e., with maps

```text
      i        r
  A -----> B -----> A
```

and a homotopy `r ∘ i ~ id`. The map `i` is called the **inclusion of the
retract data, and the map `r` is called the **(underlying map of the) retract
data\*\*.

## Definitions

### The type of witnesses that `A` is a retract of `B`

```agda
retract : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
retract A B = Σ (A → B) retraction

_retract-of_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A retract-of B = retract A B

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  inclusion-retract : retract A B → A → B
  inclusion-retract = pr1

  retraction-retract :
    (R : retract A B) → retraction (inclusion-retract R)
  retraction-retract = pr2

  map-retraction-retract : retract A B → B → A
  map-retraction-retract R = pr1 (retraction-retract R)

  is-retraction-retraction-retract :
    (R : retract A B) →
    map-retraction-retract R ∘ inclusion-retract R ~ id
  is-retraction-retraction-retract R = pr2 (retraction-retract R)
```

## Properties

### If `A` is a retract of `B` with inclusion `i : A → B`, then `x ＝ y` is a retract of `i x ＝ i y` for any two elements `x y : A`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : retract A B) (x y : A)
  where

  retract-eq :
    (x ＝ y) retract-of (inclusion-retract R x ＝ inclusion-retract R y)
  pr1 retract-eq =
    ap (inclusion-retract R)
  pr2 retract-eq =
    retraction-ap (inclusion-retract R) (retraction-retract R) x y
```
