# Retracts of types

```agda
module foundation-core.retracts-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.postcomposition-functions
open import foundation-core.precomposition-functions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

We say that a type `A` is a
{{#concept "retract" Disambiguation="of types" Agda=retracts}} of a type `B` if
the types `A` and `B` come equipped with
{{#concept "retract data" Disambiguation="of types" Agda=retract}}, i.e., with
maps

```text
      i        r
  A -----> B -----> A
```

such that `r` is a [retraction](foundation-core.retractions.md) of `i`, i.e.,
there is a [homotopy](foundation-core.homotopies.md) `r ∘ i ~ id`. The map `i`
is called the **inclusion** of the retract data, and the map `r` is called the
**underlying map of the retraction**.

## Definitions

### The type of witnesses that `A` is a retract of `B`

The predicate `retract B` is used to assert that a type is a retract of `B`,
i.e., the type `retract B A` is the type of maps from `A` to `B` that come
equipped with a retraction.

We also introduce more intuitive infix notation `A retract-of B` to assert that
`A` is a retract of `B`.

```agda
retract : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
retract B A = Σ (A → B) (retraction)

infix 6 _retract-of_

_retract-of_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A retract-of B = retract B A

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : retract B A)
  where

  inclusion-retract : A → B
  inclusion-retract = pr1 R

  retraction-retract : retraction inclusion-retract
  retraction-retract = pr2 R

  map-retraction-retract : B → A
  map-retraction-retract = map-retraction inclusion-retract retraction-retract

  is-retraction-map-retraction-retract :
    is-section map-retraction-retract inclusion-retract
  is-retraction-map-retraction-retract =
    is-retraction-map-retraction inclusion-retract retraction-retract

  section-retract : section map-retraction-retract
  pr1 section-retract = inclusion-retract
  pr2 section-retract = is-retraction-map-retraction-retract

retract-section :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) → section f → B retract-of A
retract-section f s = (pr1 s , f , pr2 s)
```

### The type of retracts of a type

```agda
retracts : {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
retracts l2 A = Σ (UU l2) (_retract-of A)

module _
  {l1 l2 : Level} {A : UU l1} (R : retracts l2 A)
  where

  type-retracts : UU l2
  type-retracts = pr1 R

  retract-retracts : type-retracts retract-of A
  retract-retracts = pr2 R

  inclusion-retracts : type-retracts → A
  inclusion-retracts = inclusion-retract retract-retracts

  retraction-retracts : retraction inclusion-retracts
  retraction-retracts = retraction-retract retract-retracts

  map-retraction-retracts : A → type-retracts
  map-retraction-retracts = map-retraction-retract retract-retracts

  is-retraction-map-retraction-retracts :
    is-section map-retraction-retracts inclusion-retracts
  is-retraction-map-retraction-retracts =
    is-retraction-map-retraction-retract retract-retracts

  section-retracts : section map-retraction-retracts
  section-retracts = section-retract retract-retracts
```

## Properties

### If `A` is a retract of `B` with inclusion `i : A → B`, then `x ＝ y` is a retract of `i x ＝ i y` for any two elements `x y : A`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) (x y : A)
  where

  retract-eq :
    (x ＝ y) retract-of (inclusion-retract R x ＝ inclusion-retract R y)
  pr1 retract-eq = ap (inclusion-retract R)
  pr2 retract-eq = retraction-ap (inclusion-retract R) (retraction-retract R)
```

### If `A` is a retract of `B` then `A → S` is a retract of `B → S` via precomposition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) (S : UU l3)
  where

  retract-precomp :
    (A → S) retract-of (B → S)
  pr1 retract-precomp =
    precomp (map-retraction-retract R) S
  pr1 (pr2 retract-precomp) =
    precomp (inclusion-retract R) S
  pr2 (pr2 retract-precomp) h =
    eq-htpy (h ·l is-retraction-map-retraction-retract R)
```

### If `A` is a retract of `B` then `S → A` is a retract of `S → B` via postcomposition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (S : UU l3) (R : A retract-of B)
  where

  retract-postcomp :
    (S → A) retract-of (S → B)
  pr1 retract-postcomp =
    postcomp S (inclusion-retract R)
  pr1 (pr2 retract-postcomp) =
    postcomp S (map-retraction-retract R)
  pr2 (pr2 retract-postcomp) h =
    eq-htpy (is-retraction-map-retraction-retract R ·r h)
```

### Every type is a retract of itself

```agda
module _
  {l : Level} {A : UU l}
  where

  id-retract : A retract-of A
  id-retract = (id , id , refl-htpy)
```

### Composition of retracts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  comp-retract : B retract-of C → A retract-of B → A retract-of C
  pr1 (comp-retract r r') =
    inclusion-retract r ∘ inclusion-retract r'
  pr2 (comp-retract r r') =
    retraction-comp
      ( inclusion-retract r)
      ( inclusion-retract r')
      ( retraction-retract r)
      ( retraction-retract r')
```

## Retract reasoning

Retracts can be constructed by equational reasoning in the following way:

```text
retract-reasoning
  X retract-of Y by retract-1
    retract-of Z by retract-2
    retract-of V by retract-3
```

The retract constructed in this way is
`comp-retract retract-3 (comp-retract retract-2 retract-1)`, i.e., the retract
is associated fully to the right.

```agda
infixl 1 retract-reasoning_
infixl 0 step-retract-reasoning

retract-reasoning_ :
  {l1 : Level} (X : UU l1) → X retract-of X
retract-reasoning X = id-retract

step-retract-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X retract-of Y) → (Z : UU l3) → (Y retract-of Z) → (X retract-of Z)
step-retract-reasoning e Z f = comp-retract f e

syntax step-retract-reasoning e Z f = e retract-of Z by f
```

## See also

- [Retracts of arrows](foundation.retracts-of-arrows.md)
