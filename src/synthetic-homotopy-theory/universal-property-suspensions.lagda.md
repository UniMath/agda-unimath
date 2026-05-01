# Universal property of suspensions

```agda
module synthetic-homotopy-theory.universal-property-suspensions where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Since suspensions are just [pushouts](synthetic-homotopy-theory.pushouts.md),
they retain the expected
[universal property](synthetic-homotopy-theory.universal-property-pushouts.md),
which states that the map `cocone-map` is an equivalence. We denote this
universal property by `universal-property-pushout-suspension`. But, due to the
special nature of the span being pushed out, the suspension of a type enjoys an
equivalent universal property, here denoted by `universal-property-suspension`.
This universal property states that the map `ev-suspension` is an equivalence.

## Definitions

### The universal property of the suspension

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (s : suspension-structure X Y)
  where

  ev-suspension :
    {l3 : Level} (Z : UU l3) → (Y → Z) → suspension-structure X Z
  pr1 (ev-suspension Z h) = h (north-suspension-structure s)
  pr1 (pr2 (ev-suspension Z h)) = h (south-suspension-structure s)
  pr2 (pr2 (ev-suspension Z h)) = h ·l meridian-suspension-structure s

  universal-property-suspension : UUω
  universal-property-suspension =
    {l : Level} (Z : UU l) → is-equiv (ev-suspension Z)
```

### The universal property of the suspension at a universe level as a pushout

```agda
universal-property-pushout-suspension :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (s : suspension-structure X Y) → UUω
universal-property-pushout-suspension X Y s =
  universal-property-pushout
    ( terminal-map X)
    ( terminal-map X)
    ( suspension-cocone-suspension-structure s)
```

## Properties

```agda
triangle-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (s : suspension-structure X Y) →
  (Z : UU l3) →
  ( ( suspension-structure-suspension-cocone) ∘
    ( cocone-map
      ( terminal-map X)
      ( terminal-map X)
      ( suspension-cocone-suspension-structure s))) ~
  ( ev-suspension s Z)
triangle-ev-suspension (N , S , merid) Z h = refl

is-equiv-ev-suspension :
  { l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  ( s : suspension-structure X Y) →
  universal-property-pushout-suspension X Y s →
  { l3 : Level} (Z : UU l3) → is-equiv (ev-suspension s Z)
is-equiv-ev-suspension {X = X} s up-Y Z =
  is-equiv-left-map-triangle
    ( ev-suspension s Z)
    ( suspension-structure-suspension-cocone)
    ( cocone-map
      ( terminal-map X)
      ( terminal-map X)
      ( suspension-cocone-suspension-structure s))
    ( inv-htpy (triangle-ev-suspension s Z))
    ( up-Y Z)
    ( is-equiv-suspension-structure-suspension-cocone)
```
