# Descent data for constant type families over the circle

```agda
module synthetic-homotopy-theory.descent-circle-constant-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-type-families
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
```

</details>

## Idea

[Descent data for the circle](synthetic-homotopy-theory.descent-circle.md) for a
[constant type family](foundation.constant-type-families.md) is simply the type
it evaluates to, together with the identity.

## Definitions

### Descent data for constant type families over the circle

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( X : UU l2)
  where

  descent-data-circle-constant-type : descent-data-circle l2
  pr1 descent-data-circle-constant-type = X
  pr2 descent-data-circle-constant-type = id-equiv

  family-descent-data-circle-constant-type : S → UU l2
  family-descent-data-circle-constant-type x = X
```

## Properties

### Characterization of descent data for constant type families over the circle

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( X : UU l2)
  where

  eq-descent-data-circle-constant-type :
    Eq-descent-data-circle
      ( descent-data-circle-constant-type l X)
      ( ev-descent-data-circle l
        ( family-descent-data-circle-constant-type l X))
  pr1 eq-descent-data-circle-constant-type = id-equiv
  pr2 eq-descent-data-circle-constant-type x =
    inv (tr-constant-type-family (loop-free-loop l) x)

  family-with-descent-data-constant-type :
    family-with-descent-data-circle l l2
  pr1 family-with-descent-data-constant-type =
    family-descent-data-circle-constant-type l X
  pr1 (pr2 family-with-descent-data-constant-type) =
    descent-data-circle-constant-type l X
  pr2 (pr2 family-with-descent-data-constant-type) =
    eq-descent-data-circle-constant-type
```
