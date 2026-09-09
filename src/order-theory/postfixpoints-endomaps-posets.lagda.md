# Postfixpoints of endomaps on posets

```agda
module order-theory.postfixpoints-endomaps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

Given an endomap on a [poset](order-theory.posets.md) `f : P → P`, a
{{#concept "postfixpoint" Disambiguation="of an endomap on a poset" Agda=is-postfixpoint-endomap-Poset}}
is an element `x` such that `x ≤ f x`.

## Definitions

```agda
module _
  {l1 l2 : Level}
  (P : Poset l1 l2)
  (f : type-Poset P → type-Poset P)
  (x : type-Poset P)
  where

  is-postfixpoint-prop-endomap-Poset : Prop l2
  is-postfixpoint-prop-endomap-Poset =
    leq-prop-Poset P x (f x)

  is-postfixpoint-endomap-Poset : UU l2
  is-postfixpoint-endomap-Poset =
    type-Prop is-postfixpoint-prop-endomap-Poset

  is-prop-is-postfixpoint-endomap-Poset :
    is-prop is-postfixpoint-endomap-Poset
  is-prop-is-postfixpoint-endomap-Poset =
    is-prop-type-Prop is-postfixpoint-prop-endomap-Poset
```
