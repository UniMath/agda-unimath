# Subtractive submonoids of commutative monoids

```agda
module group-theory.subtractive-submonoids-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.submonoids-commutative-monoids
```

</details>

## Idea

Consider a [submonoid](group-theory.submonoids-commutative-monoids.md) `H` of a [commutative monoid](group-theory.commutative-monoids.md) `M`. We say that `H` is a {{#concept "subtractive submonoid" Disambiguation="commutative monoids" Agda=subtractive-submonoid-Commutative-Monoid}} if it satisfies the following condition:

```text
  x ∈ H    and    x + y ∈ H    ⇒    y ∈ H
```

In other words, a submonoid is subtractive if it satisfies a 3-for-2 condition.

## Definitions

### The predicate of being a subtractive submonoid

```agda
module _
  {l1 l2 : Level}
  (M : Commutative-Monoid l1) (H : Commutative-Submonoid l2 M)
  where

  is-subtractive-Commutative-Submonoid :
    UU (l1 ⊔ l2)
  is-subtractive-Commutative-Submonoid =
    (x y : type-Commutative-Monoid M) →
    is-in-Commutative-Submonoid M H x →
    is-in-Commutative-Submonoid M H (mul-Commutative-Monoid M x y) →
    is-in-Commutative-Submonoid M H y
```
