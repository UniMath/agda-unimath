# Comprehension of fibered type theories

```agda
{-# OPTIONS --guardedness #-}
```

<details><summary>Imports</summary>
```agda
module type-theories.comprehension-type-theories where
open import foundation.universe-levels
open import type-theories.dependent-type-theories
open import type-theories.fibered-dependent-type-theories
```
</details>

## Idea

Given a fibered type theory `S` over `T`, we can form the comprehension type theory `∫ST` analogous to the Grothendieck construction

## Definition

```agda
{-
record comprehension
  {l1 l2 l3 l4 : Level} {A : type-theory l1 l2}
  {B : fibered.fibered-type-theory l3 l4 A} : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive
  field
    type : {!!}
    element : {!!}
    slice : {!!}
-}
```
