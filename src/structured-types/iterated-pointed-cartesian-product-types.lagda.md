# Iterated cartesian products of pointed types

```agda
module structured-types.iterated-pointed-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists

open import structured-types.pointed-cartesian-product-types
open import structured-types.pointed-types
```

</details>

## Idea

Given a [list](lists.lists.md) of
[pointed types](structured-types.pointed-types.md) `l` we define recursively the
{{#concept "iterated pointed cartesian product" Agda=iterated-product-Pointed-Type}}
of `l`.

## Definition

```agda
iterated-product-Pointed-Type :
  {l : Level} → (L : list (Pointed-Type l)) → Pointed-Type l
iterated-product-Pointed-Type nil =
  ( raise-unit _ , raise-star)
iterated-product-Pointed-Type (cons x L) =
  x ×∗ (iterated-product-Pointed-Type L)
```
