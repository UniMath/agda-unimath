# Iterated cartesian products of pointed types

```agda
open import foundation.function-extensionality-axiom

module
  structured-types.iterated-pointed-cartesian-product-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.raising-universe-levels-unit-type funext
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists

open import structured-types.pointed-cartesian-product-types funext
open import structured-types.pointed-types
```

</details>

## Idea

Given a list of pointed types `l` we define recursively the iterated pointed
cartesian product of `l`.

## Definition

```agda
iterated-product-Pointed-Type :
  {l : Level} → (L : list (Pointed-Type l)) → Pointed-Type l
iterated-product-Pointed-Type nil = raise-unit _ , raise-star
iterated-product-Pointed-Type (cons x L) =
  x ×∗ (iterated-product-Pointed-Type L)
```
