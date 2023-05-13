# Iterated cartesian products of types equipped with endomorphisms

```agda
module structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import lists.lists

open import structured-types.cartesian-products-types-equipped-with-endomorphisms
open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Idea

From a list of a types equipped with endomorphisms, we define its iterated
cartesian product recursively via the cartesian product of types equipped with
endomorphism.

## Definitions

```agda
iterated-product-Endo-list :
  {l : Level} → list (Endo l) → Endo l
iterated-product-Endo-list nil = trivial-Endo
iterated-product-Endo-list (cons A L) =
  product-Endo A (iterated-product-Endo-list L)
```
