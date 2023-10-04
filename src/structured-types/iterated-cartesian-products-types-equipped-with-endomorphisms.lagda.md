# Iterated cartesian products of types equipped with endomorphisms

```agda
module
  structured-types.iterated-cartesian-products-types-equipped-with-endomorphisms
  where
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
iterated-product-Type-With-Endomorphism-list :
  {l : Level} → list (Type-With-Endomorphism l) → Type-With-Endomorphism l
iterated-product-Type-With-Endomorphism-list nil =
  trivial-Type-With-Endomorphism
iterated-product-Type-With-Endomorphism-list (cons A L) =
  product-Type-With-Endomorphism A
    ( iterated-product-Type-With-Endomorphism-list L)
```
