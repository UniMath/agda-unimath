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

From a [list](lists.lists.md) of
[types equipped with endomorphisms](structured-types.types-equipped-with-endomorphisms.md),
we define its
{{#concept "iterated cartesian product" Disambiguation="of types equipped with endomorphisms" Agda=iterated-product-list-Type-With-Endomorphism}}
recursively via the
[cartesian product](structured-types.cartesian-products-types-equipped-with-endomorphisms.md)
of types equipped with endomorphism.

## Definitions

```agda
iterated-product-list-Type-With-Endomorphism :
  {l : Level} → list (Type-With-Endomorphism l) → Type-With-Endomorphism l
iterated-product-list-Type-With-Endomorphism nil =
  trivial-Type-With-Endomorphism
iterated-product-list-Type-With-Endomorphism (cons A L) =
  product-Type-With-Endomorphism A
    ( iterated-product-list-Type-With-Endomorphism L)
```
