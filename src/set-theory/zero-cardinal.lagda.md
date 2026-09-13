# The zero cardinal

```agda
module set-theory.zero-cardinal where
```

<details><summary>Imports</summary>

```agda
open import foundation.empty-types
open import foundation.universe-levels

open import set-theory.cardinals
```

</details>

## Idea

The {{#concept "zero cardinal" Agda=zero-Cardinal}}, or **empty cardinal**, is
the isomorphism class of [empty](foundation.empty-types.md)
[sets](foundation-core.sets.md).

## Definitions

```agda
zero-Cardinal : Cardinal lzero
zero-Cardinal = cardinality empty-Set
```
