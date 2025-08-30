# Sequences in strictly preordered sets

```agda
module order-theory.sequences-strictly-preordered-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import lists.sequences

open import order-theory.strictly-preordered-sets
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a strictly preordered set" Agda=type-sequence-Strictly-Preordered-Set}}
in a [strictly preordered set](order-theory.strictly-preordered-sets.md) is a
[sequence](lists.sequences.md) in its underlying type.

## Definition

### Sequences in a strictly preordered set

```agda
module _
  {l1 l2 : Level} (A : Strictly-Preordered-Set l1 l2)
  where

  type-sequence-Strictly-Preordered-Set : UU l1
  type-sequence-Strictly-Preordered-Set =
    sequence (type-Strictly-Preordered-Set A)
```
