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
{{#concept "sequence" Disambiguation="in a strictly preordered set" Agda=type-sequence-Strict-Preorder}}
in a [strictly preordered set](order-theory.strictly-preordered-sets.md) is a
[sequence](lists.sequences.md) in its underlying type.

## Definition

### Sequences in a strictly preordered set

```agda
module _
  {l1 l2 : Level} (A : Strict-Preorder l1 l2)
  where

  type-sequence-Strict-Preorder : UU l1
  type-sequence-Strict-Preorder =
    sequence (type-Strict-Preorder A)
```
