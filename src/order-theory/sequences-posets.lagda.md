# Sequences in posets

```agda
module order-theory.sequences-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.sequences
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

A
{{#concept "sequence" Disambiguation="in a poset" Agda-sequence-Poset}} in a
[poset](order-theory.posets.md) is a [sequence](foundation.sequences.md) in its
underlying type.

## Definitions

### Sequences in posets

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  sequence-Poset : UU l1
  sequence-Poset = sequence (type-Poset P)
```
