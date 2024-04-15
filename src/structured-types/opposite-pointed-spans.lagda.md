# Opposite pointed spans

```agda
module structured-types.opposite-pointed-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-spans
open import structured-types.pointed-types
```

</details>

## Idea

Consider a [pointed span](structured-types.pointed-spans.md) `𝒮 := (S , f , g)`
from `A` to `B`. The
{{#concept "opposite pointed span" Agda=opposite-pointed-span}} of
`𝒮 := (S , f , g)` is the pointed span `(S , g , f)` from `B` to `A`. In other
words, the opposite of a pointed span

```text
       f       g
  A <----- S -----> B
```

is the pointed span

```text
       g       f
  B <----- S -----> A.
```

## Definitions

### The opposite of a pointed span

```agda
module _
  {l1 l2 l3 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  where

  opposite-pointed-span :
    pointed-span l3 A B → pointed-span l3 B A
  pr1 (opposite-pointed-span s) =
    spanning-pointed-type-pointed-span s
  pr1 (pr2 (opposite-pointed-span s)) =
    right-pointed-map-pointed-span s
  pr2 (pr2 (opposite-pointed-span s)) =
    left-pointed-map-pointed-span s
```

## See also

- [Transpositions of span diagrams](foundation.transposition-span-diagrams.md)
