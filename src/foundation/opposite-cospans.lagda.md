# Opposite cospans

```agda
module foundation.opposite-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a [cospan](foundation.cospans.md) `(S , f , g)` from `A` to `B`. The
{{#concept "opposite cospan" Agda=opposite-cospan}} of `(S , f , g)` is the
cospan `(S , g , f)` from `B` to `A`. In other words, the opposite of a cospan

```text
       f         g
  A ------> S <------ B
```

is the cospan

```text
       g         f
  B ------> S <------ A.
```

## Definitions

### The opposite of a cospan

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  opposite-cospan : cospan l3 A B → cospan l3 B A
  pr1 (opposite-cospan s) = cospanning-type-cospan s
  pr1 (pr2 (opposite-cospan s)) = right-map-cospan s
  pr2 (pr2 (opposite-cospan s)) = left-map-cospan s
```

## See also

- [Transpositions of cospan diagrams](foundation.transposition-cospan-diagrams.md)
