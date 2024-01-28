# Opposite spans

```agda
module foundation.opposite-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

Consider a [span](foundation.spans.md) `(S , f , g)` from `A` to `B`. The
{{#concept "opposite span" Agda=opposite-span}} of `(S , f , g)` is the span
`(S , g , f)` from `B` to `A`. In other words, the opposite of a span

```text
       f       g
  A <----- S -----> B
```

is the span

```text
       g       f
  B <----- S -----> A.
```

Recall that [binary type duality](foundation.binary-type-duality.md) shows that
spans are equivalent to [binary relations](foundation.binary-relations.md) from
`A` to `B`. The opposite of a span corresponds to the opposite of a binary
relation.

## Definitions

### The opposite of a span

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  opposite-span : span l3 A B → span l3 B A
  pr1 (opposite-span s) = spanning-type-span s
  pr1 (pr2 (opposite-span s)) = right-map-span s
  pr2 (pr2 (opposite-span s)) = left-map-span s
```

## See also

- [Transpositions of span diagrams](foundation.transposition-span-diagrams.md)
