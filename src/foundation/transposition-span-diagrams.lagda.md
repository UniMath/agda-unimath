# Transposition of span diagrams

```agda
module foundation.transposition-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.opposite-spans
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "transposition" Disambiguation="span diagram" Agda=transposition-span-diagram}}
of a [span diagram](foundation.span-diagrams.md)

```text
       f       g
  A <----- S -----> B
```

is the span diagram

```text
       g       f
  B <----- S -----> A.
```

In other words, the transposition of a span diagram `(A , B , s)` is the span
diagram `(B , A , opposite-span s)` where `opposite-span s` is the
[opposite](foundation.opposite-spans.md) of the [span](foundation.spans.md) `s`
from `A` to `B`.

## Definitions

### Transposition of span diagrams

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  transposition-span-diagram : span-diagram l2 l1 l3
  pr1 transposition-span-diagram = codomain-span-diagram 𝒮
  pr1 (pr2 transposition-span-diagram) = domain-span-diagram 𝒮
  pr2 (pr2 transposition-span-diagram) = opposite-span (span-span-diagram 𝒮)
```
