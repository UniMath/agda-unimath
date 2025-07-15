# Transposition of pointed span diagrams

```agda
module structured-types.transposition-pointed-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.opposite-pointed-spans
open import structured-types.pointed-span-diagrams
```

</details>

## Idea

The
{{#concept "transposition" Disambiguation="pointed span diagram" Agda=transposition-pointed-span-diagram}}
of a [pointed span diagram](structured-types.pointed-span-diagrams.md)

```text
       f       g
  A <----- S -----> B
```

is the pointed span diagram

```text
       g       f
  B <----- S -----> A.
```

In other words, the transposition of a pointed span diagram `(A , B , s)` is the
pointed span diagram `(B , A , opposite-pointed-span s)` where
`opposite-pointed-span s` is the
[opposite](structured-types.opposite-pointed-spans.md) of the
[pointed span](structured-types.pointed-spans.md) `s` from `A` to `B`.

## Definitions

### Transposition of pointed span diagrams

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : pointed-span-diagram l1 l2 l3)
  where

  transposition-pointed-span-diagram : pointed-span-diagram l2 l1 l3
  pr1 transposition-pointed-span-diagram =
    pointed-codomain-pointed-span-diagram 𝒮
  pr1 (pr2 transposition-pointed-span-diagram) =
    pointed-domain-pointed-span-diagram 𝒮
  pr2 (pr2 transposition-pointed-span-diagram) =
    opposite-pointed-span (pointed-span-pointed-span-diagram 𝒮)
```
