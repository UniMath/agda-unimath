# Transposition of cospan diagrams

```agda
module foundation.transposition-cospan-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospan-diagrams
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.opposite-cospans
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "transposition" Disambiguation="cospan diagram" Agda=transposition-cospan-diagram}}
of a [cospan diagram](foundation.cospan-diagrams.md)

```text
       f         g
  A ------> S <------ B
```

is the cospan diagram

```text
       g         f
  B ------> S <------ A.
```

In other words, the transposition of a cospan diagram `(A , B , s)` is the
cospan diagram `(B , A , opposite-cospan s)` where `opposite-cospan s` is the
[opposite](foundation.opposite-cospans.md) of the
[cospan](foundation.cospans.md) `s` from `A` to `B`.

## Definitions

### Transposition of cospan diagrams

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : cospan-diagram l1 l2 l3)
  where

  transposition-cospan-diagram : cospan-diagram l2 l1 l3
  pr1 transposition-cospan-diagram =
    codomain-cospan-diagram 𝒮
  pr1 (pr2 transposition-cospan-diagram) =
    domain-cospan-diagram 𝒮
  pr2 (pr2 transposition-cospan-diagram) =
    opposite-cospan (cospan-cospan-diagram 𝒮)
```
