# Transposition of span diagrams

```agda
module foundation.transposition-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "trasposition" Disambiguation="span diagram"}} of a [span diagram](foundation.span-diagrams.md)

```text
       f       g
  A <----- S -----> B
```

is the span diagram

```text
       g       f
  B <----- S -----> A.
```

## Definitions

### Transposition of span diagrams

```agda
module _
  {l1 l2 l3 : Level} (s : span-diagram l1 l2 l3)
  where

  transposition-span-diagram : span-diagram l2 l1 l3
  pr1 transposition-span-diagram = codomain-span-diagram s
  pr1 (pr2 transposition-span-diagram) = domain-span-diagram s
  pr2 (pr2 transposition-span-diagram) = opposite-span (span-span-diagram s)
```
