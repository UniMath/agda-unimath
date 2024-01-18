# Diagonal cocones under diagonal span diagrams

```agda
module synthetic-homotopy-theory.diagonal-cocones-under-diagonal-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.diagonal-span-diagrams
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

Consider a map `f : A → B`. Then any map `g : B → X` induces a
{{#concept "diagonal cocone" Agda=diagonal-cocone-span-diagram Disambiguation="span diagram"}}
on the [diagonal span diagram](foundation.diagonal-span-diagrams.md)

```text
       f       f
  B <----- A -----> B.
```

## Definitions

### The diagonal cocone on a diagonal span

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  diagonal-cocone-span-diagram :
    (B → X) → cocone-span-diagram (diagonal-span-diagram f) X
  pr1 (diagonal-cocone-span-diagram g) = g
  pr1 (pr2 (diagonal-cocone-span-diagram g)) = g
  pr2 (pr2 (diagonal-cocone-span-diagram g)) = refl-htpy
```