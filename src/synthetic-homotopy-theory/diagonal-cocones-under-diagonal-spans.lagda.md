# Diagonal cocones under diagonal spans

```agda
module synthetic-homotopy-theory.diagonal-cocones-under-diagonal-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.diagonal-spans
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

Consider a map `f : A → B`. Then any map `g : B → X` induces a
{{#concept "diagonal cocone" Agda=diagonal-cocone-span Disambiguation="span"}}
on the [diagonal span](foundation.diagonal-spans.md)

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

  diagonal-cocone-span : (B → X) → cocone-span (diagonal-span f) X
  pr1 (diagonal-cocone-span g) = g
  pr1 (pr2 (diagonal-cocone-span g)) = g
  pr2 (pr2 (diagonal-cocone-span g)) = refl-htpy
```
