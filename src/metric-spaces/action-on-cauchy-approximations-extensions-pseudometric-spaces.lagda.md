# Action on Cauchy approximations of extensions of pseudometric spaces

```agda
module metric-spaces.action-on-cauchy-approximations-extensions-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-isometries-pseudometric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensions-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

An
[extension of a pseudometric space](metric-spaces.extensions-pseudometric-spaces.md)
induces an isometry between the
[Cauchy pseudocompletions](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md),
hence, an extension of the Cauchy precompletion.

## Definition

### Action of extensions of metric spaces on Cauchy approximations

```agda
module _
  {l1 l2 l3 l4 : Level} (M : Pseudometric-Space l1 l2)
  (E : extension-Pseudometric-Space l3 l4 M)
  where

  isometry-cauchy-pseudocompletion-extension-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-space-extension-Pseudometric-Space M E))
  isometry-cauchy-pseudocompletion-extension-Pseudometric-Space =
    isometry-map-cauchy-approximation-isometry-Pseudometric-Space
      ( M)
      ( pseudometric-space-extension-Pseudometric-Space M E)
      ( isometry-pseudometric-space-extension-Pseudometric-Space M E)

  map-cauchy-approximation-extension-Pseudometric-Space :
    cauchy-approximation-Pseudometric-Space M →
    cauchy-approximation-Pseudometric-Space
      ( pseudometric-space-extension-Pseudometric-Space M E)
  map-cauchy-approximation-extension-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-space-extension-Pseudometric-Space M E))
      ( isometry-cauchy-pseudocompletion-extension-Pseudometric-Space)

  is-isometry-map-cauchy-approximation-extension-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-space-extension-Pseudometric-Space M E))
      ( map-cauchy-approximation-extension-Pseudometric-Space)
  is-isometry-map-cauchy-approximation-extension-Pseudometric-Space =
    is-isometry-map-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space M)
      ( cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-space-extension-Pseudometric-Space M E))
      ( isometry-cauchy-pseudocompletion-extension-Pseudometric-Space)

  extension-cauchy-pseudocompletion-extension-Pseudometric-Space :
    extension-Pseudometric-Space
      ( l3 ⊔ l4)
      ( l4)
      ( cauchy-pseudocompletion-Pseudometric-Space M)
  pr1 extension-cauchy-pseudocompletion-extension-Pseudometric-Space =
    cauchy-pseudocompletion-Pseudometric-Space
      ( pseudometric-space-extension-Pseudometric-Space M E)
  pr2 extension-cauchy-pseudocompletion-extension-Pseudometric-Space =
    isometry-cauchy-pseudocompletion-extension-Pseudometric-Space
```

## Properties

### The action of metric extensions on Cauchy approximations is natural w.r.t. Cauchy pseudocompletions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (M : Pseudometric-Space l1 l2)
  (E : extension-Pseudometric-Space l3 l4 M)
  where

  htpy-map-cauchy-approximation-extension-Pseudometric-Space :
    ( map-cauchy-approximation-extension-Pseudometric-Space M E ∘
      map-cauchy-pseudocompletion-Pseudometric-Space M) ~
    ( ( map-cauchy-pseudocompletion-Pseudometric-Space
        ( pseudometric-space-extension-Pseudometric-Space M E)) ∘
      ( map-isometry-pseudometric-space-extension-Pseudometric-Space M E))
  htpy-map-cauchy-approximation-extension-Pseudometric-Space x =
    eq-htpy-cauchy-approximation-Pseudometric-Space
      ( pseudometric-space-extension-Pseudometric-Space M E)
      ( refl-htpy)
```
