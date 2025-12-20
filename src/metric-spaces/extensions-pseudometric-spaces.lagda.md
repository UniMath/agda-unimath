# Extensions of pseudometric spaces

```agda
module metric-spaces.extensions-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

An
{{#concept "extension" Disambiguation="of a pseudometric space" Agda=extension-Pseudometric-Space}}
of a [pseudometric space](metric-spaces.pseudometric-spaces.md) `P`is a
pseudometric space `Q` together with an
[isometry](metric-spaces.isometries-pseudometric-spaces.md) `i : P → Q`.

## Definition

### Extensions of pseudometric spaces

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (P : Pseudometric-Space l1 l2)
  where

  extension-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  extension-Pseudometric-Space =
    Σ ( Pseudometric-Space l3 l4)
      ( isometry-Pseudometric-Space P)

module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (E : extension-Pseudometric-Space l3 l4 P)
  where

  pseudometric-space-extension-Pseudometric-Space : Pseudometric-Space l3 l4
  pseudometric-space-extension-Pseudometric-Space = pr1 E

  isometry-pseudometric-space-extension-Pseudometric-Space :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
  isometry-pseudometric-space-extension-Pseudometric-Space = pr2 E

  map-isometry-pseudometric-space-extension-Pseudometric-Space :
    type-Pseudometric-Space P →
    type-Pseudometric-Space pseudometric-space-extension-Pseudometric-Space
  map-isometry-pseudometric-space-extension-Pseudometric-Space =
    map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
      ( isometry-pseudometric-space-extension-Pseudometric-Space)

  is-isometry-map-extension-Pseudometric-Space :
    is-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
      ( map-isometry-pseudometric-space-extension-Pseudometric-Space)
  is-isometry-map-extension-Pseudometric-Space =
    is-isometry-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-extension-Pseudometric-Space)
      ( isometry-pseudometric-space-extension-Pseudometric-Space)
```
