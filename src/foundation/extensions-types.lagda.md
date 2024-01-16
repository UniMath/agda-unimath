# Extensions of types

```agda
module foundation.extensions-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a type `X`. An {{#concept "extension" Disambiguation="type" Agda=extension-type}} of `X` is
an object of the coslice category of `X`, i.e., it consists of a type `Y` and a
map `f : X → Y`.

## Definitions

### Extensions of types

```agda
extension-type : {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
extension-type l2 X = Σ (UU l2) (λ Y → X → Y)

module _
  {l1 l2 : Level} {X : UU l1} (Y : extension-type l2 X)
  where

  type-extension-type : UU l2
  type-extension-type = pr1 Y

  inclusion-extension-type : X → type-extension-type
  inclusion-extension-type = pr2 Y
```
