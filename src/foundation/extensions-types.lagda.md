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

Consider a type `X`. An
{{#concept "extension" Disambiguation="type" Agda=extension-type}} of `X` is an
object of the coslice category of `X`, i.e., it consists of a type `Y` and a map
`f : X → Y`.

In the above definition of extensions of types our aim is to capture the most
general concept of what it means to be an extension of a type. Similarly, in any
[category](category-theory.categories.md) we would say that an extension of an
object `X` consists of an object `Y` equipped with a morphism `f : X → Y`.

Our notion of extensions of types are not to be confused with extension types of
cubical type theory or
[extension types of simplicial type theory](https://arxiv.org/abs/1705.07442).

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
