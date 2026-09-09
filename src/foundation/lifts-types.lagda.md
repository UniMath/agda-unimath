# Lifts of types

```agda
module foundation.lifts-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a type `X`. A {{#concept "lift" Disambiguation="type" Agda=lift-type}}
of `X` is an object in the [slice](foundation.slice.md) over `X`, i.e., it
consists of a type `Y` and a map `f : Y → X`.

In the above definition of lifts of types our aim is to capture the most general
concept of what it means to be a lift of a type. Similarly, in any
[category](category-theory.categories.md) we would say that a lift of an object
`X` consists of an object `Y` equipped with a morphism `f : Y → X`.

## Definitions

```agda
lift-type : {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
lift-type l2 X = Σ (UU l2) (λ Y → (Y → X))

module _
  {l1 l2 : Level} {X : UU l1} (Y : lift-type l2 X)
  where

  type-lift-type : UU l2
  type-lift-type = pr1 Y

  projection-lift-type : type-lift-type → X
  projection-lift-type = pr2 Y
```

## See also

- [The slice above a type](foundation.slice.md) for the same concept under a
  different name.
