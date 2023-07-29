# Orthogonal factorization systems

```agda
module orthogonal-factorization-systems.orthogonal-factorization-systems where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.factorization-operations-function-classes
open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.wide-function-classes
```

</details>

## Idea

An **orthogonal factorization system** is a pair of
[wide](orthogonal-factorization-systems.wide-function-classes.md)
[function classes](orthogonal-factorization-systems.function-classes.md) `L`,
such that for every function `f : A → B` there is a unique
[factorization](orthogonal-factorization-systems.factorizations-of-maps.md)
`f ~ r ∘ l` where the left map (by diagrammatic ordering) `l` is in `L` and the
right map `r` is in `R`.

## Definition

### Orthogonal factorization systems

```agda
is-orthogonal-factorization-system :
  {l lL lR : Level}
  (L : function-class l l lL)
  (R : function-class l l lR) →
  UU (lsuc l ⊔ lL ⊔ lR)
is-orthogonal-factorization-system {l} L R =
  ( is-wide-function-class L) ×
  ( ( is-wide-function-class R) ×
    ( (A B : UU l) → unique-factorization-operation-function-class L R A B))

orthogonal-factorization-system :
  (l lL lR : Level) → UU (lsuc l ⊔ lsuc lL ⊔ lsuc lR)
orthogonal-factorization-system l lL lR =
  Σ ( function-class l l lL)
    ( λ L →
      Σ ( function-class l l lR)
        ( is-orthogonal-factorization-system L))
```

### Components of an orthogonal factorization system

```agda
module _
  {l lL lR : Level}
  (L : function-class l l lL)
  (R : function-class l l lR)
  (is-OFS : is-orthogonal-factorization-system L R)
  where

  is-wide-left-class-is-orthogonal-factorization-system :
    is-wide-function-class L
  is-wide-left-class-is-orthogonal-factorization-system = pr1 is-OFS

  is-wide-right-class-is-orthogonal-factorization-system :
    is-wide-function-class R
  is-wide-right-class-is-orthogonal-factorization-system = pr1 (pr2 is-OFS)

  unique-factorization-operation-is-orthogonal-factorization-system :
    (A B : UU l) → unique-factorization-operation-function-class L R A B
  unique-factorization-operation-is-orthogonal-factorization-system =
    pr2 (pr2 is-OFS)

  factorization-operation-is-orthogonal-factorization-system :
    (A B : UU l) → factorization-operation-function-class L R A B
  factorization-operation-is-orthogonal-factorization-system A B f =
    center
      ( unique-factorization-operation-is-orthogonal-factorization-system A B f)

module _
  {l lL lR : Level}
  (OFS : orthogonal-factorization-system l lL lR)
  where

  left-class-orthogonal-factorization-system : function-class l l lL
  left-class-orthogonal-factorization-system = pr1 OFS

  right-class-orthogonal-factorization-system : function-class l l lR
  right-class-orthogonal-factorization-system = pr1 (pr2 OFS)

  is-orthogonal-factorization-system-orthogonal-factorization-system :
    is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
  is-orthogonal-factorization-system-orthogonal-factorization-system =
    pr2 (pr2 OFS)

  is-wide-left-class-orthogonal-factorization-system :
    is-wide-function-class left-class-orthogonal-factorization-system
  is-wide-left-class-orthogonal-factorization-system =
    is-wide-left-class-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  is-wide-right-class-orthogonal-factorization-system :
    is-wide-function-class right-class-orthogonal-factorization-system
  is-wide-right-class-orthogonal-factorization-system =
    is-wide-right-class-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  unique-factorization-operation-orthogonal-factorization-system :
    (A B : UU l) →
    unique-factorization-operation-function-class
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( A)
      ( B)
  unique-factorization-operation-orthogonal-factorization-system =
    unique-factorization-operation-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  factorization-operation-orthogonal-factorization-system :
    (A B : UU l) →
    factorization-operation-function-class
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( A)
      ( B)
  factorization-operation-orthogonal-factorization-system =
    factorization-operation-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)
```

## Properties

### Being an orthogonal factorization system is a property

```agda
module _
  {l lL lR : Level}
  (L : function-class l l lL)
  (R : function-class l l lR)
  where

  is-prop-is-orthogonal-factorization-system :
    is-prop (is-orthogonal-factorization-system L R)
  is-prop-is-orthogonal-factorization-system =
    is-prop-prod
      ( is-prop-is-wide-function-class L)
      ( is-prop-prod
        ( is-prop-is-wide-function-class R)
        ( is-prop-Π
            λ A → is-prop-Π
              λ B → is-prop-unique-factorization-operation-function-class L R))

  is-orthogonal-factorization-system-Prop : Prop (lsuc l ⊔ lL ⊔ lR)
  pr1 is-orthogonal-factorization-system-Prop =
    is-orthogonal-factorization-system L R
  pr2 is-orthogonal-factorization-system-Prop =
    is-prop-is-orthogonal-factorization-system
```

### An orthogonal factorization system is uniquely determined by its right class

This remains to be shown.

### The right class of an orthogonal factorization system is pullback-stable

This remains to be shown.

## References

- Egbert Rijke, Michael Shulman, Bas Spitters, _Modalities in homotopy type
  theory_, Logical Methods in Computer Science, Volume 16, Issue 1, 2020
  ([arXiv:1706.07526](https://arxiv.org/abs/1706.07526),
  [doi:10.23638](https://doi.org/10.23638/LMCS-16%281%3A2%292020))
