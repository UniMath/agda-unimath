# Orthogonal factorization systems

```agda
module orthogonal-factorization-systems.orthogonal-factorization-systems where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.factorization-operations-function-classes
open import orthogonal-factorization-systems.factorizations-of-maps
open import orthogonal-factorization-systems.factorizations-of-maps-function-classes
open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.lifting-structures-on-squares
open import orthogonal-factorization-systems.wide-function-classes
```

</details>

## Idea

An **orthogonal factorization system** is a pair of
[wide](orthogonal-factorization-systems.wide-function-classes.md)
[function classes](orthogonal-factorization-systems.function-classes.md) `L` and
`R`, such that for every function `f : A → B` there is a
[unique](foundation-core.contractible-types.md)
[factorization](orthogonal-factorization-systems.factorizations-of-maps.md)
`f ~ r ∘ l` where the left map (by diagrammatic ordering) `l` is in `L` and the
right map `r` is in `R`.

## Definition

### The predicate of being an orthogonal factorization system

```agda
module _
  {l lL lR : Level}
  (L : function-class l l lL)
  (R : function-class l l lR)
  where

  is-orthogonal-factorization-system : UU (lsuc l ⊔ lL ⊔ lR)
  is-orthogonal-factorization-system =
    ( is-wide-function-class L) ×
    ( ( is-wide-function-class R) ×
      ( unique-factorization-operation-function-class L R))

  is-prop-is-orthogonal-factorization-system :
    is-prop is-orthogonal-factorization-system
  is-prop-is-orthogonal-factorization-system =
    is-prop-product
      ( is-prop-is-wide-function-class L)
      ( is-prop-product
        ( is-prop-is-wide-function-class R)
        ( is-prop-unique-factorization-operation-function-class L R))

  is-orthogonal-factorization-system-Prop : Prop (lsuc l ⊔ lL ⊔ lR)
  pr1 is-orthogonal-factorization-system-Prop =
    is-orthogonal-factorization-system
  pr2 is-orthogonal-factorization-system-Prop =
    is-prop-is-orthogonal-factorization-system
```

### The type of orthogonal factorization systems

```agda
orthogonal-factorization-system :
  (l lL lR : Level) → UU (lsuc l ⊔ lsuc lL ⊔ lsuc lR)
orthogonal-factorization-system l lL lR =
  Σ ( function-class l l lL)
    ( λ L → Σ (function-class l l lR) (is-orthogonal-factorization-system L))
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

  has-equivalences-left-class-is-orthogonal-factorization-system :
    has-equivalences-function-class L
  has-equivalences-left-class-is-orthogonal-factorization-system =
    has-equivalences-is-wide-function-class L
      ( is-wide-left-class-is-orthogonal-factorization-system)

  has-equivalences-right-class-is-orthogonal-factorization-system :
    has-equivalences-function-class R
  has-equivalences-right-class-is-orthogonal-factorization-system =
    has-equivalences-is-wide-function-class R
      ( is-wide-right-class-is-orthogonal-factorization-system)

  is-closed-under-composition-left-class-is-orthogonal-factorization-system :
    is-closed-under-composition-function-class L
  is-closed-under-composition-left-class-is-orthogonal-factorization-system =
    is-closed-under-composition-is-wide-function-class L
      ( is-wide-left-class-is-orthogonal-factorization-system)

  is-closed-under-composition-right-class-is-orthogonal-factorization-system :
    is-closed-under-composition-function-class R
  is-closed-under-composition-right-class-is-orthogonal-factorization-system =
    is-closed-under-composition-is-wide-function-class R
      ( is-wide-right-class-is-orthogonal-factorization-system)

  unique-factorization-operation-is-orthogonal-factorization-system :
    unique-factorization-operation-function-class L R
  unique-factorization-operation-is-orthogonal-factorization-system =
    pr2 (pr2 is-OFS)

  factorization-operation-is-orthogonal-factorization-system :
    factorization-operation-function-class L R
  factorization-operation-is-orthogonal-factorization-system f =
    center
      ( unique-factorization-operation-is-orthogonal-factorization-system f)

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

  has-equivalences-left-class-orthogonal-factorization-system :
    has-equivalences-function-class left-class-orthogonal-factorization-system
  has-equivalences-left-class-orthogonal-factorization-system =
    has-equivalences-left-class-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  has-equivalences-right-class-orthogonal-factorization-system :
    has-equivalences-function-class right-class-orthogonal-factorization-system
  has-equivalences-right-class-orthogonal-factorization-system =
    has-equivalences-right-class-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  is-closed-under-composition-left-class-orthogonal-factorization-system :
    is-closed-under-composition-function-class
      left-class-orthogonal-factorization-system
  is-closed-under-composition-left-class-orthogonal-factorization-system =
    is-closed-under-composition-left-class-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  is-closed-under-composition-right-class-orthogonal-factorization-system :
    is-closed-under-composition-function-class
      right-class-orthogonal-factorization-system
  is-closed-under-composition-right-class-orthogonal-factorization-system =
    is-closed-under-composition-right-class-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  unique-factorization-operation-orthogonal-factorization-system :
    unique-factorization-operation-function-class
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
  unique-factorization-operation-orthogonal-factorization-system =
    unique-factorization-operation-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)

  factorization-operation-orthogonal-factorization-system :
    factorization-operation-function-class
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
  factorization-operation-orthogonal-factorization-system =
    factorization-operation-is-orthogonal-factorization-system
      ( left-class-orthogonal-factorization-system)
      ( right-class-orthogonal-factorization-system)
      ( is-orthogonal-factorization-system-orthogonal-factorization-system)
```

## Properties

### An orthogonal factorization system is uniquely determined by its right class

This remains to be shown.
[#738](https://github.com/UniMath/agda-unimath/issues/738)

### The right class of an orthogonal factorization system is pullback-stable

This remains to be shown.
[#738](https://github.com/UniMath/agda-unimath/issues/738)

## References

{{#bibliography}} {{#reference RSS20}}

## External links

- [Orthogonal factorisation systems](https://1lab.dev/Cat.Morphism.Factorisation.html#orthogonal-factorisation-systems)
  at 1lab
- [orthogonal factorization system in an (infinity,1)-category](https://ncatlab.org/nlab/show/orthogonal+factorization+system+in+an+%28infinity%2C1%29-category)
  at $n$Lab
