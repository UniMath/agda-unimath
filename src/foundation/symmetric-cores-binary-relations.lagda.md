# Symmetric cores of binary relations

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module foundation.symmetric-cores-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.equivalences
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-function-types
open import foundation.morphisms-binary-relations
open import foundation.postcomposition-functions
open import foundation.symmetric-binary-relations
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universe-levels
open import foundation.unordered-pairs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **symmetric core** of a [binary relation](foundation.binary-relations.md)
`R : A → A → 𝒰` on a type `A` is a
[symmetric binary relation](foundation.symmetric-binary-relations.md) `core R`
equipped with a counit

```text
  (x y : A) → core R {x , y} → R x y
```

that satisfies the universal property of the symmetric core, i.e., it satisfies
the property that for any symmetric relation `S : unordered-pair A → 𝒰`, the
precomposition function

```text
  hom-Symmetric-Relation S (core R) → hom-Relation (rel S) R
```

is an [equivalence](foundation-core.equivalences.md). The symmetric core of a
binary relation `R` is defined as the relation

```text
  core R (I,a) := (i : I) → R (a i) (a -i)
```

where `-i` is the element of the
[2-element type](univalent-combinatorics.2-element-types.md) obtained by
applying the swap [involution](foundation.involutions.md) to `i`. With this
definition it is easy to see that the universal property of the adjunction
should hold, since we have

```text
  ((I,a) → S (I,a) → core R (I,a)) ≃ ((x y : A) → S {x,y} → R x y).
```

## Definitions

### The symmetric core of a binary relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  symmetric-core-Relation : Symmetric-Relation l2 A
  symmetric-core-Relation p =
    (i : type-unordered-pair p) →
    R (element-unordered-pair p i) (other-element-unordered-pair p i)

  counit-symmetric-core-Relation :
    {x y : A} →
    relation-Symmetric-Relation symmetric-core-Relation x y → R x y
  counit-symmetric-core-Relation {x} {y} r =
    tr
      ( R x)
      ( compute-other-element-standard-unordered-pair x y (zero-Fin 1))
      ( r (zero-Fin 1))
```

## Properties

### The universal property of the symmetric core of a binary relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Relation l2 A)
  (S : Symmetric-Relation l3 A)
  where

  map-universal-property-symmetric-core-Relation :
    hom-Symmetric-Relation S (symmetric-core-Relation R) →
    hom-Relation (relation-Symmetric-Relation S) R
  map-universal-property-symmetric-core-Relation f x y s =
    counit-symmetric-core-Relation R (f (standard-unordered-pair x y) s)

  equiv-universal-property-symmetric-core-Relation :
    hom-Symmetric-Relation S (symmetric-core-Relation R) ≃
    hom-Relation (relation-Symmetric-Relation S) R
  equiv-universal-property-symmetric-core-Relation =
    ( equiv-Π-equiv-family
      ( λ x →
        equiv-Π-equiv-family
          ( λ y →
            equiv-postcomp
              ( S (standard-unordered-pair x y))
              ( equiv-tr
                ( R _)
                ( compute-other-element-standard-unordered-pair x y
                  ( zero-Fin 1)))))) ∘e
    ( equiv-dependent-universal-property-pointed-unordered-pairs
      ( λ p i →
        S p →
        R (element-unordered-pair p i) (other-element-unordered-pair p i))) ∘e
    ( equiv-Π-equiv-family (λ p → equiv-swap-Π))

  universal-property-symmetric-core-Relation :
    is-equiv map-universal-property-symmetric-core-Relation
  universal-property-symmetric-core-Relation =
    is-equiv-map-equiv
      ( equiv-universal-property-symmetric-core-Relation)
```
