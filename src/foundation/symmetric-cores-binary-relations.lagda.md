# Symmetric cores of binary relations

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module foundation.symmetric-cores-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.symmetric-binary-relations
open import foundation.transport
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

that satisfyies the universal property of the symmetric core, i.e., it satisfies
the property that for any symmetric relation `S : unordered-pair A → 𝒰` such
that the precomposition function

```text
  hom-Symmetric-Relation S (core R) → hom-Relation (rel S) R
```

is an [equivalence](foundation-core.equivalences.md).

## Definitions

### The symmetric core of a binary relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  symmetric-core-Relation : symmetric-binary-relation l2 A
  symmetric-core-Relation p =
    (i : type-unordered-pair p) →
    R (element-unordered-pair p i) (other-element-unordered-pair p i)

  counit-symmetric-core-Relation :
    {x y : A} →
    relation-symmetric-binary-relation symmetric-core-Relation x y → R x y
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
  (S : symmetric-binary-relation l3 A)
  where

  map-universal-property-symmetric-core-Relation :
    hom-symmetric-binary-relation S (symmetric-core-Relation R) →
    hom-Relation (relation-symmetric-binary-relation S) R
  map-universal-property-symmetric-core-Relation f x y s =
    counit-symmetric-core-Relation R (f (standard-unordered-pair x y) s)

  map-inv-universal-property-symmetric-core-Relation :
    hom-Relation (relation-symmetric-binary-relation S) R →
    hom-symmetric-binary-relation S (symmetric-core-Relation R)
  map-inv-universal-property-symmetric-core-Relation f p s i =
    f ( element-unordered-pair p i)
      ( other-element-unordered-pair p i)
      ( tr-inv-symmetric-binary-relation S
        ( standard-unordered-pair
          ( element-unordered-pair p i)
          ( other-element-unordered-pair p i))
        ( p)
        ( compute-standard-unordered-pair-element-unordered-pair p i)
        ( s))

  is-section-map-inv-universal-property-symmetric-core-Relation :
    map-universal-property-symmetric-core-Relation ∘
    map-inv-universal-property-symmetric-core-Relation ~
    id
  is-section-map-inv-universal-property-symmetric-core-Relation f =
    eq-htpy
      ( λ p →
        eq-htpy
          ( λ s →
            eq-htpy
              ( λ i →
                {! !})))
```
