# Tetrahedra in `3`-dimensional space

```agda
module finite-group-theory.tetrahedra-in-3-space where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.universe-levels

open import univalent-combinatorics.2-element-decidable-subtypes
open import univalent-combinatorics.cyclic-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

The type of
{{#concept "tetrahedra in 3-dimensional space" Agda=tetrahedron-in-3-space}} is
a type of tetrahedra that can be rotated, but not reflected. In other words, the
[symmetry group](group-theory.symmetric-groups.md) of the tetrahedra in
3-dimensional space is the
[alternating group](finite-group-theory.alternating-groups.md) `A₄`.

Note that any rotation of a tetrahedron in 3-space induces a rotation on the
[set](foundation-core.sets.md) of opposing pairs of edges. There are three such
pairs of edges.

## Definition

```agda
tetrahedron-in-3-space : UU (lsuc lzero)
tetrahedron-in-3-space =
  Σ ( Type-With-Cardinality-ℕ lzero 4)
    ( λ X →
      cyclic-structure 3
        ( Σ ( 2-Element-Decidable-Subtype lzero
              ( 2-Element-Decidable-Subtype lzero
                ( type-Type-With-Cardinality-ℕ 4 X)))
            ( λ Q →
              (x : type-Type-With-Cardinality-ℕ 4 X) →
              is-empty
                ( (P : type-2-Element-Decidable-Subtype Q) →
                  is-in-2-Element-Decidable-Subtype
                    (pr1 P)
                    ( x)))))

module _
  (T : tetrahedron-in-3-space)
  where

  vertex-tetrahedron-in-3-space : UU lzero
  vertex-tetrahedron-in-3-space = type-Type-With-Cardinality-ℕ 4 (pr1 T)

  cyclic-structure-tetrahedron-in-3-space :
    cyclic-structure 3
      ( Σ ( 2-Element-Decidable-Subtype lzero
            ( 2-Element-Decidable-Subtype lzero
              ( vertex-tetrahedron-in-3-space)))
          ( λ Q →
            (x : vertex-tetrahedron-in-3-space) →
            is-empty
              ( (P : type-2-Element-Decidable-Subtype Q) →
                is-in-2-Element-Decidable-Subtype
                  (pr1 P)
                  ( x))))
  cyclic-structure-tetrahedron-in-3-space = pr2 T
```
