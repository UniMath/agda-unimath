# Homomorphisms of algebras

```agda
module universal-algebra.homomorphisms-of-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import lists.functoriality-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

An algebra homomorphism from one algebra to another is a function between their
underlying types such that all the structure is preserved.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 : Level}
  ( Alg1 : Algebra Sg Th l3)
  ( Alg2 : Algebra Sg Th l4)
  where

  preserves-operations-Algebra :
    (type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2) →
    UU (l1 ⊔ l3 ⊔ l4)
  preserves-operations-Algebra f =
    ( op : operation-signature Sg) →
    ( v : tuple (type-Algebra Sg Th Alg1)
      ( arity-operation-signature Sg op)) →
        ( f (is-model-set-Algebra Sg Th Alg1 op v) ＝
          ( is-model-set-Algebra Sg Th Alg2 op (map-tuple f v)))

  hom-Algebra : UU (l1 ⊔ l3 ⊔ l4)
  hom-Algebra =
    Σ ( type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2)
      ( preserves-operations-Algebra)

  map-hom-Algebra :
    hom-Algebra →
    type-Algebra Sg Th Alg1 →
    type-Algebra Sg Th Alg2
  map-hom-Algebra = pr1

  preserves-operations-hom-Algebra :
    ( f : hom-Algebra) →
    preserves-operations-Algebra (map-hom-Algebra f)
  preserves-operations-hom-Algebra = pr2
```
