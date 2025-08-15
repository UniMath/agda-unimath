# Homomorphisms of algebras

```agda
module universal-algebra.homomorphisms-of-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.subtype-identity-principle
open import foundation.universe-levels
open import foundation.sets

open import foundation-core.identity-types
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.subtypes
open import foundation-core.propositions

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

  is-prop-preserves-operations-Algebra :
    (f : type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2) →
    is-prop (preserves-operations-Algebra f)
  is-prop-preserves-operations-Algebra f =
    is-prop-Π (λ x →
      is-prop-Π (λ y → pr2 (pr1 (pr1 Alg2)) (f (pr2 (pr1 Alg1) x y))
        (pr2 (pr1 Alg2) x (map-tuple f y))))

  preserves-operations-Algebra-Prop :
    (f : type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2) → Prop (l1 ⊔ l3 ⊔ l4)
  preserves-operations-Algebra-Prop f =
    ( preserves-operations-Algebra f) , (is-prop-preserves-operations-Algebra f)

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

  hom-Algebra-Subtype :
    subtype (l1 ⊔ l3 ⊔ l4) (type-Algebra Sg Th Alg1 → type-Algebra Sg Th Alg2)
  hom-Algebra-Subtype = preserves-operations-Algebra-Prop
```

## Properties

### The type of algebra homomorphisms for any theory is a set

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 l4 : Level}
  ( Alg1 : Algebra Sg Th l3)
  ( Alg2 : Algebra Sg Th l4)
  where

  is-set-hom-Algebra : is-set (hom-Algebra Sg Th Alg1 Alg2)
  is-set-hom-Algebra =
    is-set-type-subtype
    ( hom-Algebra-Subtype Sg Th Alg1 Alg2)
    ( is-set-hom-Set (set-Algebra Sg Th Alg1) (set-Algebra Sg Th Alg2))

  set-hom-Algebra : Set (l1 ⊔ l3 ⊔ l4)
  set-hom-Algebra = (hom-Algebra Sg Th Alg1 Alg2) , is-set-hom-Algebra
```
