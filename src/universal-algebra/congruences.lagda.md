# Congruences

```agda
module universal-algebra.congruences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

A congruence in an algebra is an equivalence relation that respects all
operations of the algebra.

## Definitions

```agda
module _
  { l1 : Level} ( Sg : signature l1)
  { l2 : Level} ( Th : Theory Sg l2)
  { l3 : Level} ( Alg : Algebra Sg Th l3)
  where

  relation-holds-all-vec :
    { l4 : Level} →
    ( R : Eq-Rel l4 (type-Algebra Sg Th Alg)) →
    { n : ℕ} →
    ( v : vec (type-Algebra Sg Th Alg) n) →
    ( v' : vec (type-Algebra Sg Th Alg) n) →
    UU l4
  relation-holds-all-vec {l4} R {.zero-ℕ} empty-vec empty-vec = raise-unit l4
  relation-holds-all-vec {l4} R {.(succ-ℕ _)} (x ∷ v) (x' ∷ v') =
     type-Prop (prop-Eq-Rel R x x') × (relation-holds-all-vec R v v')

  respects-operations :
    { l4 : Level} →
    ( R : Eq-Rel l4 (type-Algebra Sg Th Alg)) →
    UU (l1 ⊔ l3 ⊔ l4)
  respects-operations R =
    ( op : operation-signature Sg) →
    ( v : vec (type-Algebra Sg Th Alg)
      ( arity-operation-signature Sg op)) →
    ( v' : vec (type-Algebra Sg Th Alg)
      ( arity-operation-signature Sg op)) →
        ( relation-holds-all-vec R v v' →
          ( type-Prop
            ( prop-Eq-Rel R
              ( is-model-set-Algebra Sg Th Alg op v)
              ( is-model-set-Algebra Sg Th Alg op v'))))

  congruence-Algebra :
    ( l4 : Level) →
    UU (l1 ⊔ l3 ⊔ lsuc l4)
  congruence-Algebra l4 =
    Σ ( Eq-Rel l4 (type-Algebra Sg Th Alg))
      ( respects-operations)

  eq-rel-congruence-Algebra :
    { l4 : Level} →
    congruence-Algebra l4 → ( Eq-Rel l4 (type-Algebra Sg Th Alg))
  eq-rel-congruence-Algebra = pr1

  respects-operations-congruence-Algebra :
    { l4 : Level} →
    ( R : congruence-Algebra l4) →
    ( respects-operations (eq-rel-congruence-Algebra R))
  respects-operations-congruence-Algebra = pr2
```
