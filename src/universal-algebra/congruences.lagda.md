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
open import universal-algebra.algebras-theories
open import universal-algebra.signatures
```

</details>

## Idea

A congruence is an equivalence relation that respects all operations.

## Definitions

```agda
module _
  { l1 : Level} ( Sig : signature l1)
  { l2 : Level } ( Th : Theory Sig l2)
  { l3 : Level } ( Alg : Algebra Sig Th l3)
  { l4 : Level }
  where

  relation-holds-all-vec :
    ( R : Eq-Rel l4 (type-Algebra Sig Th Alg)) →
    { n : ℕ} →
    ( v : vec (type-Algebra Sig Th Alg) n) →
    ( v' : vec (type-Algebra Sig Th Alg) n) →
    UU l4
  relation-holds-all-vec R {.zero-ℕ} empty-vec empty-vec = raise-unit l4
  relation-holds-all-vec R {.(succ-ℕ _)} (x ∷ v) (x' ∷ v') =
     type-Prop (prop-Eq-Rel R x x') × (relation-holds-all-vec R v v')

  respects-operations :
    ( R : Eq-Rel l4 (type-Algebra Sig Th Alg) ) →
    UU (l1 ⊔ l3 ⊔ l4)
  respects-operations R =
    ( op : operations-signature Sig) →
    ( v : vec (type-Algebra Sig Th Alg)
      ( arity-operations-signature Sig op)) →
    ( v' : vec (type-Algebra Sig Th Alg)
      ( arity-operations-signature Sig op)) →
        ( relation-holds-all-vec R v v' →
          ( type-Prop
            ( prop-Eq-Rel R
              ( is-model-set-Algebra Sig Th Alg op v)
              ( is-model-set-Algebra Sig Th Alg op v'))))

  congruence-Algebra :
    UU (l1 ⊔ l3 ⊔ lsuc l4)
  congruence-Algebra =
    Σ ( Eq-Rel l4 (type-Algebra Sig Th Alg))
      ( respects-operations)
```
