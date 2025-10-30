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

open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras-of-theories
open import universal-algebra.signatures
```

</details>

## Idea

A {{#concept "congruence" Agda=congruence-Algebra}} in an
[algebra](universal-algebra.algebras-of-theories.md) is an
[equivalence relation](foundation.equivalence-relations.md) that respects all
operations of the algebra.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} (σ : signature l1) (T : Theory σ l2) (A : Algebra σ T l3)
  where

  relation-holds-all-tuple :
    {l4 : Level} →
    (R : equivalence-relation l4 (type-Algebra σ T A)) →
    {n : ℕ} →
    (v : tuple (type-Algebra σ T A) n) →
    (v' : tuple (type-Algebra σ T A) n) →
    UU l4
  relation-holds-all-tuple {l4} R {.zero-ℕ} empty-tuple empty-tuple =
    raise-unit l4
  relation-holds-all-tuple {l4} R {.(succ-ℕ _)} (x ∷ v) (x' ∷ v') =
    ( type-Prop (prop-equivalence-relation R x x')) ×
    ( relation-holds-all-tuple R v v')

  preserves-operations :
    {l4 : Level} →
    (R : equivalence-relation l4 (type-Algebra σ T A)) →
    UU (l1 ⊔ l3 ⊔ l4)
  preserves-operations R =
    ( op : operation-signature σ) →
    ( v : tuple (type-Algebra σ T A)
      ( arity-operation-signature σ op)) →
    ( v' : tuple (type-Algebra σ T A)
      ( arity-operation-signature σ op)) →
        ( relation-holds-all-tuple R v v' →
          ( type-Prop
            ( prop-equivalence-relation R
              ( is-model-set-Algebra σ T A op v)
              ( is-model-set-Algebra σ T A op v'))))

  congruence-Algebra :
    (l4 : Level) →
    UU (l1 ⊔ l3 ⊔ lsuc l4)
  congruence-Algebra l4 =
    Σ ( equivalence-relation l4 (type-Algebra σ T A))
      ( preserves-operations)

  equivalence-relation-congruence-Algebra :
    {l4 : Level} →
    congruence-Algebra l4 → equivalence-relation l4 (type-Algebra σ T A)
  equivalence-relation-congruence-Algebra = pr1

  preserves-operations-congruence-Algebra :
    {l4 : Level} →
    (R : congruence-Algebra l4) →
    preserves-operations (equivalence-relation-congruence-Algebra R)
  preserves-operations-congruence-Algebra = pr2
```
