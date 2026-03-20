# Congruences

```agda
module universal-algebra.congruences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.functoriality-set-quotients
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import lists.binary-relations-tuples
open import lists.equivalence-relations-tuples
open import lists.tuples

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.signatures
```

</details>

## Idea

A
{{#concept "congruence" Disambiguation="in an algebra of an algebraic theory, single-sorted, finitary" WD="congruence relation" WDID=Q8349849 Agda=congruence-Algebra}}
in an [algebra](universal-algebra.algebras.md) of an
[algebraic theory](universal-algebra.algebraic-theories.md) is an
[equivalence relation](foundation.equivalence-relations.md) that respects all
operations of the algebra.

## Definitions

### The predicate on an equivalence relation of preserving the operations of an algebra

```agda
module _
  {l1 l2 l3 l4 : Level} (σ : signature l1)
  (T : Algebraic-Theory l2 σ) (A : Algebra l3 σ T)
  where

  preserves-operations-relation-Algebra :
    Relation l4 (type-Algebra σ T A) → UU (l1 ⊔ l3 ⊔ l4)
  preserves-operations-relation-Algebra R =
    (op : operation-signature σ)
    {x y : tuple (type-Algebra σ T A) (arity-operation-signature σ op)} →
    rel-tuple-Relation R (arity-operation-signature σ op) x y →
    R (is-model-set-Algebra σ T A op x) (is-model-set-Algebra σ T A op y)

  preserves-operations-equivalence-relation-Algebra :
    equivalence-relation l4 (type-Algebra σ T A) → UU (l1 ⊔ l3 ⊔ l4)
  preserves-operations-equivalence-relation-Algebra R =
    preserves-operations-relation-Algebra (sim-equivalence-relation R)
```

### Congruences

```agda
congruence-Algebra :
  {l1 l2 l3 : Level} (l4 : Level)
  (σ : signature l1) (T : Algebraic-Theory l2 σ) (A : Algebra l3 σ T) →
  UU (l1 ⊔ l3 ⊔ lsuc l4)
congruence-Algebra l4 σ T A =
  Σ ( equivalence-relation l4 (type-Algebra σ T A))
    ( preserves-operations-equivalence-relation-Algebra σ T A)

module _
  {l1 l2 l3 l4 : Level} (σ : signature l1)
  (T : Algebraic-Theory l2 σ) (A : Algebra l3 σ T)
  (R : congruence-Algebra l4 σ T A)
  where

  equivalence-relation-congruence-Algebra :
    equivalence-relation l4 (type-Algebra σ T A)
  equivalence-relation-congruence-Algebra = pr1 R

  preserves-operations-congruence-Algebra :
    preserves-operations-equivalence-relation-Algebra σ T A
      ( equivalence-relation-congruence-Algebra)
  preserves-operations-congruence-Algebra = pr2 R
```
