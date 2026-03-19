# The algebraic theory of monoids

```agda
module universal-algebra.algebraic-theory-of-monoids where
```

<details><summary>Imports</summary>

```agda
open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-semigroups
open import group-theory.semigroups
open import foundation.dependent-pair-types
open import group-theory.monoids
open import group-theory.homomorphisms-semigroups
open import group-theory.homomorphisms-monoids
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import foundation.universe-levels
open import lists.tuples
```

</details>

## Idea

## Definition

```agda
data operation-Monoid : UU lzero where
  operation-monoid-operation-Semigroup : operation-Semigroup → operation-Monoid
  unit-operation-Monoid : operation-Monoid

pattern mul-operation-Monoid =
  operation-monoid-operation-Semigroup mul-operation-Semigroup-op

signature-Monoid : signature lzero
pr1 signature-Monoid = operation-Monoid
pr2 signature-Monoid (operation-monoid-operation-Semigroup op) =
  arity-operation-signature signature-Semigroup op
pr2 signature-Monoid unit-operation-Monoid = 0

data law-Monoid : UU lzero where
  law-monoid-law-Semigroup : law-Semigroup → law-Monoid
  left-unit-law-law-Monoid : law-Monoid
  right-unit-law-law-Monoid : law-Monoid

algebraic-theory-Monoid : Algebraic-Theory
```
