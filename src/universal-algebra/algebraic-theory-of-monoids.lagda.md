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
data monoid-ops : UU lzero where
  monoid-semigroup-op : operation-Semigroup → monoid-ops
  unit-monoid-op : monoid-ops

pattern mul-monoid-op = monoid-semigroup-op mul-operation-Semigroup-op

monoid-signature : signature lzero
pr1 monoid-signature = monoid-ops
pr2 monoid-signature (monoid-semigroup-op op) =
  pr2 signature-Semigroup op
pr2 monoid-signature unit-monoid-op = 0

data monoid-laws : UU lzero where
  monoid-law-law-Semigroup : law-Semigroup → monoid-laws
  left-unit-law-monoid-law : monoid-laws
  right-unit-law-monoid-law : monoid-laws
```
