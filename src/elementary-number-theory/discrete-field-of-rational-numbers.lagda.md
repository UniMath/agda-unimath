# The discrete field of rational numbers

```agda
module elementary-number-theory.discrete-field-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.discrete-fields

open import elementary-number-theory.multiplicative-group-of-rational-numbers
open import elementary-number-theory.nonzero-rational-numbers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types

open import ring-theory.division-rings
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with [addition](elementary-number-theory.addition-rational-numbers.md)
and
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a [discrete field](commutative-algebra.discrete-fields.md), i.e., a
[commutative ring](commutative-algebra.commutative-rings.md) whose
[nonzero](elementary-number-theory.nonzero-rational-numbers.md) elements are
[invertible](ring-theory.invertible-elements-rings.md).

## Definitions

### The ring of rational numbers is a division ring

```agda
is-division-ring-ℚ : is-division-Ring ring-ℚ
pr1 is-division-ring-ℚ = is-nonzero-one-ℚ ∘ inv
pr2 is-division-ring-ℚ x H = is-invertible-element-ring-is-nonzero-ℚ x (H ∘ inv)
```

### The rational numbers are a discrete field

```agda
is-discrete-field-ℚ : is-discrete-field-Commutative-Ring commutative-ring-ℚ
is-discrete-field-ℚ = is-division-ring-ℚ
```
