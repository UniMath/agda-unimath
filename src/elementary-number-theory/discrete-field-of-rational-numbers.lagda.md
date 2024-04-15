# The discrete field of rational numbers

```agda
module elementary-number-theory.discrete-field-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.discrete-fields

open import elementary-number-theory.ring-of-rational-numbers
```

</details>

## Idea

The type of [rational numbers](elementary-number-theory.rational-numbers.md)
equipped with [addition](elementary-number-theory.addition-rational-numbers.md)
and
[multiplication](elementary-number-theory.multiplication-rational-numbers.md) is
a [discrete field](commutative-algebra.discrete-fields.md).

## Definitions

```agda
is-discrete-field-ℚ : is-discrete-field-Commutative-Ring ℚ-Commutative-Ring
is-discrete-field-ℚ = is-division-Ring-ℚ-Ring
```
