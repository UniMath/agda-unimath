# The local ring of complex numbers

```agda
module complex-numbers.local-ring-of-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.local-commutative-rings

open import complex-numbers.addition-complex-numbers
open import complex-numbers.addition-nonzero-complex-numbers
open import complex-numbers.large-ring-of-complex-numbers
open import complex-numbers.multiplicative-inverses-nonzero-complex-numbers
open import complex-numbers.nonzero-complex-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-disjunction
open import foundation.universe-levels
```

</details>

## Idea

The
[commutative ring of complex numbers](complex-numbers.large-ring-of-complex-numbers.md)
is [local](commutative-algebra.local-commutative-rings.md).

## Definition

```agda
is-local-commutative-ring-ℂ :
  (l : Level) → is-local-Commutative-Ring (commutative-ring-ℂ l)
is-local-commutative-ring-ℂ l z w is-invertible-z+w =
  map-disjunction
    ( is-invertible-is-nonzero-ℂ z)
    ( is-invertible-is-nonzero-ℂ w)
    ( is-nonzero-either-is-nonzero-add-ℂ
      ( z)
      ( w)
      ( is-nonzero-is-invertible-ℂ
        ( z +ℂ w)
        ( is-invertible-z+w)))

local-commutative-ring-ℂ : (l : Level) → Local-Commutative-Ring (lsuc l)
local-commutative-ring-ℂ l =
  ( commutative-ring-ℂ l , is-local-commutative-ring-ℂ l)
```
