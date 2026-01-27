# Tuples in rings

```agda
module ring-theory.tuples-in-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.coproduct-types

open import lists.tuples

open import ring-theory.rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definitions

### Zero tuple

```agda
zero-tuple-type-Ring :
  {l : Level} → (R : Ring l) → (n : ℕ) → tuple (type-Ring R) n
zero-tuple-type-Ring R zero-ℕ = empty-tuple
zero-tuple-type-Ring R (succ-ℕ n) =
  zero-Ring R ∷ zero-tuple-type-Ring R n
```

## Properties

### Any component of the zero tuple is the zero element

```agda
zero-component-zero-tuple-type-Ring :
  {l : Level} →
  {R : Ring l}
  (n : ℕ) →
  (i : Fin n) →
  zero-Ring R ＝ component-tuple n (zero-tuple-type-Ring R n) i
zero-component-zero-tuple-type-Ring (succ-ℕ n) (inr _) = refl
zero-component-zero-tuple-type-Ring (succ-ℕ n) (inl i) =
  zero-component-zero-tuple-type-Ring n i
```
