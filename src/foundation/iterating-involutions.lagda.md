# Iterating involutions

```agda
module foundation.iterating-involutions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.iterating-functions
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Definition

### Iterating involutions

```agda
module _
  {l : Level} {X : UU l} (f : X → X) (P : is-involution f)
  where

  iterate-involution :
    (n : ℕ) (x : X) → iterate n f x ＝ iterate (nat-Fin 2 (mod-two-ℕ n)) f x
  iterate-involution zero-ℕ x = refl
  iterate-involution (succ-ℕ n) x =
    ap f (iterate-involution n x) ∙ (cases-iterate-involution (mod-two-ℕ n))
    where
    cases-iterate-involution : (k : Fin 2) →
      Id (f (iterate (nat-Fin 2 k) f x)) (iterate (nat-Fin 2 (succ-Fin 2 k)) f x)
    cases-iterate-involution (inl (inr star)) = refl
    cases-iterate-involution (inr star) = P x
```
