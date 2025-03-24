# Iterating involutions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.iterating-involutions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic-standard-finite-types funext univalence truncations
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.involutions funext univalence
open import foundation.iterating-functions funext univalence truncations
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.identity-types

open import univalent-combinatorics.standard-finite-types funext univalence truncations
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
    cases-iterate-involution :
      (k : Fin 2) →
      f (iterate (nat-Fin 2 k) f x) ＝ iterate (nat-Fin 2 (succ-Fin 2 k)) f x
    cases-iterate-involution (inl (inr _)) = refl
    cases-iterate-involution (inr _) = P x
```
