# Dirichlet convolution

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.dirichlet-convolution
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.arithmetic-functions funext
open import elementary-number-theory.bounded-sums-arithmetic-functions funext
open import elementary-number-theory.modular-arithmetic-standard-finite-types funext
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers funext

open import foundation.dependent-pair-types
open import foundation.empty-types funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import ring-theory.rings funext
```

</details>

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  dirichlet-convolution-arithmetic-functions-Ring :
    (f g : type-arithmetic-functions-Ring R) →
    type-arithmetic-functions-Ring R
  dirichlet-convolution-arithmetic-functions-Ring f g (pair zero-ℕ H) =
    ex-falso (H refl)
  dirichlet-convolution-arithmetic-functions-Ring f g (pair (succ-ℕ n) H) =
    bounded-sum-arithmetic-function-Ring R
      ( succ-ℕ n)
      ( λ x → div-ℕ-Decidable-Prop (pr1 x) (succ-ℕ n) (pr2 x))
      ( λ (x , K) H →
        mul-Ring R
          ( f ( pair x K))
          ( g ( quotient-div-nonzero-ℕ x (succ-nonzero-ℕ' n) H)))
```
