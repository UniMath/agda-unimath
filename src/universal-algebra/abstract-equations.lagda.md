# Abstract equations

```agda
module universal-algebra.abstract-equations where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import universal-algebra.signatures
open import universal-algebra.terms-signatures
```

</details>

## Idea

An abstract equation is a pair of terms.

## Definitions

### Abstract equations

```agda
module _ {l1 : Level} (Sig : signature l1) where

  Abstract-Equation : UU l1
  Abstract-Equation = Term Sig × Term Sig

  lhs-Abstract-Equation : Abstract-Equation → Term Sig
  lhs-Abstract-Equation = pr1

  rhs-Abstract-Equation : Abstract-Equation → Term Sig
  rhs-Abstract-Equation = pr2
```
