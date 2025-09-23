# Abstract equations over signatures

```agda
module universal-algebra.abstract-equations-over-signatures where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

An **abstract equation** over a signature `σ` is a statement of a form "`x`
equals `y`", where `x` and `y` are terms over `σ`. Thus, the data of an abstract
equation is simply two terms over a common signature.

## Definitions

### Abstract equations

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  Abstract-Equation : UU l1
  Abstract-Equation = Term σ × Term σ

  lhs-Abstract-Equation : Abstract-Equation → Term σ
  lhs-Abstract-Equation = pr1

  rhs-Abstract-Equation : Abstract-Equation → Term σ
  rhs-Abstract-Equation = pr2
```
