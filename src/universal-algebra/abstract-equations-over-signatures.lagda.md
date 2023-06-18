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

An **abstract equation** over a signature `Sg` is a statement of a form "`x`
equals `y`", where `x` and `y` are terms over `Sg`. Thus, the data of an
abstract equation is simply two terms over a common signature.

## Definitions

### Abstract equations

```agda
module _
  {l1 : Level} (Sg : signature l1)
  where

  Abstract-Equation : UU l1
  Abstract-Equation = Term Sg × Term Sg

  lhs-Abstract-Equation : Abstract-Equation → Term Sg
  lhs-Abstract-Equation = pr1

  rhs-Abstract-Equation : Abstract-Equation → Term Sg
  rhs-Abstract-Equation = pr2
```
