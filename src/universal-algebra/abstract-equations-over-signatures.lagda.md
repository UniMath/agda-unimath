# Abstract equations over signatures

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module universal-algebra.abstract-equations-over-signatures
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import universal-algebra.signatures funext univalence
open import universal-algebra.terms-over-signatures funext univalence truncations
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
