# Universal algebra

## Modules in the universal algebra namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module universal-algebra
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import universal-algebra.abstract-equations-over-signatures funext univalence truncations public
open import universal-algebra.algebraic-theories funext univalence truncations public
open import universal-algebra.algebraic-theory-of-groups funext univalence truncations public
open import universal-algebra.algebras-of-theories funext univalence truncations public
open import universal-algebra.congruences funext univalence truncations public
open import universal-algebra.homomorphisms-of-algebras funext univalence truncations public
open import universal-algebra.kernels funext univalence truncations public
open import universal-algebra.models-of-signatures funext univalence truncations public
open import universal-algebra.quotient-algebras funext univalence truncations public
open import universal-algebra.signatures funext univalence public
open import universal-algebra.terms-over-signatures funext univalence truncations public
```
