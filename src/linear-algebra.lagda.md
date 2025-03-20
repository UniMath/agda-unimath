# Linear algebra

## Modules in the linear algebra namespace

```agda
open import foundation.function-extensionality-axiom

module
  linear-algebra
  (funext : function-extensionality)
  where

open import linear-algebra.constant-matrices funext public
open import linear-algebra.constant-vectors funext public
open import linear-algebra.diagonal-matrices-on-rings funext public
open import linear-algebra.functoriality-matrices funext public
open import linear-algebra.functoriality-vectors funext public
open import linear-algebra.matrices funext public
open import linear-algebra.matrices-on-rings funext public
open import linear-algebra.multiplication-matrices public
open import linear-algebra.scalar-multiplication-matrices funext public
open import linear-algebra.scalar-multiplication-vectors funext public
open import linear-algebra.scalar-multiplication-vectors-on-rings funext public
open import linear-algebra.transposition-matrices funext public
open import linear-algebra.vectors funext public
open import linear-algebra.vectors-on-commutative-rings funext public
open import linear-algebra.vectors-on-commutative-semirings funext public
open import linear-algebra.vectors-on-euclidean-domains funext public
open import linear-algebra.vectors-on-rings funext public
open import linear-algebra.vectors-on-semirings funext public
```
