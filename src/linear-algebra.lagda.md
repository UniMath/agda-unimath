# Linear algebra

## Modules in the linear algebra namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module linear-algebra
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import linear-algebra.constant-matrices funext univalence truncations public
open import linear-algebra.constant-vectors funext univalence truncations public
open import linear-algebra.diagonal-matrices-on-rings funext univalence truncations public
open import linear-algebra.functoriality-matrices funext univalence truncations public
open import linear-algebra.functoriality-vectors funext univalence truncations public
open import linear-algebra.matrices funext univalence truncations public
open import linear-algebra.matrices-on-rings funext univalence truncations public
open import linear-algebra.multiplication-matrices public
open import linear-algebra.scalar-multiplication-matrices funext univalence truncations public
open import linear-algebra.scalar-multiplication-vectors funext univalence truncations public
open import linear-algebra.scalar-multiplication-vectors-on-rings funext univalence truncations public
open import linear-algebra.transposition-matrices funext univalence truncations public
open import linear-algebra.vectors funext univalence truncations public
open import linear-algebra.vectors-on-commutative-rings funext univalence truncations public
open import linear-algebra.vectors-on-commutative-semirings funext univalence truncations public
open import linear-algebra.vectors-on-euclidean-domains funext univalence truncations public
open import linear-algebra.vectors-on-rings funext univalence truncations public
open import linear-algebra.vectors-on-semirings funext univalence truncations public
```
