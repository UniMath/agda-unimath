# Polytopes

## Modules in the polytopes namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module polytopes
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import polytopes.abstract-polytopes funext univalence truncations public
```
