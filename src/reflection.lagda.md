# Reflection

```agda
{-# OPTIONS --rewriting #-}
```

## Modules in the reflection namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module reflection
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import reflection.abstractions public
open import reflection.arguments public
open import reflection.boolean-reflection funext univalence truncations public
open import reflection.definitions public
open import reflection.erasing-equality public
open import reflection.fixity funext univalence truncations public
open import reflection.group-solver funext univalence truncations public
open import reflection.literals public
open import reflection.metavariables public
open import reflection.names public
open import reflection.precategory-solver funext univalence truncations public
open import reflection.rewriting public
open import reflection.terms public
open import reflection.type-checking-monad public
```
