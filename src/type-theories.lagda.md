# Type theories

```agda
{-# OPTIONS --guardedness #-}
```

## Modules in the type theories namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module type-theories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import type-theories.comprehension-type-theories public
open import type-theories.dependent-type-theories funext univalence public
open import type-theories.fibered-dependent-type-theories funext univalence public
open import type-theories.pi-types-precategories-with-attributes funext univalence truncations public
open import type-theories.pi-types-precategories-with-families funext univalence truncations public
open import type-theories.precategories-with-attributes funext univalence truncations public
open import type-theories.precategories-with-families funext univalence truncations public
open import type-theories.sections-dependent-type-theories funext univalence public
open import type-theories.simple-type-theories funext univalence public
open import type-theories.unityped-type-theories funext univalence public
```
