# Globular types

```agda
{-# OPTIONS --guardedness #-}
```

## Modules in the globular types namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module globular-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import globular-types.base-change-dependent-globular-types funext public
open import globular-types.base-change-dependent-reflexive-globular-types funext univalence truncations public
open import globular-types.binary-dependent-globular-types funext public
open import globular-types.binary-dependent-reflexive-globular-types funext univalence truncations public
open import globular-types.binary-globular-maps public
open import globular-types.colax-reflexive-globular-maps funext univalence truncations public
open import globular-types.colax-transitive-globular-maps funext univalence truncations public
open import globular-types.composition-structure-globular-types public
open import globular-types.constant-globular-types public
open import globular-types.dependent-globular-types funext public
open import globular-types.dependent-reflexive-globular-types funext univalence truncations public
open import globular-types.dependent-sums-globular-types funext public
open import globular-types.discrete-dependent-reflexive-globular-types funext univalence truncations public
open import globular-types.discrete-globular-types funext univalence truncations public
open import globular-types.discrete-reflexive-globular-types funext univalence truncations public
open import globular-types.empty-globular-types funext univalence truncations public
open import globular-types.equality-globular-types funext univalence truncations public
open import globular-types.exponentials-globular-types funext public
open import globular-types.fibers-globular-maps funext public
open import globular-types.globular-equivalences funext public
open import globular-types.globular-maps funext public
open import globular-types.globular-types public
open import globular-types.large-colax-reflexive-globular-maps funext univalence truncations public
open import globular-types.large-colax-transitive-globular-maps funext univalence truncations public
open import globular-types.large-globular-maps funext public
open import globular-types.large-globular-types public
open import globular-types.large-lax-reflexive-globular-maps funext univalence truncations public
open import globular-types.large-lax-transitive-globular-maps funext univalence truncations public
open import globular-types.large-reflexive-globular-maps funext univalence truncations public
open import globular-types.large-reflexive-globular-types funext univalence truncations public
open import globular-types.large-symmetric-globular-types funext univalence truncations public
open import globular-types.large-transitive-globular-maps funext univalence truncations public
open import globular-types.large-transitive-globular-types funext univalence truncations public
open import globular-types.lax-reflexive-globular-maps funext univalence truncations public
open import globular-types.lax-transitive-globular-maps funext univalence truncations public
open import globular-types.points-globular-types funext public
open import globular-types.points-reflexive-globular-types funext univalence truncations public
open import globular-types.pointwise-extensions-binary-families-globular-types funext public
open import globular-types.pointwise-extensions-binary-families-reflexive-globular-types funext univalence truncations public
open import globular-types.pointwise-extensions-families-globular-types funext public
open import globular-types.pointwise-extensions-families-reflexive-globular-types funext univalence truncations public
open import globular-types.products-families-of-globular-types funext public
open import globular-types.reflexive-globular-equivalences funext univalence truncations public
open import globular-types.reflexive-globular-maps funext univalence truncations public
open import globular-types.reflexive-globular-types funext univalence truncations public
open import globular-types.sections-dependent-globular-types funext public
open import globular-types.superglobular-types funext univalence truncations public
open import globular-types.symmetric-globular-types funext univalence truncations public
open import globular-types.terminal-globular-types funext univalence public
open import globular-types.transitive-globular-maps funext univalence truncations public
open import globular-types.transitive-globular-types funext univalence truncations public
open import globular-types.unit-globular-type public
open import globular-types.unit-reflexive-globular-type funext univalence truncations public
open import globular-types.universal-globular-type funext public
open import globular-types.universal-reflexive-globular-type funext univalence truncations public
```
