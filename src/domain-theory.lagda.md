# Domain theory

## Modules in the domain theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module domain-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import domain-theory.directed-complete-posets funext univalence truncations public
open import domain-theory.directed-families-posets funext univalence truncations public
open import domain-theory.kleenes-fixed-point-theorem-omega-complete-posets funext univalence truncations public
open import domain-theory.kleenes-fixed-point-theorem-posets funext univalence truncations public
open import domain-theory.omega-complete-posets funext univalence truncations public
open import domain-theory.omega-continuous-maps-omega-complete-posets funext univalence truncations public
open import domain-theory.omega-continuous-maps-posets funext univalence truncations public
open import domain-theory.reindexing-directed-families-posets funext univalence truncations public
open import domain-theory.scott-continuous-maps-posets funext univalence truncations public
```
