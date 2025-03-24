# Finite group theory

## Modules in the finite group theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module finite-group-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import finite-group-theory.abstract-quaternion-group funext univalence truncations public
open import finite-group-theory.alternating-concrete-groups funext univalence truncations public
open import finite-group-theory.alternating-groups funext univalence truncations public
open import finite-group-theory.cartier-delooping-sign-homomorphism funext univalence truncations public
open import finite-group-theory.concrete-quaternion-group funext univalence truncations public
open import finite-group-theory.delooping-sign-homomorphism funext univalence truncations public
open import finite-group-theory.finite-abelian-groups funext univalence truncations public
open import finite-group-theory.finite-commutative-monoids funext univalence truncations public
open import finite-group-theory.finite-groups funext univalence truncations public
open import finite-group-theory.finite-monoids funext univalence truncations public
open import finite-group-theory.finite-semigroups funext univalence truncations public
open import finite-group-theory.finite-type-groups funext univalence truncations public
open import finite-group-theory.groups-of-order-2 funext univalence truncations public
open import finite-group-theory.orbits-permutations funext univalence truncations public
open import finite-group-theory.permutations funext univalence truncations public
open import finite-group-theory.permutations-standard-finite-types funext univalence truncations public
open import finite-group-theory.sign-homomorphism funext univalence truncations public
open import finite-group-theory.simpson-delooping-sign-homomorphism funext univalence truncations public
open import finite-group-theory.subgroups-finite-groups funext univalence truncations public
open import finite-group-theory.tetrahedra-in-3-space funext univalence truncations public
open import finite-group-theory.transpositions funext univalence truncations public
open import finite-group-theory.transpositions-standard-finite-types funext univalence truncations public
```
