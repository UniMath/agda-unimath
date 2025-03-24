# Higher group theory

## Modules in the higher group theory namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module higher-group-theory
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import higher-group-theory.abelian-higher-groups funext univalence truncations public
open import higher-group-theory.automorphism-groups funext univalence truncations public
open import higher-group-theory.cartesian-products-higher-groups funext univalence truncations public
open import higher-group-theory.conjugation funext univalence truncations public
open import higher-group-theory.cyclic-higher-groups funext univalence truncations public
open import higher-group-theory.deloopable-groups funext univalence truncations public
open import higher-group-theory.deloopable-h-spaces funext univalence truncations public
open import higher-group-theory.deloopable-types funext univalence truncations public
open import higher-group-theory.eilenberg-mac-lane-spaces funext univalence truncations public
open import higher-group-theory.equivalences-higher-groups funext univalence truncations public
open import higher-group-theory.fixed-points-higher-group-actions funext univalence truncations public
open import higher-group-theory.free-higher-group-actions funext univalence truncations public
open import higher-group-theory.higher-group-actions funext univalence truncations public
open import higher-group-theory.higher-groups funext univalence truncations public
open import higher-group-theory.homomorphisms-higher-group-actions funext univalence truncations public
open import higher-group-theory.homomorphisms-higher-groups funext univalence truncations public
open import higher-group-theory.integers-higher-group funext univalence truncations public
open import higher-group-theory.iterated-cartesian-products-higher-groups funext univalence truncations public
open import higher-group-theory.iterated-deloopings-of-pointed-types funext univalence truncations public
open import higher-group-theory.orbits-higher-group-actions funext univalence truncations public
open import higher-group-theory.small-higher-groups funext univalence truncations public
open import higher-group-theory.subgroups-higher-groups funext univalence truncations public
open import higher-group-theory.symmetric-higher-groups funext univalence truncations public
open import higher-group-theory.transitive-higher-group-actions funext univalence truncations public
open import higher-group-theory.trivial-higher-groups funext univalence truncations public
```
