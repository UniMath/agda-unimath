# Orthogonal factorization systems

## Examples of higher modalities

{{#include tables/higher-modalities.md}}

## Modules in the orthogonal factorization systems namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module orthogonal-factorization-systems
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import orthogonal-factorization-systems.cd-structures funext univalence truncations public
open import orthogonal-factorization-systems.cellular-maps funext univalence truncations public
open import orthogonal-factorization-systems.closed-modalities funext univalence truncations public
open import orthogonal-factorization-systems.continuation-modalities funext univalence truncations public
open import orthogonal-factorization-systems.double-lifts-families-of-elements funext public
open import orthogonal-factorization-systems.double-negation-sheaves funext univalence truncations public
open import orthogonal-factorization-systems.extensions-double-lifts-families-of-elements funext public
open import orthogonal-factorization-systems.extensions-lifts-families-of-elements funext public
open import orthogonal-factorization-systems.extensions-maps funext univalence public
open import orthogonal-factorization-systems.factorization-operations funext univalence truncations public
open import orthogonal-factorization-systems.factorization-operations-function-classes funext univalence truncations public
open import orthogonal-factorization-systems.factorization-operations-global-function-classes funext univalence truncations public
open import orthogonal-factorization-systems.factorizations-of-maps funext univalence truncations public
open import orthogonal-factorization-systems.factorizations-of-maps-function-classes funext univalence truncations public
open import orthogonal-factorization-systems.factorizations-of-maps-global-function-classes funext univalence truncations public
open import orthogonal-factorization-systems.families-of-types-local-at-maps funext univalence truncations public
open import orthogonal-factorization-systems.fiberwise-orthogonal-maps funext univalence truncations public
open import orthogonal-factorization-systems.function-classes funext univalence truncations public
open import orthogonal-factorization-systems.functoriality-higher-modalities funext univalence truncations public
open import orthogonal-factorization-systems.functoriality-localizations-at-global-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.functoriality-pullback-hom funext univalence truncations public
open import orthogonal-factorization-systems.functoriality-reflective-global-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.global-function-classes funext univalence truncations public
open import orthogonal-factorization-systems.higher-modalities funext univalence truncations public
open import orthogonal-factorization-systems.identity-modality funext univalence truncations public
open import orthogonal-factorization-systems.large-lawvere-tierney-topologies funext univalence truncations public
open import orthogonal-factorization-systems.lawvere-tierney-topologies funext univalence truncations public
open import orthogonal-factorization-systems.lifting-operations funext univalence truncations public
open import orthogonal-factorization-systems.lifting-structures-on-squares funext univalence truncations public
open import orthogonal-factorization-systems.lifts-families-of-elements funext public
open import orthogonal-factorization-systems.lifts-maps funext univalence truncations public
open import orthogonal-factorization-systems.localizations-at-global-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.localizations-at-maps funext univalence truncations public
open import orthogonal-factorization-systems.localizations-at-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.locally-small-modal-operators funext univalence truncations public
open import orthogonal-factorization-systems.maps-local-at-maps funext univalence truncations public
open import orthogonal-factorization-systems.mere-lifting-properties funext univalence truncations public
open import orthogonal-factorization-systems.modal-induction funext univalence truncations public
open import orthogonal-factorization-systems.modal-operators funext univalence truncations public
open import orthogonal-factorization-systems.modal-subuniverse-induction funext univalence truncations public
open import orthogonal-factorization-systems.null-families-of-types funext univalence truncations public
open import orthogonal-factorization-systems.null-maps funext univalence truncations public
open import orthogonal-factorization-systems.null-types funext univalence truncations public
open import orthogonal-factorization-systems.open-modalities funext univalence truncations public
open import orthogonal-factorization-systems.orthogonal-factorization-systems funext univalence truncations public
open import orthogonal-factorization-systems.orthogonal-maps funext univalence truncations public
open import orthogonal-factorization-systems.precomposition-lifts-families-of-elements funext univalence public
open import orthogonal-factorization-systems.pullback-hom funext univalence truncations public
open import orthogonal-factorization-systems.raise-modalities funext univalence truncations public
open import orthogonal-factorization-systems.reflective-global-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.reflective-modalities funext univalence truncations public
open import orthogonal-factorization-systems.reflective-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.regular-cd-structures public
open import orthogonal-factorization-systems.sigma-closed-modalities funext univalence truncations public
open import orthogonal-factorization-systems.sigma-closed-reflective-modalities funext univalence truncations public
open import orthogonal-factorization-systems.sigma-closed-reflective-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.stable-orthogonal-factorization-systems funext univalence truncations public
open import orthogonal-factorization-systems.types-colocal-at-maps funext univalence truncations public
open import orthogonal-factorization-systems.types-local-at-maps funext univalence truncations public
open import orthogonal-factorization-systems.types-separated-at-maps funext univalence truncations public
open import orthogonal-factorization-systems.uniquely-eliminating-modalities funext univalence truncations public
open import orthogonal-factorization-systems.universal-property-localizations-at-global-subuniverses funext univalence truncations public
open import orthogonal-factorization-systems.wide-function-classes funext univalence truncations public
open import orthogonal-factorization-systems.wide-global-function-classes funext univalence truncations public
open import orthogonal-factorization-systems.zero-modality funext univalence truncations public
```
