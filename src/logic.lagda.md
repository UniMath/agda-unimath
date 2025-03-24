# Logic

## Modules in the logic namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module logic
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import logic.complements-de-morgan-subtypes funext univalence truncations public
open import logic.complements-decidable-subtypes funext univalence truncations public
open import logic.complements-double-negation-stable-subtypes funext univalence truncations public
open import logic.de-morgan-embeddings funext univalence truncations public
open import logic.de-morgan-maps funext univalence truncations public
open import logic.de-morgan-propositions funext univalence truncations public
open import logic.de-morgan-subtypes funext univalence truncations public
open import logic.de-morgan-types funext univalence truncations public
open import logic.de-morgans-law funext univalence truncations public
open import logic.double-negation-eliminating-maps funext univalence truncations public
open import logic.double-negation-elimination funext univalence truncations public
open import logic.double-negation-stable-embeddings funext univalence truncations public
open import logic.double-negation-stable-subtypes funext univalence truncations public
open import logic.functoriality-existential-quantification funext univalence truncations public
open import logic.markovian-types funext univalence truncations public
open import logic.markovs-principle funext univalence truncations public
```
