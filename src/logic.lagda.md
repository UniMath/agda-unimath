# Logic

## Modules in the logic namespace

```agda
open import foundation.function-extensionality-axiom

module
  logic
  (funext : function-extensionality)
  where

open import logic.complements-de-morgan-subtypes funext public
open import logic.complements-decidable-subtypes funext public
open import logic.complements-double-negation-stable-subtypes funext public
open import logic.de-morgan-embeddings funext public
open import logic.de-morgan-maps funext public
open import logic.de-morgan-propositions funext public
open import logic.de-morgan-subtypes funext public
open import logic.de-morgan-types funext public
open import logic.de-morgans-law funext public
open import logic.double-negation-eliminating-maps funext public
open import logic.double-negation-elimination funext public
open import logic.double-negation-stable-embeddings funext public
open import logic.double-negation-stable-subtypes funext public
open import logic.functoriality-existential-quantification funext public
open import logic.markovian-types funext public
open import logic.markovs-principle funext public
```
