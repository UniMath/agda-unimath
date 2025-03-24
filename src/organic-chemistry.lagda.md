# Organic chemistry

## Modules in the organic chemistry namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module organic-chemistry
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import organic-chemistry.alcohols funext univalence truncations public
open import organic-chemistry.alkanes funext univalence truncations public
open import organic-chemistry.alkenes funext univalence truncations public
open import organic-chemistry.alkynes funext univalence truncations public
open import organic-chemistry.ethane funext univalence truncations public
open import organic-chemistry.hydrocarbons funext univalence truncations public
open import organic-chemistry.methane funext univalence truncations public
open import organic-chemistry.saturated-carbons funext univalence truncations public
```
