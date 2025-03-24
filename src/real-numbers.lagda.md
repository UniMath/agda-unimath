# Real numbers

## Modules in the real numbers namespace

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module real-numbers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import real-numbers.addition-lower-dedekind-real-numbers funext univalence truncations public
open import real-numbers.addition-upper-dedekind-real-numbers funext univalence truncations public
open import real-numbers.apartness-real-numbers funext univalence truncations public
open import real-numbers.arithmetically-located-dedekind-cuts funext univalence truncations public
open import real-numbers.dedekind-real-numbers funext univalence truncations public
open import real-numbers.inequality-lower-dedekind-real-numbers funext univalence truncations public
open import real-numbers.inequality-real-numbers funext univalence truncations public
open import real-numbers.inequality-upper-dedekind-real-numbers funext univalence truncations public
open import real-numbers.lower-dedekind-real-numbers funext univalence truncations public
open import real-numbers.maximum-lower-dedekind-real-numbers funext univalence truncations public
open import real-numbers.maximum-real-numbers funext univalence truncations public
open import real-numbers.maximum-upper-dedekind-real-numbers funext univalence truncations public
open import real-numbers.metric-space-of-real-numbers funext univalence truncations public
open import real-numbers.minimum-lower-dedekind-real-numbers funext univalence truncations public
open import real-numbers.minimum-real-numbers funext univalence truncations public
open import real-numbers.minimum-upper-dedekind-real-numbers funext univalence truncations public
open import real-numbers.negation-lower-upper-dedekind-real-numbers funext univalence truncations public
open import real-numbers.negation-real-numbers funext univalence truncations public
open import real-numbers.raising-universe-levels-real-numbers funext univalence truncations public
open import real-numbers.rational-lower-dedekind-real-numbers funext univalence truncations public
open import real-numbers.rational-real-numbers funext univalence truncations public
open import real-numbers.rational-upper-dedekind-real-numbers funext univalence truncations public
open import real-numbers.similarity-real-numbers funext univalence truncations public
open import real-numbers.strict-inequality-real-numbers funext univalence truncations public
open import real-numbers.upper-dedekind-real-numbers funext univalence truncations public
```
