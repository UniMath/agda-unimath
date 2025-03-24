# Equivalences between finite types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.equivalences
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation.equivalences funext public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.embeddings funext univalence truncations
open import univalent-combinatorics.finite-types funext univalence truncations
open import univalent-combinatorics.surjective-maps funext univalence truncations
```

</details>

## Properties

### For a map between finite types, being an equivalence is decidable

```agda
is-decidable-is-equiv-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-equiv f)
is-decidable-is-equiv-is-finite f HA HB =
  is-decidable-iff
    ( λ p → is-equiv-is-emb-is-surjective (pr1 p) (pr2 p))
    ( λ K → pair (is-surjective-is-equiv K) (is-emb-is-equiv K))
    ( is-decidable-product
      ( is-decidable-is-surjective-is-finite f HA HB)
      ( is-decidable-is-emb-is-finite f HA HB))
```
