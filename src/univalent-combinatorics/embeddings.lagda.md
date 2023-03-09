# Injective maps

```agda
module univalent-combinatorics.embeddings where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddings public

open import foundation.decidable-types
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.injective-maps
```

</details>

## Idea

Embeddings in the presence of finite types enjoy further properties.

## Properties

```agda
is-decidable-is-emb-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-emb f)
is-decidable-is-emb-is-finite f HA HB =
  is-decidable-iff
    ( is-emb-is-injective (is-set-is-finite HB))
    ( is-injective-is-emb)
    ( is-decidable-is-injective-is-finite f HA HB)
```
