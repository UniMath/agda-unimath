# Unions of finite subtypes

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.unions-subtypes
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation.unions-subtypes funext univalence truncations public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality funext univalence truncations
open import foundation.propositional-truncations funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types funext univalence truncations
open import univalent-combinatorics.counting funext univalence truncations
open import univalent-combinatorics.counting-decidable-subtypes funext univalence truncations
open import univalent-combinatorics.counting-dependent-pair-types funext univalence truncations
open import univalent-combinatorics.embeddings funext univalence truncations
open import univalent-combinatorics.finite-types funext univalence truncations
```

</details>

## Properties

### If `A` has decidable equalities, `P` and `Q` are subtypes of A equipped with a counting, then `P ∪ Q` is equipped with a counting

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l2 A) (Q : subtype l3 A)
  where

  count-union-subtypes-count-has-decidable-equalities :
    has-decidable-equality A → count (type-subtype P) →
    count (type-subtype Q) → count (type-subtype (union-subtype P Q))
  count-union-subtypes-count-has-decidable-equalities dec-A count-P count-Q =
    count-decidable-emb
      ( decidable-emb-tot-trunc-Prop-count
        ( count-fiber-count-Σ dec-A (count-Σ-coproduct count-P count-Q)))
      ( count-Σ-coproduct count-P count-Q)
```

### If `A` has decidable equalities and `P` and `Q` are both finite, then `P ∪ Q` is also finite

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : subtype l2 A) (Q : subtype l3 A)
  where

  finite-union-subtypes-finite-has-decidable-equalities :
    has-decidable-equality A → is-finite (type-subtype P) →
    is-finite (type-subtype Q) → is-finite (type-subtype (union-subtype P Q))
  finite-union-subtypes-finite-has-decidable-equalities dec-A fin-P fin-Q =
    apply-twice-universal-property-trunc-Prop
      ( fin-P)
      ( fin-Q)
      ( is-finite-Prop (type-subtype (union-subtype P Q)))
      ( λ count-P count-Q →
        unit-trunc-Prop
          ( count-union-subtypes-count-has-decidable-equalities
            P
            Q
            dec-A
            count-P
            count-Q))
```
