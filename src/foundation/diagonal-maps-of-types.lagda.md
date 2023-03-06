# Diagonal maps of types

<details><summary>Imports</summary>
```agda
module foundation.diagonal-maps-of-types where
open import foundation-core.diagonal-maps-of-types public
open import foundation-core.0-maps
open import foundation-core.1-types
open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.embeddings
open import foundation-core.faithful-maps
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
```
</details>

## Properties

### A type is (k+1)-truncated if and only if the diagonal is k-truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-trunc-is-trunc-map-diagonal :
      (k : 𝕋) → is-trunc-map k (diagonal A) → is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-diagonal k is-trunc-d x y =
      is-trunc-is-equiv' k
        ( fib (diagonal A) (pair x y))
        ( eq-fib-diagonal A (pair x y))
        ( is-equiv-eq-fib-diagonal A (pair x y))
        ( is-trunc-d (pair x y))

  abstract
    is-prop-is-contr-map-diagonal : is-contr-map (diagonal A) → is-prop A
    is-prop-is-contr-map-diagonal = is-trunc-is-trunc-map-diagonal neg-two-𝕋

  abstract
    is-set-is-prop-map-diagonal : is-prop-map (diagonal A) → is-set A
    is-set-is-prop-map-diagonal = is-trunc-is-trunc-map-diagonal neg-one-𝕋

  abstract
    is-set-is-emb-diagonal : is-emb (diagonal A) → is-set A
    is-set-is-emb-diagonal H =
      is-set-is-prop-map-diagonal (is-prop-map-is-emb H)

  abstract
    is-1-type-is-0-map-diagonal : is-0-map (diagonal A) → is-1-type A
    is-1-type-is-0-map-diagonal = is-trunc-is-trunc-map-diagonal zero-𝕋

  abstract
    is-1-type-is-faithful-diagonal : is-faithful (diagonal A) → is-1-type A
    is-1-type-is-faithful-diagonal H =
      is-1-type-is-0-map-diagonal (is-0-map-is-faithful H)

  abstract
    is-trunc-map-diagonal-is-trunc :
      (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal A)
    is-trunc-map-diagonal-is-trunc k is-trunc-A t =
      is-trunc-is-equiv k
        ( pr1 t ＝ pr2 t)
        ( eq-fib-diagonal A t)
        ( is-equiv-eq-fib-diagonal A t)
          ( is-trunc-A (pr1 t) (pr2 t))

  abstract
    is-contr-map-diagonal-is-prop : is-prop A → is-contr-map (diagonal A)
    is-contr-map-diagonal-is-prop = is-trunc-map-diagonal-is-trunc neg-two-𝕋

  abstract
    is-prop-map-diagonal-is-set : is-set A → is-prop-map (diagonal A)
    is-prop-map-diagonal-is-set = is-trunc-map-diagonal-is-trunc neg-one-𝕋

  abstract
    is-emb-diagonal-is-set : is-set A → is-emb (diagonal A)
    is-emb-diagonal-is-set H =
      is-emb-is-prop-map (is-prop-map-diagonal-is-set H)

  abstract
    is-0-map-diagonal-is-1-type : is-1-type A → is-0-map (diagonal A)
    is-0-map-diagonal-is-1-type = is-trunc-map-diagonal-is-trunc zero-𝕋

  abstract
    is-faithful-diagonal-is-1-type : is-1-type A → is-faithful (diagonal A)
    is-faithful-diagonal-is-1-type H =
      is-faithful-is-0-map (is-0-map-diagonal-is-1-type H)

diagonal-emb :
  {l : Level} (A : Set l) → (type-Set A) ↪ ((type-Set A) × (type-Set A))
pr1 (diagonal-emb A) = diagonal (type-Set A)
pr2 (diagonal-emb A) = is-emb-diagonal-is-set (is-set-type-Set A)

diagonal-faithful-map :
  {l : Level} (A : 1-Type l) →
  faithful-map (type-1-Type A) (type-1-Type A × type-1-Type A)
pr1 (diagonal-faithful-map A) = diagonal (type-1-Type A)
pr2 (diagonal-faithful-map A) =
  is-faithful-diagonal-is-1-type (is-1-type-type-1-Type A)
```
