# Diagonal maps into cartesian products of types

```agda
open import foundation.function-extensionality-axiom

module
  foundation.diagonal-maps-cartesian-products-of-types
  (funext : function-extensionality)
  where

open import foundation-core.diagonal-maps-cartesian-products-of-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.0-maps funext
open import foundation.dependent-pair-types
open import foundation.faithful-maps funext
open import foundation.universe-levels

open import foundation-core.1-types funext
open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.truncated-maps funext
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### A type is `k+1`-truncated if and only if the diagonal is `k`-truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  abstract
    is-trunc-is-trunc-map-diagonal-product :
      (k : 𝕋) → is-trunc-map k (diagonal-product A) → is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-map-diagonal-product k is-trunc-d x y =
      is-trunc-is-equiv' k
        ( fiber (diagonal-product A) (pair x y))
        ( eq-fiber-diagonal-product A (pair x y))
        ( is-equiv-eq-fiber-diagonal-product A (pair x y))
        ( is-trunc-d (pair x y))

  abstract
    is-prop-is-contr-map-diagonal-product :
      is-contr-map (diagonal-product A) → is-prop A
    is-prop-is-contr-map-diagonal-product =
      is-trunc-is-trunc-map-diagonal-product neg-two-𝕋

  abstract
    is-set-is-prop-map-diagonal-product :
      is-prop-map (diagonal-product A) → is-set A
    is-set-is-prop-map-diagonal-product =
      is-trunc-is-trunc-map-diagonal-product neg-one-𝕋

  abstract
    is-set-is-emb-diagonal-product : is-emb (diagonal-product A) → is-set A
    is-set-is-emb-diagonal-product H =
      is-set-is-prop-map-diagonal-product (is-prop-map-is-emb H)

  abstract
    is-1-type-is-0-map-diagonal-product :
      is-0-map (diagonal-product A) → is-1-type A
    is-1-type-is-0-map-diagonal-product =
      is-trunc-is-trunc-map-diagonal-product zero-𝕋

  abstract
    is-1-type-is-faithful-diagonal-product :
      is-faithful (diagonal-product A) → is-1-type A
    is-1-type-is-faithful-diagonal-product H =
      is-1-type-is-0-map-diagonal-product (is-0-map-is-faithful H)

  abstract
    is-trunc-map-diagonal-product-is-trunc :
      (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal-product A)
    is-trunc-map-diagonal-product-is-trunc k is-trunc-A t =
      is-trunc-is-equiv k
        ( pr1 t ＝ pr2 t)
        ( eq-fiber-diagonal-product A t)
        ( is-equiv-eq-fiber-diagonal-product A t)
          ( is-trunc-A (pr1 t) (pr2 t))

  abstract
    is-contr-map-diagonal-product-is-prop :
      is-prop A → is-contr-map (diagonal-product A)
    is-contr-map-diagonal-product-is-prop =
      is-trunc-map-diagonal-product-is-trunc neg-two-𝕋

  abstract
    is-prop-map-diagonal-product-is-set :
      is-set A → is-prop-map (diagonal-product A)
    is-prop-map-diagonal-product-is-set =
      is-trunc-map-diagonal-product-is-trunc neg-one-𝕋

  abstract
    is-emb-diagonal-product-is-set : is-set A → is-emb (diagonal-product A)
    is-emb-diagonal-product-is-set H =
      is-emb-is-prop-map (is-prop-map-diagonal-product-is-set H)

  abstract
    is-0-map-diagonal-product-is-1-type :
      is-1-type A → is-0-map (diagonal-product A)
    is-0-map-diagonal-product-is-1-type =
      is-trunc-map-diagonal-product-is-trunc zero-𝕋

  abstract
    is-faithful-diagonal-product-is-1-type :
      is-1-type A → is-faithful (diagonal-product A)
    is-faithful-diagonal-product-is-1-type H =
      is-faithful-is-0-map (is-0-map-diagonal-product-is-1-type H)

diagonal-product-emb :
  {l : Level} (A : Set l) → type-Set A ↪ type-Set A × type-Set A
pr1 (diagonal-product-emb A) =
  diagonal-product (type-Set A)
pr2 (diagonal-product-emb A) =
  is-emb-diagonal-product-is-set (is-set-type-Set A)

diagonal-product-faithful-map :
  {l : Level} (A : 1-Type l) →
  faithful-map (type-1-Type A) (type-1-Type A × type-1-Type A)
pr1 (diagonal-product-faithful-map A) =
  diagonal-product (type-1-Type A)
pr2 (diagonal-product-faithful-map A) =
  is-faithful-diagonal-product-is-1-type (is-1-type-type-1-Type A)
```
