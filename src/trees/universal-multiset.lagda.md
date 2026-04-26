# The universal multiset

```agda
module trees.universal-multiset where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.small-types
open import foundation.small-universes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import trees.functoriality-w-types
open import trees.multisets
open import trees.small-multisets
open import trees.w-types
```

</details>

## Idea

The {{#concept "universal multiset" Agda=universal-multiset-𝕍}} of
[universe level](foundation.universe-levels.md) `l` is the
[multiset](trees.multisets.md) of level `lsuc l` built out of `𝕍 l` and
[resizings](trees.small-multisets.md) of the multisets it contains.

## Definition

```agda
universal-multiset-𝕍 : (l : Level) → 𝕍 (lsuc l)
universal-multiset-𝕍 l =
  tree-𝕎
    ( 𝕍 l)
    ( λ X → resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))
```

## Properties

### If `UU l1` is `UU l`-small, then the universal multiset of level `l1` is `UU l`-small

```agda
is-small-universal-multiset-𝕍 :
  (l : Level) {l1 : Level} →
  is-small-universe l l1 → is-small-𝕍 l (universal-multiset-𝕍 l1)
is-small-universal-multiset-𝕍 l {l1} (pair (pair U e) H) =
  pair
    ( pair
      ( 𝕎 U (λ x → pr1 (H (map-inv-equiv e x))))
      ( equiv-𝕎
        ( λ u → type-is-small (H (map-inv-equiv e u)))
        ( e)
        ( λ X →
          tr
            ( λ t → X ≃ pr1 (H t))
            ( inv (is-retraction-map-inv-equiv e X))
            ( pr2 (H X)))))
    ( f)
    where
    f :
      (X : 𝕍 l1) →
      is-small-𝕍 l (resize-𝕍 X (is-small-multiset-𝕍 is-small-lsuc X))
    f (tree-𝕎 A α) =
      pair
        ( pair
          ( type-is-small (H A))
          ( equiv-is-small (H A) ∘e inv-equiv (compute-raise (lsuc l1) A)))
        ( λ x → f (α (map-inv-raise x)))
```
