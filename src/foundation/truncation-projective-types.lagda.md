# Truncation-projective types

```agda
module foundation.truncation-projective-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.iterated-successors-truncation-levels
open import foundation.connected-maps
open import foundation.postcomposition-functions
open import foundation.projective-types
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.sets
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) $k$, a
type $X$ is $𝑘$-{{#concept "projective" Disambiguation="truncation, at a type"}}
if [postcomposition](foundation.postcomposition-functions.md) by any
$(k-1)$-[connected map](foundation.connected-maps.md) into any
$k$-[truncated](foundation.truncated-types.md) codomain is
[surjective](foundation.surjective-maps.md).

## Definitions

### 𝑘-projective types

```agda
is-trunc-projective-Level :
  {l1 : Level} (l2 l3 : Level) → ℕ → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-trunc-projective-Level l2 l3 k X =
  ( A : UU l2) (B : Truncated-Type l3 (truncation-level-ℕ k))
  ( f :
    connected-map
      ( truncation-level-minus-one-ℕ k)
      ( A)
      ( type-Truncated-Type B)) →
  is-surjective (postcomp X (map-connected-map f))

is-trunc-projective : {l1 : Level} → ℕ → UU l1 → UUω
is-trunc-projective k X = {l2 l3 : Level} → is-trunc-projective-Level l2 l3 k X
```

## Properties

### Set-projectivity is equivalent to 0-projectivity

```agda
is-set-projective-is-0-projective-Level :
  {l1 l2 l3 : Level} {X : UU l1} →
  is-trunc-projective-Level l2 l3 zero-ℕ X →
  is-set-projective-Level l2 l3 X
is-set-projective-is-0-projective-Level H A B f =
  H ( A)
    ( type-Set B , is-set-type-Set B)
    ( map-surjection f ,
      is-neg-one-connected-map-is-surjective (is-surjective-map-surjection f))

is-0-projective-is-set-projective-Level :
  {l1 l2 l3 : Level} {X : UU l1} →
  is-set-projective-Level l2 l3 X →
  is-trunc-projective-Level l2 l3 zero-ℕ X
is-0-projective-is-set-projective-Level H A B f =
  H ( A)
    ( type-Truncated-Type B , is-trunc-type-Truncated-Type B)
    ( neg-one-connected-map-surjective-map f)

is-set-projective-is-0-projective :
  {l1 : Level} {X : UU l1} →
  is-trunc-projective zero-ℕ X →
  is-set-projective X
is-set-projective-is-0-projective H {l2} {l3} =
  is-set-projective-is-0-projective-Level (H {l2} {l3})

is-trunc-projective-zero-ℕ-is-set-projective :
  {l1 : Level} {X : UU l1} →
  is-set-projective X →
  is-trunc-projective zero-ℕ X
is-trunc-projective-zero-ℕ-is-set-projective H {l2} {l3} =
  is-0-projective-is-set-projective-Level (H {l2} {l3})
```

### 𝑘-projective 𝑘-types are (𝑘 + 𝑛)-projective for all 𝑛

```agda
is-add-trunc-projective-is-trunc-projective :
  {l1 : Level} (k n : ℕ) {X : UU l1} →
  is-trunc (truncation-level-ℕ k) X →
  is-trunc-projective k X →
  is-trunc-projective (k +ℕ n) X
is-add-trunc-projective-is-trunc-projective {l1} k n {X} K H A B f h =
  map-is-inhabited
    ( map-equiv (compute-Π-fiber-postcomp X (map-connected-map f) h))
    ( map-is-inhabited
      ( map-inv-equiv
        ( compute-fiber-postcomp-pr1 (fiber (map-connected-map f) ∘ h) id))
      ( H ( Σ X (fiber (map-connected-map f) ∘ h))
          ( X , K)
          ( pr1 ,
            λ x →
            is-connected-equiv'
              ( inv-equiv-fiber-pr1
                ( fiber (map-connected-map f) ∘ h)
                ( x))
              ( is-connected-is-connected-add+2-𝕋
                ( truncation-level-minus-one-ℕ k)
                ( truncation-level-minus-two-ℕ n)
                ( tr
                  ( λ t →
                    is-connected t (fiber (map-connected-map f) (h x)))
                  ( add+2-truncation-level-minus-one-ℕ k n)
                  ( is-connected-map-connected-map f (h x)))))
          ( id)))
```

### Projective types in the alternative sense are 𝑛-projective for all 𝑛

```agda
is-trunc-projective-is-projective-Level' :
  {l1 : Level} (l2 l3 : Level) (n : ℕ) {X : UU l1} →
  is-projective-Level' (l2 ⊔ l3) X →
  is-trunc-projective-Level l2 l3 n X
is-trunc-projective-is-projective-Level' l2 l3 n {X} H A B f h =
  map-is-inhabited
    ( map-equiv (compute-Π-fiber-postcomp X (map-connected-map f) h))
    ( H ( λ x → fiber (map-connected-map f) (h x))
        ( λ x →
          is-inhabited-is-connected (is-connected-map-connected-map f (h x))))

is-trunc-projective-is-projective' :
  {l1 : Level} (n : ℕ) {X : UU l1} →
  is-projective' X →
  is-trunc-projective n X
is-trunc-projective-is-projective' n H {l2} {l3} =
  is-trunc-projective-is-projective-Level' l2 l3 n (H {l2 ⊔ l3})
```
