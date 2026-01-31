# Postcomposition of extensions of maps

```agda
module orthogonal-factorization-systems.postcomposition-extensions-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.postcomposition-functions
open import foundation.truncated-maps
open import foundation.truncation-levels
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.monomorphisms

open import orthogonal-factorization-systems.extensions-maps
```

</details>

## Idea

Given a map `i : A → B` and a map `f : A → X`, then we may
{{#concept "postcompose" Disambiguation="extension of map by map" Agda=postcomp-extension-map}}
any [extension](orthogonal-factorization-systems.extensions-maps.md)
`α : extension-map i f` by a map `g : X → Y` to obtain an extension of `g ∘ f`
along `i`, `gα : extension-map i (g ∘ f)`.

## Definition

### Postcomposition of extensions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  postcomp-extension-map :
    (i : A → B) (f : A → X) (g : X → Y) →
    extension-map i f → extension-map i (g ∘ f)
  postcomp-extension-map i f g =
    map-Σ (is-extension-of-map i (g ∘ f)) (postcomp B g) (λ j H → g ·l H)
```

## Properties

### Postcomposition of extensions by an equivalence is an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-equiv-postcomp-extension-map :
    (f : A → B) (i : A → X) (g : X → Y) → is-equiv g →
    is-equiv (postcomp-extension-map f i g)
  is-equiv-postcomp-extension-map f i g G =
    is-equiv-map-Σ
      ( is-extension-of-map f (g ∘ i))
      ( is-equiv-postcomp-is-equiv g G B)
      ( λ j →
        is-equiv-map-Π-is-fiberwise-equiv
          ( λ x → is-emb-is-equiv G (i x) (j (f x))))

  equiv-postcomp-extension-map :
    (f : A → B) (i : A → X) (g : X ≃ Y) →
    extension-map f i ≃ extension-map f (map-equiv g ∘ i)
  equiv-postcomp-extension-map f i (g , G) =
    ( postcomp-extension-map f i g , is-equiv-postcomp-extension-map f i g G)
```

### Postcomposition of extensions by an embedding is an embedding

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-emb-postcomp-extension-map :
    (f : A → B) (i : A → X) (g : X → Y) → is-emb g →
    is-emb (postcomp-extension-map f i g)
  is-emb-postcomp-extension-map f i g H =
    is-emb-map-Σ
      ( is-extension-of-map f (g ∘ i))
      ( is-mono-is-emb g H B)
      ( λ j →
        is-emb-is-equiv
          ( is-equiv-map-Π-is-fiberwise-equiv
            (λ x → H (i x) (j (f x)))))

  emb-postcomp-extension-map :
    (f : A → B) (i : A → X) (g : X ↪ Y) →
    extension-map f i ↪ extension-map f (map-emb g ∘ i)
  emb-postcomp-extension-map f i (g , G) =
    postcomp-extension-map f i g , is-emb-postcomp-extension-map f i g G
```

### Postcomposition of extensions by a `k`-truncated map is `k`-truncated

```agda
module _
  {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-trunc-map-postcomp-extension-map :
    (f : A → B) (i : A → X) (g : X → Y) → is-trunc-map k g →
    is-trunc-map k (postcomp-extension-map f i g)
  is-trunc-map-postcomp-extension-map f i g G =
    is-trunc-map-map-Σ k
      ( is-extension-of-map f (g ∘ i))
      ( is-trunc-map-postcomp-is-trunc-map k g G B)
      ( λ j →
        is-trunc-map-map-Π k
          ( λ a → ap g)
          ( λ a → is-trunc-map-ap-is-trunc-map k g G (i a) (j (f a))))

  trunc-map-postcomp-extension-map :
    (f : A → B) (i : A → X) (g : trunc-map k X Y) →
    trunc-map k (extension-map f i) (extension-map f (map-trunc-map g ∘ i))
  trunc-map-postcomp-extension-map f i (g , G) =
    ( postcomp-extension-map f i g ,
      is-trunc-map-postcomp-extension-map f i g G)
```

## See also

- In [`foundation.surjective-maps`](foundation.surjective-maps.md) it is shown
  that postcomposition of extensions along surjective maps by an embedding is an
  equivalence.
