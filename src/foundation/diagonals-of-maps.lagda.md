# Diagonals of maps

```agda
module foundation.diagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.standard-pullbacks
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definition

```agda
diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  A → standard-pullback f f
diagonal-map f x = (x , x , refl)
```

## Properties

### The fiber of the diagonal of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : standard-pullback f f)
  where

  fiber-ap-fiber-diagonal-map :
    fiber (diagonal-map f) t → fiber (ap f) (pr2 (pr2 t))
  fiber-ap-fiber-diagonal-map (z , refl) = (refl , refl)

  fiber-diagonal-map-fiber-ap :
    fiber (ap f) (pr2 (pr2 t)) → fiber (diagonal-map f) t
  fiber-diagonal-map-fiber-ap (refl , refl) = (pr1 t , refl)

  abstract
    is-section-fiber-diagonal-map-fiber-ap :
      is-section fiber-ap-fiber-diagonal-map fiber-diagonal-map-fiber-ap
    is-section-fiber-diagonal-map-fiber-ap (refl , refl) = refl

  abstract
    is-retraction-fiber-diagonal-map-fiber-ap :
      is-retraction fiber-ap-fiber-diagonal-map fiber-diagonal-map-fiber-ap
    is-retraction-fiber-diagonal-map-fiber-ap (x , refl) = refl

  abstract
    is-equiv-fiber-ap-fiber-diagonal-map :
      is-equiv fiber-ap-fiber-diagonal-map
    is-equiv-fiber-ap-fiber-diagonal-map =
      is-equiv-is-invertible
        ( fiber-diagonal-map-fiber-ap)
        ( is-section-fiber-diagonal-map-fiber-ap)
        ( is-retraction-fiber-diagonal-map-fiber-ap)
```

### A map is `k+1`-truncated if and only if its diagonal is `k`-truncated

```agda
abstract
  is-trunc-diagonal-map-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map (succ-𝕋 k) f → is-trunc-map k (diagonal-map f)
  is-trunc-diagonal-map-is-trunc-map k f is-trunc-f (x , y , p) =
    is-trunc-is-equiv k (fiber (ap f) p)
      ( fiber-ap-fiber-diagonal-map f (triple x y p))
      ( is-equiv-fiber-ap-fiber-diagonal-map f (triple x y p))
      ( is-trunc-map-ap-is-trunc-map-succ k f is-trunc-f x y p)

abstract
  is-trunc-map-is-trunc-diagonal-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map k (diagonal-map f) → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-diagonal-map k f is-trunc-δ b (x , p) (x' , p') =
    is-trunc-is-equiv k
      ( fiber (ap f) (p ∙ (inv p')))
      ( fiber-ap-eq-fiber f (x , p) (x' , p'))
      ( is-equiv-fiber-ap-eq-fiber f (x , p) (x' , p'))
      ( is-trunc-is-equiv' k
        ( fiber (diagonal-map f) (triple x x' (p ∙ (inv p'))))
        ( fiber-ap-fiber-diagonal-map f (triple x x' (p ∙ (inv p'))))
        ( is-equiv-fiber-ap-fiber-diagonal-map f (triple x x' (p ∙ (inv p'))))
        ( is-trunc-δ (triple x x' (p ∙ (inv p')))))

abstract
  is-equiv-diagonal-map-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-emb f → is-equiv (diagonal-map f)
  is-equiv-diagonal-map-is-emb f is-emb-f =
    is-equiv-is-contr-map
      ( is-trunc-diagonal-map-is-trunc-map neg-two-𝕋 f
        ( is-prop-map-is-emb is-emb-f))

abstract
  is-emb-is-equiv-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (diagonal-map f) → is-emb f
  is-emb-is-equiv-diagonal-map f is-equiv-δ =
    is-emb-is-prop-map
      ( is-trunc-map-is-trunc-diagonal-map neg-two-𝕋 f
        ( is-contr-map-is-equiv is-equiv-δ))
```
