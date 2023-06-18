# Diagonals of maps

```agda
module foundation.diagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-fibers-of-maps
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositional-maps
open import foundation-core.pullbacks
open import foundation-core.truncated-maps
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Definition

```agda
diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  A → canonical-pullback f f
diagonal-map f x = triple x x refl
```

## Properties

### The fiber of the diagonal of a map

```agda
fib-ap-fib-diagonal-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  (fib (diagonal-map f) t) → (fib (ap f) (pr2 (pr2 t)))
pr1 (fib-ap-fib-diagonal-map f .(diagonal-map f z) (z , refl)) = refl
pr2 (fib-ap-fib-diagonal-map f .(diagonal-map f z) (z , refl)) = refl

fib-diagonal-map-fib-ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  (fib (ap f) (pr2 (pr2 t))) → (fib (diagonal-map f) t)
pr1 (fib-diagonal-map-fib-ap f (x , .x , .(ap f refl)) (refl , refl)) = x
pr2 (fib-diagonal-map-fib-ap f (x , .x , .(ap f refl)) (refl , refl)) = refl

abstract
  is-section-fib-diagonal-map-fib-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    ((fib-ap-fib-diagonal-map f t) ∘ (fib-diagonal-map-fib-ap f t)) ~ id
  is-section-fib-diagonal-map-fib-ap f (x , .x , .refl) (refl , refl) =
    refl

abstract
  is-retraction-fib-diagonal-map-fib-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    ((fib-diagonal-map-fib-ap f t) ∘ (fib-ap-fib-diagonal-map f t)) ~ id
  is-retraction-fib-diagonal-map-fib-ap f .(x , x , refl) (x , refl) =
    refl

abstract
  is-equiv-fib-ap-fib-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    is-equiv (fib-ap-fib-diagonal-map f t)
  is-equiv-fib-ap-fib-diagonal-map f t =
    is-equiv-has-inverse
      ( fib-diagonal-map-fib-ap f t)
      ( is-section-fib-diagonal-map-fib-ap f t)
      ( is-retraction-fib-diagonal-map-fib-ap f t)
```

### A map is `k+1`-truncated if and only if its diagonal is `k`-truncated

```agda
abstract
  is-trunc-diagonal-map-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map (succ-𝕋 k) f → is-trunc-map k (diagonal-map f)
  is-trunc-diagonal-map-is-trunc-map k f is-trunc-f (x , y , p) =
    is-trunc-is-equiv k (fib (ap f) p)
      ( fib-ap-fib-diagonal-map f (triple x y p))
      ( is-equiv-fib-ap-fib-diagonal-map f (triple x y p))
      ( is-trunc-map-ap-is-trunc-map k f is-trunc-f x y p)

abstract
  is-trunc-map-is-trunc-diagonal-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map k (diagonal-map f) → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-diagonal-map k f is-trunc-δ b (x , p) (x' , p') =
    is-trunc-is-equiv k
      ( fib (ap f) (p ∙ (inv p')))
      ( fib-ap-eq-fib f (x , p) (x' , p'))
      ( is-equiv-fib-ap-eq-fib f (x , p) (x' , p'))
      ( is-trunc-is-equiv' k
        ( fib (diagonal-map f) (triple x x' (p ∙ (inv p'))))
        ( fib-ap-fib-diagonal-map f (triple x x' (p ∙ (inv p'))))
        ( is-equiv-fib-ap-fib-diagonal-map f (triple x x' (p ∙ (inv p'))))
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
