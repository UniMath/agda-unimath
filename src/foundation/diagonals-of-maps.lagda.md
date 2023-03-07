# Diagonals of maps

```agda
module foundation.diagonals-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-fibers-of-maps
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.pullbacks
open import foundation.truncated-maps
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
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
pr1 (fib-ap-fib-diagonal-map f .(diagonal-map f z) (pair z refl)) = refl
pr2 (fib-ap-fib-diagonal-map f .(diagonal-map f z) (pair z refl)) = refl

fib-diagonal-map-fib-ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  (t : canonical-pullback f f) →
  (fib (ap f) (pr2 (pr2 t))) → (fib (diagonal-map f) t)
pr1
  ( fib-diagonal-map-fib-ap f
    ( pair x (pair .x .(ap f refl)))
    ( pair refl refl)) = x
pr2 (fib-diagonal-map-fib-ap f
  ( pair x (pair .x .(ap f refl)))
  ( pair refl refl)) = refl

abstract
  issec-fib-diagonal-map-fib-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    ((fib-ap-fib-diagonal-map f t) ∘ (fib-diagonal-map-fib-ap f t)) ~ id
  issec-fib-diagonal-map-fib-ap f (pair x (pair .x .refl)) (pair refl refl) =
    refl

abstract
  isretr-fib-diagonal-map-fib-ap :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    ((fib-diagonal-map-fib-ap f t) ∘ (fib-ap-fib-diagonal-map f t)) ~ id
  isretr-fib-diagonal-map-fib-ap f .(pair x (pair x refl)) (pair x refl) =
    refl

abstract
  is-equiv-fib-ap-fib-diagonal-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (t : canonical-pullback f f) →
    is-equiv (fib-ap-fib-diagonal-map f t)
  is-equiv-fib-ap-fib-diagonal-map f t =
    is-equiv-has-inverse
      ( fib-diagonal-map-fib-ap f t)
      ( issec-fib-diagonal-map-fib-ap f t)
      ( isretr-fib-diagonal-map-fib-ap f t)
```

### A map is `(k+1)`-truncated if and only if its diagonal is `k`-truncated

```agda
abstract
  is-trunc-diagonal-map-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map (succ-𝕋 k) f → is-trunc-map k (diagonal-map f)
  is-trunc-diagonal-map-is-trunc-map k f is-trunc-f (pair x (pair y p)) =
    is-trunc-is-equiv k (fib (ap f) p)
      ( fib-ap-fib-diagonal-map f (triple x y p))
      ( is-equiv-fib-ap-fib-diagonal-map f (triple x y p))
      ( is-trunc-map-ap-is-trunc-map k f is-trunc-f x y p)

abstract
  is-trunc-map-is-trunc-diagonal-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B) →
    is-trunc-map k (diagonal-map f) → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-is-trunc-diagonal-map
    k f is-trunc-δ b (pair x p) (pair x' p') =
    is-trunc-is-equiv k
      ( fib (ap f) (p ∙ (inv p')))
      ( fib-ap-eq-fib f (pair x p) (pair x' p'))
      ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
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
