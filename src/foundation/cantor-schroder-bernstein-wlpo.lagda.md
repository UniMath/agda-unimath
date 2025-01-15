# The Cantor–Schröder–Bernstein-WLPO theorem

```agda
module foundation.cantor-schroder-bernstein-wlpo where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-embeddings
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.injective-maps
open import foundation.perfect-images
open import foundation.split-surjective-maps
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.sets

open import logic.double-negation-stable-embeddings
```

</details>

## Idea

> TODO

## Statement

```agda
statement-Cantor-Schröder-Bernstein-WLPO :
  (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
statement-Cantor-Schröder-Bernstein-WLPO l1 l2 =
  {X : UU l1} {Y : UU l2} → (X ↪ᵈ Y) → (Y ↪ᵈ X) → X ≃ Y
```

## Proof

### The law of excluded middle implies Cantor-Schröder-Bernstein-WLPO

```agda
module _
  {l1 l2 : Level} (wlpo : level-WLPO (l1 ⊔ l2))
  {X : UU l1} {Y : UU l2} (f : X ↪ᵈ Y) (g : Y ↪ᵈ X)
  where

  map-Cantor-Schröder-Bernstein-WLPO' :
    (x : X) →
    is-decidable (is-perfect-image (map-decidable-emb f) (map-decidable-emb g) x) →
    Y
  map-Cantor-Schröder-Bernstein-WLPO' x (inl y) =
    inverse-of-perfect-image x y
  map-Cantor-Schröder-Bernstein-WLPO' x (inr y) =
    map-decidable-emb f x

  map-Cantor-Schröder-Bernstein-WLPO : X → Y
  map-Cantor-Schröder-Bernstein-WLPO x =
    map-Cantor-Schröder-Bernstein-WLPO' x
      ( is-decidable-is-perfect-image-WLPO wlpo
        ( is-decidable-emb-map-decidable-emb g)
        ( is-decidable-emb-map-decidable-emb f)
        ( x))

  is-injective-map-Cantor-Schröder-Bernstein-WLPO :
    is-injective map-Cantor-Schröder-Bernstein-WLPO
  is-injective-map-Cantor-Schröder-Bernstein-WLPO {x} {x'} =
    l (is-decidable-is-perfect-image-WLPO wlpo (is-decidable-emb-map-decidable-emb g) (is-decidable-emb-map-decidable-emb f) x)
    (is-decidable-is-perfect-image-WLPO wlpo (is-decidable-emb-map-decidable-emb g) (is-decidable-emb-map-decidable-emb f) x')
    where
    l :
      (d : is-decidable (is-perfect-image (map-decidable-emb f) (map-decidable-emb g) x))
      (d' : is-decidable (is-perfect-image (map-decidable-emb f) (map-decidable-emb g) x')) →
      ( map-Cantor-Schröder-Bernstein-WLPO' x d) ＝
      ( map-Cantor-Schröder-Bernstein-WLPO' x' d') →
      x ＝ x'
    l (inl ρ) (inl ρ') p =
      ( inv (is-section-inverse-of-perfect-image x ρ)) ∙
      ( ap (map-decidable-emb g) p ∙ is-section-inverse-of-perfect-image x' ρ')
    l (inl ρ) (inr nρ') p =
      ex-falso (perfect-image-has-distinct-image x' x nρ' ρ (inv p))
    l (inr nρ) (inl ρ') p =
      ex-falso (perfect-image-has-distinct-image x x' nρ ρ' p)
    l (inr nρ) (inr nρ') p =
      is-injective-map-decidable-emb f p

  is-split-surjective-map-Cantor-Schröder-Bernstein-WLPO :
    is-split-surjective map-Cantor-Schröder-Bernstein-WLPO
  is-split-surjective-map-Cantor-Schröder-Bernstein-WLPO y =
    pair x p
    where
    a :
      is-decidable
        ( is-perfect-image (map-decidable-emb f) (map-decidable-emb g) (map-decidable-emb g y)) →
      Σ ( X)
        ( λ x →
          ( (d : is-decidable (is-perfect-image (map-decidable-emb f) (map-decidable-emb g) x)) →
            map-Cantor-Schröder-Bernstein-WLPO' x d ＝ y))
    a (inl γ) =
      pair (map-decidable-emb g y) ψ
      where
      ψ :
        ( d :
          is-decidable
            ( is-perfect-image (map-decidable-emb f) (map-decidable-emb g) (map-decidable-emb g y))) →
        map-Cantor-Schröder-Bernstein-WLPO' (map-decidable-emb g y) d ＝ y
      ψ (inl v') =
        is-retraction-inverse-of-perfect-image
          { is-emb-g = is-emb-map-decidable-emb g}
          ( y)
          ( v')
      ψ (inr v) = ex-falso (v γ)
    a (inr γ) =
      pair x ψ
      where
      w :
        Σ ( fiber (map-decidable-emb f) y)
          ( λ s → ¬ (is-perfect-image (map-decidable-emb f) (map-decidable-emb g) (pr1 s)))
      w =
        has-not-perfect-fiber-is-not-perfect-image
          (is-double-negation-stable-emb-is-decidable-emb (is-decidable-emb-map-decidable-emb g)) (is-double-negation-stable-emb-is-decidable-emb (is-decidable-emb-map-decidable-emb f))
          ( y)
          ( γ)
      x : X
      x = pr1 (pr1 w)
      p : map-decidable-emb f x ＝ y
      p = pr2 (pr1 w)
      ψ :
        ( d : is-decidable (is-perfect-image (map-decidable-emb f) (map-decidable-emb g) x)) →
        map-Cantor-Schröder-Bernstein-WLPO' x d ＝ y
      ψ (inl v) = ex-falso ((pr2 w) v)
      ψ (inr v) = p
    b :
      Σ ( X)
        ( λ x →
          ( (d : is-decidable (is-perfect-image (map-decidable-emb f) (map-decidable-emb g) x)) →
            map-Cantor-Schröder-Bernstein-WLPO' x d ＝ y))
    b =
      a ( is-decidable-is-perfect-image-WLPO wlpo
          (is-decidable-emb-map-decidable-emb g) (is-decidable-emb-map-decidable-emb f)
          ( map-decidable-emb g y))
    x : X
    x = pr1 b
    p : map-Cantor-Schröder-Bernstein-WLPO x ＝ y
    p =
      pr2 b (is-decidable-is-perfect-image-WLPO wlpo (is-decidable-emb-map-decidable-emb g) (is-decidable-emb-map-decidable-emb f) x)

  is-equiv-map-Cantor-Schröder-Bernstein-WLPO :
    is-equiv map-Cantor-Schröder-Bernstein-WLPO
  is-equiv-map-Cantor-Schröder-Bernstein-WLPO =
    is-equiv-is-split-surjective-is-injective
      map-Cantor-Schröder-Bernstein-WLPO
      is-injective-map-Cantor-Schröder-Bernstein-WLPO
      is-split-surjective-map-Cantor-Schröder-Bernstein-WLPO

Cantor-Schröder-Bernstein-WLPO :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  statement-Cantor-Schröder-Bernstein-WLPO l1 l2
Cantor-Schröder-Bernstein-WLPO wlpo f g =
  ( map-Cantor-Schröder-Bernstein-WLPO wlpo f g ,
    is-equiv-map-Cantor-Schröder-Bernstein-WLPO wlpo f g)
```
