# Precomposition of dependent functions

```agda
module foundation.precomposition-dependent-functions where

open import foundation-core.precomposition-dependent-functions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.truncated-maps
open import foundation-core.truncation-levels
```

</details>

## Properties

### Equivalences induce an equivalence from the type of homotopies between two dependent functions to the type of homotopies between their precomposites

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1}
  where

  equiv-htpy-precomp-htpy-Π :
    {B : UU l2} {C : B → UU l3} (f g : (b : B) → C b) (e : A ≃ B) →
    (f ~ g) ≃ (f ∘ map-equiv e ~ g ∘ map-equiv e)
  equiv-htpy-precomp-htpy-Π f g e =
    equiv-precomp-Π e (eq-value f g)
```

### Precomposing functions `Π B C` by `f : A → B` is `k+1`-truncated if and only if precomposing homotopies is `k`-truncated

```agda
is-trunc-map-succ-precomp-Π :
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {f : A → B}
  {C : B → UU l3} →
  ((g h : (b : B) → C b) → is-trunc-map k (precomp-Π f (eq-value g h))) →
  is-trunc-map (succ-𝕋 k) (precomp-Π f C)
is-trunc-map-succ-precomp-Π {k = k} {f = f} {C = C} H =
  is-trunc-map-is-trunc-map-ap k (precomp-Π f C)
    ( λ g h →
      is-trunc-map-top-is-trunc-map-bottom-is-equiv k
        ( ap (precomp-Π f C))
        ( htpy-eq)
        ( htpy-eq)
        ( precomp-Π f (eq-value g h))
        ( coherence-square-htpy-eq-ap-precomp-Π f g h)
        ( funext g h)
        ( funext (g ∘ f) (h ∘ f))
        ( H g h))
```
