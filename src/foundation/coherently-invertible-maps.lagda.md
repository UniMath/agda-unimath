# Coherently invertible maps

```agda
module foundation.coherently-invertible-maps where

open import foundation-core.coherently-invertible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.whiskering-homotopies
```

</details>

## Properties

### Being coherently invertible is a property

```agda
abstract
  is-prop-is-coherently-invertible :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-coherently-invertible f)
  is-prop-is-coherently-invertible {A = A} {B} f =
    is-prop-is-proof-irrelevant
      ( λ H →
        is-contr-equiv'
          ( Σ ( section f)
              ( λ s →
                Σ ( ( map-section f s ∘ f) ~ id)
                  ( λ H →
                    ( htpy-right-whisk (is-section-map-section f s) f) ~
                    ( htpy-left-whisk f H))))
          ( associative-Σ
            ( B → A)
            ( λ g → (f ∘ g) ~ id)
            ( λ s →
              Σ ( ( map-section f s ∘ f) ~ id)
                ( λ H →
                  ( htpy-right-whisk (is-section-map-section f s) f) ~
                  ( htpy-left-whisk f H))))
          ( is-contr-Σ
            ( is-contr-section-is-equiv (is-equiv-is-coherently-invertible H))
            ( section-is-coherently-invertible H)
            ( is-contr-equiv'
              ( (x : A) →
                Σ ( map-inv-is-coherently-invertible H (f x) ＝ x)
                  ( λ p →
                    is-retraction-is-coherently-invertible H (f x) ＝ ap f p))
              ( distributive-Π-Σ)
              ( is-contr-Π
                ( λ x →
                  is-contr-equiv'
                    ( fiber
                      ( ap f)
                      ( is-retraction-is-coherently-invertible H (f x)))
                    ( equiv-tot
                      ( λ p →
                        equiv-inv
                          ( ap f p)
                          ( is-retraction-is-coherently-invertible H (f x))))
                    ( is-contr-map-is-equiv
                      ( is-emb-is-equiv
                        ( is-equiv-is-coherently-invertible H)
                        ( map-inv-is-coherently-invertible H (f x)) x)
                      ( is-retraction-is-coherently-invertible H (f x))))))))

abstract
  is-equiv-is-coherently-invertible-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv (is-coherently-invertible-is-equiv {f = f})
  is-equiv-is-coherently-invertible-is-equiv f =
    is-equiv-is-prop
      ( is-property-is-equiv f)
      ( is-prop-is-coherently-invertible f)
      ( is-equiv-is-coherently-invertible)
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
