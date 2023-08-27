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
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sections
```

</details>

## Properties

### Being coherently invertible is a property

```agda
abstract
  is-prop-is-coherently-invertible :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-coherently-invertible f)
  is-prop-is-coherently-invertible {l1} {l2} {A} {B} f =
    is-prop-is-proof-irrelevant
      ( λ H →
        is-contr-equiv'
          ( Σ ( section f)
              ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
                ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
          ( associative-Σ (B → A)
            ( λ g → ((f ∘ g) ~ id))
            ( λ sf → Σ (((pr1 sf) ∘ f) ~ id)
              ( λ H → (htpy-right-whisk (pr2 sf) f) ~ (htpy-left-whisk f H))))
          ( is-contr-Σ
            ( is-contr-section-is-equiv (E H))
            ( pair (g H) (G H))
            ( is-contr-equiv'
              ( (x : A) →
                Σ ( Id (g H (f x)) x)
                  ( λ p → Id (G H (f x)) (ap f p)))
              ( distributive-Π-Σ)
              ( is-contr-Π
                ( λ x →
                  is-contr-equiv'
                    ( fib (ap f) (G H (f x)))
                    ( equiv-tot
                      ( λ p → equiv-inv (ap f p) (G H (f x))))
                    ( is-contr-map-is-equiv
                      ( is-emb-is-equiv (E H) (g H (f x)) x)
                      ( (G H) (f x))))))))
    where
    E : is-coherently-invertible f → is-equiv f
    E H = is-equiv-is-coherently-invertible H
    g : is-coherently-invertible f → (B → A)
    g H = pr1 H
    G : (H : is-coherently-invertible f) → (f ∘ g H) ~ id
    G H = pr1 (pr2 H)

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
