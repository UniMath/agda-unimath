# The universal property of truncations

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.universal-property-truncation
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation-core.universal-property-truncation funext public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types funext
open import foundation.function-extensionality funext
open import foundation.identity-types funext
open import foundation.propositional-truncations funext univalence
open import foundation.surjective-maps funext univalence truncations
open import foundation.type-arithmetic-dependent-function-types funext univalence
open import foundation.universal-property-dependent-pair-types funext
open import foundation.universal-property-identity-types funext univalence truncations
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-function-types funext
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Properties

### A map `f : A → B` is a `k+1`-truncation if and only if it is surjective and `ap f : (x ＝ y) → (f x ＝ f y)` is a `k`-truncation for all `x y : A`

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 (succ-𝕋 k))
  {f : A → type-Truncated-Type B} (H : is-surjective f)
  ( K :
    (x y : A) → is-truncation (Id-Truncated-Type B (f x) (f y)) (ap f {x} {y}))
  where

  unique-extension-fiber-is-truncation-is-truncation-ap :
    {l : Level} (C : Truncated-Type l (succ-𝕋 k))
    (g : A → type-Truncated-Type C) (y : type-Truncated-Type B) →
    is-contr
      ( Σ ( type-Truncated-Type C)
          ( λ z → (t : fiber f y) → g (pr1 t) ＝ z))
  unique-extension-fiber-is-truncation-is-truncation-ap C g =
    apply-dependent-universal-property-surjection-is-surjective f H
      ( λ y → is-contr-Prop _)
      ( λ x →
        is-contr-equiv
          ( Σ (type-Truncated-Type C) (λ z → g x ＝ z))
          ( equiv-tot
            ( λ z →
              ( ( equiv-ev-refl' x) ∘e
                ( equiv-Π-equiv-family
                  ( λ x' →
                    equiv-is-truncation
                      ( Id-Truncated-Type B (f x') (f x))
                      ( ap f)
                      ( K x' x)
                      ( Id-Truncated-Type C (g x') z)))) ∘e
              ( equiv-ev-pair)))
          ( is-torsorial-Id (g x)))

  is-truncation-is-truncation-ap :
    is-truncation B f
  is-truncation-is-truncation-ap C =
    is-equiv-is-contr-map
      ( λ g →
        is-contr-equiv'
          ( (y : type-Truncated-Type B) →
            Σ ( type-Truncated-Type C)
              ( λ z → (t : fiber f y) → (g (pr1 t) ＝ z)))
          ( ( equiv-tot
              ( λ h →
                ( ( ( inv-equiv (equiv-funext)) ∘e
                    ( equiv-Π-equiv-family
                      ( λ x →
                        equiv-inv (g x) (h (f x)) ∘e equiv-ev-refl (f x)))) ∘e
                  ( equiv-swap-Π)) ∘e
                ( equiv-Π-equiv-family (λ x → equiv-ev-pair)))) ∘e
            ( distributive-Π-Σ))
          ( is-contr-Π
            ( unique-extension-fiber-is-truncation-is-truncation-ap C g)))

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 (succ-𝕋 k))
  {f : A → type-Truncated-Type B}
  where

  is-surjective-is-truncation :
    is-truncation B f → is-surjective f
  is-surjective-is-truncation H =
    map-inv-is-equiv
      ( dependent-universal-property-truncation-is-truncation B f H
        ( λ y → truncated-type-trunc-Prop k (fiber f y)))
      ( λ x → unit-trunc-Prop (pair x refl))
```
