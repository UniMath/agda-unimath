# Coherently invertible maps

```agda
module foundation.coherently-invertible-maps where

open import foundation-core.coherently-invertible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Properties

### Coherently invertible maps have a contractible type of sections

**Proof:** Since coherently invertible maps are
[contractible maps](foundation.contractible-maps.md), and products of
[contractible types](foundation-core.contractible-types.md) are contractible, it
follows that the type

```text
  (b : B) → fiber f b
```

is contractible, for any coherently invertible map `f`. However, by the
[type theoretic principle of choice](foundation.type-theoretic-principle-of-choice.md)
it follows that this type is equivalent to the type

```text
  Σ (B → A) (λ g → (b : B) → f (g b) ＝ b),
```

which is the type of [sections](foundation.sections.md) of `f`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-contr-section-is-coherently-invertible :
      {f : A → B} → is-coherently-invertible f → is-contr (section f)
    is-contr-section-is-coherently-invertible {f} F =
      is-contr-equiv'
        ( (b : B) → fiber f b)
        ( distributive-Π-Σ)
        ( is-contr-Π (is-contr-map-is-coherently-invertible F))
```

### Being coherently invertible is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-proof-irrelevant-is-coherently-invertible :
      is-proof-irrelevant (is-coherently-invertible f)
    is-proof-irrelevant-is-coherently-invertible H =
      is-contr-equiv'
        ( _)
        ( associative-Σ)
        ( is-contr-Σ
          ( is-contr-section-is-coherently-invertible H)
          ( section-is-coherently-invertible H)
          ( is-contr-equiv'
            ( _)
            ( distributive-Π-Σ)
            ( is-contr-Π
              ( λ x →
                is-contr-equiv'
                  ( _)
                  ( equiv-tot
                    ( λ p →
                      equiv-inv
                        ( ap f p)
                        ( is-section-map-inv-is-coherently-invertible H (f x))))
                  ( is-contr-map-is-coherently-invertible
                    ( is-coherently-invertible-ap-is-coherently-invertible H)
                    ( is-section-map-inv-is-coherently-invertible H (f x)))))))

  abstract
    is-prop-is-coherently-invertible : is-prop (is-coherently-invertible f)
    is-prop-is-coherently-invertible =
      is-prop-is-proof-irrelevant is-proof-irrelevant-is-coherently-invertible

  abstract
    is-equiv-is-coherently-invertible-is-equiv :
      is-equiv (is-coherently-invertible-is-equiv {f = f})
    is-equiv-is-coherently-invertible-is-equiv =
      is-equiv-has-converse-is-prop
        ( is-property-is-equiv f)
        ( is-prop-is-coherently-invertible)
        ( is-equiv-is-coherently-invertible)
```

### Being transpose coherently invertible is a property

This remains to be formalized.

## References

{{#bibliography}} {{#reference UF13}}

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
