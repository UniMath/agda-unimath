# Coherently invertible maps

```agda
module foundation.coherently-invertible-maps where

open import foundation-core.coherently-invertible-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-composition

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Properties

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
        ( associative-Σ _ _ _)
        ( is-contr-Σ
          ( is-contr-section-is-equiv (is-equiv-is-coherently-invertible H))
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
                  ( is-contr-map-is-equiv
                    ( is-emb-is-equiv
                      ( is-equiv-is-coherently-invertible H)
                      ( map-inv-is-coherently-invertible H (f x)) x)
                    ( is-section-map-inv-is-coherently-invertible H (f x)))))))

  abstract
    is-prop-is-coherently-invertible : is-prop (is-coherently-invertible f)
    is-prop-is-coherently-invertible =
      is-prop-is-proof-irrelevant is-proof-irrelevant-is-coherently-invertible

  abstract
    is-equiv-is-coherently-invertible-is-equiv :
      is-equiv (is-coherently-invertible-is-equiv {f = f})
    is-equiv-is-coherently-invertible-is-equiv =
      is-equiv-is-prop
        ( is-property-is-equiv f)
        ( is-prop-is-coherently-invertible)
        ( is-equiv-is-coherently-invertible)
```

### Coherently invertible maps are coherently invertible in both senses

This is Lemma 4.2.2 in _Homotopy Type Theory – Univalent Foundations of
Mathematics_.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  inv-coh-is-transpose-coherently-invertible-is-coherently-invertible' :
    {f : A → B} (H : is-coherently-invertible f) →
    ( ( map-inv-is-coherently-invertible H) ·l
      ( is-section-map-inv-is-coherently-invertible H) ·r
      ( f ∘ map-inv-is-coherently-invertible H)) ~
    ( ( map-inv-is-coherently-invertible H ∘ f) ·l
      ( is-retraction-map-inv-is-coherently-invertible H) ·r
      ( map-inv-is-coherently-invertible H))
  inv-coh-is-transpose-coherently-invertible-is-coherently-invertible' {f} H =
    ( preserves-comp-right-whisker-comp
      ( f)
      ( map-inv-is-coherently-invertible H)
      ( ( map-inv-is-coherently-invertible H) ·l
        ( is-section-map-inv-is-coherently-invertible H))) ∙h
    ( double-whisker-comp²
      ( map-inv-is-coherently-invertible H)
      ( coh-is-coherently-invertible H)
      ( map-inv-is-coherently-invertible H)) ∙h
    ( preserves-comp-left-whisker-comp
      ( map-inv-is-coherently-invertible H)
      ( f)
      ( is-retraction-map-inv-is-coherently-invertible H ·r
        map-inv-is-coherently-invertible H))

  coh-is-transpose-coherently-invertible-is-coherently-invertible' :
    {f : A → B} (H : is-coherently-invertible f) →
    ( ( map-inv-is-coherently-invertible H ∘ f) ·l
      ( is-retraction-map-inv-is-coherently-invertible H) ·r
      ( map-inv-is-coherently-invertible H)) ~
    ( ( map-inv-is-coherently-invertible H) ·l
      ( is-section-map-inv-is-coherently-invertible H) ·r
      ( f ∘ map-inv-is-coherently-invertible H))
  coh-is-transpose-coherently-invertible-is-coherently-invertible' {f} H =
    ( inv-preserves-comp-left-whisker-comp
      ( map-inv-is-coherently-invertible H)
      ( f)
      ( ( is-retraction-map-inv-is-coherently-invertible H) ·r
        ( map-inv-is-coherently-invertible H))) ∙h
    ( double-whisker-comp²
      ( map-inv-is-coherently-invertible H)
      ( inv-htpy (coh-is-coherently-invertible H))
      ( map-inv-is-coherently-invertible H)) ∙h
    ( preserves-comp-right-whisker-comp
      ( f)
      ( map-inv-is-coherently-invertible H)
      ( ( map-inv-is-coherently-invertible H) ·l
        ( is-section-map-inv-is-coherently-invertible H)))

  coh-is-transpose-coherently-invertible-is-coherently-invertible :
    {f : A → B} (H : is-coherently-invertible f) →
    coherence-is-transpose-coherently-invertible
      ( f)
      ( map-inv-is-coherently-invertible H)
      ( is-section-map-inv-is-coherently-invertible H)
      ( is-retraction-map-inv-is-coherently-invertible H)
  coh-is-transpose-coherently-invertible-is-coherently-invertible {f} H =
    {!   !}
```

## References

1. Univalent Foundations Project, _Homotopy Type Theory – Univalent Foundations
   of Mathematics_ (2013) ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729))

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
