# Path-split maps

```agda
module foundation.path-split-maps where

open import foundation-core.path-split-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.propositions
```

</details>

## Properties

### Being path-split is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-is-path-split : (f : A → B) → is-prop (is-path-split f)
    is-prop-is-path-split f =
      is-prop-is-proof-irrelevant
        ( λ is-path-split-f →
          ( is-contr-prod
            ( is-contr-section-is-equiv
              ( is-equiv-is-path-split f is-path-split-f))
            ( is-contr-Π
              ( λ x → is-contr-Π
                ( λ y → is-contr-section-is-equiv
                  ( is-emb-is-equiv
                    ( is-equiv-is-path-split f is-path-split-f) x y))))))

  abstract
    is-equiv-is-path-split-is-equiv :
      (f : A → B) → is-equiv (is-path-split-is-equiv f)
    is-equiv-is-path-split-is-equiv f =
      is-equiv-is-prop
        ( is-property-is-equiv f)
        ( is-prop-is-path-split f)
        ( is-equiv-is-path-split f)

  equiv-is-path-split-is-equiv : (f : A → B) → is-equiv f ≃ is-path-split f
  equiv-is-path-split-is-equiv f =
    pair (is-path-split-is-equiv f) (is-equiv-is-path-split-is-equiv f)

  abstract
    is-equiv-is-equiv-is-path-split :
      (f : A → B) → is-equiv (is-equiv-is-path-split f)
    is-equiv-is-equiv-is-path-split f =
      is-equiv-is-prop
        ( is-prop-is-path-split f)
        ( is-property-is-equiv f)
        ( is-path-split-is-equiv f)

  equiv-is-equiv-is-path-split : (f : A → B) → is-path-split f ≃ is-equiv f
  equiv-is-equiv-is-path-split f =
    pair (is-equiv-is-path-split f) (is-equiv-is-equiv-is-path-split f)
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).

## References

1. Univalent Foundations Project, _Homotopy Type Theory – Univalent Foundations
   of Mathematics_ (2013) ([website](https://homotopytypetheory.org/book/),
   [arXiv:1308.0729](https://arxiv.org/abs/1308.0729),
   [DOI:10.48550](https://doi.org/10.48550/arXiv.1308.0729))
2. Mike Shulman, _Universal properties without function extensionality_
   (November 2014)
   ([HoTT Blog](https://homotopytypetheory.org/2014/11/02/universal-properties-without-function-extensionality/))
