# Images of semiring homomorphisms

```agda
module ring-theory.images-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.universe-levels
open import foundation.universal-property-image

open import ring-theory.homomorphisms-semirings
open import ring-theory.poset-of-subsemirings
open import ring-theory.pullbacks-subsemirings
open import ring-theory.semirings
open import ring-theory.subsemirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The {{#concept "image" Disambiguation="semiring homomorphism" Agda=im-Semiring}} of a [semiring homomorphism](ring-theory.homomorphisms-semirings.md)
`f : R → S` consists of the [image](foundation.images.md) of the underlying map
of `f`. This [subset](ring-theory.subsets-semirings.md) contains `0` and `1`
and is closed under addition and multiplication. It is therefore a
[subsemiring](ring-theory.subsemirings.md) of the [semiring](ring-theory.semirings.md)
`S`. Alternatively, it can be described as the least subsemiring of `H` that
contains all the values of `f`.

## Definitions

### The universal property of the image of a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (K : Subsemiring l3 S)
  where

  is-image-Semiring : UUω
  is-image-Semiring =
    {l : Level} (L : Subsemiring l S) →
    leq-Subsemiring S K L ↔
    ((g : type-Semiring R) → is-in-Subsemiring S L (map-hom-Semiring R S f g))
```

### The image subsemiring under a semiring homomorphism

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  subset-im-Semiring : subset-Semiring (l1 ⊔ l2) S
  subset-im-Semiring = subtype-im (map-hom-Semiring R S f)

  is-image-subtype-subset-im-Semiring :
    is-image-subtype (map-hom-Semiring R S f) subset-im-Semiring
  is-image-subtype-subset-im-Semiring =
    is-image-subtype-subtype-im (map-hom-Semiring R S f)

  is-in-im-Semiring : type-Semiring S → UU (l1 ⊔ l2)
  is-in-im-Semiring = is-in-subset-Semiring S subset-im-Semiring

  abstract
    contains-zero-im-Semiring :
      contains-zero-subset-Semiring S subset-im-Semiring
    contains-zero-im-Semiring =
      unit-trunc-Prop (zero-Semiring R , preserves-zero-hom-Semiring R S f)

  abstract
    is-closed-under-addition-im-Semiring :
      is-closed-under-addition-subset-Semiring S subset-im-Semiring
    is-closed-under-addition-im-Semiring H K =
      apply-twice-universal-property-trunc-Prop H K
        ( subset-im-Semiring (add-Semiring S _ _))
        ( λ { (x , refl) (y , refl) →
              unit-trunc-Prop
                ( add-Semiring R x y , preserves-addition-hom-Semiring R S f)})

  abstract
    is-additive-submonoid-im-Semiring :
      is-additive-submonoid-subset-Semiring S subset-im-Semiring
    pr1 is-additive-submonoid-im-Semiring =
      contains-zero-im-Semiring
    pr2 is-additive-submonoid-im-Semiring =
      is-closed-under-addition-im-Semiring

  abstract
    contains-one-im-Semiring :
      contains-one-subset-Semiring S subset-im-Semiring
    contains-one-im-Semiring =
      unit-trunc-Prop (one-Semiring R , preserves-one-hom-Semiring R S f)

  abstract
    is-closed-under-multiplication-im-Semiring :
      is-closed-under-multiplication-subset-Semiring S subset-im-Semiring
    is-closed-under-multiplication-im-Semiring {x} {y} K L =
      apply-twice-universal-property-trunc-Prop K L
        ( subset-im-Semiring (mul-Semiring S x y))
        ( λ where
          ( g , refl) (h , refl) →
            unit-trunc-Prop
              ( mul-Semiring R g h , preserves-mul-hom-Semiring R S f))

  is-subsemiring-im-Semiring :
    is-subsemiring-subset-Semiring S subset-im-Semiring
  pr1 is-subsemiring-im-Semiring =
    is-additive-submonoid-im-Semiring
  pr1 (pr2 is-subsemiring-im-Semiring) =
    contains-one-im-Semiring
  pr2 (pr2 is-subsemiring-im-Semiring) =
    is-closed-under-multiplication-im-Semiring

  im-Semiring : Subsemiring (l1 ⊔ l2) S
  pr1 im-Semiring = subset-im-Semiring
  pr2 im-Semiring = is-subsemiring-im-Semiring

  is-image-im-Semiring :
    is-image-Semiring R S f im-Semiring
  is-image-im-Semiring K =
    is-image-subtype-subset-im-Semiring (subset-Subsemiring S K)

  contains-values-im-Semiring :
    (g : type-Semiring R) →
    is-in-Subsemiring S im-Semiring (map-hom-Semiring R S f g)
  contains-values-im-Semiring =
    forward-implication
      ( is-image-im-Semiring im-Semiring)
      ( refl-leq-Subsemiring S im-Semiring)

  leq-im-Semiring :
    {l : Level} (K : Subsemiring l S) →
    ((g : type-Semiring R) → is-in-Subsemiring S K (map-hom-Semiring R S f g)) →
    leq-Subsemiring S im-Semiring K
  leq-im-Semiring K =
    backward-implication (is-image-im-Semiring K)
```
