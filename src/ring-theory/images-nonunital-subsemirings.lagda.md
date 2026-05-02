# Images of nonunital subsemirings

```agda
module ring-theory.images-nonunital-subsemirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.images-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.galois-connections-large-posets
open import order-theory.order-preserving-maps-large-posets
open import order-theory.order-preserving-maps-large-preorders

open import ring-theory.homomorphisms-semirings
open import ring-theory.images-semirings
open import ring-theory.poset-of-nonunital-subsemirings
open import ring-theory.pullbacks-nonunital-subsemirings
open import ring-theory.semirings
open import ring-theory.nonunital-subsemirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The {{#concept "image" Disambiguation="nonunital subsemiring" Agda=im-Nonunital-Subsemiring}}
of a [nonunital subsemiring](ring-theory.nonunital-subsemirings.md) `U ⊆ R` under a [homomorphism](ring-theory.homomorphisms-subsemirings.md) `f : R → S` between [semirings](ring-theory.semirings.md) `R` and `S` is the nonunital subsemiring consisting of the values of `f`. In other words, the underlying [subtype](foundation.subtypes.md) of the nonunital subsemiring `im f U ⊆ S` is the [image](foundation.images.md) of the underlying subtype of `U`.

Since the image of a nonunital subsemiring satisfies the following adjoint relation

```text
  (im f S ⊆ T) ↔ (S ⊆ T ∘ f)
```

it follows that we obtain a
[Galois connection](order-theory.galois-connections.md).

## Definitions

### The universal property of the image subsemiring of a nonunital subsemiring

```agda
module _
  {l1 l2 l3 l4 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (K : Nonunital-Subsemiring l3 R) (L : Nonunital-Subsemiring l4 S)
  where

  is-image-Nonunital-Subsemiring : UUω
  is-image-Nonunital-Subsemiring =
    {l : Level} (U : Nonunital-Subsemiring l S) →
    leq-Nonunital-Subsemiring S L U ↔
    leq-Nonunital-Subsemiring R K (pullback-Nonunital-Subsemiring R S f U)
```

### The image of a nonunital subsemiring under a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (U : Nonunital-Subsemiring l3 R)
  where

  subset-im-Nonunital-Subsemiring : subset-Semiring (l1 ⊔ l2 ⊔ l3) S
  subset-im-Nonunital-Subsemiring =
    im-subtype (map-hom-Semiring R S f) (subset-Nonunital-Subsemiring R U)

  is-in-im-Nonunital-Subsemiring : type-Semiring S → UU (l1 ⊔ l2 ⊔ l3)
  is-in-im-Nonunital-Subsemiring = is-in-subtype subset-im-Nonunital-Subsemiring

  abstract
    contains-zero-im-Nonunital-Subsemiring :
      contains-zero-subset-Semiring S subset-im-Nonunital-Subsemiring
    contains-zero-im-Nonunital-Subsemiring =
      unit-trunc-Prop
        ( zero-Nonunital-Subsemiring R U ,
          preserves-zero-hom-Semiring R S f)

  abstract
    is-closed-under-addition-im-Nonunital-Subsemiring :
      is-closed-under-addition-subset-Semiring S subset-im-Nonunital-Subsemiring
    is-closed-under-addition-im-Nonunital-Subsemiring H K =
      apply-twice-universal-property-trunc-Prop H K
        ( subset-im-Nonunital-Subsemiring _)
        ( λ { (x , refl) (y , refl) →
              unit-trunc-Prop
                ( add-Nonunital-Subsemiring R U x y ,
                  preserves-addition-hom-Semiring R S f)})

  abstract
    is-additive-submonoid-im-Nonunital-Subsemiring :
      is-additive-submonoid-subset-Semiring S subset-im-Nonunital-Subsemiring
    pr1 is-additive-submonoid-im-Nonunital-Subsemiring =
      contains-zero-im-Nonunital-Subsemiring
    pr2 is-additive-submonoid-im-Nonunital-Subsemiring =
      is-closed-under-addition-im-Nonunital-Subsemiring

  abstract
    is-closed-under-multiplication-im-Nonunital-Subsemiring :
      is-closed-under-multiplication-subset-Semiring S subset-im-Nonunital-Subsemiring
    is-closed-under-multiplication-im-Nonunital-Subsemiring {x} {y} u v =
      apply-twice-universal-property-trunc-Prop u v
        ( subset-im-Nonunital-Subsemiring (mul-Semiring S x y))
        ( λ where
          ((x' , k) , refl) ((y' , l) , refl) →
            unit-trunc-Prop
              ( ( mul-Nonunital-Subsemiring R U (x' , k) (y' , l)) ,
                ( preserves-mul-hom-Semiring R S f)))

  im-Nonunital-Subsemiring :
    Nonunital-Subsemiring (l1 ⊔ l2 ⊔ l3) S
  pr1 im-Nonunital-Subsemiring =
    subset-im-Nonunital-Subsemiring
  pr1 (pr2 im-Nonunital-Subsemiring) =
    is-additive-submonoid-im-Nonunital-Subsemiring
  pr2 (pr2 im-Nonunital-Subsemiring) =
    is-closed-under-multiplication-im-Nonunital-Subsemiring

  forward-implication-is-image-im-Nonunital-Subsemiring :
    {l : Level} (V : Nonunital-Subsemiring l S) →
    leq-Nonunital-Subsemiring S im-Nonunital-Subsemiring V →
    leq-Nonunital-Subsemiring R U (pullback-Nonunital-Subsemiring R S f V)
  forward-implication-is-image-im-Nonunital-Subsemiring V =
    forward-implication-adjoint-relation-image-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Nonunital-Subsemiring R U)
      ( subset-Nonunital-Subsemiring S V)

  backward-implication-is-image-im-Nonunital-Subsemiring :
    {l : Level} (V : Nonunital-Subsemiring l S) →
    leq-Nonunital-Subsemiring R U (pullback-Nonunital-Subsemiring R S f V) →
    leq-Nonunital-Subsemiring S im-Nonunital-Subsemiring V
  backward-implication-is-image-im-Nonunital-Subsemiring V =
    backward-implication-adjoint-relation-image-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Nonunital-Subsemiring R U)
      ( subset-Nonunital-Subsemiring S V)

  is-image-im-Nonunital-Subsemiring :
    is-image-Nonunital-Subsemiring R S f U im-Nonunital-Subsemiring
  is-image-im-Nonunital-Subsemiring V =
    adjoint-relation-image-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Nonunital-Subsemiring R U)
      ( subset-Nonunital-Subsemiring S V)
```

### The image-pullback Galois connection on nonunital subsemirings

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-im-Nonunital-Subsemiring :
    {l3 l4 : Level} (K : Nonunital-Subsemiring l3 R) (L : Nonunital-Subsemiring l4 R) →
    leq-Nonunital-Subsemiring R K L →
    leq-Nonunital-Subsemiring S (im-Nonunital-Subsemiring R S f K) (im-Nonunital-Subsemiring R S f L)
  preserves-order-im-Nonunital-Subsemiring K L =
    preserves-order-im-subtype
      ( map-hom-Semiring R S f)
      ( subset-Nonunital-Subsemiring R K)
      ( subset-Nonunital-Subsemiring R L)

  im-large-poset-hom-Semiring :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( Nonunital-Subsemiring-Large-Poset R)
      ( Nonunital-Subsemiring-Large-Poset S)
  map-hom-Large-Preorder im-large-poset-hom-Semiring =
    im-Nonunital-Subsemiring R S f
  preserves-order-hom-Large-Preorder
    im-large-poset-hom-Semiring =
    preserves-order-im-Nonunital-Subsemiring

  image-pullback-galois-connection-Nonunital-Subsemiring :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( Nonunital-Subsemiring-Large-Poset R)
      ( Nonunital-Subsemiring-Large-Poset S)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Nonunital-Subsemiring =
    im-large-poset-hom-Semiring
  upper-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Nonunital-Subsemiring =
    pullback-hom-large-poset-Nonunital-Subsemiring R S f
  adjoint-relation-galois-connection-Large-Poset
    image-pullback-galois-connection-Nonunital-Subsemiring K =
    is-image-im-Nonunital-Subsemiring R S f K
```

## Properties

### Any nonunital subsemiring `V` of `S` has the same elements as `im f U` if and only if `V` satisfies the universal property of the image of `U` under `f`

```agda
module _
  {l1 l2 l3 l4 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (U : Nonunital-Subsemiring l3 R) (V : Nonunital-Subsemiring l4 S)
  where

  is-image-has-same-elements-Nonunital-Subsemiring :
    has-same-elements-Nonunital-Subsemiring S
      ( im-Nonunital-Subsemiring R S f U) V →
    is-image-Nonunital-Subsemiring R S f U V
  is-image-has-same-elements-Nonunital-Subsemiring s =
    is-lower-element-sim-galois-connection-Large-Poset
      ( Nonunital-Subsemiring-Large-Poset R)
      ( Nonunital-Subsemiring-Large-Poset S)
      ( image-pullback-galois-connection-Nonunital-Subsemiring R S f)
      ( U)
      ( V)
      ( sim-has-same-elements-Nonunital-Subsemiring S
        ( im-Nonunital-Subsemiring R S f U)
        ( V)
        ( s))

  has-same-elements-is-image-Nonunital-Subsemiring :
    is-image-Nonunital-Subsemiring R S f U V →
    has-same-elements-Nonunital-Subsemiring S
      ( im-Nonunital-Subsemiring R S f U) V
  has-same-elements-is-image-Nonunital-Subsemiring i =
    has-same-elements-sim-Nonunital-Subsemiring S
      ( im-Nonunital-Subsemiring R S f U)
      ( V)
      ( sim-is-lower-element-galois-connection-Large-Poset
        ( Nonunital-Subsemiring-Large-Poset R)
        ( Nonunital-Subsemiring-Large-Poset S)
        ( image-pullback-galois-connection-Nonunital-Subsemiring R S f)
        ( U)
        ( V)
        ( i))
```

