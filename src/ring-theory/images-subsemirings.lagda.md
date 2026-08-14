# Images of subsemirings

```agda
module ring-theory.images-subsemirings where
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
open import ring-theory.poset-of-subsemirings
open import ring-theory.pullbacks-subsemirings
open import ring-theory.semirings
open import ring-theory.subsemirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

The {{#concept "image" Disambiguation="subsemiring" Agda=im-Subsemiring}}
of a [subsemiring](ring-theory.subsemirings.md) `U ⊆ R` under a [homomorphism](ring-theory.homomorphisms-subsemirings.md) `f : R → S` between [semirings](ring-theory.semirings.md) `R` and `S` is the subsemiring consisting of the values of `f`. In other words, the underlying [subtype](foundation.subtypes.md) of the subsemiring `im f U ⊆ S` is the [image](foundation.images.md) of the underlying subtype of `U`.

Since the image of a subsemiring satisfies the following adjoint relation

```text
  (im f S ⊆ V) ↔ (S ⊆ V ∘ f)
```

it follows that we obtain a
[Galois connection](order-theory.galois-connections.md).

## Definitions

### The universal property of the image subsemiring of a subsemiring

```agda
module _
  {l1 l2 l3 l4 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (K : Subsemiring l3 R) (L : Subsemiring l4 S)
  where

  is-image-Subsemiring : UUω
  is-image-Subsemiring =
    {l : Level} (U : Subsemiring l S) →
    leq-Subsemiring S L U ↔ leq-Subsemiring R K (pullback-Subsemiring R S f U)
```

### The image of a subsemiring under a semiring homomorphism

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  (U : Subsemiring l3 R)
  where

  subset-im-Subsemiring : subset-Semiring (l1 ⊔ l2 ⊔ l3) S
  subset-im-Subsemiring =
    im-subtype (map-hom-Semiring R S f) (subset-Subsemiring R U)

  is-in-im-Subsemiring : type-Semiring S → UU (l1 ⊔ l2 ⊔ l3)
  is-in-im-Subsemiring = is-in-subtype subset-im-Subsemiring

  abstract
    contains-zero-im-Subsemiring :
      contains-zero-subset-Semiring S subset-im-Subsemiring
    contains-zero-im-Subsemiring =
      unit-trunc-Prop (zero-Subsemiring R U , preserves-zero-hom-Semiring R S f)

  abstract
    is-closed-under-addition-im-Subsemiring :
      is-closed-under-addition-subset-Semiring S subset-im-Subsemiring
    is-closed-under-addition-im-Subsemiring H K =
      apply-twice-universal-property-trunc-Prop H K
        ( subset-im-Subsemiring _)
        ( λ { (x , refl) (y , refl) →
              unit-trunc-Prop
                ( add-Subsemiring R U x y ,
                  preserves-addition-hom-Semiring R S f)})

  abstract
    is-additive-submonoid-im-Subsemiring :
      is-additive-submonoid-subset-Semiring S subset-im-Subsemiring
    pr1 is-additive-submonoid-im-Subsemiring =
      contains-zero-im-Subsemiring
    pr2 is-additive-submonoid-im-Subsemiring =
      is-closed-under-addition-im-Subsemiring

  abstract
    contains-one-im-Subsemiring :
      contains-one-subset-Semiring S subset-im-Subsemiring
    contains-one-im-Subsemiring =
      unit-trunc-Prop (one-Subsemiring R U , preserves-one-hom-Semiring R S f)

  abstract
    is-closed-under-multiplication-im-Subsemiring :
      is-closed-under-multiplication-subset-Semiring S subset-im-Subsemiring
    is-closed-under-multiplication-im-Subsemiring {x} {y} u v =
      apply-twice-universal-property-trunc-Prop u v
        ( subset-im-Subsemiring (mul-Semiring S x y))
        ( λ where
          ((x' , k) , refl) ((y' , l) , refl) →
            unit-trunc-Prop
              ( ( mul-Subsemiring R U (x' , k) (y' , l)) ,
                ( preserves-mul-hom-Semiring R S f)))

  im-Subsemiring :
    Subsemiring (l1 ⊔ l2 ⊔ l3) S
  pr1 im-Subsemiring =
    subset-im-Subsemiring
  pr1 (pr2 im-Subsemiring) =
    is-additive-submonoid-im-Subsemiring
  pr1 (pr2 (pr2 im-Subsemiring)) =
    contains-one-im-Subsemiring
  pr2 (pr2 (pr2 im-Subsemiring)) =
    is-closed-under-multiplication-im-Subsemiring

  forward-implication-is-image-im-Subsemiring :
    {l : Level} (V : Subsemiring l S) →
    leq-Subsemiring S im-Subsemiring V →
    leq-Subsemiring R U (pullback-Subsemiring R S f V)
  forward-implication-is-image-im-Subsemiring V =
    forward-implication-adjoint-relation-image-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Subsemiring R U)
      ( subset-Subsemiring S V)

  backward-implication-is-image-im-Subsemiring :
    {l : Level} (V : Subsemiring l S) →
    leq-Subsemiring R U (pullback-Subsemiring R S f V) →
    leq-Subsemiring S im-Subsemiring V
  backward-implication-is-image-im-Subsemiring V =
    backward-implication-adjoint-relation-image-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Subsemiring R U)
      ( subset-Subsemiring S V)

  is-image-im-Subsemiring :
    is-image-Subsemiring R S f U im-Subsemiring
  is-image-im-Subsemiring V =
    adjoint-relation-image-pullback-subtype
      ( map-hom-Semiring R S f)
      ( subset-Subsemiring R U)
      ( subset-Subsemiring S V)
```

### The image-pullback Galois connection on subsemirings

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : Semiring l2) (f : hom-Semiring R S)
  where

  preserves-order-im-Subsemiring :
    {l3 l4 : Level} (U : Subsemiring l3 R) (V : Subsemiring l4 R) →
    leq-Subsemiring R U V →
    leq-Subsemiring S (im-Subsemiring R S f U) (im-Subsemiring R S f V)
  preserves-order-im-Subsemiring U V =
    preserves-order-im-subtype
      ( map-hom-Semiring R S f)
      ( subset-Subsemiring R U)
      ( subset-Subsemiring R V)

  im-large-poset-hom-Semiring :
    hom-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( Subsemiring-Large-Poset R)
      ( Subsemiring-Large-Poset S)
  map-hom-Large-Preorder im-large-poset-hom-Semiring =
    im-Subsemiring R S f
  preserves-order-hom-Large-Preorder
    im-large-poset-hom-Semiring =
    preserves-order-im-Subsemiring

  image-pullback-galois-connection-Subsemiring :
    galois-connection-Large-Poset
      ( λ l → l1 ⊔ l2 ⊔ l)
      ( λ l → l)
      ( Subsemiring-Large-Poset R)
      ( Subsemiring-Large-Poset S)
  lower-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemiring =
    im-large-poset-hom-Semiring
  upper-adjoint-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemiring =
    pullback-hom-large-poset-Subsemiring R S f
  adjoint-relation-galois-connection-Large-Poset
    image-pullback-galois-connection-Subsemiring U =
    is-image-im-Subsemiring R S f U
```

## Properties

### Any subsemiring `V` of `S` has the same elements as `im f U` if and only if `V` satisfies the universal property of the image of `U` under `f`

```agda
module _
  {l1 l2 l3 l4 : Level} (R : Semiring l1) (S : Semiring l2)
  (f : hom-Semiring R S) (U : Subsemiring l3 R) (V : Subsemiring l4 S)
  where

  is-image-has-same-elements-Subsemiring :
    has-same-elements-Subsemiring S (im-Subsemiring R S f U) V →
    is-image-Subsemiring R S f U V
  is-image-has-same-elements-Subsemiring s =
    is-lower-element-sim-galois-connection-Large-Poset
      ( Subsemiring-Large-Poset R)
      ( Subsemiring-Large-Poset S)
      ( image-pullback-galois-connection-Subsemiring R S f)
      ( U)
      ( V)
      ( sim-has-same-elements-Subsemiring S (im-Subsemiring R S f U) V s)

  has-same-elements-is-image-Subsemiring :
    is-image-Subsemiring R S f U V →
    has-same-elements-Subsemiring S (im-Subsemiring R S f U) V
  has-same-elements-is-image-Subsemiring i =
    has-same-elements-sim-Subsemiring S
      ( im-Subsemiring R S f U)
      ( V)
      ( sim-is-lower-element-galois-connection-Large-Poset
        ( Subsemiring-Large-Poset R)
        ( Subsemiring-Large-Poset S)
        ( image-pullback-galois-connection-Subsemiring R S f)
        ( U)
        ( V)
        ( i))
```

