# Fundamental theorem of equivalence relations

```agda
module foundation.fundamental-theorem-of-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.full-subtypes
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
```

</details>

## Idea

{{#concept "The fundamental theorem of equivalence relations" Agda=equiv-equivalence-relation-partition}}
states that, given a type `A`, the type of
[equivalence relations](foundation.equivalence-relations.md) on `A` is
equivalent to the type of [partitions](foundation.partitions.md) on `A`.

## Theorem

### The type of equivalence relations on `A` is equivalent to the type of partitions on `A`

#### The partition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-block-prop-partition-equivalence-relation :
    subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-block-prop-partition-equivalence-relation Q =
    is-equivalence-class-Prop R (subtype-inhabited-subtype Q)

  is-block-partition-equivalence-relation :
    inhabited-subtype l2 A → UU (l1 ⊔ l2)
  is-block-partition-equivalence-relation Q =
    type-Prop (is-block-prop-partition-equivalence-relation Q)

  abstract
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation :
      is-partition
        ( is-equivalence-class-inhabited-subtype-equivalence-relation R)
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation x =
      is-contr-equiv
        ( Σ ( Σ ( equivalence-class R)
                ( λ C → is-in-equivalence-class R C x))
            ( λ t → is-inhabited-subtype (subtype-equivalence-class R (pr1 t))))
        ( ( equiv-right-swap-Σ) ∘e
          ( equiv-Σ
            ( λ Q → is-in-subtype (subtype-equivalence-class R (pr1 Q)) x)
            ( equiv-right-swap-Σ)
            ( λ Q → id-equiv)))
        ( is-contr-Σ
          ( is-torsorial-is-in-equivalence-class R x)
          ( center-total-is-in-equivalence-class R x)
          ( is-proof-irrelevant-is-prop
            ( is-prop-type-trunc-Prop)
            ( is-inhabited-subtype-equivalence-class R (class R x))))

  partition-equivalence-relation : partition l2 (l1 ⊔ l2) A
  pr1 partition-equivalence-relation =
    is-block-prop-partition-equivalence-relation
  pr2 partition-equivalence-relation =
    is-partition-is-equivalence-class-inhabited-subtype-equivalence-relation

  equiv-block-equivalence-class :
    equivalence-class R ≃ block-partition partition-equivalence-relation
  equiv-block-equivalence-class =
    ( compute-block-partition partition-equivalence-relation) ∘e
    ( ( equiv-right-swap-Σ) ∘e
      ( inv-equiv-inclusion-is-full-subtype
        ( is-inhabited-subtype-Prop ∘ subtype-equivalence-class R)
        ( is-inhabited-subtype-equivalence-class R)))
```

#### The equivalence relation obtained from a partition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : partition l2 l3 A)
  where

  sim-partition : A → A → UU (l1 ⊔ l2)
  sim-partition x y =
    Σ ( block-partition P)
      ( λ Q → is-in-block-partition P Q x × is-in-block-partition P Q y)

  is-proof-irrelevant-sim-partition :
    (x y : A) → is-proof-irrelevant (sim-partition x y)
  is-proof-irrelevant-sim-partition x y (Q , p , q) =
    is-contr-equiv'
      ( Σ ( Σ ( block-partition P)
              ( λ B → is-in-block-partition P B x))
          ( λ B → is-in-block-partition P (pr1 B) y))
      ( associative-Σ)
      ( is-contr-Σ
        ( is-contr-block-containing-element-partition P x)
        ( Q , p)
        ( is-proof-irrelevant-is-prop
          ( is-prop-is-in-block-partition P Q y)
          ( q)))

  is-prop-sim-partition : (x y : A) → is-prop (sim-partition x y)
  is-prop-sim-partition x y =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-sim-partition x y)

  prop-equivalence-relation-partition : Relation-Prop (l1 ⊔ l2) A
  pr1 (prop-equivalence-relation-partition x y) = sim-partition x y
  pr2 (prop-equivalence-relation-partition x y) = is-prop-sim-partition x y

  refl-sim-partition : is-reflexive sim-partition
  pr1 (refl-sim-partition x) = class-partition P x
  pr1 (pr2 (refl-sim-partition x)) = is-in-block-class-partition P x
  pr2 (pr2 (refl-sim-partition x)) = is-in-block-class-partition P x

  symmetric-sim-partition : is-symmetric sim-partition
  pr1 (symmetric-sim-partition x y (Q , p , q)) = Q
  pr1 (pr2 (symmetric-sim-partition x y (Q , p , q))) = q
  pr2 (pr2 (symmetric-sim-partition x y (Q , p , q))) = p

  transitive-sim-partition : is-transitive sim-partition
  pr1 (transitive-sim-partition x y z (B , p , q) (B' , p' , q')) = B
  pr1 (pr2 (transitive-sim-partition x y z (B , p , q) (B' , p' , q'))) =
    backward-implication
      ( has-same-elements-eq-inhabited-subtype
        ( inhabited-subtype-block-partition P B)
        ( inhabited-subtype-block-partition P B')
        ( ap
          ( inhabited-subtype-block-partition P)
          ( ap
            ( pr1)
            ( eq-is-contr
              ( is-contr-block-containing-element-partition P y)
              { B , p}
              { B' , q'})))
        ( x))
      ( p')
  pr2 (pr2 (transitive-sim-partition x y z (B , p , q) (B' , p' , q'))) = q

  equivalence-relation-partition : equivalence-relation (l1 ⊔ l2) A
  pr1 equivalence-relation-partition = prop-equivalence-relation-partition
  pr1 (pr2 equivalence-relation-partition) = refl-sim-partition
  pr1 (pr2 (pr2 equivalence-relation-partition)) = symmetric-sim-partition
  pr2 (pr2 (pr2 equivalence-relation-partition)) = transitive-sim-partition

  is-inhabited-subtype-prop-equivalence-relation-partition :
    (a : A) → is-inhabited-subtype (prop-equivalence-relation-partition a)
  is-inhabited-subtype-prop-equivalence-relation-partition a =
    unit-trunc-Prop (a , refl-sim-partition a)

  inhabited-subtype-equivalence-relation-partition :
    (a : A) → inhabited-subtype (l1 ⊔ l2) A
  pr1 (inhabited-subtype-equivalence-relation-partition a) =
    prop-equivalence-relation-partition a
  pr2 (inhabited-subtype-equivalence-relation-partition a) =
    is-inhabited-subtype-prop-equivalence-relation-partition a

  is-block-inhabited-subtype-equivalence-relation-partition :
    (a : A) →
    is-block-partition
      ( partition-equivalence-relation equivalence-relation-partition)
      ( inhabited-subtype-equivalence-relation-partition a)
  is-block-inhabited-subtype-equivalence-relation-partition a =
    unit-trunc-Prop (a , (λ x → (id , id)))
```

#### The equivalence relation obtained from the partition induced by an equivalence relation `R` is `R` itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  relate-same-elements-equivalence-relation-partition-equivalence-relation :
    relate-same-elements-equivalence-relation
      ( equivalence-relation-partition (partition-equivalence-relation R))
      ( R)
  pr1
    ( relate-same-elements-equivalence-relation-partition-equivalence-relation
      x y)
    ( C , p , q) =
    apply-universal-property-trunc-Prop
      ( is-block-inhabited-subtype-block-partition
        ( partition-equivalence-relation R)
        ( C))
      ( prop-equivalence-relation R x y)
      ( λ (z , K) →
        transitive-equivalence-relation R
          x _ y
          ( forward-implication (K y) q)
          ( symmetric-equivalence-relation R _ x (forward-implication (K x) p)))
  pr1
    ( pr2
      ( relate-same-elements-equivalence-relation-partition-equivalence-relation
        x y)
      ( r)) =
    make-block-partition
      ( partition-equivalence-relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
  pr1
    ( pr2
      ( pr2
        ( relate-same-elements-equivalence-relation-partition-equivalence-relation
          x y)
        ( r))) =
    make-is-in-block-partition
      ( partition-equivalence-relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( x)
      ( refl-equivalence-relation R x)
  pr2
    ( pr2
      ( pr2
        ( relate-same-elements-equivalence-relation-partition-equivalence-relation
          x y)
        ( r))) =
    make-is-in-block-partition
      ( partition-equivalence-relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( y)
      ( r)

is-section-equivalence-relation-partition-equivalence-relation :
  {l : Level} {A : UU l} (R : equivalence-relation l A) →
  equivalence-relation-partition (partition-equivalence-relation R) ＝ R
is-section-equivalence-relation-partition-equivalence-relation R =
  eq-relate-same-elements-equivalence-relation
    ( equivalence-relation-partition (partition-equivalence-relation R))
    ( R)
    ( relate-same-elements-equivalence-relation-partition-equivalence-relation
      R)
```

#### The partition obtained from the equivalence relation induced by a partition is the partition itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : partition l1 l2 A)
  where

  abstract
    is-block-is-equivalence-class-equivalence-relation-partition :
      (Q : inhabited-subtype l1 A) →
      is-equivalence-class
        ( equivalence-relation-partition P)
        ( subtype-inhabited-subtype Q) →
      is-block-partition P Q
    is-block-is-equivalence-class-equivalence-relation-partition Q H =
      apply-universal-property-trunc-Prop H
        ( subtype-partition P Q)
        ( λ (a , K) →
          tr
            ( is-block-partition P)
            ( inv
              ( eq-has-same-elements-inhabited-subtype Q
                ( inhabited-subtype-block-partition P (class-partition P a))
                ( λ x →
                  ( iff-equiv
                    ( ( left-unit-law-Σ-is-contr
                        ( is-contr-block-containing-element-partition P a)
                        ( center-block-containing-element-partition P a)) ∘e
                      ( inv-associative-Σ))) ∘iff
                  ( K x))))
            ( is-block-class-partition P a))

  abstract
    is-equivalence-class-is-block-partition :
      (Q : inhabited-subtype l1 A) →
      is-block-partition P Q →
      is-equivalence-class
        ( equivalence-relation-partition P)
        ( subtype-inhabited-subtype Q)
    is-equivalence-class-is-block-partition Q H =
      apply-universal-property-trunc-Prop
        ( is-inhabited-subtype-inhabited-subtype Q)
        ( is-equivalence-class-Prop
          ( equivalence-relation-partition P)
          ( subtype-inhabited-subtype Q))
        ( λ (a , q) →
          unit-trunc-Prop
            ( pair
              ( a)
              ( λ x →
                iff-equiv
                ( ( inv-equiv
                    ( ( left-unit-law-Σ-is-contr
                        ( is-contr-block-containing-element-partition P a)
                        ( ( make-block-partition P Q H) ,
                          ( make-is-in-block-partition P Q H a q))) ∘e
                      ( inv-associative-Σ))) ∘e
                  ( compute-is-in-block-partition P Q H x)))))

  has-same-elements-partition-equivalence-relation-partition :
    has-same-elements-subtype
      ( subtype-partition
        ( partition-equivalence-relation (equivalence-relation-partition P)))
      ( subtype-partition P)
  pr1 (has-same-elements-partition-equivalence-relation-partition Q) H =
    is-block-is-equivalence-class-equivalence-relation-partition Q H
  pr2 (has-same-elements-partition-equivalence-relation-partition Q) H =
    is-equivalence-class-is-block-partition Q H

is-retraction-equivalence-relation-partition-equivalence-relation :
  {l : Level} {A : UU l} (P : partition l l A) →
  partition-equivalence-relation (equivalence-relation-partition P) ＝ P
is-retraction-equivalence-relation-partition-equivalence-relation P =
  eq-has-same-blocks-partition
    ( partition-equivalence-relation (equivalence-relation-partition P))
    ( P)
    ( has-same-elements-partition-equivalence-relation-partition P)
```

#### The map `equivalence-relation-partition` is an equivalence

```agda
abstract
  is-equiv-equivalence-relation-partition :
    {l : Level} {A : UU l} →
    is-equiv (equivalence-relation-partition {l} {l} {l} {A})
  is-equiv-equivalence-relation-partition =
    is-equiv-is-invertible
      partition-equivalence-relation
      is-section-equivalence-relation-partition-equivalence-relation
      is-retraction-equivalence-relation-partition-equivalence-relation

equiv-equivalence-relation-partition :
  {l : Level} {A : UU l} → partition l l A ≃ equivalence-relation l A
equiv-equivalence-relation-partition =
  ( equivalence-relation-partition , is-equiv-equivalence-relation-partition)
```

## External links

- [Fundamental theorem of equivalence relations](https://en.wikipedia.org/wiki/Fundamental_theorem_of_equivalence_relations)
  on Wikipedia
