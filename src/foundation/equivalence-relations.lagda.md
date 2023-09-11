# Equivalence relations

```agda
module foundation.equivalence-relations where

open import foundation-core.equivalence-relations public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-classes
open import foundation.full-subtypes
open import foundation.fundamental-theorem-of-identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sigma-decompositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport-along-identifications
```

</details>

## Properties

### Characterization of equality in the type of equivalence relations

```agda
relate-same-elements-Equivalence-Relation :
  {l1 l2 l3 : Level} {A : UU l1} →
  Equivalence-Relation l2 A → Equivalence-Relation l3 A → UU (l1 ⊔ l2 ⊔ l3)
relate-same-elements-Equivalence-Relation R S =
  relates-same-elements-Relation-Prop
    ( prop-Equivalence-Relation R)
    ( prop-Equivalence-Relation S)

module _
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A)
  where

  refl-relate-same-elements-Equivalence-Relation :
    relate-same-elements-Equivalence-Relation R R
  refl-relate-same-elements-Equivalence-Relation =
    refl-relates-same-elements-Relation-Prop (prop-Equivalence-Relation R)

  is-contr-total-relate-same-elements-Equivalence-Relation :
    is-contr
      ( Σ
        ( Equivalence-Relation l2 A)
        ( relate-same-elements-Equivalence-Relation R))
  is-contr-total-relate-same-elements-Equivalence-Relation =
    is-contr-total-Eq-subtype
      ( is-contr-total-relates-same-elements-Relation-Prop
        ( prop-Equivalence-Relation R))
      ( is-prop-is-equivalence-relation)
      ( prop-Equivalence-Relation R)
      ( refl-relate-same-elements-Equivalence-Relation)
      ( is-equivalence-relation-prop-Equivalence-Relation R)

  relate-same-elements-eq-Equivalence-Relation :
    (S : Equivalence-Relation l2 A) →
    (R ＝ S) → relate-same-elements-Equivalence-Relation R S
  relate-same-elements-eq-Equivalence-Relation .R refl =
    refl-relate-same-elements-Equivalence-Relation

  is-equiv-relate-same-elements-eq-Equivalence-Relation :
    (S : Equivalence-Relation l2 A) →
    is-equiv (relate-same-elements-eq-Equivalence-Relation S)
  is-equiv-relate-same-elements-eq-Equivalence-Relation =
    fundamental-theorem-id
      is-contr-total-relate-same-elements-Equivalence-Relation
      relate-same-elements-eq-Equivalence-Relation

  extensionality-Equivalence-Relation :
    (S : Equivalence-Relation l2 A) →
    (R ＝ S) ≃ relate-same-elements-Equivalence-Relation R S
  pr1 (extensionality-Equivalence-Relation S) =
    relate-same-elements-eq-Equivalence-Relation S
  pr2 (extensionality-Equivalence-Relation S) =
    is-equiv-relate-same-elements-eq-Equivalence-Relation S

  eq-relate-same-elements-Equivalence-Relation :
    (S : Equivalence-Relation l2 A) →
    relate-same-elements-Equivalence-Relation R S → (R ＝ S)
  eq-relate-same-elements-Equivalence-Relation S =
    map-inv-equiv (extensionality-Equivalence-Relation S)
```

### The type of equivalence relations on `A` is equivalent to the type of partitions on `A`

#### The partition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A)
  where

  is-block-partition-Equivalence-Relation-Prop :
    subtype (l1 ⊔ l2) (inhabited-subtype l2 A)
  is-block-partition-Equivalence-Relation-Prop Q =
    is-equivalence-class-Prop R (subtype-inhabited-subtype Q)

  is-block-partition-Equivalence-Relation :
    inhabited-subtype l2 A → UU (l1 ⊔ l2)
  is-block-partition-Equivalence-Relation Q =
    type-Prop (is-block-partition-Equivalence-Relation-Prop Q)

  is-partition-is-equivalence-class-inhabited-subtype-Equivalence-Relation :
    is-partition (is-equivalence-class-inhabited-subtype-Equivalence-Relation R)
  is-partition-is-equivalence-class-inhabited-subtype-Equivalence-Relation x =
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
        ( is-contr-total-is-in-equivalence-class R x)
        ( center-total-is-in-equivalence-class R x)
        ( is-proof-irrelevant-is-prop
          ( is-prop-type-trunc-Prop)
          ( is-inhabited-subtype-equivalence-class R (class R x))))

  partition-Equivalence-Relation : partition l2 (l1 ⊔ l2) A
  pr1 partition-Equivalence-Relation =
    is-block-partition-Equivalence-Relation-Prop
  pr2 partition-Equivalence-Relation =
    is-partition-is-equivalence-class-inhabited-subtype-Equivalence-Relation

  equiv-block-equivalence-class :
    equivalence-class R ≃ block-partition partition-Equivalence-Relation
  equiv-block-equivalence-class =
    ( compute-block-partition partition-Equivalence-Relation) ∘e
    ( ( equiv-right-swap-Σ) ∘e
      ( inv-equiv
        ( equiv-inclusion-is-full-subtype
          ( is-inhabited-subtype-Prop ∘ subtype-equivalence-class R)
          ( is-inhabited-subtype-equivalence-class R))))
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
      ( associative-Σ
        ( block-partition P)
        ( λ U → is-in-block-partition P U x)
        ( λ U → is-in-block-partition P (pr1 U) y))
      ( is-contr-Σ
        ( is-contr-block-containing-element-partition P x)
        ( pair Q p)
        ( is-proof-irrelevant-is-prop
          ( is-prop-is-in-block-partition P Q y)
          ( q)))

  is-prop-sim-partition : (x y : A) → is-prop (sim-partition x y)
  is-prop-sim-partition x y =
    is-prop-is-proof-irrelevant (is-proof-irrelevant-sim-partition x y)

  prop-eq-rel-partition : Relation-Prop (l1 ⊔ l2) A
  pr1 (prop-eq-rel-partition x y) = sim-partition x y
  pr2 (prop-eq-rel-partition x y) = is-prop-sim-partition x y

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

  eq-rel-partition : Equivalence-Relation (l1 ⊔ l2) A
  pr1 eq-rel-partition = prop-eq-rel-partition
  pr1 (pr2 eq-rel-partition) = refl-sim-partition
  pr1 (pr2 (pr2 eq-rel-partition)) = symmetric-sim-partition
  pr2 (pr2 (pr2 eq-rel-partition)) = transitive-sim-partition

  is-inhabited-subtype-prop-eq-rel-partition :
    (a : A) → is-inhabited-subtype (prop-eq-rel-partition a)
  is-inhabited-subtype-prop-eq-rel-partition a =
    unit-trunc-Prop (a , refl-sim-partition a)

  inhabited-subtype-eq-rel-partition :
    (a : A) → inhabited-subtype (l1 ⊔ l2) A
  pr1 (inhabited-subtype-eq-rel-partition a) = prop-eq-rel-partition a
  pr2 (inhabited-subtype-eq-rel-partition a) =
    is-inhabited-subtype-prop-eq-rel-partition a

  is-block-inhabited-subtype-eq-rel-partition :
    (a : A) →
    is-block-partition
      ( partition-Equivalence-Relation eq-rel-partition)
      ( inhabited-subtype-eq-rel-partition a)
  is-block-inhabited-subtype-eq-rel-partition a =
    unit-trunc-Prop (a , λ x → pair id id)
```

#### The equivalence relation obtained from the partition induced by an equivalence relation `R` is `R` itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A)
  where

  relate-same-elements-eq-rel-partition-Equivalence-Relation :
    relate-same-elements-Equivalence-Relation
      ( eq-rel-partition (partition-Equivalence-Relation R))
      ( R)
  pr1
    ( relate-same-elements-eq-rel-partition-Equivalence-Relation x y)
    ( C , p , q) =
    apply-universal-property-trunc-Prop
      ( is-block-inhabited-subtype-block-partition
        ( partition-Equivalence-Relation R)
        ( C))
      ( prop-Equivalence-Relation R x y)
      ( λ (z , K) →
        transitive-Equivalence-Relation R
          x _ y
          ( forward-implication (K y) q)
          ( symmetric-Equivalence-Relation R _ x (forward-implication (K x) p)))
  pr1 (pr2 (relate-same-elements-eq-rel-partition-Equivalence-Relation x y) r) =
    make-block-partition
      ( partition-Equivalence-Relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
  pr1
    ( pr2
      ( pr2
        ( relate-same-elements-eq-rel-partition-Equivalence-Relation x y) r)) =

    make-is-in-block-partition
      ( partition-Equivalence-Relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( x)
      ( refl-Equivalence-Relation R x)
  pr2
    ( pr2
      ( pr2
        ( relate-same-elements-eq-rel-partition-Equivalence-Relation x y) r)) =

    make-is-in-block-partition
      ( partition-Equivalence-Relation R)
      ( inhabited-subtype-equivalence-class R (class R x))
      ( is-equivalence-class-equivalence-class R (class R x))
      ( y)
      ( r)

is-section-eq-rel-partition-Equivalence-Relation :
  {l : Level} {A : UU l} (R : Equivalence-Relation l A) →
  eq-rel-partition (partition-Equivalence-Relation R) ＝ R
is-section-eq-rel-partition-Equivalence-Relation R =
  eq-relate-same-elements-Equivalence-Relation
    ( eq-rel-partition (partition-Equivalence-Relation R))
    ( R)
    ( relate-same-elements-eq-rel-partition-Equivalence-Relation R)
```

#### The partition obtained from the equivalence relation induced by a partition is the partition itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : partition l1 l2 A)
  where

  is-block-is-equivalence-class-eq-rel-partition :
    (Q : inhabited-subtype l1 A) →
    is-equivalence-class (eq-rel-partition P) (subtype-inhabited-subtype Q) →
    is-block-partition P Q
  is-block-is-equivalence-class-eq-rel-partition Q H =
    apply-universal-property-trunc-Prop H
      ( subtype-partition P Q)
      ( λ (a , K) →
        tr
          ( is-block-partition P)
          ( inv
            ( eq-has-same-elements-inhabited-subtype Q
              ( inhabited-subtype-block-partition P (class-partition P a))
              ( λ x →
                logical-equivalence-reasoning
                  is-in-inhabited-subtype Q x
                    ↔ Σ ( block-partition P)
                        ( λ B →
                          is-in-block-partition P B a ×
                          is-in-block-partition P B x)
                      by K x
                    ↔ is-in-block-partition P (class-partition P a) x
                      by
                      iff-equiv
                        ( ( left-unit-law-Σ-is-contr
                            ( is-contr-block-containing-element-partition P a)
                            ( center-block-containing-element-partition P a)) ∘e
                          ( inv-associative-Σ
                            ( block-partition P)
                            ( λ B → is-in-block-partition P B a)
                            ( λ B → is-in-block-partition P (pr1 B) x))))))
          ( is-block-class-partition P a))

  is-equivalence-class-is-block-partition :
    (Q : inhabited-subtype l1 A) →
    is-block-partition P Q →
    is-equivalence-class (eq-rel-partition P) (subtype-inhabited-subtype Q)
  is-equivalence-class-is-block-partition Q H =
    apply-universal-property-trunc-Prop
      ( is-inhabited-subtype-inhabited-subtype Q)
      ( is-equivalence-class-Prop
        ( eq-rel-partition P)
        ( subtype-inhabited-subtype Q))
      ( λ (a , q) →
        unit-trunc-Prop
          ( pair
            ( a)
            ( λ x →
              iff-equiv
              ( equivalence-reasoning
                is-in-inhabited-subtype Q x
                  ≃ is-in-block-partition P (make-block-partition P Q H) x
                    by
                    compute-is-in-block-partition P Q H x
                  ≃ Σ ( block-partition P)
                      ( λ B →
                        is-in-block-partition P B a ×
                        is-in-block-partition P B x)
                    by
                    inv-equiv
                      ( ( left-unit-law-Σ-is-contr
                          ( is-contr-block-containing-element-partition P a)
                          ( pair
                            ( make-block-partition P Q H)
                            ( make-is-in-block-partition P Q H a q))) ∘e
                        ( inv-associative-Σ
                          ( block-partition P)
                          ( λ B → is-in-block-partition P B a)
                          ( λ B → is-in-block-partition P (pr1 B) x)))))))

  has-same-elements-partition-eq-rel-partition :
    has-same-elements-subtype
      ( subtype-partition (partition-Equivalence-Relation (eq-rel-partition P)))
      ( subtype-partition P)
  pr1 (has-same-elements-partition-eq-rel-partition Q) H =
    is-block-is-equivalence-class-eq-rel-partition Q H
  pr2 (has-same-elements-partition-eq-rel-partition Q) H =
    is-equivalence-class-is-block-partition Q H

is-retraction-eq-rel-partition-Equivalence-Relation :
  {l : Level} {A : UU l} (P : partition l l A) →
  partition-Equivalence-Relation (eq-rel-partition P) ＝ P
is-retraction-eq-rel-partition-Equivalence-Relation P =
  eq-has-same-blocks-partition
    ( partition-Equivalence-Relation (eq-rel-partition P))
    ( P)
    ( has-same-elements-partition-eq-rel-partition P)
```

#### The map `eq-rel-partition` is an equivalence

```agda
is-equiv-eq-rel-partition :
  {l : Level} {A : UU l} → is-equiv (eq-rel-partition {l} {l} {l} {A})
is-equiv-eq-rel-partition =
  is-equiv-is-invertible
    partition-Equivalence-Relation
    is-section-eq-rel-partition-Equivalence-Relation
    is-retraction-eq-rel-partition-Equivalence-Relation

equiv-eq-rel-partition :
  {l : Level} {A : UU l} → partition l l A ≃ Equivalence-Relation l A
pr1 equiv-eq-rel-partition = eq-rel-partition
pr2 equiv-eq-rel-partition = is-equiv-eq-rel-partition
```

### Equivalence relations are equivalent to set-indexed Σ-decompositions

#### The Σ-decomposition obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A)
  where

  set-indexed-Σ-decomposition-Equivalence-Relation :
    Set-Indexed-Σ-Decomposition (l1 ⊔ l2) (l1 ⊔ l2) A
  set-indexed-Σ-decomposition-Equivalence-Relation =
    set-indexed-Σ-decomposition-partition (partition-Equivalence-Relation R)
```

### The type of equivalence relations on `A` is equivalent to the type of sets `X` equipped with a surjective map from `A` into `X`

#### The surjection into a set obtained from an equivalence relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A)
  where

  surjection-into-set-Equivalence-Relation :
    Surjection-Into-Set (l1 ⊔ l2) A
  pr1 surjection-into-set-Equivalence-Relation = quotient-Set R
  pr2 surjection-into-set-Equivalence-Relation = surjection-quotient-map R
```

#### The equivalence relation obtained from a surjection into a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (X : Set l2) (f : A → type-Set X)
  where

  rel-map-into-set : Relation-Prop l2 A
  rel-map-into-set x y = Id-Prop X (f x) (f y)

  sim-map-into-set : Relation l2 A
  sim-map-into-set x y = type-Prop (rel-map-into-set x y)

  refl-sim-map-into-set : is-reflexive sim-map-into-set
  refl-sim-map-into-set x = refl

  symmetric-sim-map-into-set : is-symmetric sim-map-into-set
  symmetric-sim-map-into-set x y H = inv H

  transitive-sim-map-into-set : is-transitive sim-map-into-set
  transitive-sim-map-into-set x y z H K = K ∙ H

  eq-rel-map-into-set : Equivalence-Relation l2 A
  pr1 eq-rel-map-into-set = rel-map-into-set
  pr1 (pr2 eq-rel-map-into-set) x = refl-sim-map-into-set x
  pr1 (pr2 (pr2 eq-rel-map-into-set)) x y = symmetric-sim-map-into-set x y
  pr2 (pr2 (pr2 eq-rel-map-into-set)) x y z = transitive-sim-map-into-set x y z

  is-effective-map-into-set :
    is-effective eq-rel-map-into-set f
  is-effective-map-into-set x y = id-equiv

eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} →
  Surjection-Into-Set l2 A → Equivalence-Relation l2 A
eq-rel-Surjection-Into-Set f =
  eq-rel-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)

is-effective-map-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  is-effective (eq-rel-Surjection-Into-Set f) (map-Surjection-Into-Set f)
is-effective-map-Surjection-Into-Set f =
  is-effective-map-into-set
    ( set-Surjection-Into-Set f)
    ( map-Surjection-Into-Set f)
```

#### The equivalence relation obtained from the quotient map induced by an equivalence relation is that same equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation l2 A)
  where

  relate-same-elements-eq-rel-surjection-into-set-Equivalence-Relation :
    relate-same-elements-Equivalence-Relation
      ( eq-rel-Surjection-Into-Set (surjection-into-set-Equivalence-Relation R))
      ( R)
  relate-same-elements-eq-rel-surjection-into-set-Equivalence-Relation x y =
    iff-equiv (is-effective-quotient-map R x y)

is-retraction-eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (R : Equivalence-Relation (l1 ⊔ l2) A) →
  eq-rel-Surjection-Into-Set (surjection-into-set-Equivalence-Relation R) ＝ R
is-retraction-eq-rel-Surjection-Into-Set R =
  eq-relate-same-elements-Equivalence-Relation
    ( eq-rel-Surjection-Into-Set (surjection-into-set-Equivalence-Relation R))
    ( R)
    ( relate-same-elements-eq-rel-surjection-into-set-Equivalence-Relation R)
```

#### The surjection into a set obtained from the equivalence relation induced by a surjection into a set is the original surjection into a set

```agda
equiv-surjection-into-set-eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set l2 A) →
  equiv-Surjection-Into-Set
    ( surjection-into-set-Equivalence-Relation (eq-rel-Surjection-Into-Set f))
    ( f)
equiv-surjection-into-set-eq-rel-Surjection-Into-Set f =
  center
    ( uniqueness-set-quotient
      ( eq-rel-Surjection-Into-Set f)
      ( quotient-Set (eq-rel-Surjection-Into-Set f))
      ( reflecting-map-quotient-map (eq-rel-Surjection-Into-Set f))
      ( is-set-quotient-set-quotient (eq-rel-Surjection-Into-Set f))
      ( set-Surjection-Into-Set f)
      ( pair
        ( map-Surjection-Into-Set f)
        ( λ H → H))
      ( is-set-quotient-is-surjective-and-effective
        ( eq-rel-Surjection-Into-Set f)
        ( set-Surjection-Into-Set f)
        ( pr1 (pr2 f) , (λ {x} {y} z → z))
        ( pair
          ( is-surjective-Surjection-Into-Set f)
          ( is-effective-map-Surjection-Into-Set f))))

is-section-eq-rel-Surjection-Into-Set :
  {l1 l2 : Level} {A : UU l1} (f : Surjection-Into-Set (l1 ⊔ l2) A) →
  surjection-into-set-Equivalence-Relation (eq-rel-Surjection-Into-Set f) ＝ f
is-section-eq-rel-Surjection-Into-Set f =
  eq-equiv-Surjection-Into-Set
    ( surjection-into-set-Equivalence-Relation (eq-rel-Surjection-Into-Set f))
    ( f)
    ( equiv-surjection-into-set-eq-rel-Surjection-Into-Set f)
```

#### The type of equivalence relations on `A` is equivalent to the type of surjections from `A` into a set

```agda
is-equiv-surjection-into-set-Equivalence-Relation :
  {l1 : Level} {A : UU l1} →
  is-equiv (surjection-into-set-Equivalence-Relation {l1} {l1} {A})
is-equiv-surjection-into-set-Equivalence-Relation {l1} {A} =
  is-equiv-is-invertible
    ( eq-rel-Surjection-Into-Set {l1} {l1} {A})
    ( is-section-eq-rel-Surjection-Into-Set {l1} {l1} {A})
    ( is-retraction-eq-rel-Surjection-Into-Set {l1} {l1} {A})

equiv-surjection-into-set-Equivalence-Relation :
  {l1 : Level} (A : UU l1) →
  Equivalence-Relation l1 A ≃ Surjection-Into-Set l1 A
pr1 (equiv-surjection-into-set-Equivalence-Relation A) =
  surjection-into-set-Equivalence-Relation
pr2 (equiv-surjection-into-set-Equivalence-Relation A) =
  is-equiv-surjection-into-set-Equivalence-Relation
```

### Equality on a set is an equivalence relation

```agda
module _
  {l1 : Level} (A : Set l1)
  where

  Id-Equivalence-Relation : Equivalence-Relation l1 (type-Set A)
  pr1 Id-Equivalence-Relation = Id-Prop A
  pr1 (pr2 Id-Equivalence-Relation) _ = refl
  pr1 (pr2 (pr2 Id-Equivalence-Relation)) _ _ = inv
  pr2 (pr2 (pr2 Id-Equivalence-Relation)) _ _ _ H K = K ∙ H

  id-reflects-Id-Equivalence-Relation :
    reflects-Equivalence-Relation Id-Equivalence-Relation id
  id-reflects-Id-Equivalence-Relation = id

  id-reflecting-map-Id-Equivalence-Relation :
    reflecting-map-Equivalence-Relation Id-Equivalence-Relation (type-Set A)
  pr1 id-reflecting-map-Id-Equivalence-Relation = id
  pr2 id-reflecting-map-Id-Equivalence-Relation =
    id-reflects-Id-Equivalence-Relation

  is-surjective-and-effective-id-Id-Equivalence-Relation :
    is-surjective-and-effective Id-Equivalence-Relation id
  pr1 is-surjective-and-effective-id-Id-Equivalence-Relation a =
    unit-trunc-Prop (a , refl)
  pr2 is-surjective-and-effective-id-Id-Equivalence-Relation a b = id-equiv
```

### For any set `A`, `Id` is a set quotient for the equality relation

```agda
module _
  {l : Level} (A : Set l)
  where

  is-set-quotient-id-Id-Equivalence-Relation :
    {l' : Level} →
    is-set-quotient
      ( l')
      ( Id-Equivalence-Relation A)
      ( A)
      ( id-reflecting-map-Id-Equivalence-Relation A)
  is-set-quotient-id-Id-Equivalence-Relation =
    is-set-quotient-is-surjective-and-effective (Id-Equivalence-Relation A) A
      ( id-reflecting-map-Id-Equivalence-Relation A)
      ( is-surjective-and-effective-id-Id-Equivalence-Relation A)
```
