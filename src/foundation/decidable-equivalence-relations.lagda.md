# Decidable equivalence relations

```agda
module foundation.decidable-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-relations
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.equivalence-classes
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.functoriality-cartesian-product-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.images
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.slice
open import foundation.surjective-maps
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universal-property-image
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A decidable equivalence relation on a type `X` is an equivalence relation `R` on
`X` such that `R x y` is a decidable proposition for each `x y : X`.

## Definitions

### Decidable equivalence relations

```agda
is-decidable-equivalence-relation :
  {l1 l2 : Level} → {A : UU l1} → equivalence-relation l2 A → UU (l1 ⊔ l2)
is-decidable-equivalence-relation {A = A} R =
  (x y : A) → is-decidable ( sim-equivalence-relation R x y)

Decidable-equivalence-relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-equivalence-relation l2 X =
  Σ ( Decidable-Relation l2 X)
    ( λ R → is-equivalence-relation (relation-Decidable-Relation R))

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-equivalence-relation l2 X)
  where

  decidable-relation-Decidable-equivalence-relation :
    Decidable-Relation l2 X
  decidable-relation-Decidable-equivalence-relation = pr1 R

  relation-Decidable-equivalence-relation : X → X → Prop l2
  relation-Decidable-equivalence-relation =
    relation-Decidable-Relation
      decidable-relation-Decidable-equivalence-relation

  sim-Decidable-equivalence-relation : X → X → UU l2
  sim-Decidable-equivalence-relation =
    rel-Decidable-Relation decidable-relation-Decidable-equivalence-relation

  is-prop-sim-Decidable-equivalence-relation :
    (x y : X) → is-prop (sim-Decidable-equivalence-relation x y)
  is-prop-sim-Decidable-equivalence-relation =
    is-prop-rel-Decidable-Relation
      decidable-relation-Decidable-equivalence-relation

  is-decidable-sim-Decidable-equivalence-relation :
    (x y : X) → is-decidable (sim-Decidable-equivalence-relation x y)
  is-decidable-sim-Decidable-equivalence-relation =
    is-decidable-Decidable-Relation
      decidable-relation-Decidable-equivalence-relation

  is-equivalence-relation-Decidable-equivalence-relation :
    is-equivalence-relation relation-Decidable-equivalence-relation
  is-equivalence-relation-Decidable-equivalence-relation = pr2 R

  equivalence-relation-Decidable-equivalence-relation :
    equivalence-relation l2 X
  pr1 equivalence-relation-Decidable-equivalence-relation =
    relation-Decidable-equivalence-relation
  pr2 equivalence-relation-Decidable-equivalence-relation =
    is-equivalence-relation-Decidable-equivalence-relation

  refl-Decidable-equivalence-relation :
    is-reflexive sim-Decidable-equivalence-relation
  refl-Decidable-equivalence-relation =
    refl-equivalence-relation
      equivalence-relation-Decidable-equivalence-relation

  symmetric-Decidable-equivalence-relation :
    is-symmetric sim-Decidable-equivalence-relation
  symmetric-Decidable-equivalence-relation =
    symmetric-equivalence-relation
      equivalence-relation-Decidable-equivalence-relation

  equiv-symmetric-Decidable-equivalence-relation :
    {x y : X} →
    sim-Decidable-equivalence-relation x y ≃
    sim-Decidable-equivalence-relation y x
  equiv-symmetric-Decidable-equivalence-relation {x} {y} =
    equiv-prop
      ( is-prop-sim-Decidable-equivalence-relation x y)
      ( is-prop-sim-Decidable-equivalence-relation y x)
      ( symmetric-Decidable-equivalence-relation x y)
      ( symmetric-Decidable-equivalence-relation y x)

  transitive-Decidable-equivalence-relation :
    is-transitive sim-Decidable-equivalence-relation
  transitive-Decidable-equivalence-relation =
    transitive-equivalence-relation
      equivalence-relation-Decidable-equivalence-relation

equiv-equivalence-relation-is-decidable-Dec-equivalence-relation :
  {l1 l2 : Level} {X : UU l1} →
  Decidable-equivalence-relation l2 X ≃
  Σ ( equivalence-relation l2 X)
    ( λ R → is-decidable-equivalence-relation R)
pr1 equiv-equivalence-relation-is-decidable-Dec-equivalence-relation R =
  ( equivalence-relation-Decidable-equivalence-relation R ,
    is-decidable-sim-Decidable-equivalence-relation R)
pr2 equiv-equivalence-relation-is-decidable-Dec-equivalence-relation =
  is-equiv-is-invertible
    ( λ (R , d) →
      ( map-inv-equiv
          ( equiv-relation-is-decidable-Decidable-Relation)
          ( prop-equivalence-relation R , d) ,
        is-equivalence-relation-prop-equivalence-relation R))
    ( refl-htpy)
    ( refl-htpy)
```

### Equivalence classes of decidable equivalence relations

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-equivalence-relation l2 X)
  where

  is-equivalence-class-Decidable-equivalence-relation :
    decidable-subtype l2 X → UU (l1 ⊔ lsuc l2)
  is-equivalence-class-Decidable-equivalence-relation P =
    ∃ X (λ x → P ＝ decidable-relation-Decidable-equivalence-relation R x)

  equivalence-class-Decidable-equivalence-relation : UU (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-equivalence-relation =
    im (decidable-relation-Decidable-equivalence-relation R)

  class-Decidable-equivalence-relation :
    X → equivalence-class-Decidable-equivalence-relation
  pr1 (class-Decidable-equivalence-relation x) =
    decidable-relation-Decidable-equivalence-relation R x
  pr2 (class-Decidable-equivalence-relation x) =
    intro-∃ x refl

  emb-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation ↪ decidable-subtype l2 X
  emb-equivalence-class-Decidable-equivalence-relation =
    emb-im (decidable-relation-Decidable-equivalence-relation R)

  decidable-subtype-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation → decidable-subtype l2 X
  decidable-subtype-equivalence-class-Decidable-equivalence-relation =
    map-emb emb-equivalence-class-Decidable-equivalence-relation

  subtype-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation → subtype l2 X
  subtype-equivalence-class-Decidable-equivalence-relation =
    subtype-decidable-subtype ∘
    decidable-subtype-equivalence-class-Decidable-equivalence-relation

  is-in-subtype-equivalence-class-Decidable-equivalence-relation :
    equivalence-class-Decidable-equivalence-relation → X → UU l2
  is-in-subtype-equivalence-class-Decidable-equivalence-relation =
    is-in-subtype ∘ subtype-equivalence-class-Decidable-equivalence-relation

  is-prop-is-in-subtype-equivalence-class-Decidable-equivalence-relation :
    (P : equivalence-class-Decidable-equivalence-relation) (x : X) →
    is-prop (is-in-subtype-equivalence-class-Decidable-equivalence-relation P x)
  is-prop-is-in-subtype-equivalence-class-Decidable-equivalence-relation P =
    is-prop-is-in-subtype
      ( subtype-equivalence-class-Decidable-equivalence-relation P)

  is-set-equivalence-class-Decidable-equivalence-relation :
    is-set equivalence-class-Decidable-equivalence-relation
  is-set-equivalence-class-Decidable-equivalence-relation =
    is-set-im
      ( decidable-relation-Decidable-equivalence-relation R)
      ( is-set-decidable-subtype)

  equivalence-class-Decidable-equivalence-relation-Set : Set (l1 ⊔ lsuc l2)
  pr1 equivalence-class-Decidable-equivalence-relation-Set =
    equivalence-class-Decidable-equivalence-relation
  pr2 equivalence-class-Decidable-equivalence-relation-Set =
    is-set-equivalence-class-Decidable-equivalence-relation

  unit-im-equivalence-class-Decidable-equivalence-relation :
    hom-slice
      ( decidable-relation-Decidable-equivalence-relation R)
      ( decidable-subtype-equivalence-class-Decidable-equivalence-relation)
  unit-im-equivalence-class-Decidable-equivalence-relation =
    unit-im (decidable-relation-Decidable-equivalence-relation R)

  is-image-equivalence-class-Decidable-equivalence-relation :
    is-image
      ( decidable-relation-Decidable-equivalence-relation R)
      ( emb-equivalence-class-Decidable-equivalence-relation)
      ( unit-im-equivalence-class-Decidable-equivalence-relation)
  is-image-equivalence-class-Decidable-equivalence-relation =
    is-image-im (decidable-relation-Decidable-equivalence-relation R)

  is-surjective-class-Decidable-equivalence-relation :
    is-surjective class-Decidable-equivalence-relation
  is-surjective-class-Decidable-equivalence-relation =
    is-surjective-map-unit-im
      ( decidable-relation-Decidable-equivalence-relation R)
```

## Properties

### We characterize the identity type of the equivalence classes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A) (a : A)
  where

  abstract
    center-total-subtype-equivalence-class-Decidable-equivalence-relation :
      Σ ( equivalence-class-Decidable-equivalence-relation R)
        ( λ P →
          is-in-subtype-equivalence-class-Decidable-equivalence-relation R P a)
    pr1 center-total-subtype-equivalence-class-Decidable-equivalence-relation =
      class-Decidable-equivalence-relation R a
    pr2 center-total-subtype-equivalence-class-Decidable-equivalence-relation =
      refl-Decidable-equivalence-relation R a

    contraction-total-subtype-equivalence-class-Decidable-equivalence-relation :
      ( t :
        Σ ( equivalence-class-Decidable-equivalence-relation R)
          ( λ P →
            is-in-subtype-equivalence-class-Decidable-equivalence-relation
              R P a)) →
      center-total-subtype-equivalence-class-Decidable-equivalence-relation ＝ t
    contraction-total-subtype-equivalence-class-Decidable-equivalence-relation
      ( pair (pair P p) H) =
      eq-type-subtype
        ( λ Q → subtype-equivalence-class-Decidable-equivalence-relation R Q a)
        ( apply-universal-property-trunc-Prop
          ( p)
          ( Id-Prop
            ( equivalence-class-Decidable-equivalence-relation-Set R)
            ( class-Decidable-equivalence-relation R a)
            ( pair P p))
          ( α))
      where
      α : fiber (pr1 R) P → class-Decidable-equivalence-relation R a ＝ pair P p
      α (pair x refl) =
        eq-type-subtype
          ( λ z →
            trunc-Prop
              ( fiber (decidable-relation-Decidable-equivalence-relation R) z))
          ( eq-htpy
            ( λ y →
              eq-iff-Decidable-Prop
                ( pr1 R a y)
                ( pr1 R x y)
                ( λ K → transitive-Decidable-equivalence-relation R x a y K H)
                ( λ K → transitive-Decidable-equivalence-relation R a x y K
                  ( symmetric-Decidable-equivalence-relation R x a H))))

    is-torsorial-subtype-equivalence-class-Decidable-equivalence-relation :
      is-torsorial
        ( λ P →
          is-in-subtype-equivalence-class-Decidable-equivalence-relation R P a)
    pr1
      is-torsorial-subtype-equivalence-class-Decidable-equivalence-relation =
      center-total-subtype-equivalence-class-Decidable-equivalence-relation
    pr2
      is-torsorial-subtype-equivalence-class-Decidable-equivalence-relation =
      contraction-total-subtype-equivalence-class-Decidable-equivalence-relation

  related-eq-quotient-Decidable-equivalence-relation :
    (q : equivalence-class-Decidable-equivalence-relation R) →
      class-Decidable-equivalence-relation R a ＝ q →
    is-in-subtype-equivalence-class-Decidable-equivalence-relation R q a
  related-eq-quotient-Decidable-equivalence-relation
    .(class-Decidable-equivalence-relation R a) refl =
    refl-Decidable-equivalence-relation R a

  abstract
    is-equiv-related-eq-quotient-Decidable-equivalence-relation :
      (q : equivalence-class-Decidable-equivalence-relation R) →
      is-equiv (related-eq-quotient-Decidable-equivalence-relation q)
    is-equiv-related-eq-quotient-Decidable-equivalence-relation =
      fundamental-theorem-id
        ( is-torsorial-subtype-equivalence-class-Decidable-equivalence-relation)
        ( related-eq-quotient-Decidable-equivalence-relation)

  abstract
    effective-quotient-Decidable-equivalence-relation' :
      (q : equivalence-class-Decidable-equivalence-relation R) →
      ( class-Decidable-equivalence-relation R a ＝ q) ≃
      ( is-in-subtype-equivalence-class-Decidable-equivalence-relation R q a)
    pr1 (effective-quotient-Decidable-equivalence-relation' q) =
      related-eq-quotient-Decidable-equivalence-relation q
    pr2 (effective-quotient-Decidable-equivalence-relation' q) =
      is-equiv-related-eq-quotient-Decidable-equivalence-relation q

  abstract
    eq-effective-quotient-Decidable-equivalence-relation' :
      (q : equivalence-class-Decidable-equivalence-relation R) →
      is-in-subtype-equivalence-class-Decidable-equivalence-relation R q a →
      class-Decidable-equivalence-relation R a ＝ q
    eq-effective-quotient-Decidable-equivalence-relation' q =
      map-inv-is-equiv
        ( is-equiv-related-eq-quotient-Decidable-equivalence-relation q)
```

### The quotient map into the large set quotient is effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  abstract
    is-effective-class-Decidable-equivalence-relation :
      is-effective
        ( equivalence-relation-Decidable-equivalence-relation R)
        ( class-Decidable-equivalence-relation R)
    is-effective-class-Decidable-equivalence-relation x y =
      ( equiv-symmetric-Decidable-equivalence-relation R) ∘e
      ( effective-quotient-Decidable-equivalence-relation' R x
        ( class-Decidable-equivalence-relation R y))

  abstract
    apply-effectiveness-class-Decidable-equivalence-relation :
      {x y : A} →
      ( class-Decidable-equivalence-relation R x ＝
        class-Decidable-equivalence-relation R y) →
      sim-Decidable-equivalence-relation R x y
    apply-effectiveness-class-Decidable-equivalence-relation {x} {y} =
      map-equiv (is-effective-class-Decidable-equivalence-relation x y)

  abstract
    apply-effectiveness-class-Decidable-equivalence-relation' :
      {x y : A} → sim-Decidable-equivalence-relation R x y →
      class-Decidable-equivalence-relation R x ＝
      class-Decidable-equivalence-relation R y
    apply-effectiveness-class-Decidable-equivalence-relation' {x} {y} =
      map-inv-equiv (is-effective-class-Decidable-equivalence-relation x y)
```

### The quotient map into the large set quotient is surjective and effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  is-surjective-and-effective-class-Decidable-equivalence-relation :
    is-surjective-and-effective
      ( equivalence-relation-Decidable-equivalence-relation R)
      ( class-Decidable-equivalence-relation R)
  pr1 is-surjective-and-effective-class-Decidable-equivalence-relation =
    is-surjective-class-Decidable-equivalence-relation R
  pr2 is-surjective-and-effective-class-Decidable-equivalence-relation =
    is-effective-class-Decidable-equivalence-relation R
```

### The quotient map into the large set quotient is a reflecting map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  quotient-reflecting-map-equivalence-class-Decidable-equivalence-relation :
    reflecting-map-equivalence-relation
      ( equivalence-relation-Decidable-equivalence-relation R)
      ( equivalence-class-Decidable-equivalence-relation R)
  pr1 quotient-reflecting-map-equivalence-class-Decidable-equivalence-relation =
    class-Decidable-equivalence-relation R
  pr2 quotient-reflecting-map-equivalence-class-Decidable-equivalence-relation =
    apply-effectiveness-class-Decidable-equivalence-relation' R
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-equivalence-relation l2 A)
  where

  transitive-is-in-subtype-equivalence-class-Decidable-equivalence-relation :
    (P : equivalence-class-Decidable-equivalence-relation R) (a b : A) →
    is-in-subtype-equivalence-class-Decidable-equivalence-relation R P a →
    sim-Decidable-equivalence-relation R a b →
    is-in-subtype-equivalence-class-Decidable-equivalence-relation R P b
  transitive-is-in-subtype-equivalence-class-Decidable-equivalence-relation
    P a b p q =
    apply-universal-property-trunc-Prop
      ( pr2 P)
      ( subtype-equivalence-class-Decidable-equivalence-relation R P b)
      ( λ (pair x T) →
        tr
          ( λ Z →
            is-in-subtype-equivalence-class-Decidable-equivalence-relation
              R Z b)
          { x = class-Decidable-equivalence-relation R x} {y = P}
          ( eq-pair-Σ
            ( T)
            ( all-elements-equal-type-trunc-Prop _ _))
          ( transitive-Decidable-equivalence-relation R _ a b q
            ( tr
              ( λ Z →
                is-in-subtype-equivalence-class-Decidable-equivalence-relation
                  R Z a)
              { x = P}
              { y = class-Decidable-equivalence-relation R x}
              ( eq-pair-Σ (inv T) (all-elements-equal-type-trunc-Prop _ _))
              ( p))))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-decidable-is-in-equivalence-class-is-decidable :
    ((a b : A) → is-decidable (sim-equivalence-relation R a b)) →
    (T : equivalence-class R) →
    (a : A) →
    is-decidable (is-in-equivalence-class R T a)
  is-decidable-is-in-equivalence-class-is-decidable F T a =
    apply-universal-property-trunc-Prop
      ( pr2 T)
      ( is-decidable-Prop
        ( subtype-equivalence-class R T a))
      ( λ (pair t P) →
        is-decidable-iff
          ( backward-implication (P a))
          ( forward-implication (P a))
          ( F t a))
```

#### The type of decidable equivalence relations on `A` is equivalent to the type of surjections from `A` into a type with decidable equality

```agda
has-decidable-equality-type-Surjection-Into-Set :
  {l1 : Level} {A : UU l1} (surj : Surjection-Into-Set l1 A) →
  ( is-decidable-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set surj)) →
  has-decidable-equality (type-Surjection-Into-Set surj)
has-decidable-equality-type-Surjection-Into-Set surj is-dec-rel x y =
  apply-twice-dependent-universal-property-surj-is-surjective
    ( map-Surjection-Into-Set surj)
    ( is-surjective-Surjection-Into-Set surj)
    ( λ (s t : (type-Surjection-Into-Set surj)) →
      ( is-decidable (s ＝ t) ,
        is-prop-is-decidable ( is-set-type-Surjection-Into-Set surj s t)))
    ( λ a1 a2 → is-dec-rel a1 a2)
    ( x)
    ( y)

is-decidable-equivalence-relation-Surjection-Into-Set :
  {l1 : Level} {A : UU l1} (surj : Surjection-Into-Set l1 A) →
  has-decidable-equality (type-Surjection-Into-Set surj) →
  is-decidable-equivalence-relation
    ( equivalence-relation-Surjection-Into-Set surj)
is-decidable-equivalence-relation-Surjection-Into-Set surj dec-eq x y =
  dec-eq (map-Surjection-Into-Set surj x) (map-Surjection-Into-Set surj y)

equiv-Surjection-Into-Set-Decidable-equivalence-relation :
  {l1 : Level} (A : UU l1) →
  Decidable-equivalence-relation l1 A ≃
  Σ (UU l1) (λ X → (A ↠ X) × has-decidable-equality X)
equiv-Surjection-Into-Set-Decidable-equivalence-relation {l1} A =
  ( ( equiv-Σ
      ( λ z → (A ↠ z) × has-decidable-equality z)
      ( id-equiv)
      ( λ X →
        ( equiv-prod
          ( id-equiv)
          ( inv-equiv
              ( equiv-add-redundant-prop
                ( is-prop-is-set ( X))
                ( is-set-has-decidable-equality)) ∘e
            commutative-prod) ∘e
        ( equiv-left-swap-Σ)))) ∘e
    ( ( associative-Σ
        ( UU l1)
        ( λ X → is-set X)
        ( λ X → (A ↠ pr1 X) × has-decidable-equality (pr1 X))) ∘e
      ( ( associative-Σ
          ( Set l1)
          ( λ X → (A ↠ type-Set X))
          ( λ X → has-decidable-equality (pr1 (pr1 X)))) ∘e
        ( ( equiv-type-subtype
            ( λ surj →
              is-prop-Π
                ( λ x →
                  is-prop-Π
                    ( λ y →
                      is-prop-is-decidable
                        ( is-prop-sim-equivalence-relation
                          ( equivalence-relation-Surjection-Into-Set surj)
                          ( x)
                          ( y)))))
            ( λ _ → is-prop-has-decidable-equality)
            ( λ s → has-decidable-equality-type-Surjection-Into-Set s)
            ( λ s → is-decidable-equivalence-relation-Surjection-Into-Set s)) ∘e
          ( ( inv-equiv
              ( equiv-Σ-equiv-base
                ( λ R → is-decidable-equivalence-relation R)
                ( inv-equiv
                  ( equiv-surjection-into-set-equivalence-relation A)))) ∘e
            ( equiv-equivalence-relation-is-decidable-Dec-equivalence-relation))))))
```
