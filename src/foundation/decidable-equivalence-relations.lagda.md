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

Decidable-Equivalence-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-Equivalence-Relation l2 X =
  Σ ( Decidable-Relation l2 X)
    ( λ R → is-equivalence-relation (relation-Decidable-Relation R))

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Equivalence-Relation l2 X)
  where

  decidable-relation-Decidable-Equivalence-Relation :
    Decidable-Relation l2 X
  decidable-relation-Decidable-Equivalence-Relation = pr1 R

  relation-Decidable-Equivalence-Relation : X → X → Prop l2
  relation-Decidable-Equivalence-Relation =
    relation-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  sim-Decidable-Equivalence-Relation : X → X → UU l2
  sim-Decidable-Equivalence-Relation =
    rel-Decidable-Relation decidable-relation-Decidable-Equivalence-Relation

  is-prop-sim-Decidable-Equivalence-Relation :
    (x y : X) → is-prop (sim-Decidable-Equivalence-Relation x y)
  is-prop-sim-Decidable-Equivalence-Relation =
    is-prop-rel-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  is-decidable-sim-Decidable-Equivalence-Relation :
    (x y : X) → is-decidable (sim-Decidable-Equivalence-Relation x y)
  is-decidable-sim-Decidable-Equivalence-Relation =
    is-decidable-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  is-equivalence-relation-Decidable-Equivalence-Relation :
    is-equivalence-relation relation-Decidable-Equivalence-Relation
  is-equivalence-relation-Decidable-Equivalence-Relation = pr2 R

  equivalence-relation-Decidable-Equivalence-Relation :
    equivalence-relation l2 X
  pr1 equivalence-relation-Decidable-Equivalence-Relation =
    relation-Decidable-Equivalence-Relation
  pr2 equivalence-relation-Decidable-Equivalence-Relation =
    is-equivalence-relation-Decidable-Equivalence-Relation

  refl-Decidable-Equivalence-Relation :
    is-reflexive sim-Decidable-Equivalence-Relation
  refl-Decidable-Equivalence-Relation =
    refl-equivalence-relation
      equivalence-relation-Decidable-Equivalence-Relation

  symmetric-Decidable-Equivalence-Relation :
    is-symmetric sim-Decidable-Equivalence-Relation
  symmetric-Decidable-Equivalence-Relation =
    symmetric-equivalence-relation
      equivalence-relation-Decidable-Equivalence-Relation

  equiv-symmetric-Decidable-Equivalence-Relation :
    {x y : X} →
    sim-Decidable-Equivalence-Relation x y ≃
    sim-Decidable-Equivalence-Relation y x
  equiv-symmetric-Decidable-Equivalence-Relation {x} {y} =
    equiv-iff-is-prop
      ( is-prop-sim-Decidable-Equivalence-Relation x y)
      ( is-prop-sim-Decidable-Equivalence-Relation y x)
      ( symmetric-Decidable-Equivalence-Relation x y)
      ( symmetric-Decidable-Equivalence-Relation y x)

  transitive-Decidable-Equivalence-Relation :
    is-transitive sim-Decidable-Equivalence-Relation
  transitive-Decidable-Equivalence-Relation =
    transitive-equivalence-relation
      equivalence-relation-Decidable-Equivalence-Relation

equiv-equivalence-relation-is-decidable-Decidable-Equivalence-Relation :
  {l1 l2 : Level} {X : UU l1} →
  Decidable-Equivalence-Relation l2 X ≃
  Σ ( equivalence-relation l2 X)
    ( λ R → is-decidable-equivalence-relation R)
pr1 equiv-equivalence-relation-is-decidable-Decidable-Equivalence-Relation R =
  ( equivalence-relation-Decidable-Equivalence-Relation R ,
    is-decidable-sim-Decidable-Equivalence-Relation R)
pr2 equiv-equivalence-relation-is-decidable-Decidable-Equivalence-Relation =
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
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Equivalence-Relation l2 X)
  where

  is-equivalence-class-Decidable-Equivalence-Relation :
    decidable-subtype l2 X → UU (l1 ⊔ lsuc l2)
  is-equivalence-class-Decidable-Equivalence-Relation P =
    exists-structure
      ( X)
      ( λ x → P ＝ decidable-relation-Decidable-Equivalence-Relation R x)

  equivalence-class-Decidable-Equivalence-Relation : UU (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-Equivalence-Relation =
    im (decidable-relation-Decidable-Equivalence-Relation R)

  class-Decidable-Equivalence-Relation :
    X → equivalence-class-Decidable-Equivalence-Relation
  pr1 (class-Decidable-Equivalence-Relation x) =
    decidable-relation-Decidable-Equivalence-Relation R x
  pr2 (class-Decidable-Equivalence-Relation x) =
    intro-exists x refl

  emb-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation ↪ decidable-subtype l2 X
  emb-equivalence-class-Decidable-Equivalence-Relation =
    emb-im (decidable-relation-Decidable-Equivalence-Relation R)

  decidable-subtype-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation → decidable-subtype l2 X
  decidable-subtype-equivalence-class-Decidable-Equivalence-Relation =
    map-emb emb-equivalence-class-Decidable-Equivalence-Relation

  subtype-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation → subtype l2 X
  subtype-equivalence-class-Decidable-Equivalence-Relation =
    subtype-decidable-subtype ∘
    decidable-subtype-equivalence-class-Decidable-Equivalence-Relation

  is-in-subtype-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation → X → UU l2
  is-in-subtype-equivalence-class-Decidable-Equivalence-Relation =
    is-in-subtype ∘ subtype-equivalence-class-Decidable-Equivalence-Relation

  is-prop-is-in-subtype-equivalence-class-Decidable-Equivalence-Relation :
    (P : equivalence-class-Decidable-Equivalence-Relation) (x : X) →
    is-prop (is-in-subtype-equivalence-class-Decidable-Equivalence-Relation P x)
  is-prop-is-in-subtype-equivalence-class-Decidable-Equivalence-Relation P =
    is-prop-is-in-subtype
      ( subtype-equivalence-class-Decidable-Equivalence-Relation P)

  is-set-equivalence-class-Decidable-Equivalence-Relation :
    is-set equivalence-class-Decidable-Equivalence-Relation
  is-set-equivalence-class-Decidable-Equivalence-Relation =
    is-set-im
      ( decidable-relation-Decidable-Equivalence-Relation R)
      ( is-set-decidable-subtype)

  equivalence-class-Decidable-Equivalence-Relation-Set : Set (l1 ⊔ lsuc l2)
  pr1 equivalence-class-Decidable-Equivalence-Relation-Set =
    equivalence-class-Decidable-Equivalence-Relation
  pr2 equivalence-class-Decidable-Equivalence-Relation-Set =
    is-set-equivalence-class-Decidable-Equivalence-Relation

  unit-im-equivalence-class-Decidable-Equivalence-Relation :
    hom-slice
      ( decidable-relation-Decidable-Equivalence-Relation R)
      ( decidable-subtype-equivalence-class-Decidable-Equivalence-Relation)
  unit-im-equivalence-class-Decidable-Equivalence-Relation =
    unit-im (decidable-relation-Decidable-Equivalence-Relation R)

  is-image-equivalence-class-Decidable-Equivalence-Relation :
    is-image
      ( decidable-relation-Decidable-Equivalence-Relation R)
      ( emb-equivalence-class-Decidable-Equivalence-Relation)
      ( unit-im-equivalence-class-Decidable-Equivalence-Relation)
  is-image-equivalence-class-Decidable-Equivalence-Relation =
    is-image-im (decidable-relation-Decidable-Equivalence-Relation R)

  is-surjective-class-Decidable-Equivalence-Relation :
    is-surjective class-Decidable-Equivalence-Relation
  is-surjective-class-Decidable-Equivalence-Relation =
    is-surjective-map-unit-im
      ( decidable-relation-Decidable-Equivalence-Relation R)
```

## Properties

### We characterize the identity type of the equivalence classes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-Equivalence-Relation l2 A) (a : A)
  where

  abstract
    center-total-subtype-equivalence-class-Decidable-Equivalence-Relation :
      Σ ( equivalence-class-Decidable-Equivalence-Relation R)
        ( λ P →
          is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R P a)
    pr1 center-total-subtype-equivalence-class-Decidable-Equivalence-Relation =
      class-Decidable-Equivalence-Relation R a
    pr2 center-total-subtype-equivalence-class-Decidable-Equivalence-Relation =
      refl-Decidable-Equivalence-Relation R a

    contraction-total-subtype-equivalence-class-Decidable-Equivalence-Relation :
      ( t :
        Σ ( equivalence-class-Decidable-Equivalence-Relation R)
          ( λ P →
            is-in-subtype-equivalence-class-Decidable-Equivalence-Relation
              R P a)) →
      center-total-subtype-equivalence-class-Decidable-Equivalence-Relation ＝ t
    contraction-total-subtype-equivalence-class-Decidable-Equivalence-Relation
      ( pair (pair P p) H) =
      eq-type-subtype
        ( λ Q → subtype-equivalence-class-Decidable-Equivalence-Relation R Q a)
        ( apply-universal-property-trunc-Prop
          ( p)
          ( Id-Prop
            ( equivalence-class-Decidable-Equivalence-Relation-Set R)
            ( class-Decidable-Equivalence-Relation R a)
            ( pair P p))
          ( α))
      where
      α : fiber (pr1 R) P → class-Decidable-Equivalence-Relation R a ＝ pair P p
      α (pair x refl) =
        eq-type-subtype
          ( λ z →
            trunc-Prop
              ( fiber (decidable-relation-Decidable-Equivalence-Relation R) z))
          ( eq-htpy
            ( λ y →
              eq-iff-Decidable-Prop
                ( pr1 R a y)
                ( pr1 R x y)
                ( λ K → transitive-Decidable-Equivalence-Relation R x a y K H)
                ( λ K → transitive-Decidable-Equivalence-Relation R a x y K
                  ( symmetric-Decidable-Equivalence-Relation R x a H))))

    is-torsorial-subtype-equivalence-class-Decidable-Equivalence-Relation :
      is-torsorial
        ( λ P →
          is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R P a)
    pr1
      is-torsorial-subtype-equivalence-class-Decidable-Equivalence-Relation =
      center-total-subtype-equivalence-class-Decidable-Equivalence-Relation
    pr2
      is-torsorial-subtype-equivalence-class-Decidable-Equivalence-Relation =
      contraction-total-subtype-equivalence-class-Decidable-Equivalence-Relation

  related-eq-quotient-Decidable-Equivalence-Relation :
    (q : equivalence-class-Decidable-Equivalence-Relation R) →
      class-Decidable-Equivalence-Relation R a ＝ q →
    is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R q a
  related-eq-quotient-Decidable-Equivalence-Relation
    .(class-Decidable-Equivalence-Relation R a) refl =
    refl-Decidable-Equivalence-Relation R a

  abstract
    is-equiv-related-eq-quotient-Decidable-Equivalence-Relation :
      (q : equivalence-class-Decidable-Equivalence-Relation R) →
      is-equiv (related-eq-quotient-Decidable-Equivalence-Relation q)
    is-equiv-related-eq-quotient-Decidable-Equivalence-Relation =
      fundamental-theorem-id
        ( is-torsorial-subtype-equivalence-class-Decidable-Equivalence-Relation)
        ( related-eq-quotient-Decidable-Equivalence-Relation)

  abstract
    effective-quotient-Decidable-Equivalence-Relation' :
      (q : equivalence-class-Decidable-Equivalence-Relation R) →
      ( class-Decidable-Equivalence-Relation R a ＝ q) ≃
      ( is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R q a)
    pr1 (effective-quotient-Decidable-Equivalence-Relation' q) =
      related-eq-quotient-Decidable-Equivalence-Relation q
    pr2 (effective-quotient-Decidable-Equivalence-Relation' q) =
      is-equiv-related-eq-quotient-Decidable-Equivalence-Relation q

  abstract
    eq-effective-quotient-Decidable-Equivalence-Relation' :
      (q : equivalence-class-Decidable-Equivalence-Relation R) →
      is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R q a →
      class-Decidable-Equivalence-Relation R a ＝ q
    eq-effective-quotient-Decidable-Equivalence-Relation' q =
      map-inv-is-equiv
        ( is-equiv-related-eq-quotient-Decidable-Equivalence-Relation q)
```

### The quotient map into the large set quotient is effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-Equivalence-Relation l2 A)
  where

  abstract
    is-effective-class-Decidable-Equivalence-Relation :
      is-effective
        ( equivalence-relation-Decidable-Equivalence-Relation R)
        ( class-Decidable-Equivalence-Relation R)
    is-effective-class-Decidable-Equivalence-Relation x y =
      ( equiv-symmetric-Decidable-Equivalence-Relation R) ∘e
      ( effective-quotient-Decidable-Equivalence-Relation' R x
        ( class-Decidable-Equivalence-Relation R y))

  abstract
    apply-effectiveness-class-Decidable-Equivalence-Relation :
      {x y : A} →
      ( class-Decidable-Equivalence-Relation R x ＝
        class-Decidable-Equivalence-Relation R y) →
      sim-Decidable-Equivalence-Relation R x y
    apply-effectiveness-class-Decidable-Equivalence-Relation {x} {y} =
      map-equiv (is-effective-class-Decidable-Equivalence-Relation x y)

  abstract
    apply-effectiveness-class-Decidable-Equivalence-Relation' :
      {x y : A} → sim-Decidable-Equivalence-Relation R x y →
      class-Decidable-Equivalence-Relation R x ＝
      class-Decidable-Equivalence-Relation R y
    apply-effectiveness-class-Decidable-Equivalence-Relation' {x} {y} =
      map-inv-equiv (is-effective-class-Decidable-Equivalence-Relation x y)
```

### The quotient map into the large set quotient is surjective and effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-Equivalence-Relation l2 A)
  where

  is-surjective-and-effective-class-Decidable-Equivalence-Relation :
    is-surjective-and-effective
      ( equivalence-relation-Decidable-Equivalence-Relation R)
      ( class-Decidable-Equivalence-Relation R)
  pr1 is-surjective-and-effective-class-Decidable-Equivalence-Relation =
    is-surjective-class-Decidable-Equivalence-Relation R
  pr2 is-surjective-and-effective-class-Decidable-Equivalence-Relation =
    is-effective-class-Decidable-Equivalence-Relation R
```

### The quotient map into the large set quotient is a reflecting map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-Equivalence-Relation l2 A)
  where

  quotient-reflecting-map-equivalence-class-Decidable-Equivalence-Relation :
    reflecting-map-equivalence-relation
      ( equivalence-relation-Decidable-Equivalence-Relation R)
      ( equivalence-class-Decidable-Equivalence-Relation R)
  pr1 quotient-reflecting-map-equivalence-class-Decidable-Equivalence-Relation =
    class-Decidable-Equivalence-Relation R
  pr2 quotient-reflecting-map-equivalence-class-Decidable-Equivalence-Relation =
    apply-effectiveness-class-Decidable-Equivalence-Relation' R
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-Equivalence-Relation l2 A)
  where

  transitive-is-in-subtype-equivalence-class-Decidable-Equivalence-Relation :
    (P : equivalence-class-Decidable-Equivalence-Relation R) (a b : A) →
    is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R P a →
    sim-Decidable-Equivalence-Relation R a b →
    is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R P b
  transitive-is-in-subtype-equivalence-class-Decidable-Equivalence-Relation
    P a b p q =
    apply-universal-property-trunc-Prop
      ( pr2 P)
      ( subtype-equivalence-class-Decidable-Equivalence-Relation R P b)
      ( λ (pair x T) →
        tr
          ( λ Z →
            is-in-subtype-equivalence-class-Decidable-Equivalence-Relation
              R Z b)
          { x = class-Decidable-Equivalence-Relation R x} {y = P}
          ( eq-pair-Σ
            ( T)
            ( all-elements-equal-type-trunc-Prop _ _))
          ( transitive-Decidable-Equivalence-Relation R _ a b q
            ( tr
              ( λ Z →
                is-in-subtype-equivalence-class-Decidable-Equivalence-Relation
                  R Z a)
              { x = P}
              { y = class-Decidable-Equivalence-Relation R x}
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
      ( is-decidable-Prop (subtype-equivalence-class R T a))
      ( λ (t , P) →
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
  apply-twice-dependent-universal-property-surjection-is-surjective
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

equiv-Surjection-Into-Set-Decidable-Equivalence-Relation :
  {l1 : Level} (A : UU l1) →
  Decidable-Equivalence-Relation l1 A ≃
  Σ (UU l1) (λ X → (A ↠ X) × has-decidable-equality X)
equiv-Surjection-Into-Set-Decidable-Equivalence-Relation {l1} A =
  ( equiv-tot
    ( λ X →
      ( equiv-product-right
        ( ( equiv-remove-redundant-prop
            ( is-prop-is-set X)
            ( is-set-has-decidable-equality)) ∘e
          ( commutative-product)) ∘e
        ( equiv-left-swap-Σ)))) ∘e
  ( associative-Σ) ∘e
  ( associative-Σ) ∘e
  ( equiv-type-subtype
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
  ( inv-equiv
    ( equiv-Σ-equiv-base
      ( λ R → is-decidable-equivalence-relation R)
      ( inv-equiv
        ( equiv-surjection-into-set-equivalence-relation A)))) ∘e
  ( equiv-equivalence-relation-is-decidable-Decidable-Equivalence-Relation)
```
