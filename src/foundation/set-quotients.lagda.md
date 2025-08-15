# Set quotients

```agda
module foundation.set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-classes
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.slice
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-image
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.equivalence-relations
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.small-types
open import foundation-core.subtypes
```

</details>

## Definitions

### Set quotients

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  set-quotient : UU (l1 ⊔ l2)
  set-quotient = small-type-Small-Type (equivalence-class-Small-Type R)

  compute-set-quotient : equivalence-class R ≃ set-quotient
  compute-set-quotient =
    equiv-is-small-type-Small-Type (equivalence-class-Small-Type R)

  set-quotient-equivalence-class : equivalence-class R → set-quotient
  set-quotient-equivalence-class = map-equiv compute-set-quotient

  equivalence-class-set-quotient : set-quotient → equivalence-class R
  equivalence-class-set-quotient = map-inv-equiv compute-set-quotient

  is-section-equivalence-class-set-quotient :
    (set-quotient-equivalence-class ∘ equivalence-class-set-quotient) ~ id
  is-section-equivalence-class-set-quotient =
    is-section-map-inv-equiv compute-set-quotient

  is-retraction-equivalence-class-set-quotient :
    (equivalence-class-set-quotient ∘ set-quotient-equivalence-class) ~ id
  is-retraction-equivalence-class-set-quotient =
    is-retraction-map-inv-equiv compute-set-quotient

  emb-equivalence-class-set-quotient : set-quotient ↪ equivalence-class R
  emb-equivalence-class-set-quotient =
    emb-equiv (inv-equiv compute-set-quotient)

  emb-set-quotient-equivalence-class : equivalence-class R ↪ set-quotient
  emb-set-quotient-equivalence-class = emb-equiv compute-set-quotient

  quotient-map : A → set-quotient
  quotient-map = set-quotient-equivalence-class ∘ class R

  is-surjective-quotient-map : is-surjective quotient-map
  is-surjective-quotient-map =
    is-surjective-left-comp-equiv compute-set-quotient (is-surjective-class R)

  surjection-quotient-map : A ↠ set-quotient
  pr1 surjection-quotient-map = quotient-map
  pr2 surjection-quotient-map = is-surjective-quotient-map

  emb-subtype-set-quotient : set-quotient ↪ subtype l2 A
  emb-subtype-set-quotient =
    comp-emb (emb-equivalence-class R) emb-equivalence-class-set-quotient

  subtype-set-quotient : set-quotient → subtype l2 A
  subtype-set-quotient =
    subtype-equivalence-class R ∘ equivalence-class-set-quotient

  is-inhabited-subtype-set-quotient :
    (x : set-quotient) → is-inhabited-subtype (subtype-set-quotient x)
  is-inhabited-subtype-set-quotient x =
    is-inhabited-subtype-equivalence-class R (equivalence-class-set-quotient x)

  inhabited-subtype-set-quotient : set-quotient → inhabited-subtype l2 A
  inhabited-subtype-set-quotient =
    inhabited-subtype-equivalence-class R ∘ equivalence-class-set-quotient

  is-in-equivalence-class-set-quotient :
    (x : set-quotient) → A → UU l2
  is-in-equivalence-class-set-quotient x =
    is-in-equivalence-class R (equivalence-class-set-quotient x)

  is-prop-is-in-equivalence-class-set-quotient :
    (x : set-quotient) (a : A) →
    is-prop (is-in-equivalence-class-set-quotient x a)
  is-prop-is-in-equivalence-class-set-quotient x =
    is-prop-is-in-equivalence-class R (equivalence-class-set-quotient x)

  is-in-equivalence-class-set-quotient-Prop :
    (x : set-quotient) → (A → Prop l2)
  is-in-equivalence-class-set-quotient-Prop x =
    is-in-equivalence-class-Prop R (equivalence-class-set-quotient x)

  is-set-set-quotient : is-set set-quotient
  is-set-set-quotient =
    is-set-equiv'
      ( equivalence-class R)
      ( compute-set-quotient)
      ( is-set-equivalence-class R)

  quotient-Set : Set (l1 ⊔ l2)
  pr1 quotient-Set = set-quotient
  pr2 quotient-Set = is-set-set-quotient

  unit-im-set-quotient :
    hom-slice (prop-equivalence-relation R) subtype-set-quotient
  pr1 unit-im-set-quotient = quotient-map
  pr2 unit-im-set-quotient =
    ( ( subtype-equivalence-class R) ·l
      ( inv-htpy is-retraction-equivalence-class-set-quotient)) ·r
    ( class R)

  is-image-set-quotient :
    is-image
      ( prop-equivalence-relation R)
      ( emb-subtype-set-quotient)
      ( unit-im-set-quotient)
  is-image-set-quotient =
    is-image-is-surjective
      ( prop-equivalence-relation R)
      ( emb-subtype-set-quotient)
      ( unit-im-set-quotient)
      ( is-surjective-quotient-map)
```

### The map `class : A → equivalence-class R` is an effective quotient map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-effective-quotient-map : is-effective R (quotient-map R)
  is-effective-quotient-map x y =
    equivalence-reasoning
      ( quotient-map R x ＝ quotient-map R y)
      ≃ ( equivalence-class-set-quotient R (quotient-map R x) ＝
          equivalence-class-set-quotient R (quotient-map R y))
        by equiv-ap-emb (emb-equivalence-class-set-quotient R)
      ≃ ( class R x ＝ equivalence-class-set-quotient R (quotient-map R y))
        by
        ( equiv-concat
          ( (inv ( is-retraction-equivalence-class-set-quotient R (class R x))))
          ( equivalence-class-set-quotient R (quotient-map R y)))
      ≃ ( class R x ＝ class R y)
        by
        ( equiv-concat'
          ( class R x)
          ( is-retraction-equivalence-class-set-quotient R (class R y)))
      ≃ ( sim-equivalence-relation R x y)
        by
        ( is-effective-class R x y)

  apply-effectiveness-quotient-map :
    {x y : A} → quotient-map R x ＝ quotient-map R y →
    sim-equivalence-relation R x y
  apply-effectiveness-quotient-map {x} {y} =
    map-equiv (is-effective-quotient-map x y)

  apply-effectiveness-quotient-map' :
    {x y : A} → sim-equivalence-relation R x y →
    quotient-map R x ＝ quotient-map R y
  apply-effectiveness-quotient-map' {x} {y} =
    map-inv-equiv (is-effective-quotient-map x y)

  is-surjective-and-effective-quotient-map :
    is-surjective-and-effective R (quotient-map R)
  pr1 is-surjective-and-effective-quotient-map = is-surjective-quotient-map R
  pr2 is-surjective-and-effective-quotient-map = is-effective-quotient-map

  reflecting-map-quotient-map :
    reflecting-map-equivalence-relation R (set-quotient R)
  pr1 reflecting-map-quotient-map = quotient-map R
  pr2 reflecting-map-quotient-map = apply-effectiveness-quotient-map'
```

### The set quotient of `R` is a set quotient of `R`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  is-set-quotient-set-quotient :
    is-set-quotient R (quotient-Set R) (reflecting-map-quotient-map R)
  is-set-quotient-set-quotient =
    is-set-quotient-is-surjective-and-effective R
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( is-surjective-and-effective-quotient-map R)

  inv-precomp-set-quotient :
    {l : Level} (X : Set l) →
    reflecting-map-equivalence-relation R (type-Set X) →
    hom-Set (quotient-Set R) X
  inv-precomp-set-quotient X =
    pr1 (pr1 (is-set-quotient-set-quotient X))

  is-section-inv-precomp-set-quotient :
    {l : Level} (X : Set l) →
    (f : reflecting-map-equivalence-relation R (type-Set X)) →
    (a : A) →
    inv-precomp-set-quotient X f (quotient-map R a) ＝
      map-reflecting-map-equivalence-relation R f a
  is-section-inv-precomp-set-quotient X f =
    htpy-eq
      ( ap
        ( map-reflecting-map-equivalence-relation R)
        ( is-section-map-inv-is-equiv
          ( is-set-quotient-set-quotient X)
          ( f)))

  is-retraction-inv-precomp-set-quotient :
    {l : Level} (X : Set l) (f : hom-Set (quotient-Set R) X) →
    inv-precomp-set-quotient X
      ( precomp-Set-Quotient R
        ( quotient-Set R)
        ( reflecting-map-quotient-map R)
        ( X)
        ( f)) ＝
    f
  is-retraction-inv-precomp-set-quotient X f =
    is-retraction-map-inv-is-equiv (is-set-quotient-set-quotient X) f
```

### Induction into propositions on the set quotient

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  equiv-induction-set-quotient :
    {l : Level} (P : set-quotient R → Prop l) →
    ((y : set-quotient R) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (quotient-map R x)))
  equiv-induction-set-quotient =
    equiv-dependent-universal-property-surjection-is-surjective
      ( quotient-map R)
      ( is-surjective-quotient-map R)

  induction-set-quotient :
    {l : Level} (P : set-quotient R → Prop l) →
    ((x : A) → type-Prop (P (quotient-map R x))) →
    ((y : set-quotient R) → type-Prop (P y))
  induction-set-quotient P =
    map-inv-equiv (equiv-induction-set-quotient P)
```

### Double induction for set quotients

#### The most general case

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  (P : set-quotient R → set-quotient S → Prop l5)
  where

  equiv-double-induction-set-quotient :
    ((x : set-quotient R) (y : set-quotient S) → type-Prop (P x y)) ≃
    ( (x : A) (y : B) →
      type-Prop (P (quotient-map R x) (quotient-map S y)))
  equiv-double-induction-set-quotient =
    ( equiv-Π-equiv-family
      ( λ x →
        equiv-induction-set-quotient S (P (quotient-map R x)))) ∘e
    ( equiv-induction-set-quotient R
      ( λ x → Π-Prop (set-quotient S) (P x)))

  double-induction-set-quotient :
    ( (x : A) (y : B) →
      type-Prop (P (quotient-map R x) (quotient-map S y))) →
    (x : set-quotient R) (y : set-quotient S) → type-Prop (P x y)
  double-induction-set-quotient =
    map-inv-equiv equiv-double-induction-set-quotient
```

#### Double induction over a single set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (P : (x y : set-quotient R) → Prop l3)
  where

  equiv-double-induction-set-quotient' :
    ((x y : set-quotient R) → type-Prop (P x y)) ≃
    ((x y : A) → type-Prop (P (quotient-map R x) (quotient-map R y)))
  equiv-double-induction-set-quotient' =
    equiv-double-induction-set-quotient R R P

  double-induction-set-quotient' :
    ( (x y : A) →
      type-Prop (P (quotient-map R x) (quotient-map R y))) →
    (x y : set-quotient R) → type-Prop (P x y)
  double-induction-set-quotient' =
    double-induction-set-quotient R R P
```

### Triple induction for set quotients

#### The most general case

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  {C : UU l5} (T : equivalence-relation l6 C)
  (P : set-quotient R → set-quotient S → set-quotient T → Prop l7)
  where

  equiv-triple-induction-set-quotient :
    ( (x : set-quotient R) (y : set-quotient S) (z : set-quotient T) →
      type-Prop (P x y z)) ≃
    ( (x : A) (y : B) (z : C) →
      type-Prop
        ( P (quotient-map R x) (quotient-map S y) (quotient-map T z)))
  equiv-triple-induction-set-quotient =
    ( equiv-Π-equiv-family
      ( λ x →
        equiv-double-induction-set-quotient S T
          ( P (quotient-map R x)))) ∘e
    ( equiv-induction-set-quotient R
      ( λ x →
        Π-Prop
          ( set-quotient S)
          ( λ y → Π-Prop (set-quotient T) (P x y))))

  triple-induction-set-quotient :
    ( (x : A) (y : B) (z : C) →
      type-Prop
        ( P ( quotient-map R x)
            ( quotient-map S y)
            ( quotient-map T z))) →
    ( x : set-quotient R) (y : set-quotient S)
    ( z : set-quotient T) → type-Prop (P x y z)
  triple-induction-set-quotient =
    map-inv-equiv equiv-triple-induction-set-quotient
```

#### Triple induction over a single set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (P : (x y z : set-quotient R) → Prop l3)
  where

  equiv-triple-induction-set-quotient' :
    ((x y z : set-quotient R) → type-Prop (P x y z)) ≃
    ( (x y z : A) →
      type-Prop
        ( P (quotient-map R x) (quotient-map R y) (quotient-map R z)))
  equiv-triple-induction-set-quotient' =
    equiv-triple-induction-set-quotient R R R P

  triple-induction-set-quotient' :
    ( (x y z : A) →
      type-Prop
        ( P ( quotient-map R x)
            ( quotient-map R y)
            ( quotient-map R z))) →
    ( x y z : set-quotient R) → type-Prop (P x y z)
  triple-induction-set-quotient' =
    triple-induction-set-quotient R R R P
```

### Every set quotient is equivalent to the set quotient

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (Uf : is-set-quotient R B f)
  where

  equiv-uniqueness-set-quotient-set-quotient :
    set-quotient R ≃ type-Set B
  equiv-uniqueness-set-quotient-set-quotient =
    equiv-uniqueness-set-quotient R
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( is-set-quotient-set-quotient R)
      B f Uf
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (x : A) (y : set-quotient R)
  where

  Eq-quotient-map-quotient : UU (l1 ⊔ l2)
  Eq-quotient-map-quotient = quotient-map R x ＝ y

  is-prop-Eq-quotient-map-quotient : is-prop Eq-quotient-map-quotient
  is-prop-Eq-quotient-map-quotient =
    is-set-set-quotient R (quotient-map R x) y

  Eq-prop-quotient-map-quotient : Prop (l1 ⊔ l2)
  Eq-prop-quotient-map-quotient =
    ( Eq-quotient-map-quotient , is-prop-Eq-quotient-map-quotient)

module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A) (x : A)
  where

  is-torsorial-Eq-quotient-map-quotient :
    is-torsorial (Eq-quotient-map-quotient R x)
  pr1 is-torsorial-Eq-quotient-map-quotient =
    ( quotient-map R x , refl)
  pr2 is-torsorial-Eq-quotient-map-quotient (y , H) =
    eq-type-subtype (Eq-prop-quotient-map-quotient R x) H
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  Σ-quotient-Set : UU (l1 ⊔ l2)
  Σ-quotient-Set =
    Σ (set-quotient R) (type-subtype ∘ subtype-set-quotient R)

  map-Σ-quotient-Set : Σ-quotient-Set → A
  map-Σ-quotient-Set (X , x , x∈X) = x


  -- postulate
  --   lemma-quotient-Set :
  --     (x : A) → is-in-equivalence-class-set-quotient R (quotient-map R x) x
  lemma-quotient-Set :
    (x : A) → is-in-equivalence-class-set-quotient R (quotient-map R x) x
  lemma-quotient-Set x =
    {!!}

  map-split-Σ-quotient-Set : A → Σ-quotient-Set
  map-split-Σ-quotient-Set x =
    ( quotient-map R x , x , lemma-quotient-Set x)

  lemma-contr-map-Σ-quotient-Set :
    (x : A) (y : fiber map-Σ-quotient-Set x) →
    (map-split-Σ-quotient-Set x , refl) ＝ y
  lemma-contr-map-Σ-quotient-Set x ((Y , y , y∈Y) , H) =
    eq-pair-Σ
      ( eq-pair-Σ {!!} {!!})
      {!!}

  is-contr-map-Σ-quotient-Set : is-contr-map map-Σ-quotient-Set
  is-contr-map-Σ-quotient-Set x =
    ( ( map-split-Σ-quotient-Set x , refl) ,
      ( lemma-contr-map-Σ-quotient-Set x))

  is-section-map-Σ-quotient-Set :
    map-Σ-quotient-Set ∘ map-split-Σ-quotient-Set ~ id
  is-section-map-Σ-quotient-Set x = refl

  is-retraction-map-Σ-quotient-Set :
    map-split-Σ-quotient-Set ∘ map-Σ-quotient-Set ~ id
  is-retraction-map-Σ-quotient-Set (X , x , x∈X) =
    eq-pair-Σ
      ( α)
      ( eq-pair-Σ
        {!!}
        {!!})
    where

    α : quotient-map R x ＝ X
    α = {!!}


  is-equiv-map-Σ-quotient-Set : is-equiv map-Σ-quotient-Set
  is-equiv-map-Σ-quotient-Set =
    is-equiv-is-invertible
      ( map-split-Σ-quotient-Set)
      ( is-section-map-Σ-quotient-Set)
      ( is-retraction-map-Σ-quotient-Set)
```

## See also

- [Set coequalizers](foundation.set-coequalizers.md) for an equivalent notion
  implemented here using set quotients.
