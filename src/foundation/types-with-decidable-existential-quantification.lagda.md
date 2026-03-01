# Types with decidable existential quantification

```agda
module foundation.types-with-decidable-existential-quantification where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-embeddings
open import foundation.decidable-equality
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-dense-equality
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.logical-operations-booleans
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import logic.double-negation-dense-maps
open import logic.propositionally-decidable-maps
open import logic.propositionally-decidable-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X`
{{#concept "has decidable existential quantification" Disambiguation="on type" Agda=has-decidable-∃}}
if for every [decidable type family](foundation.decidable-type-families.md) `P`,
there [exists](foundation.existential-quantification.md) an element in some
fiber of `P`, or `P` is the empty family. In other words, we have a witness of
type

```text
  (P : decidable-family X) → is-decidable (∃ x. P x).
```

## Definitions

### The predicate of having decidable existential quantification

```agda
has-decidable-∃-Level : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-∃-Level l2 X =
  (P : decidable-family l2 X) →
  is-decidable (exists-structure X (family-decidable-family P))

has-decidable-∃ : {l1 : Level} → UU l1 → UUω
has-decidable-∃ X = {l2 : Level} → has-decidable-∃-Level l2 X

module _
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-prop-has-decidable-∃-Level : is-prop (has-decidable-∃-Level l2 X)
  is-prop-has-decidable-∃-Level =
    is-prop-Π
      ( λ P →
        is-prop-is-decidable
          ( is-prop-exists-structure X (family-decidable-family P)))

  has-decidable-∃-level-Prop : Prop (l1 ⊔ lsuc l2)
  pr1 has-decidable-∃-level-Prop = has-decidable-∃-Level l2 X
  pr2 has-decidable-∃-level-Prop = is-prop-has-decidable-∃-Level
```

### The predicate of having small decidable existential quantification

```agda
has-decidable-∃-bool : {l1 : Level} → UU l1 → UU l1
has-decidable-∃-bool X =
  (b : X → bool) → is-decidable (exists-structure X (is-true ∘ b))
```

### The type of types with decidable existential quantification

```agda
record Type-With-Decidable-∃ (l : Level) : UUω
  where
  field
    type-Type-With-Decidable-∃ : UU l

    has-decidable-∃-type-Type-With-Decidable-∃ :
      has-decidable-∃ type-Type-With-Decidable-∃

open Type-With-Decidable-∃ public
```

### The predicate of having decidable existential quantification on subtypes

```agda
has-decidable-exists-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-exists-Level l2 X =
  (P : decidable-subtype l2 X) →
  is-decidable (exists X (subtype-decidable-subtype P))

has-decidable-exists : {l1 : Level} → UU l1 → UUω
has-decidable-exists X =
  {l2 : Level} → has-decidable-exists-Level l2 X
```

### The predicate of pointedly having decidable existential quantification

```agda
has-decidable-∃-pointed-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-∃-pointed-Level l2 X =
  ( P : decidable-family l2 X) →
  exists-structure X
    ( λ x₀ →
      family-decidable-family P x₀ → (x : X) → family-decidable-family P x)

has-decidable-∃-pointed : {l1 : Level} → UU l1 → UUω
has-decidable-∃-pointed X = {l2 : Level} → has-decidable-∃-pointed-Level l2 X
```

### The predicate of pointedly having decidable existential quantification on subtypes

```agda
has-decidable-exists-pointed-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-exists-pointed-Level l2 X =
  ( P : decidable-subtype l2 X) →
  exists-structure X
    ( λ x₀ →
      is-in-decidable-subtype P x₀ → (x : X) → is-in-decidable-subtype P x)

has-decidable-exists-pointed : {l1 : Level} → UU l1 → UUω
has-decidable-exists-pointed X =
  {l2 : Level} → has-decidable-exists-pointed-Level l2 X
```

### The small predicate of pointedly having decidable existential quantification

```agda
has-decidable-∃-pointed-bool : {l : Level} → UU l → UU l
has-decidable-∃-pointed-bool X =
  (b : X → bool) →
  exists-structure X (λ x₀ → is-true (b x₀) → (x : X) → is-true (b x))

has-decidable-∃-pointed-bool' : {l : Level} → UU l → UU l
has-decidable-∃-pointed-bool' X =
  (b : X → bool) →
  exists-structure X (λ x₀ → is-false (b x₀) → (x : X) → is-false (b x))
```

## Properties

### Types with decidable existential quantification are propositionally decidable

```agda
abstract
  is-inhabited-or-empty-has-decidable-∃-Level :
    {l1 l2 : Level} {X : UU l1} →
    has-decidable-∃-Level l2 X → is-inhabited-or-empty X
  is-inhabited-or-empty-has-decidable-∃-Level {l2 = l2} h =
    is-inhabited-or-empty-is-decidable-trunc-Prop
      ( is-decidable-equiv'
        ( equiv-trunc-Prop
          ( right-unit-law-Σ-is-contr (λ _ → is-contr-raise-unit)))
        ( h ((λ _ → raise-unit l2) , (λ _ → inl raise-star))))

  is-inhabited-or-empty-has-decidable-∃ :
    {l1 : Level} {X : UU l1} → has-decidable-∃ X → is-inhabited-or-empty X
  is-inhabited-or-empty-has-decidable-∃ f =
    is-inhabited-or-empty-is-decidable-trunc-Prop
      ( is-decidable-equiv'
        ( equiv-trunc-Prop (right-unit-law-Σ-is-contr (λ _ → is-contr-unit)))
        ( f ((λ _ → unit) , (λ _ → inl star))))

  is-inhabited-or-empty-merely-has-decidable-∃-Level :
    {l1 l2 : Level} {X : UU l1} →
    type-trunc-Prop (has-decidable-∃-Level l2 X) →
    is-inhabited-or-empty X
  is-inhabited-or-empty-merely-has-decidable-∃-Level {X = X} =
    rec-trunc-Prop
      ( is-inhabited-or-empty-Prop X)
      ( is-inhabited-or-empty-has-decidable-∃-Level)
```

### Decidable Σ-types imply decidable existential quantification

```agda
abstract
  has-decidable-∃-Level-has-decidable-Σ-Level :
    {l1 l2 : Level} {X : UU l1} →
    has-decidable-Σ-Level l2 X → has-decidable-∃-Level l2 X
  has-decidable-∃-Level-has-decidable-Σ-Level h P =
    is-decidable-trunc-Prop-is-decidable (h P)

  has-decidable-∃-has-decidable-Σ :
    {l1 : Level} {X : UU l1} →
    has-decidable-Σ X → has-decidable-∃ X
  has-decidable-∃-has-decidable-Σ h P =
    is-decidable-trunc-Prop-is-decidable (h P)
```

### Equivalence of the different notions of having decidable existential quantification

#### Types with decidable existential quantification on subtypes have decidable existential quantification

```agda
abstract
  has-decidable-∃-has-decidable-exists :
    {l1 : Level} {X : UU l1} →
    has-decidable-exists X → has-decidable-∃ X
  has-decidable-∃-has-decidable-exists f P =
    map-coproduct
      ( map-trunc-Prop
        ( λ xp →
          pr1 xp ,
          rec-coproduct
            ( id)
            ( ex-falso ∘ pr2 xp)
            ( is-decidable-decidable-family P (pr1 xp))))
      ( λ nxp xp →
        nxp
          ( map-trunc-Prop
            ( λ xp →
              pr1 xp ,
              intro-double-negation (pr2 xp))
            ( xp)))
      ( f ( λ x →
            neg-type-Decidable-Prop
              ( ¬ (family-decidable-family P x))
              ( is-decidable-neg (is-decidable-decidable-family P x))))
```

#### A type has decidable existential quantification if and only if it satisfies the small predicate of having decidable existential quantification

```agda
module _
  {l : Level} {X : UU l}
  where abstract

  has-decidable-exists-has-decidable-∃-bool :
    has-decidable-∃-bool X → has-decidable-exists X
  has-decidable-exists-has-decidable-∃-bool f P =
    is-decidable-equiv
      ( equiv-trunc-Prop
        ( equiv-tot (compute-equiv-bool-Decidable-Prop ∘ P)))
      ( f (bool-Decidable-Prop ∘ P))

  has-decidable-∃-has-decidable-∃-bool :
    has-decidable-∃-bool X → has-decidable-∃ X
  has-decidable-∃-has-decidable-∃-bool f =
    has-decidable-∃-has-decidable-exists
      ( has-decidable-exists-has-decidable-∃-bool
        ( f))

  has-decidable-∃-bool-has-decidable-exists :
    has-decidable-exists X → has-decidable-∃-bool X
  has-decidable-∃-bool-has-decidable-exists f P =
    f (is-true-Decidable-Prop ∘ P)

  has-decidable-∃-bool-has-decidable-∃ :
    has-decidable-∃ X → has-decidable-∃-bool X
  has-decidable-∃-bool-has-decidable-∃ f P =
    f (is-true ∘ P , λ x → has-decidable-equality-bool (P x) true)
```

#### A pointed type with decidable existential quantification has pointedly decidable existential quantification

```agda
abstract
  has-decidable-∃-pointed-has-decidable-∃-has-element :
    {l : Level} {X : UU l} →
    X → has-decidable-∃ X → has-decidable-∃-pointed X
  has-decidable-∃-pointed-has-decidable-∃-has-element x₀ f P =
    rec-coproduct
      ( map-trunc-Prop (λ xr → (pr1 xr , ex-falso ∘ pr2 xr)))
      ( λ nx →
        intro-exists
          ( x₀)
          ( λ _ x →
            rec-coproduct
              ( id)
              ( λ npx → ex-falso (nx (intro-exists x npx)))
              ( is-decidable-decidable-family P x)))
      ( f (neg-decidable-family P))
```

#### The two small predicates of pointedly having decidable existential quantification are equivalent

```agda
abstract
  flip-has-decidable-∃-pointed-bool :
    {l : Level} {X : UU l} →
    has-decidable-∃-pointed-bool' X →
    has-decidable-∃-pointed-bool X
  flip-has-decidable-∃-pointed-bool H b =
    map-trunc-Prop
      ( λ xb →
        pr1 xb ,
        ( λ p x →
          is-true-is-false-neg-bool
            ( pr2 xb
              ( is-false-is-true-neg-bool
                ( is-involution-neg-bool (b (pr1 xb)) ∙ p))
              ( x))))
      ( H (neg-bool ∘ b))
```

```agda
abstract
  flip-has-decidable-∃-pointed-bool' :
    {l : Level} {X : UU l} →
    has-decidable-∃-pointed-bool X →
    has-decidable-∃-pointed-bool' X
  flip-has-decidable-∃-pointed-bool' H b =
    map-trunc-Prop
      ( λ xb →
        pr1 xb ,
        ( λ p x →
          is-false-is-true-neg-bool
            ( pr2 xb
              ( is-true-is-false-neg-bool
                ( is-involution-neg-bool (b (pr1 xb)) ∙ p))
              ( x))))
      ( H (neg-bool ∘ b))
```

#### A type has pointedly decidable existential quantification if and only if it pointedly has small decidable existential quantification

```agda
abstract
  has-decidable-exists-pointed-has-decidable-∃-pointed-bool :
    {l : Level} {X : UU l} →
    has-decidable-∃-pointed-bool X →
    has-decidable-exists-pointed X
  has-decidable-exists-pointed-has-decidable-∃-pointed-bool
    f P =
    map-trunc-Prop
      ( λ xb →
        pr1 xb ,
        ( λ Px₀ x →
          map-inv-equiv
            ( compute-equiv-bool-Decidable-Prop (P x))
              ( pr2 xb
                ( map-equiv
                  ( compute-equiv-bool-Decidable-Prop (P (pr1 xb)))
                  ( Px₀))
                ( x))))
      ( f (bool-Decidable-Prop ∘ P))

abstract
  has-decidable-∃-pointed-bool-has-decidable-exists-pointed :
    {l : Level} {X : UU l} →
    has-decidable-exists-pointed X →
    has-decidable-∃-pointed-bool X
  has-decidable-∃-pointed-bool-has-decidable-exists-pointed
    f b =
    f (is-true-Decidable-Prop ∘ b)
```

#### Types that pointedly have decidable existential quantification on subtypes has pointedly decidable existential quantification

```agda
abstract
  has-decidable-∃-pointed-has-decidable-exists-pointed :
    {l1 : Level} {X : UU l1} →
    has-decidable-exists-pointed X →
    has-decidable-∃-pointed X
  has-decidable-∃-pointed-has-decidable-exists-pointed
    {X = X} f P =
      map-trunc-Prop
        ( λ g →
          ( pr1 g) ,
          ( λ p x →
            rec-coproduct
              ( id)
              ( ex-falso ∘ pr2 g (intro-double-negation p) x)
              ( is-decidable-decidable-family P x)))
        ( f
          ( λ x →
            neg-type-Decidable-Prop
              ( ¬ (family-decidable-family P x))
              ( is-decidable-neg (is-decidable-decidable-family P x))))
```

#### Types that pointedly have decidable existential quantification have decidable existential quantification

```agda
abstract
  has-decidable-∃-has-decidable-∃-pointed :
    {l1 : Level} {X : UU l1} →
    has-decidable-∃-pointed X →
    has-decidable-∃ X
  has-decidable-∃-has-decidable-∃-pointed {X = X} f P =
    rec-trunc-Prop
      ( is-decidable-Prop
        ( exists-structure-Prop X (family-decidable-family P)))
      ( λ g →
        rec-coproduct
          ( λ px₀ → inl (intro-exists (pr1 g) px₀))
          ( λ npx₀ →
            inr
              ( λ ex →
                rec-trunc-Prop
                  ( empty-Prop)
                  ( λ xp →
                    pr2 g npx₀ (pr1 xp) (pr2 xp))
                  ( ex)))
          ( is-decidable-decidable-family P (pr1 g)))
      ( f (neg-decidable-family P))
```

### Having decidable existential quantification transfers along double negation dense maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (h : X ↠¬¬ Y)
  where abstract

  has-decidable-∃-double-negation-dense-map :
    has-decidable-∃ X → has-decidable-∃ Y
  has-decidable-∃-double-negation-dense-map f P =
    map-coproduct
      ( map-trunc-Prop
        ( λ xp → map-double-negation-dense-map h (pr1 xp) , pr2 xp))
      ( λ nxpf yp →
        rec-trunc-Prop
          ( empty-Prop)
          ( λ yp' →
            is-double-negation-dense-map-double-negation-dense-map
              ( h)
              ( pr1 yp')
              ( λ xr →
                nxpf
                  ( unit-trunc-Prop
                    ( pr1 xr ,
                      tr
                        ( family-decidable-family P)
                        ( inv (pr2 xr))
                        ( pr2 yp')))))
          ( yp))
      ( f (base-change-decidable-family P (map-double-negation-dense-map h)))
```

### Having decidable existential quantification transfers along surjections

```agda
abstract
  has-decidable-∃-surjection :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    X ↠ Y →
    has-decidable-∃ X → has-decidable-∃ Y
  has-decidable-∃-surjection h =
    has-decidable-∃-double-negation-dense-map
      ( double-negation-dense-map-surjection h)
```

### Types with decidable existential quantification are closed under retracts

```agda
abstract
  has-decidable-∃-retract :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    Y retract-of X → has-decidable-∃ X → has-decidable-∃ Y
  has-decidable-∃-retract R =
    has-decidable-∃-double-negation-dense-map
      ( double-negation-dense-map-retract R)
```

### Types with decidable existential quantification are closed under equivalences

```agda
abstract
  has-decidable-∃-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    Y ≃ X → has-decidable-∃ X → has-decidable-∃ Y
  has-decidable-∃-equiv e =
    has-decidable-∃-retract (retract-equiv e)

  has-decidable-∃-equiv' :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    X ≃ Y → has-decidable-∃ X → has-decidable-∃ Y
  has-decidable-∃-equiv' e =
    has-decidable-∃-retract (retract-inv-equiv e)
```

### Decidable types with double negation dense equality have decidable existential quantification

```agda
abstract
  has-decidable-∃-is-decidable-has-double-negation-dense-equality :
    {l1 : Level} {X : UU l1} →
    has-double-negation-dense-equality X →
    is-decidable X → has-decidable-∃ X
  has-decidable-∃-is-decidable-has-double-negation-dense-equality
    H d =
    has-decidable-∃-has-decidable-Σ
      ( has-decidable-Σ-is-decidable-has-double-negation-dense-equality H d)

  has-decidable-∃-is-inhabited-or-empty-has-double-negation-dense-equality :
    {l1 : Level} {X : UU l1} →
    has-double-negation-dense-equality X →
    is-inhabited-or-empty X → has-decidable-∃ X
  has-decidable-∃-is-inhabited-or-empty-has-double-negation-dense-equality
    H d P =
    is-decidable-trunc-Prop-is-inhabited-or-empty
      ( is-inhabited-or-empty-Σ-has-double-negation-dense-equality-base H d
        ( λ x →
          is-inhabited-or-empty-is-decidable
            ( is-decidable-decidable-family P x)))
```

### Decidable subtypes of types with decidable existential quantification have decidable existential quantification

```agda
abstract
  has-decidable-∃-type-decidable-subtype :
    {l1 l2 : Level} {X : UU l1} →
    has-decidable-∃ X →
    (P : decidable-subtype l2 X) →
    has-decidable-∃ (type-decidable-subtype P)
  has-decidable-∃-type-decidable-subtype {X = X} f P Q =
    is-decidable-equiv
      ( equiv-trunc-Prop associative-Σ)
      ( f ( comp-decidable-family-decidable-subtype P
            ( base-change-decidable-family Q ∘ pair)))

  has-decidable-∃-decidable-emb :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    has-decidable-∃ X → (Y ↪ᵈ X) → has-decidable-∃ Y
  has-decidable-∃-decidable-emb f h =
    has-decidable-∃-equiv'
      ( compute-type-decidable-subtype-decidable-emb h)
      ( has-decidable-∃-type-decidable-subtype f
        ( decidable-subtype-decidable-emb h))
```

### The empty type has decidable existential quantification

```agda
abstract
  has-decidable-∃-empty : has-decidable-∃ empty
  has-decidable-∃-empty =
    has-decidable-∃-has-decidable-Σ has-decidable-Σ-empty
```

### The unit type has decidable existential quantification

```agda
abstract
  has-decidable-∃-unit : has-decidable-∃ unit
  has-decidable-∃-unit =
    has-decidable-∃-has-decidable-Σ has-decidable-Σ-unit
```

### Coproducts of types with decidable existential quantification

Coproducts of types with decidable existential quantification have decidable
existential quantification. Conversely, if the coproduct has decidable
existential quantification and a summand has an element, then that summand also
has decidable existential quantification.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where abstract

  has-decidable-∃-coproduct :
    has-decidable-∃ X →
    has-decidable-∃ Y →
    has-decidable-∃ (X + Y)
  has-decidable-∃-coproduct f g P =
    rec-coproduct
      ( λ xp →
        inl
          ( map-trunc-Prop
            ( λ xp' → inl (pr1 xp') , pr2 xp')
            ( xp)))
      ( λ nx →
        rec-coproduct
          ( λ yp →
            inl
              ( map-trunc-Prop
                ( λ yp' → inr (pr1 yp') , pr2 yp')
                ( yp)))
          ( λ ny →
            inr
              ( λ e →
                rec-trunc-Prop
                  empty-Prop
                  ( λ where
                    (inl x , p) → nx (unit-trunc-Prop (x , p))
                    (inr y , p) → ny (unit-trunc-Prop (y , p)))
                  ( e)))
          ( g (base-change-decidable-family P inr)))
      ( f (base-change-decidable-family P inl))

  has-decidable-∃-left-summand-coproduct :
    has-decidable-∃ (X + Y) →
    X → has-decidable-∃ X
  has-decidable-∃-left-summand-coproduct f x =
    has-decidable-∃-retract (retract-left-summand-coproduct x) f

  has-decidable-∃-right-summand-coproduct :
    has-decidable-∃ (X + Y) →
    Y → has-decidable-∃ Y
  has-decidable-∃-right-summand-coproduct f y =
    has-decidable-∃-retract (retract-right-summand-coproduct y) f
```

### Dependent sums of types with decidable existential quantification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where abstract

  has-decidable-∃-Σ :
    has-decidable-∃ A →
    ((x : A) → has-decidable-∃ (B x)) →
    has-decidable-∃ (Σ A B)
  has-decidable-∃-Σ f g P =
    is-decidable-iff
      ( λ e →
        apply-universal-property-trunc-Prop
          ( e)
          ( trunc-Prop (Σ (Σ A B) (family-decidable-family P)))
          ( λ (x , t) → map-trunc-Prop (λ (y , p) → (x , y) , p) t))
      ( map-trunc-Prop
        ( λ ((x , y) , p) → (x , unit-trunc-Prop (y , p))))
      ( f
        ( ( λ x →
            exists-structure (B x) (λ y → family-decidable-family P (x , y))) ,
          ( λ x → g x (base-change-decidable-family P (x ,_)))))
```

### The total space of decidable families of types with double negation dense equality over types with decidable existential quantification have decidable existential quantification

```agda
abstract
  has-decidable-∃-Σ-decidable-family-has-double-negation-dense-equality :
    {l1 l2 : Level} {X : UU l1} →
    has-decidable-∃ X →
    (P : decidable-family l2 X) →
    ( (x : X) →
      has-double-negation-dense-equality (family-decidable-family P x)) →
    has-decidable-∃ (Σ X (family-decidable-family P))
  has-decidable-∃-Σ-decidable-family-has-double-negation-dense-equality
    f P H =
    has-decidable-∃-Σ f
      ( λ x →
        has-decidable-∃-is-decidable-has-double-negation-dense-equality
          ( H x)
          ( is-decidable-decidable-family P x))
```

### Dependent sums of types with decidable existential quantification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where abstract

  has-decidable-∃-base-has-decidable-∃-Σ :
    has-decidable-∃ (Σ A B) →
    ((x : A) → B x) →
    has-decidable-∃ A
  has-decidable-∃-base-has-decidable-∃-Σ f s =
    has-decidable-∃-retract (retract-base-Σ-section-family s) f
```

### Products of types with decidable existential quantification

```agda
abstract
  has-decidable-∃-product :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    has-decidable-∃ A → has-decidable-∃ B → has-decidable-∃ (A × B)
  has-decidable-∃-product f g = has-decidable-∃-Σ f (λ _ → g)
```

### Factors of products with decidable existential quantification

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where abstract

  has-decidable-∃-left-factor-product :
    has-decidable-∃ (X × Y) → Y → has-decidable-∃ X
  has-decidable-∃-left-factor-product f y =
    has-decidable-∃-retract (retract-left-factor-product y) f

  has-decidable-∃-right-factor-product :
    has-decidable-∃ (X × Y) → X → has-decidable-∃ Y
  has-decidable-∃-right-factor-product f x =
    has-decidable-∃-retract (retract-right-factor-product x) f
```

### Standard finite types have decidable existential quantification

```agda
abstract
  has-decidable-∃-Fin : (n : ℕ) → has-decidable-∃ (Fin n)
  has-decidable-∃-Fin n =
    has-decidable-∃-has-decidable-Σ (has-decidable-Σ-Fin n)
```

### Types equipped with a counting have decidable existential quantification

```agda
abstract
  has-decidable-∃-count :
    {l : Level} {X : UU l} → count X → has-decidable-∃ X
  has-decidable-∃-count f =
    has-decidable-∃-has-decidable-Σ (has-decidable-Σ-count f)
```

### The booleans have decidable existential quantification

```agda
abstract
  has-decidable-∃-bool' : has-decidable-∃ bool
  has-decidable-∃-bool' =
    has-decidable-∃-has-decidable-Σ has-decidable-Σ-bool'
```

### The subuniverse of propositions has decidable existential quantification

```agda
abstract
  has-decidable-∃-Prop : {l : Level} → has-decidable-∃ (Prop l)
  has-decidable-∃-Prop {l} =
    has-decidable-∃-has-decidable-Σ (has-decidable-Σ-Prop {l})
```

### Decidable existential quantification on the domain yields propositionally decidable fibers

```agda
abstract
  is-inhabited-or-empty-map-has-decidable-∃-Level :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    has-decidable-∃-Level l2 A →
    has-decidable-equality B →
    (f : A → B) →
    is-inhabited-or-empty-map f
  is-inhabited-or-empty-map-has-decidable-∃-Level h d f y =
    is-inhabited-or-empty-is-decidable-trunc-Prop
      ( h ( (λ x → f x ＝ y) , (λ x → d (f x) y)))
```

## See also

- [Types with decidable Π-types](foundation.types-with-decidable-dependent-product-types.md)
- [Types with decidable universal quantifications](foundation.types-with-decidable-universal-quantifications.md)
