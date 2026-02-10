# Types with decidable Σ-types

```agda
module foundation.types-with-decidable-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-embeddings
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-dense-equality
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-operations-booleans
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import logic.double-negation-dense-maps

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X`
{{#concept "has decidable Σ-types" Disambiguation="on type" Agda=has-decidable-Σ}}
if for every [decidable type family](foundation.decidable-type-families.md) `P`,
we can construct an element in some fiber of `P` or determine that `P` is the
empty family. In other words, we have a witness of type

```text
  (P : decidable-family X) → is-decidable (Σ x. P x).
```

**Terminology.** In the terminology of Martín Escardó, a type that has decidable
Σ-types for families of propositions is referred to as _searchable_,
_exhaustively searchable_, _exhaustibly searchable_, _exhaustible_,
_omniscient_, _satisfying the principle of omniscience_, _compact_, or
_Σ-compact_. {{#cite Esc08}} {{#cite TypeTopology}}

## Definitions

### The predicate of having decidable Σ-types

```agda
has-decidable-Σ-Level : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-Σ-Level l2 X =
  (P : decidable-family l2 X) → is-decidable (Σ X (family-decidable-family P))

has-decidable-Σ : {l1 : Level} → UU l1 → UUω
has-decidable-Σ X = {l2 : Level} → has-decidable-Σ-Level l2 X
```

### The predicate of having small decidable Σ-types

```agda
has-decidable-Σ-bool : {l1 : Level} → UU l1 → UU l1
has-decidable-Σ-bool X = (b : X → bool) → is-decidable (Σ X (is-true ∘ b))
```

### The type of types with decidable Σ-types

```agda
record Type-With-Decidable-Σ (l : Level) : UUω
  where
  field
    type-Type-With-Decidable-Σ : UU l

    has-decidable-Σ-type-Type-With-Decidable-Σ :
      has-decidable-Σ type-Type-With-Decidable-Σ

open Type-With-Decidable-Σ public
```

### The predicate of having decidable Σ-types on subtypes

```agda
has-decidable-type-subtype-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-type-subtype-Level l2 X =
  (P : decidable-subtype l2 X) → is-decidable (Σ X (is-in-decidable-subtype P))

has-decidable-type-subtype : {l1 : Level} → UU l1 → UUω
has-decidable-type-subtype X =
  {l2 : Level} → has-decidable-type-subtype-Level l2 X
```

### The predicate of pointedly having decidable Σ-types

```agda
has-decidable-Σ-pointed-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-Σ-pointed-Level l2 X =
  ( P : decidable-family l2 X) →
  Σ X
    ( λ x₀ →
      family-decidable-family P x₀ → (x : X) → family-decidable-family P x)

has-decidable-Σ-pointed : {l1 : Level} → UU l1 → UUω
has-decidable-Σ-pointed X = {l2 : Level} → has-decidable-Σ-pointed-Level l2 X
```

### The predicate of pointedly having decidable Σ-types on subtypes

```agda
has-decidable-type-subtype-pointed-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-type-subtype-pointed-Level l2 X =
  ( P : decidable-subtype l2 X) →
  Σ X
    ( λ x₀ →
      is-in-decidable-subtype P x₀ → (x : X) → is-in-decidable-subtype P x)

has-decidable-type-subtype-pointed : {l1 : Level} → UU l1 → UUω
has-decidable-type-subtype-pointed X =
  {l2 : Level} → has-decidable-type-subtype-pointed-Level l2 X
```

### The small predicate of pointedly having decidable Σ-types

```agda
has-decidable-Σ-pointed-bool : {l : Level} → UU l → UU l
has-decidable-Σ-pointed-bool X =
  (b : X → bool) → Σ X (λ x₀ → is-true (b x₀) → (x : X) → is-true (b x))

has-decidable-Σ-pointed-bool' : {l : Level} → UU l → UU l
has-decidable-Σ-pointed-bool' X =
  (b : X → bool) → Σ X (λ x₀ → is-false (b x₀) → (x : X) → is-false (b x))
```

## Properties

### Types with decidable Σ-types are decidable

```agda
is-decidable-type-has-decidable-Σ :
  {l1 : Level} {X : UU l1} → has-decidable-Σ X → is-decidable X
is-decidable-type-has-decidable-Σ f =
  is-decidable-equiv'
    ( right-unit-law-product)
    ( f ((λ _ → unit) , (λ _ → inl star)))
```

### Types with decidable Σ-types on subtypes have decidable Σ-types

```agda
abstract
  has-decidable-Σ-has-decidable-type-subtype :
    {l1 : Level} {X : UU l1} →
    has-decidable-type-subtype X → has-decidable-Σ X
  has-decidable-Σ-has-decidable-type-subtype f P =
    map-coproduct
      ( λ xp →
        pr1 xp ,
        rec-coproduct
          ( id)
          ( ex-falso ∘ pr2 xp)
          ( is-decidable-decidable-family P (pr1 xp)))
      ( λ nxp xp → nxp (pr1 xp , intro-double-negation (pr2 xp)))
      ( f ( λ x →
            neg-type-Decidable-Prop
              ( ¬ (family-decidable-family P x))
              ( is-decidable-neg (is-decidable-decidable-family P x))))
```

### Equivalence of the different notions of having decidable Σ-types

###### A type has decidable Σ-types if and only if it satisfies the small predicate of having decidable Σ-types

```agda
module _
  {l : Level} {X : UU l}
  where

  has-decidable-type-subtype-has-decidable-Σ-bool :
    has-decidable-Σ-bool X → has-decidable-type-subtype X
  has-decidable-type-subtype-has-decidable-Σ-bool f P =
    is-decidable-equiv
      ( equiv-tot (compute-equiv-bool-Decidable-Prop ∘ P))
      ( f (bool-Decidable-Prop ∘ P))

  abstract
    has-decidable-Σ-has-decidable-Σ-bool :
      has-decidable-Σ-bool X → has-decidable-Σ X
    has-decidable-Σ-has-decidable-Σ-bool f =
      has-decidable-Σ-has-decidable-type-subtype
        ( has-decidable-type-subtype-has-decidable-Σ-bool
          ( f))

  has-decidable-Σ-bool-has-decidable-type-subtype :
    has-decidable-type-subtype X → has-decidable-Σ-bool X
  has-decidable-Σ-bool-has-decidable-type-subtype f P =
    f (is-true-Decidable-Prop ∘ P)

  has-decidable-Σ-bool-has-decidable-Σ :
    has-decidable-Σ X → has-decidable-Σ-bool X
  has-decidable-Σ-bool-has-decidable-Σ f P =
    f (is-true ∘ P , λ x → has-decidable-equality-bool (P x) true)
```

#### A pointed type with decidable Σ-types has pointedly decidable Σ-types

```agda
has-decidable-Σ-pointed-has-decidable-Σ-has-element :
  {l : Level} {X : UU l} →
  X → has-decidable-Σ X → has-decidable-Σ-pointed X
has-decidable-Σ-pointed-has-decidable-Σ-has-element x₀ f P =
  rec-coproduct
    ( λ xr → (pr1 xr , ex-falso ∘ pr2 xr))
    ( λ nx →
      ( x₀ ,
        λ _ x →
        rec-coproduct
          ( id)
          ( λ npx → ex-falso (nx (x , npx)))
          ( is-decidable-decidable-family P x)))
    ( f (neg-decidable-family P))
```

#### The two small predicates of pointedly having decidable Σ-types are equivalent

```agda
flip-has-decidable-Σ-pointed-bool :
  {l : Level} {X : UU l} →
  has-decidable-Σ-pointed-bool' X →
  has-decidable-Σ-pointed-bool X
pr1 (flip-has-decidable-Σ-pointed-bool H b) =
  pr1 (H (neg-bool ∘ b))
pr2 (flip-has-decidable-Σ-pointed-bool H b) p x =
  is-true-is-false-neg-bool
    ( pr2
      ( H (neg-bool ∘ b))
      ( is-false-is-true-neg-bool
        ( is-involution-neg-bool (b (pr1 (H (neg-bool ∘ b)))) ∙ p))
      ( x))

flip-has-decidable-Σ-pointed-bool' :
  {l : Level} {X : UU l} →
  has-decidable-Σ-pointed-bool X →
  has-decidable-Σ-pointed-bool' X
pr1 (flip-has-decidable-Σ-pointed-bool' H b) =
  pr1 (H (neg-bool ∘ b))
pr2 (flip-has-decidable-Σ-pointed-bool' H b) p x =
  is-false-is-true-neg-bool
    ( pr2
      ( H (neg-bool ∘ b))
      ( is-true-is-false-neg-bool
        ( is-involution-neg-bool (b (pr1 (H (neg-bool ∘ b)))) ∙ p))
      ( x))
```

#### A type has pointedly decidable Σ-types if and only if it pointedly has small decidable Σ-types

```agda
abstract
  has-decidable-type-subtype-pointed-has-decidable-Σ-pointed-bool :
    {l : Level} {X : UU l} →
    has-decidable-Σ-pointed-bool X →
    has-decidable-type-subtype-pointed X
  has-decidable-type-subtype-pointed-has-decidable-Σ-pointed-bool
    f P =
    ( pr1 (f (bool-Decidable-Prop ∘ P))) ,
    ( λ Px₀ x →
      map-inv-equiv
        ( compute-equiv-bool-Decidable-Prop (P x))
          ( pr2
            ( f (bool-Decidable-Prop ∘ P))
            ( map-equiv
              ( compute-equiv-bool-Decidable-Prop
                ( P (pr1 (f (bool-Decidable-Prop ∘ P)))))
              ( Px₀))
            ( x)))

has-decidable-Σ-pointed-bool-has-decidable-type-subtype-pointed :
  {l : Level} {X : UU l} →
  has-decidable-type-subtype-pointed X →
  has-decidable-Σ-pointed-bool X
has-decidable-Σ-pointed-bool-has-decidable-type-subtype-pointed
  f b =
  f (is-true-Decidable-Prop ∘ b)
```

#### Types that pointedly have decidable Σ-types on subtypes has pointedly decidable Σ-types

```agda
abstract
  has-decidable-Σ-pointed-has-decidable-type-subtype-pointed :
    {l1 : Level} {X : UU l1} →
    has-decidable-type-subtype-pointed X →
    has-decidable-Σ-pointed X
  has-decidable-Σ-pointed-has-decidable-type-subtype-pointed
    {X = X} f P =
      ( pr1 g) ,
      ( λ p x →
        rec-coproduct
          ( id)
          ( ex-falso ∘ pr2 g (intro-double-negation p) x)
          ( is-decidable-decidable-family P x))
      where
        g : Σ X
              ( λ x₀ →
                ¬¬ (family-decidable-family P x₀) →
                (x : X) → ¬¬ (family-decidable-family P x))
        g =
          f
          ( λ x →
            neg-type-Decidable-Prop
              ( ¬ (family-decidable-family P x))
              ( is-decidable-neg (is-decidable-decidable-family P x)))
```

#### Types that pointedly have decidable Σ-types have decidable Σ-types

```agda
abstract
  has-decidable-Σ-has-decidable-Σ-pointed :
    {l1 : Level} {X : UU l1} →
    has-decidable-Σ-pointed X →
    has-decidable-Σ X
  has-decidable-Σ-has-decidable-Σ-pointed {X = X} f P =
    let (x₀ , dPx₀) = f (neg-decidable-family P) in
    rec-coproduct
      ( λ px₀ → inl (x₀ , px₀))
      ( λ npx₀ → inr (λ (x , p) → dPx₀ npx₀ x p))
      ( is-decidable-decidable-family P x₀)
```

### Having decidable Σ-types transfers along double negation dense maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (h : X ↠¬¬ Y)
  where

  has-decidable-Σ-double-negation-dense-map :
    has-decidable-Σ X → has-decidable-Σ Y
  has-decidable-Σ-double-negation-dense-map f P =
    map-coproduct
      ( λ xp → map-double-negation-dense-map h (pr1 xp) , pr2 xp)
      ( λ nxpf yp →
        is-double-negation-dense-map-double-negation-dense-map
          ( h)
          ( pr1 yp)
          ( λ xr →
            nxpf
              ( pr1 xr ,
                tr (family-decidable-family P) (inv (pr2 xr)) (pr2 yp))))
      ( f (base-change-decidable-family P (map-double-negation-dense-map h)))
```

### Having decidable Σ-types transfers along surjections

```agda
has-decidable-Σ-surjection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  X ↠ Y →
  has-decidable-Σ X → has-decidable-Σ Y
has-decidable-Σ-surjection h =
  has-decidable-Σ-double-negation-dense-map
    ( double-negation-dense-map-surjection h)
```

### Types with decidable Σ-types are closed under retracts

```agda
has-decidable-Σ-retract :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  Y retract-of X → has-decidable-Σ X → has-decidable-Σ Y
has-decidable-Σ-retract R =
  has-decidable-Σ-double-negation-dense-map
    ( double-negation-dense-map-retract R)
```

### Types with decidable Σ-types are closed under equivalences

```agda
has-decidable-Σ-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  Y ≃ X → has-decidable-Σ X → has-decidable-Σ Y
has-decidable-Σ-equiv e =
  has-decidable-Σ-retract (retract-equiv e)

has-decidable-Σ-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  X ≃ Y → has-decidable-Σ X → has-decidable-Σ Y
has-decidable-Σ-equiv' e =
  has-decidable-Σ-retract (retract-inv-equiv e)
```

### Decidable types with double negation dense equality have decidable Σ-types

```agda
has-decidable-Σ-is-decidable-has-double-negation-dense-equality :
  {l1 : Level} {X : UU l1} → has-double-negation-dense-equality X →
  is-decidable X → has-decidable-Σ X
has-decidable-Σ-is-decidable-has-double-negation-dense-equality
  H d P =
  is-decidable-Σ-has-double-negation-dense-equality-base H d
    ( is-decidable-decidable-family P)
```

### Decidable subtypes of types with decidable Σ-types have decidable Σ-types

```agda
has-decidable-Σ-type-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} →
  has-decidable-Σ X →
  (P : decidable-subtype l2 X) →
  has-decidable-Σ (type-decidable-subtype P)
has-decidable-Σ-type-decidable-subtype {X = X} f P Q =
  is-decidable-equiv
    ( associative-Σ)
    ( f ( comp-decidable-family-decidable-subtype P
          ( base-change-decidable-family Q ∘ pair)))

has-decidable-Σ-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  has-decidable-Σ X → Y ↪ᵈ X → has-decidable-Σ Y
has-decidable-Σ-decidable-emb f h =
  has-decidable-Σ-equiv'
    ( compute-type-decidable-subtype-decidable-emb h)
    ( has-decidable-Σ-type-decidable-subtype f
      ( decidable-subtype-decidable-emb h))
```

### The empty type has decidable Σ-types

```agda
has-decidable-Σ-empty : has-decidable-Σ empty
has-decidable-Σ-empty P = inr pr1
```

### The unit type has decidable Σ-types

```agda
has-decidable-Σ-unit : has-decidable-Σ unit
has-decidable-Σ-unit P =
  rec-coproduct
    ( inl ∘ pair star)
    ( inr ∘ map-neg pr2)
    ( is-decidable-decidable-family P star)
```

### Coproducts of types with decidable Σ-types

Coproducts of types with decidable Σ-types have decidable Σ-types. Conversely,
if the coproduct has decidable Σ-types and a summand has an element, then that
summand also has decidable Σ-types.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-decidable-Σ-coproduct :
    has-decidable-Σ X →
    has-decidable-Σ Y →
    has-decidable-Σ (X + Y)
  has-decidable-Σ-coproduct f g P =
    rec-coproduct
      ( λ xp → inl (inl (pr1 xp) , pr2 xp))
      ( λ nx →
        rec-coproduct
          ( λ yp → inl (inr (pr1 yp) , pr2 yp))
          ( λ ny →
            inr
              ( λ where
                (inl x , p) → nx (x , p)
                (inr y , p) → ny (y , p)))
          ( g (base-change-decidable-family P inr)))
      ( f (base-change-decidable-family P inl))

  has-decidable-Σ-left-summand-coproduct :
    has-decidable-Σ (X + Y) →
    X → has-decidable-Σ X
  has-decidable-Σ-left-summand-coproduct f x =
    has-decidable-Σ-retract (retract-left-summand-coproduct x) f

  has-decidable-Σ-right-summand-coproduct :
    has-decidable-Σ (X + Y) →
    Y → has-decidable-Σ Y
  has-decidable-Σ-right-summand-coproduct f y =
    has-decidable-Σ-retract (retract-right-summand-coproduct y) f
```

### Dependent sums of types with decidable Σ-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-decidable-Σ-Σ :
    has-decidable-Σ A →
    ((x : A) → has-decidable-Σ (B x)) →
    has-decidable-Σ (Σ A B)
  has-decidable-Σ-Σ f g {l} P =
    is-decidable-equiv
      ( associative-Σ)
      ( f ( ( λ x → Σ (B x) (λ y → family-decidable-family P (x , y))) ,
            ( λ x → g x (base-change-decidable-family P (x ,_)))))
```

### The total space of decidable families of types with double negation dense equality over types with decidable Σ-types have decidable Σ-types

```agda
abstract
  has-decidable-Σ-Σ-decidable-family-has-double-negation-dense-equality :
    {l1 l2 : Level} {X : UU l1} →
    has-decidable-Σ X →
    (P : decidable-family l2 X) →
    ( (x : X) →
      has-double-negation-dense-equality (family-decidable-family P x)) →
    has-decidable-Σ (Σ X (family-decidable-family P))
  has-decidable-Σ-Σ-decidable-family-has-double-negation-dense-equality
    f P H =
    has-decidable-Σ-Σ f
      ( λ x →
        has-decidable-Σ-is-decidable-has-double-negation-dense-equality
          ( H x)
          ( is-decidable-decidable-family P x))
```

### Dependent sums of types with decidable Σ-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-decidable-Σ-base-has-decidable-Σ-Σ :
    has-decidable-Σ (Σ A B) →
    ((x : A) → B x) →
    has-decidable-Σ A
  has-decidable-Σ-base-has-decidable-Σ-Σ f s =
    has-decidable-Σ-retract (retract-base-Σ-section-family s) f
```

### Products of types with decidable Σ-types

```agda
has-decidable-Σ-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-Σ A → has-decidable-Σ B → has-decidable-Σ (A × B)
has-decidable-Σ-product f g = has-decidable-Σ-Σ f (λ _ → g)
```

### Factors of products with decidable Σ-types

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-decidable-Σ-left-factor-product :
    has-decidable-Σ (X × Y) → Y → has-decidable-Σ X
  has-decidable-Σ-left-factor-product f y =
    has-decidable-Σ-retract (retract-left-factor-product y) f

  has-decidable-Σ-right-factor-product :
    has-decidable-Σ (X × Y) → X → has-decidable-Σ Y
  has-decidable-Σ-right-factor-product f x =
    has-decidable-Σ-retract (retract-right-factor-product x) f
```

### Standard finite types have decidable Σ-types

```agda
has-decidable-Σ-Fin : (n : ℕ) → has-decidable-Σ (Fin n)
has-decidable-Σ-Fin zero-ℕ = has-decidable-Σ-empty
has-decidable-Σ-Fin (succ-ℕ n) =
  has-decidable-Σ-coproduct
    ( has-decidable-Σ-Fin n)
    ( has-decidable-Σ-unit)
```

### Types equipped with a counting have decidable Σ-types

```agda
has-decidable-Σ-count :
  {l : Level} {X : UU l} → count X → has-decidable-Σ X
has-decidable-Σ-count f =
  has-decidable-Σ-equiv'
    ( equiv-count f)
    ( has-decidable-Σ-Fin (number-of-elements-count f))
```

### The booleans have decidable Σ-types

```agda
has-decidable-Σ-bool' : has-decidable-Σ bool
has-decidable-Σ-bool' =
  has-decidable-Σ-equiv' (equiv-bool-Fin-2) (has-decidable-Σ-Fin 2)
```

### The subuniverse of propositions has decidable Σ-types

```agda
has-decidable-Σ-Prop : {l : Level} → has-decidable-Σ (Prop l)
has-decidable-Σ-Prop {l} =
  has-decidable-Σ-double-negation-dense-map
    ( double-negation-dense-map-raise-prop-bool l)
    ( has-decidable-Σ-bool')
```

## References

{{#bibliography}}

## See also

- [Types with decidable existential quantifications](foundation.types-with-decidable-existential-quantifications.md)
- [Types with decidable Π-types](foundation.types-with-decidable-dependent-product-types.md)
- [Types with decidable universal quantifications](foundation.types-with-decidable-universal-quantifications.md)
