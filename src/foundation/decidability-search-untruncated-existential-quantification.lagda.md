# Σ-Decidability search

```agda
module foundation.decidability-search-untruncated-existential-quantification where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.irrefutable-equality
open import foundation.locally-small-types
open import foundation.logical-operations-booleans
open import foundation.mere-equality
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.small-types
open import foundation.surjective-maps
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types

open import logic.complements-decidable-subtypes
open import logic.de-morgan-subtypes
open import logic.double-negation-dense-maps
open import logic.propositionally-decidable-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X` has
{{#concept "Σ-decidability search" Disambiguation="on type" Agda=has-Σ-decidability-search}}
if we have a terminating algorithm `f` that, for every
[decidable type family](foundation.decidable-type-families.md) `P` on `X`
computes an element in `P` or produces a proof that `P` is the empty family. In
other words, `f` is an element of type

```text
  (P : decidable-family X) → is-decidable (Σ x. P x).
```

**Terminology.** In the terminology of Martín Escardó, a type that has
decidability search on decidable _subtypes_ is referred to as _searchable_,
_exhaustively searchable_, _exhaustibly searchable_, _exhaustible_,
_omniscient_, _satisfying the principle of omniscience_, _compact_, or
_Σ-compact_. {{#cite Esc08}} {{#cite TypeTopology}} We reserve the term
_Σ-decidability searchable_ for types for which there (merely)
[exists](foundation.existential-quantification.md) a Σ-decidability search on
`X`.

## Definitions

### The predicate of having Σ-decidability search

```agda
has-Σ-decidability-search-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-Σ-decidability-search-Level l2 X =
  (P : decidable-family l2 X) → is-decidable (Σ X (family-decidable-family P))

has-Σ-decidability-search : {l1 : Level} → UU l1 → UUω
has-Σ-decidability-search X =
  {l2 : Level} → has-Σ-decidability-search-Level l2 X
```

### The predicate of having small Σ-decidability search

```agda
has-Σ-decidability-search-bool : {l1 : Level} → UU l1 → UU l1
has-Σ-decidability-search-bool X =
  (b : X → bool) → is-decidable (Σ X (is-true ∘ b))
```

### The type of types with Σ-decidability search

```agda
record Type-With-Σ-Decidability-Search (l : Level) : UUω
  where
  field

    type-Type-With-Σ-Decidability-Search : UU l

    has-Σ-decidability-search-type-Type-With-Σ-Decidability-Search :
      has-Σ-decidability-search type-Type-With-Σ-Decidability-Search

open Type-With-Σ-Decidability-Search public
```

### The predicate of having Σ-decidability search on subtypes

```agda
has-Σ-decidability-search-on-subtypes-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-Σ-decidability-search-on-subtypes-Level l2 X =
  (P : decidable-subtype l2 X) → is-decidable (Σ X (is-in-decidable-subtype P))

has-Σ-decidability-search-on-subtypes : {l1 : Level} → UU l1 → UUω
has-Σ-decidability-search-on-subtypes X =
  {l2 : Level} → has-Σ-decidability-search-on-subtypes-Level l2 X
```

### The predicate of having pointed Σ-decidability search

```agda
has-pointed-Σ-decidability-search-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-pointed-Σ-decidability-search-Level l2 X =
  ( P : decidable-family l2 X) →
  Σ X
    ( λ x₀ →
      family-decidable-family P x₀ → (x : X) → family-decidable-family P x)

has-pointed-Σ-decidability-search : {l1 : Level} → UU l1 → UUω
has-pointed-Σ-decidability-search X =
  {l2 : Level} → has-pointed-Σ-decidability-search-Level l2 X
```

### The predicate of having pointed Σ-decidability search on subtypes

```agda
has-pointed-Σ-decidability-search-on-subtypes-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-pointed-Σ-decidability-search-on-subtypes-Level l2 X =
  ( P : decidable-subtype l2 X) →
  Σ X
    ( λ x₀ →
      is-in-decidable-subtype P x₀ → (x : X) → is-in-decidable-subtype P x)

has-pointed-Σ-decidability-search-on-subtypes : {l1 : Level} → UU l1 → UUω
has-pointed-Σ-decidability-search-on-subtypes X =
  {l2 : Level} → has-pointed-Σ-decidability-search-on-subtypes-Level l2 X
```

### The small predicate of having pointed Σ-decidability search

```agda
has-pointed-Σ-decidability-search-bool : {l : Level} → UU l → UU l
has-pointed-Σ-decidability-search-bool X =
  (b : X → bool) → Σ X (λ x₀ → is-true (b x₀) → (x : X) → is-true (b x))

has-pointed-Σ-decidability-search-bool' : {l : Level} → UU l → UU l
has-pointed-Σ-decidability-search-bool' X =
  (b : X → bool) → Σ X (λ x₀ → is-false (b x₀) → (x : X) → is-false (b x))
```

## Properties

### Types with Σ-decidability search are decidable

```agda
is-decidable-type-has-Σ-decidability-search :
  {l1 : Level} {X : UU l1} → has-Σ-decidability-search X → is-decidable X
is-decidable-type-has-Σ-decidability-search f =
  is-decidable-equiv'
    ( right-unit-law-product)
    ( f ((λ _ → unit) , (λ _ → inl star)))
```

### Types with Σ-decidability search on subtypes have Σ-decidability search

```agda
abstract
  has-Σ-decidability-search-has-Σ-decidability-search-on-subtypes :
    {l1 : Level} {X : UU l1} →
    has-Σ-decidability-search-on-subtypes X → has-Σ-decidability-search X
  has-Σ-decidability-search-has-Σ-decidability-search-on-subtypes f P =
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

### A type has Σ-decidability search if and only if it satisfies the small predicate of having Σ-decidability search

```agda
module _
  {l : Level} {X : UU l}
  where

  has-Σ-decidability-search-on-subtypes-has-Σ-decidability-search-bool :
    has-Σ-decidability-search-bool X →
    has-Σ-decidability-search-on-subtypes X
  has-Σ-decidability-search-on-subtypes-has-Σ-decidability-search-bool f P =
    is-decidable-equiv
      ( equiv-tot (compute-equiv-bool-Decidable-Prop ∘ P))
      ( f (bool-Decidable-Prop ∘ P))

  abstract
    has-Σ-decidability-search-has-Σ-decidability-search-bool :
      has-Σ-decidability-search-bool X → has-Σ-decidability-search X
    has-Σ-decidability-search-has-Σ-decidability-search-bool f =
      has-Σ-decidability-search-has-Σ-decidability-search-on-subtypes
        ( has-Σ-decidability-search-on-subtypes-has-Σ-decidability-search-bool
          ( f))

  has-Σ-decidability-search-bool-has-Σ-decidability-search-on-subtypes :
    has-Σ-decidability-search-on-subtypes X → has-Σ-decidability-search-bool X
  has-Σ-decidability-search-bool-has-Σ-decidability-search-on-subtypes f P =
    f (is-true-Decidable-Prop ∘ P)

  has-Σ-decidability-search-bool-has-Σ-decidability-search :
    has-Σ-decidability-search X → has-Σ-decidability-search-bool X
  has-Σ-decidability-search-bool-has-Σ-decidability-search f P =
    f (is-true ∘ P , λ x → has-decidable-equality-bool (P x) true)
```

### A pointed type with Σ-decidability search has pointed Σ-decidability search

```agda
has-pointed-Σ-decidability-search-has-Σ-decidability-search-has-element :
  {l : Level} {X : UU l} →
  X → has-Σ-decidability-search X → has-pointed-Σ-decidability-search X
has-pointed-Σ-decidability-search-has-Σ-decidability-search-has-element x₀ f P =
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

### The two small predicate of having pointed Σ-decidability search are equivalent

```agda
flip-has-pointed-Σ-decidability-search-bool :
  {l : Level} {X : UU l} →
  has-pointed-Σ-decidability-search-bool' X →
  has-pointed-Σ-decidability-search-bool X
pr1 (flip-has-pointed-Σ-decidability-search-bool H b) = pr1 (H (neg-bool ∘ b))
pr2 (flip-has-pointed-Σ-decidability-search-bool H b) p x =
  is-true-is-false-neg-bool
    ( pr2
      ( H (neg-bool ∘ b))
      ( is-false-is-true-neg-bool
        ( is-involution-neg-bool (b (pr1 (H (neg-bool ∘ b)))) ∙ p))
      ( x))
```

> The converse remains to be formalized.

### A type has pointed Σ-decidability search if and only if it has small pointed Σ-decidability search

```agda
abstract
  has-pointed-Σ-decidability-search-on-subtypes-has-pointed-Σ-decidability-search-bool :
    {l : Level} {X : UU l} →
    has-pointed-Σ-decidability-search-bool X →
    has-pointed-Σ-decidability-search-on-subtypes X
  has-pointed-Σ-decidability-search-on-subtypes-has-pointed-Σ-decidability-search-bool
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

has-pointed-Σ-decidability-search-bool-has-pointed-Σ-decidability-search-on-subtypes :
  {l : Level} {X : UU l} →
  has-pointed-Σ-decidability-search-on-subtypes X →
  has-pointed-Σ-decidability-search-bool X
has-pointed-Σ-decidability-search-bool-has-pointed-Σ-decidability-search-on-subtypes
  f b =
  f (is-true-Decidable-Prop ∘ b)
```

### Types with pointed Σ-decidability search on subtypes has pointed Σ-decidability search

```agda
abstract
  has-pointed-Σ-decidability-search-has-pointed-Σ-decidability-search-on-subtypes :
    {l1 : Level} {X : UU l1} →
    has-pointed-Σ-decidability-search-on-subtypes X →
    has-pointed-Σ-decidability-search X
  has-pointed-Σ-decidability-search-has-pointed-Σ-decidability-search-on-subtypes
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

### Types with pointed Σ-decidability search have Σ-decidability search

```agda
is-decidable-Σ-is-this-other-thing :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
  ((x : X) → ¬ (Y x)) → ¬ (Σ X Y)
is-decidable-Σ-is-this-other-thing f xp = f (pr1 xp) (pr2 xp)

has-Σ-decidability-search-has-pointed-Σ-decidability-search :
  {l : Level} {X : UU l} →
  has-pointed-Σ-decidability-search X → has-Σ-decidability-search X
has-Σ-decidability-search-has-pointed-Σ-decidability-search {X = X} f P =
  map-coproduct
    ( pair (pr1 (f P)))
    ( λ np xp → np TODO)
    ( is-decidable-decidable-family P (pr1 (f P)))
  where postulate TODO : _ -- TODO
```

### Decidability search transfers along double negation dense maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (h : X ↠¬¬ Y)
  where

  has-Σ-decidability-search-double-negation-dense-map :
    has-Σ-decidability-search X → has-Σ-decidability-search Y
  has-Σ-decidability-search-double-negation-dense-map f P =
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
      ( f (reindex-decidable-family P (map-double-negation-dense-map h)))
```

### Decidability search transfers along surjections

```agda
has-Σ-decidability-search-surjection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↠ Y →
  has-Σ-decidability-search X → has-Σ-decidability-search Y
has-Σ-decidability-search-surjection h =
  has-Σ-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-surjection h)
```

### Types with Σ-decidability search are closed under retracts

```agda
has-Σ-decidability-search-retract :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  Y retract-of X → has-Σ-decidability-search X → has-Σ-decidability-search Y
has-Σ-decidability-search-retract R =
  has-Σ-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-retract R)
```

### Types with Σ-decidability search are closed under equivalences

```agda
has-Σ-decidability-search-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  Y ≃ X → has-Σ-decidability-search X → has-Σ-decidability-search Y
has-Σ-decidability-search-equiv e =
  has-Σ-decidability-search-retract (retract-equiv e)

has-Σ-decidability-search-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  X ≃ Y → has-Σ-decidability-search X → has-Σ-decidability-search Y
has-Σ-decidability-search-equiv' e =
  has-Σ-decidability-search-retract (retract-inv-equiv e)
```

### Decidable types that with double negation dense equality have Σ-decidability search

```agda
has-Σ-decidability-search-is-decidable-has-double-negation-dense-equality :
  {l1 : Level} {X : UU l1} → has-double-negation-dense-equality X →
  is-decidable X → has-Σ-decidability-search X
has-Σ-decidability-search-is-decidable-has-double-negation-dense-equality
  H d P =
  is-decidable-Σ-has-double-negation-dense-equality-base H d
    ( is-decidable-decidable-family P)
```

**Comment.** It might suffice for the above result that `X` is inhabited or
empty.

### Decidable subtypes of types with Σ-decidability search have Σ-decidability search

```agda
has-Σ-decidability-search-type-decidable-subtype :
  {l1 l2 : Level} {X : UU l1} →
  has-Σ-decidability-search X →
  (P : decidable-subtype l2 X) →
  has-Σ-decidability-search (type-decidable-subtype P)
has-Σ-decidability-search-type-decidable-subtype {X = X} f P Q =
  is-decidable-equiv
    ( associative-Σ X (is-in-decidable-subtype P) (family-decidable-family Q))
    ( f ( comp-decidable-family-decidable-subtype P
          ( reindex-decidable-family Q ∘ pair)))

has-Σ-decidability-search-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  has-Σ-decidability-search X → Y ↪ᵈ X → has-Σ-decidability-search Y
has-Σ-decidability-search-decidable-emb f h =
  has-Σ-decidability-search-equiv'
    ( compute-type-decidable-subtype-decidable-emb h)
    ( has-Σ-decidability-search-type-decidable-subtype f
      ( decidable-subtype-decidable-emb h))
```

### The empty type has Σ-decidability search

```agda
has-Σ-decidability-search-empty : has-Σ-decidability-search empty
has-Σ-decidability-search-empty P = inr pr1
```

### The unit type has Σ-decidability search

```agda
has-Σ-decidability-search-unit : has-Σ-decidability-search unit
has-Σ-decidability-search-unit P =
  rec-coproduct
    ( inl ∘ pair star)
    ( inr ∘ map-neg pr2)
    ( is-decidable-decidable-family P star)
```

### Coproducts of types with Σ-decidability search

Coproducts of types with Σ-decidability search have Σ-decidability search.
Conversely, if the coproduct has Σ-decidability search and a summand has an
element, then that summand also has Σ-decidability search.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-Σ-decidability-search-coproduct :
    has-Σ-decidability-search X →
    has-Σ-decidability-search Y →
    has-Σ-decidability-search (X + Y)
  has-Σ-decidability-search-coproduct f g P =
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
          ( g (reindex-decidable-family P inr)))
      ( f (reindex-decidable-family P inl))

  has-Σ-decidability-search-left-summand-coproduct :
    has-Σ-decidability-search (X + Y) →
    X → has-Σ-decidability-search X
  has-Σ-decidability-search-left-summand-coproduct f x =
    has-Σ-decidability-search-retract (retract-left-summand-coproduct x) f

  has-Σ-decidability-search-right-summand-coproduct :
    has-Σ-decidability-search (X + Y) →
    Y → has-Σ-decidability-search Y
  has-Σ-decidability-search-right-summand-coproduct f y =
    has-Σ-decidability-search-retract (retract-right-summand-coproduct y) f
```

### Dependent sums of types with Σ-decidability search

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-Σ-decidability-search-Σ :
    has-Σ-decidability-search A →
    ((x : A) → has-Σ-decidability-search (B x)) →
    has-Σ-decidability-search (Σ A B)
  has-Σ-decidability-search-Σ f g {l} P =
    is-decidable-equiv
      ( associative-Σ A B (family-decidable-family P))
      ( f ( ( λ x → Σ (B x) (λ y → family-decidable-family P (x , y))) ,
            ( λ x → g x (reindex-decidable-family P (λ b → (x , b))))))
```

### The total space of decidable families of types with double negation dense equality over types with Σ-decidability search have Σ-decidability search

```agda
abstract
  has-Σ-decidability-search-Σ-decidable-family-has-double-negation-dense-equality :
    {l1 l2 : Level} {X : UU l1} →
    has-Σ-decidability-search X →
    (P : decidable-family l2 X) →
    ( (x : X) →
      has-double-negation-dense-equality (family-decidable-family P x)) →
    has-Σ-decidability-search (Σ X (family-decidable-family P))
  has-Σ-decidability-search-Σ-decidable-family-has-double-negation-dense-equality
    f P H =
    has-Σ-decidability-search-Σ f
      ( λ x →
        has-Σ-decidability-search-is-decidable-has-double-negation-dense-equality
          ( H x)
          ( is-decidable-decidable-family P x))
```

### Dependent sums of types with Σ-decidability search

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-Σ-decidability-search-base-has-Σ-decidability-search-Σ :
    has-Σ-decidability-search (Σ A B) →
    ((x : A) → B x) →
    has-Σ-decidability-search A
  has-Σ-decidability-search-base-has-Σ-decidability-search-Σ f s =
    has-Σ-decidability-search-retract (retract-base-Σ-section-family s) f
```

### Products of types with Σ-decidability search

```agda
has-Σ-decidability-search-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-Σ-decidability-search A →
  has-Σ-decidability-search B →
  has-Σ-decidability-search (A × B)
has-Σ-decidability-search-product f g = has-Σ-decidability-search-Σ f (λ _ → g)
```

### Factors of products with Σ-decidability search

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-Σ-decidability-search-left-factor-product :
    has-Σ-decidability-search (X × Y) →
    Y → has-Σ-decidability-search X
  has-Σ-decidability-search-left-factor-product f y =
    has-Σ-decidability-search-retract (retract-left-factor-product y) f

  has-Σ-decidability-search-right-factor-product :
    has-Σ-decidability-search (X × Y) →
    X → has-Σ-decidability-search Y
  has-Σ-decidability-search-right-factor-product f x =
    has-Σ-decidability-search-retract (retract-right-factor-product x) f
```

### Standard finite types have Σ-decidability search

```agda
has-Σ-decidability-search-Fin : (n : ℕ) → has-Σ-decidability-search (Fin n)
has-Σ-decidability-search-Fin zero-ℕ = has-Σ-decidability-search-empty
has-Σ-decidability-search-Fin (succ-ℕ n) =
  has-Σ-decidability-search-coproduct
    ( has-Σ-decidability-search-Fin n)
    ( has-Σ-decidability-search-unit)
```

### Types equipped with a counting have Σ-decidability search

```agda
has-Σ-decidability-search-count :
  {l : Level} {X : UU l} → count X → has-Σ-decidability-search X
has-Σ-decidability-search-count f =
  has-Σ-decidability-search-equiv'
    ( equiv-count f)
    ( has-Σ-decidability-search-Fin (number-of-elements-count f))
```

### The booleans have Σ-decidability search

```agda
has-Σ-decidability-search-bool' : has-Σ-decidability-search bool
has-Σ-decidability-search-bool' =
  has-Σ-decidability-search-equiv'
    ( equiv-bool-Fin-2)
    ( has-Σ-decidability-search-Fin 2)
```

### The subuniverse of propositions has Σ-decidability search

```agda
-- has-Σ-decidability-search-Prop : {l : Level} → has-Σ-decidability-search (Prop l)
-- has-Σ-decidability-search-Prop {l} P =
--   rec-coproduct
--     ( λ p → inl (raise-unit-Prop l , p))
--     ( λ np →
--       rec-coproduct
--         ( λ q → inl (raise-empty-Prop l , q))
--         (λ nq → inr {!   !})
--         ( is-decidable-decidable-family P (raise-empty-Prop l)))
--     ( is-decidable-decidable-family P (raise-unit-Prop l))
```

> The above results depends on certain properties of the subuniverse of
> propositions that are not formalized at the time of writing.

## References

{{#bibliography}}

## See also

- [Π-decidability search](foundation.decidability-search-untruncated-universal-quantification.md)
- [∀-decidability search](foundation.decidability-search-universal-quantification.md)
