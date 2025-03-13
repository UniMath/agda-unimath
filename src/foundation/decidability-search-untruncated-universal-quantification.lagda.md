# Π-Decidability search

```agda
module foundation.decidability-search-untruncated-universal-quantification where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidability-search-untruncated-existential-quantification
open import foundation.decidable-dependent-function-types
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
open import foundation.evaluation-functions
open import foundation.fibers-of-maps
open import foundation.full-subtypes
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.irrefutable-equality
open import foundation.locally-small-types
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
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-types

open import logic.complements-decidable-subtypes
open import logic.de-morgan-subtypes
open import logic.de-morgan-types
open import logic.double-negation-dense-maps
open import logic.propositionally-decidable-types

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X` has
{{#concept "Π-decidability search" Disambiguation="on type" Agda=has-Π-decidability-search}}
if we have a terminating algorithm `f` that, for every
[decidable type family](foundation.decidable-type-families.md) `P` on `X`
computes a section of `P`, `(x : X) → P x`, or produces a proof that no such
section exists, in other words, exhibits a fiber of `P` that is
[empty](foundation.empty-types.md).

```text
  (P : decidable-family X) → is-decidable (∀ x. P x)
```

**Terminology.** In the terminology of Martín Escardó, a type that has universal
decidability search is referred to as _weakly compact_ or _satisfying the weak
principle of omniscience_, or _Π-compact_. {{#cite TypeTopology}} We reserve the
term _Π-decidability searchable_ for types for which there (merely)
[exists](foundation.existential-quantification.md) a Π-decidability search.

## Definitions

### The predicate of having Π-decidability search

```agda
has-Π-decidability-search-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-Π-decidability-search-Level l2 X =
  (P : decidable-family l2 X) →
  is-decidable ((x : X) → family-decidable-family P x)

has-Π-decidability-search : {l1 : Level} → UU l1 → UUω
has-Π-decidability-search X =
  {l2 : Level} → has-Π-decidability-search-Level l2 X
```

### The type of types with Π-decidability search

```agda
record Type-With-Π-Decidability-Search (l : Level) : UUω
  where
  field

    type-Type-With-Π-Decidability-Search : UU l

    has-Π-decidability-search-type-Type-With-Π-Decidability-Search :
      has-Π-decidability-search
        type-Type-With-Π-Decidability-Search
```

## Properties

### Types with Π-decidability search are De Morgan

```agda
is-de-morgan-has-Π-decidability-search-Prop :
  {l1 : Level} {X : UU l1} →
  has-Π-decidability-search X → is-de-morgan X
is-de-morgan-has-Π-decidability-search-Prop f =
  f ((λ _ → empty) , (λ _ → inr id))
```

### Π-Decidability search transfers along double negation dense maps

```agda
has-Π-decidability-search-double-negation-dense-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↠¬¬ Y →
  has-Π-decidability-search X →
  has-Π-decidability-search Y
has-Π-decidability-search-double-negation-dense-map h f P =
  map-coproduct
    ( λ p x →
      rec-coproduct
        ( id)
        ( λ np →
          ex-falso
            ( is-double-negation-dense-map-double-negation-dense-map h x
              ( λ yp →
                np (tr (family-decidable-family P) (pr2 yp) (p (pr1 yp))))))
        ( is-decidable-decidable-family P x))
    ( λ nph p → nph (p ∘ map-double-negation-dense-map h))
    ( f (reindex-decidable-family P (map-double-negation-dense-map h)))
```

### Π-Decidability search transfers along surjections

```agda
has-Π-decidability-search-surjection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↠ Y →
  has-Π-decidability-search X → has-Π-decidability-search Y
has-Π-decidability-search-surjection h =
  has-Π-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-surjection h)
```

### Types with Π-decidability search are closed under retracts

```agda
has-Π-decidability-search-retract :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y retract-of X →
  has-Π-decidability-search X → has-Π-decidability-search Y
has-Π-decidability-search-retract R =
  has-Π-decidability-search-double-negation-dense-map
    ( double-negation-dense-map-retract R)
```

### Types with Π-decidability search are closed under equivalences

```agda
has-Π-decidability-search-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y ≃ X →
  has-Π-decidability-search X → has-Π-decidability-search Y
has-Π-decidability-search-equiv e =
  has-Π-decidability-search-retract (retract-equiv e)

has-Π-decidability-search-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ≃ Y →
  has-Π-decidability-search X → has-Π-decidability-search Y
has-Π-decidability-search-equiv' e =
  has-Π-decidability-search-retract (retract-inv-equiv e)
```

### The empty type has decidability search

```agda
has-Π-decidability-search-empty :
  has-Π-decidability-search empty
has-Π-decidability-search-empty P = inl ind-empty
```

### The unit type has decidability search

```agda
has-Π-decidability-search-unit : has-Π-decidability-search unit
has-Π-decidability-search-unit P =
  map-coproduct
    ( λ p _ → p)
    ( λ np p → np (p star))
    ( is-decidable-decidable-family P star)
```

### Coproducts of types with Π-decidability search

Coproducts of types with decidability search for untruncated universal
quantification have Π-decidability search. Conversely, if the coproduct has
decidability search and a summand has an element, then that summand also has
decidability search.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-Π-decidability-search-coproduct :
    has-Π-decidability-search X →
    has-Π-decidability-search Y →
    has-Π-decidability-search (X + Y)
  has-Π-decidability-search-coproduct f g P =
    rec-coproduct
      ( λ pl →
        rec-coproduct
          ( λ pr → inl (ind-coproduct (family-decidable-family P) pl pr))
          ( λ npr → inr (λ p → npr (p ∘ inr)))
          ( g (reindex-decidable-family P inr)))
      ( λ npl → inr (λ p → npl (p ∘ inl)))
      ( f (reindex-decidable-family P inl))

  has-Π-decidability-search-left-summand-coproduct :
    has-Π-decidability-search (X + Y) →
    X → has-Π-decidability-search X
  has-Π-decidability-search-left-summand-coproduct f x =
    has-Π-decidability-search-retract
      ( retract-left-summand-coproduct x)
      ( f)

  has-Π-decidability-search-right-summand-coproduct :
    has-Π-decidability-search (X + Y) →
    Y → has-Π-decidability-search Y
  has-Π-decidability-search-right-summand-coproduct f y =
    has-Π-decidability-search-retract
      ( retract-right-summand-coproduct y)
      ( f)
```

### Dependent sums of types with Π-decidability search

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-Π-decidability-search-Σ :
    has-Π-decidability-search A →
    ((x : A) → has-Π-decidability-search (B x)) →
    has-Π-decidability-search (Σ A B)
  has-Π-decidability-search-Σ f g P =
    is-decidable-equiv equiv-ev-pair
      ( f ( ( λ x → (y : B x) → family-decidable-family P (x , y)) ,
            ( λ x → g x (reindex-decidable-family P (pair x)))))

  has-Π-decidability-search-base-has-Π-decidability-search-Σ :
    has-Π-decidability-search (Σ A B) →
    ((x : A) → B x) →
    has-Π-decidability-search A
  has-Π-decidability-search-base-has-Π-decidability-search-Σ
    f s =
    has-Π-decidability-search-retract
      ( retract-base-Σ-section-family s)
      ( f)
```

### Products of types with Π-decidability search

```agda
has-Π-decidability-search-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-Π-decidability-search A →
  has-Π-decidability-search B →
  has-Π-decidability-search (A × B)
has-Π-decidability-search-product f g =
  has-Π-decidability-search-Σ f (λ _ → g)
```

### Factors of products with Π-decidability search

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-Π-decidability-search-left-factor-product :
    has-Π-decidability-search (X × Y) →
    Y → has-Π-decidability-search X
  has-Π-decidability-search-left-factor-product f y =
    has-Π-decidability-search-retract (retract-left-factor-product y) f

  has-Π-decidability-search-right-factor-product :
    has-Π-decidability-search (X × Y) →
    X → has-Π-decidability-search Y
  has-Π-decidability-search-right-factor-product f x =
    has-Π-decidability-search-retract (retract-right-factor-product x) f
```

### Standard finite types have Π-decidability search

```agda
has-Π-decidability-search-Fin :
  (n : ℕ) → has-Π-decidability-search (Fin n)
has-Π-decidability-search-Fin zero-ℕ =
  has-Π-decidability-search-empty
has-Π-decidability-search-Fin (succ-ℕ n) =
  has-Π-decidability-search-coproduct
    ( has-Π-decidability-search-Fin n)
    ( has-Π-decidability-search-unit)
```

### Types equipped with a counting have Π-decidability search

```agda
has-Π-decidability-search-count :
  {l : Level} {X : UU l} → count X → has-Π-decidability-search X
has-Π-decidability-search-count f =
  has-Π-decidability-search-equiv'
    ( equiv-count f)
    ( has-Π-decidability-search-Fin (number-of-elements-count f))
```

### The booleans have Π-decidability search

```agda
has-Π-decidability-search-bool : has-Π-decidability-search bool
has-Π-decidability-search-bool =
  has-Π-decidability-search-equiv'
    ( equiv-bool-Fin-2)
    ( has-Π-decidability-search-Fin 2)
```

### Types with decidability search have Π-decidability search

```agda
has-Π-decidability-search-has-Σ-decidability-search :
  {l : Level} {X : UU l} →
  has-Σ-decidability-search X →
  has-Π-decidability-search X
has-Π-decidability-search-has-Σ-decidability-search f P =
  rec-coproduct
    ( λ xnp → inr (λ p → pr2 xnp (p (pr1 xnp))))
    ( λ nxnp →
      inl
        ( λ x →
          rec-coproduct
            ( id)
            ( λ np → ex-falso (nxnp (x , np)))
            ( is-decidable-decidable-family P x)))
    ( f (neg-decidable-family P))
```

### Decidable types with double negation dense equality have Π-decidability search

```agda
abstract
  has-Π-decidability-search-is-decidable-has-double-negation-dense-equality :
    {l : Level} {X : UU l} →
    has-double-negation-dense-equality X →
    is-decidable X →
    has-Π-decidability-search X
  has-Π-decidability-search-is-decidable-has-double-negation-dense-equality
    H d =
    has-Π-decidability-search-has-Σ-decidability-search
      ( has-Σ-decidability-search-is-decidable-has-double-negation-dense-equality
        ( H)
        ( d))
```

### The total space of decidable families with double negation dense equality over types with Π-decidability search have Π-decidability search

```agda
abstract
  has-Π-decidability-search-Σ-decidable-family-has-double-negation-dense-equality :
    {l1 l2 : Level} {X : UU l1} →
    has-Π-decidability-search X →
    (P : decidable-family l2 X) →
    ( (x : X) →
      has-double-negation-dense-equality (family-decidable-family P x)) →
    has-Π-decidability-search (Σ X (family-decidable-family P))
  has-Π-decidability-search-Σ-decidable-family-has-double-negation-dense-equality
    f P H =
    has-Π-decidability-search-Σ f
      ( λ x →
        has-Π-decidability-search-is-decidable-has-double-negation-dense-equality
          ( H x)
          ( is-decidable-decidable-family P x))
```

### Decidable subtypes of types with Π-decidability search have Π-decidability search

```agda
abstract
  has-Π-decidability-search-type-decidable-subtype :
    {l1 l2 : Level} {X : UU l1} →
    has-Π-decidability-search X →
    (P : decidable-subtype l2 X) →
    has-Π-decidability-search (type-decidable-subtype P)
  has-Π-decidability-search-type-decidable-subtype {X = X} f P =
    has-Π-decidability-search-Σ-decidable-family-has-double-negation-dense-equality
      ( f)
      ( decidable-family-decidable-subtype P)
      ( λ x p q →
        intro-double-negation
          ( eq-is-prop (is-prop-is-in-decidable-subtype P x)))

has-Π-decidability-search-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y ↪ᵈ X →
  has-Π-decidability-search X → has-Π-decidability-search Y
has-Π-decidability-search-decidable-emb h f =
  has-Π-decidability-search-equiv'
    ( compute-type-decidable-subtype-decidable-emb h)
    ( has-Π-decidability-search-type-decidable-subtype f
      ( decidable-subtype-decidable-emb h))
```

## References

{{#bibliography}}

## See also

- [Σ-decidability search](foundation.decidability-search-untruncated-existential-quantification.md)
- [∀-decidability search](foundation.decidability-search-universal-quantification.md)
