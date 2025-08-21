# Types with decidable Π-types

```agda
module foundation.types-with-decidable-dependent-product-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-subtypes
open import foundation.decidable-type-families
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.double-negation-dense-equality
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.irrefutable-equality
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.surjective-maps
open import foundation.transport-along-identifications
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import logic.de-morgan-types
open import logic.double-negation-dense-maps

open import univalent-combinatorics.counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A type `X` {{#concept "has decidable Π-types" Agda=has-decidable-Π}} if for
every [decidable type family](foundation.decidable-type-families.md) `P` on `X`,
we can compute a section of `P`, `(x : X) → P x`, or determine that no such
section exists. In other words, we have a witness of type

```text
  (P : decidable-family X) → is-decidable (Π x. P x).
```

**Terminology.** In the terminology of Martín Escardó, a type that has decidable
Π-types is referred to as _weakly compact_, _Π-compact_, or _satisfying the weak
principle of omniscience_. {{#cite TypeTopology}}

## Definitions

### The predicate of having decidable Π-types

```agda
has-decidable-Π-Level :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
has-decidable-Π-Level l2 X =
  (P : decidable-family l2 X) →
  is-decidable ((x : X) → family-decidable-family P x)

has-decidable-Π : {l1 : Level} → UU l1 → UUω
has-decidable-Π X =
  {l2 : Level} → has-decidable-Π-Level l2 X
```

### The type of types with decidable Π-types

```agda
record Type-With-Decidable-Π (l : Level) : UUω
  where
  field
    type-Type-With-Decidable-Π : UU l

    has-decidable-Π-type-Type-With-Decidable-Π :
      has-decidable-Π type-Type-With-Decidable-Π
```

## Properties

### Types with decidable Π-types are De Morgan

```agda
is-de-morgan-has-decidable-Π-Prop :
  {l1 : Level} {X : UU l1} → has-decidable-Π X → is-de-morgan X
is-de-morgan-has-decidable-Π-Prop f =
  f ((λ _ → empty) , (λ _ → inr id))
```

### Having decidable Π-types transfers along double negation dense maps

```agda
has-decidable-Π-double-negation-dense-map :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  X ↠¬¬ Y → has-decidable-Π X → has-decidable-Π Y
has-decidable-Π-double-negation-dense-map h f P =
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
    ( f (base-change-decidable-family P (map-double-negation-dense-map h)))
```

### Having decidable Π-types transfers along surjections

```agda
has-decidable-Π-surjection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ↠ Y →
  has-decidable-Π X → has-decidable-Π Y
has-decidable-Π-surjection h =
  has-decidable-Π-double-negation-dense-map
    ( double-negation-dense-map-surjection h)
```

### Types with decidable Π-types are closed under retracts

```agda
has-decidable-Π-retract :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y retract-of X →
  has-decidable-Π X → has-decidable-Π Y
has-decidable-Π-retract R =
  has-decidable-Π-double-negation-dense-map
    ( double-negation-dense-map-retract R)
```

### Types with decidable Π-types are closed under equivalences

```agda
has-decidable-Π-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y ≃ X →
  has-decidable-Π X → has-decidable-Π Y
has-decidable-Π-equiv e =
  has-decidable-Π-retract (retract-equiv e)

has-decidable-Π-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → X ≃ Y →
  has-decidable-Π X → has-decidable-Π Y
has-decidable-Π-equiv' e =
  has-decidable-Π-retract (retract-inv-equiv e)
```

### The empty type has decidable Π-types

```agda
has-decidable-Π-empty :
  has-decidable-Π empty
has-decidable-Π-empty P = inl ind-empty
```

### The unit type has decidable Π-types

```agda
has-decidable-Π-unit : has-decidable-Π unit
has-decidable-Π-unit P =
  map-coproduct
    ( λ p _ → p)
    ( λ np p → np (p star))
    ( is-decidable-decidable-family P star)
```

### Coproducts of types with decidable Π-types

Coproducts of types with decidable Π-types for untruncated universal
quantification have decidable Π-types. Conversely, if the coproduct has
decidable Π-types and a summand has an element, then that summand also has
decidable Π-types.

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-decidable-Π-coproduct :
    has-decidable-Π X →
    has-decidable-Π Y →
    has-decidable-Π (X + Y)
  has-decidable-Π-coproduct f g P =
    rec-coproduct
      ( λ pl →
        rec-coproduct
          ( λ pr → inl (ind-coproduct (family-decidable-family P) pl pr))
          ( λ npr → inr (λ p → npr (p ∘ inr)))
          ( g (base-change-decidable-family P inr)))
      ( λ npl → inr (λ p → npl (p ∘ inl)))
      ( f (base-change-decidable-family P inl))

  has-decidable-Π-left-summand-coproduct :
    has-decidable-Π (X + Y) →
    X → has-decidable-Π X
  has-decidable-Π-left-summand-coproduct f x =
    has-decidable-Π-retract
      ( retract-left-summand-coproduct x)
      ( f)

  has-decidable-Π-right-summand-coproduct :
    has-decidable-Π (X + Y) →
    Y → has-decidable-Π Y
  has-decidable-Π-right-summand-coproduct f y =
    has-decidable-Π-retract
      ( retract-right-summand-coproduct y)
      ( f)
```

### Dependent sums of types with decidable Π-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  has-decidable-Π-Σ :
    has-decidable-Π A →
    ((x : A) → has-decidable-Π (B x)) →
    has-decidable-Π (Σ A B)
  has-decidable-Π-Σ f g P =
    is-decidable-equiv equiv-ev-pair
      ( f ( ( λ x → (y : B x) → family-decidable-family P (x , y)) ,
            ( λ x → g x (base-change-decidable-family P (pair x)))))

  has-decidable-Π-base-has-decidable-Π-Σ :
    has-decidable-Π (Σ A B) →
    ((x : A) → B x) →
    has-decidable-Π A
  has-decidable-Π-base-has-decidable-Π-Σ
    f s =
    has-decidable-Π-retract
      ( retract-base-Σ-section-family s)
      ( f)
```

### Products of types with decidable Π-types

```agda
has-decidable-Π-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  has-decidable-Π A →
  has-decidable-Π B →
  has-decidable-Π (A × B)
has-decidable-Π-product f g =
  has-decidable-Π-Σ f (λ _ → g)
```

### Factors of products with decidable Π-types

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  has-decidable-Π-left-factor-product :
    has-decidable-Π (X × Y) →
    Y → has-decidable-Π X
  has-decidable-Π-left-factor-product f y =
    has-decidable-Π-retract (retract-left-factor-product y) f

  has-decidable-Π-right-factor-product :
    has-decidable-Π (X × Y) →
    X → has-decidable-Π Y
  has-decidable-Π-right-factor-product f x =
    has-decidable-Π-retract (retract-right-factor-product x) f
```

### Standard finite types have decidable Π-types

```agda
has-decidable-Π-Fin :
  (n : ℕ) → has-decidable-Π (Fin n)
has-decidable-Π-Fin zero-ℕ =
  has-decidable-Π-empty
has-decidable-Π-Fin (succ-ℕ n) =
  has-decidable-Π-coproduct
    ( has-decidable-Π-Fin n)
    ( has-decidable-Π-unit)
```

### Types equipped with a counting have decidable Π-types

```agda
has-decidable-Π-count :
  {l : Level} {X : UU l} → count X → has-decidable-Π X
has-decidable-Π-count f =
  has-decidable-Π-equiv'
    ( equiv-count f)
    ( has-decidable-Π-Fin (number-of-elements-count f))
```

### The booleans have decidable Π-types

```agda
has-decidable-Π-bool : has-decidable-Π bool
has-decidable-Π-bool =
  has-decidable-Π-equiv'
    ( equiv-bool-Fin-2)
    ( has-decidable-Π-Fin 2)
```

### Types with decidable Σ-types have decidable Π-types

```agda
has-decidable-Π-has-decidable-Σ :
  {l : Level} {X : UU l} →
  has-decidable-Σ X →
  has-decidable-Π X
has-decidable-Π-has-decidable-Σ f P =
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

### Decidable types with double negation dense equality have decidable Π-types

```agda
abstract
  has-decidable-Π-is-decidable-has-double-negation-dense-equality :
    {l : Level} {X : UU l} →
    has-double-negation-dense-equality X →
    is-decidable X →
    has-decidable-Π X
  has-decidable-Π-is-decidable-has-double-negation-dense-equality
    H d =
    has-decidable-Π-has-decidable-Σ
      ( has-decidable-Σ-is-decidable-has-double-negation-dense-equality H d)
```

### The total space of decidable families with double negation dense equality over types with decidable Π-types have decidable Π-types

```agda
abstract
  has-decidable-Π-Σ-decidable-family-has-double-negation-dense-equality :
    {l1 l2 : Level} {X : UU l1} →
    has-decidable-Π X →
    (P : decidable-family l2 X) →
    ( (x : X) →
      has-double-negation-dense-equality (family-decidable-family P x)) →
    has-decidable-Π (Σ X (family-decidable-family P))
  has-decidable-Π-Σ-decidable-family-has-double-negation-dense-equality
    f P H =
    has-decidable-Π-Σ f
      ( λ x →
        has-decidable-Π-is-decidable-has-double-negation-dense-equality
          ( H x)
          ( is-decidable-decidable-family P x))
```

### Decidable subtypes of types with decidable Π-types have decidable Π-types

```agda
abstract
  has-decidable-Π-type-decidable-subtype :
    {l1 l2 : Level} {X : UU l1} →
    has-decidable-Π X →
    (P : decidable-subtype l2 X) →
    has-decidable-Π (type-decidable-subtype P)
  has-decidable-Π-type-decidable-subtype {X = X} f P =
    has-decidable-Π-Σ-decidable-family-has-double-negation-dense-equality
      ( f)
      ( decidable-family-decidable-subtype P)
      ( λ x p q →
        intro-double-negation
          ( eq-is-prop (is-prop-is-in-decidable-subtype P x)))

has-decidable-Π-decidable-emb :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → Y ↪ᵈ X →
  has-decidable-Π X → has-decidable-Π Y
has-decidable-Π-decidable-emb h f =
  has-decidable-Π-equiv'
    ( compute-type-decidable-subtype-decidable-emb h)
    ( has-decidable-Π-type-decidable-subtype f
      ( decidable-subtype-decidable-emb h))
```

## References

{{#bibliography}}

## See also

- [Types with decidable Σ-types](foundation.types-with-decidable-dependent-pair-types.md)
- [Types with decidable universal quantifications](foundation.types-with-decidable-universal-quantifications.md)
