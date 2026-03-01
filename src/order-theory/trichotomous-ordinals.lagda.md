# Trichotomous ordinals

```agda
module order-theory.trichotomous-ordinals where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.cotransitive-strict-orders
open import order-theory.ordinals
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
open import order-theory.total-preorders
open import order-theory.transitive-well-founded-relations
open import order-theory.trichotomous-strict-orders
open import order-theory.well-founded-relations
```

</details>

## Idea

A
{{#concept "trichotomous ordinal" Agda=is-trichotomous-Ordinal Agda=Trichotomous-Ordinal}}
is an [ordinal](order-theory.ordinals.md) `α` such that for all `x` and `y` in
`α`, either `x < y`, `x = y`, or `x > y`.

## Definitions

### The predicate on ordinals of being trichotomous

```agda
is-trichotomous-Ordinal :
  {l1 l2 : Level} → Ordinal l1 l2 → UU (l1 ⊔ l2)
is-trichotomous-Ordinal α =
  is-trichotomous-Strict-Order
    ( strict-order-Ordinal α)
```

### The type of trichotomous ordinals

```agda
Trichotomous-Ordinal : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Trichotomous-Ordinal l1 l2 =
  Σ (Ordinal l1 l2) is-trichotomous-Ordinal

module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  ordinal-Trichotomous-Ordinal : Ordinal l1 l2
  ordinal-Trichotomous-Ordinal = pr1 α

  is-trichotomous-ordinal-Trichotomous-Ordinal :
    is-trichotomous-Ordinal ordinal-Trichotomous-Ordinal
  is-trichotomous-ordinal-Trichotomous-Ordinal =
    pr2 α

  type-Trichotomous-Ordinal : UU l1
  type-Trichotomous-Ordinal =
    type-Ordinal ordinal-Trichotomous-Ordinal

  le-prop-Trichotomous-Ordinal :
    Relation-Prop l2 type-Trichotomous-Ordinal
  le-prop-Trichotomous-Ordinal =
    le-prop-Ordinal ordinal-Trichotomous-Ordinal

  is-ordinal-Trichotomous-Ordinal :
    is-ordinal le-prop-Trichotomous-Ordinal
  is-ordinal-Trichotomous-Ordinal =
    is-ordinal-Ordinal ordinal-Trichotomous-Ordinal

  le-Trichotomous-Ordinal : Relation l2 type-Trichotomous-Ordinal
  le-Trichotomous-Ordinal = le-Ordinal ordinal-Trichotomous-Ordinal

  is-transitive-well-founded-relation-le-Trichotomous-Ordinal :
    is-transitive-well-founded-relation-Relation le-Trichotomous-Ordinal
  is-transitive-well-founded-relation-le-Trichotomous-Ordinal =
    is-transitive-well-founded-relation-le-Ordinal ordinal-Trichotomous-Ordinal

  is-extensional-Trichotomous-Ordinal :
    extensionality-principle-Ordinal le-prop-Trichotomous-Ordinal
  is-extensional-Trichotomous-Ordinal =
    is-extensional-Ordinal ordinal-Trichotomous-Ordinal

  transitive-well-founded-relation-Trichotomous-Ordinal :
    Transitive-Well-Founded-Relation l2 type-Trichotomous-Ordinal
  transitive-well-founded-relation-Trichotomous-Ordinal =
    transitive-well-founded-relation-Ordinal ordinal-Trichotomous-Ordinal

  transitive-le-Trichotomous-Ordinal :
    is-transitive le-Trichotomous-Ordinal
  transitive-le-Trichotomous-Ordinal =
    transitive-le-Ordinal ordinal-Trichotomous-Ordinal

  is-well-founded-relation-le-Trichotomous-Ordinal :
    is-well-founded-Relation le-Trichotomous-Ordinal
  is-well-founded-relation-le-Trichotomous-Ordinal =
    is-well-founded-relation-le-Ordinal ordinal-Trichotomous-Ordinal

  well-founded-relation-Trichotomous-Ordinal :
    Well-Founded-Relation l2 type-Trichotomous-Ordinal
  well-founded-relation-Trichotomous-Ordinal =
    well-founded-relation-Ordinal ordinal-Trichotomous-Ordinal

  is-asymmetric-le-Trichotomous-Ordinal :
    is-asymmetric le-Trichotomous-Ordinal
  is-asymmetric-le-Trichotomous-Ordinal =
    is-asymmetric-le-Ordinal ordinal-Trichotomous-Ordinal

  is-irreflexive-le-Trichotomous-Ordinal :
    is-irreflexive le-Trichotomous-Ordinal
  is-irreflexive-le-Trichotomous-Ordinal =
    is-irreflexive-le-Ordinal ordinal-Trichotomous-Ordinal

  leq-Trichotomous-Ordinal :
    Relation (l1 ⊔ l2) type-Trichotomous-Ordinal
  leq-Trichotomous-Ordinal =
    leq-Ordinal ordinal-Trichotomous-Ordinal

  is-prop-leq-Trichotomous-Ordinal :
    {x y : type-Trichotomous-Ordinal} →
    is-prop (leq-Trichotomous-Ordinal x y)
  is-prop-leq-Trichotomous-Ordinal =
    is-prop-leq-Ordinal ordinal-Trichotomous-Ordinal

  leq-prop-Trichotomous-Ordinal :
    Relation-Prop (l1 ⊔ l2) type-Trichotomous-Ordinal
  leq-prop-Trichotomous-Ordinal =
    leq-prop-Ordinal ordinal-Trichotomous-Ordinal

  refl-leq-Trichotomous-Ordinal :
    is-reflexive leq-Trichotomous-Ordinal
  refl-leq-Trichotomous-Ordinal =
    refl-leq-Ordinal ordinal-Trichotomous-Ordinal

  leq-eq-Trichotomous-Ordinal :
    {x y : type-Trichotomous-Ordinal} →
    x ＝ y → leq-Trichotomous-Ordinal x y
  leq-eq-Trichotomous-Ordinal =
    leq-eq-Ordinal ordinal-Trichotomous-Ordinal

  transitive-leq-Trichotomous-Ordinal :
    is-transitive leq-Trichotomous-Ordinal
  transitive-leq-Trichotomous-Ordinal =
    transitive-leq-Ordinal ordinal-Trichotomous-Ordinal

  leq-le-Trichotomous-Ordinal :
    {x y : type-Trichotomous-Ordinal} →
    le-Trichotomous-Ordinal x y →
    leq-Trichotomous-Ordinal x y
  leq-le-Trichotomous-Ordinal =
    leq-le-Ordinal ordinal-Trichotomous-Ordinal

  antisymmetric-leq-Trichotomous-Ordinal :
    is-antisymmetric leq-Trichotomous-Ordinal
  antisymmetric-leq-Trichotomous-Ordinal =
    antisymmetric-leq-Ordinal ordinal-Trichotomous-Ordinal

  is-preorder-leq-Trichotomous-Ordinal :
    is-preorder-Relation-Prop leq-prop-Trichotomous-Ordinal
  is-preorder-leq-Trichotomous-Ordinal =
    is-preorder-leq-Ordinal ordinal-Trichotomous-Ordinal

  preorder-Trichotomous-Ordinal : Preorder l1 (l1 ⊔ l2)
  preorder-Trichotomous-Ordinal =
    preorder-Ordinal ordinal-Trichotomous-Ordinal

  poset-Trichotomous-Ordinal : Poset l1 (l1 ⊔ l2)
  poset-Trichotomous-Ordinal =
    poset-Ordinal ordinal-Trichotomous-Ordinal

  is-set-type-Trichotomous-Ordinal :
    is-set type-Trichotomous-Ordinal
  is-set-type-Trichotomous-Ordinal =
    is-set-type-Ordinal ordinal-Trichotomous-Ordinal

  set-Trichotomous-Ordinal : Set l1
  set-Trichotomous-Ordinal = set-Ordinal ordinal-Trichotomous-Ordinal

  trichotomy-Trichotomous-Ordinal :
    (x y : type-Trichotomous-Ordinal) →
    (le-Trichotomous-Ordinal x y) + (x ＝ y) + (le-Trichotomous-Ordinal y x)
  trichotomy-Trichotomous-Ordinal =
    is-trichotomous-ordinal-Trichotomous-Ordinal

  ind-Trichotomous-Ordinal :
    {l3 : Level} (P : type-Trichotomous-Ordinal → UU l3) →
    ( {x : type-Trichotomous-Ordinal} →
      ({u : type-Trichotomous-Ordinal} → le-Trichotomous-Ordinal u x → P u) →
      P x) →
    (x : type-Trichotomous-Ordinal) → P x
  ind-Trichotomous-Ordinal = ind-Ordinal ordinal-Trichotomous-Ordinal
```

## Properties

### Being trichotomous is a property

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  where

  is-prop-is-trichotomous-Ordinal : is-prop (is-trichotomous-Ordinal α)
  is-prop-is-trichotomous-Ordinal =
    is-prop-is-trichotomous-Strict-Order (strict-order-Ordinal α)

  is-trichotomous-prop-Ordinal : Prop (l1 ⊔ l2)
  is-trichotomous-prop-Ordinal =
    is-trichotomous-prop-Strict-Order (strict-order-Ordinal α)
```

### Decidable ordinals are trichotomous

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (let _<_ = le-Ordinal α)
  (dle-α : (x y : type-Ordinal α) → is-decidable (x < y))
  where

  abstract
    lower-bound-is-decidable-Ordinal :
      (a b : type-Ordinal α) →
      ({u : type-Ordinal α} → u < a → ¬ (u < b) → ¬ (b < u) → u ＝ b) →
      ¬ (b < a) → (u : type-Ordinal α) → u < a → u < b
    lower-bound-is-decidable-Ordinal a b IH b≮a u u<a =
      rec-ternary-coproduct
        ( id)
        ( λ p →
          ex-falso (b≮a (transitive-le-Ordinal α b u a u<a (pr2 p))))
        ( λ p →
          ex-falso
            ( b≮a
              ( tr
                ( λ t → le-Ordinal α t a)
                ( IH u<a (pr1 p) (pr2 p))
                ( u<a))))
        ( rec-coproduct
          ( inl)
          ( λ u≮b →
            rec-coproduct
              ( λ b<u → inr (inl (u≮b , b<u)))
              ( λ b≮u → inr (inr (u≮b , b≮u)))
              ( dle-α b u))
          ( dle-α u b))

  abstract
    eq-incomparable-is-decidable-Ordinal :
      (x y : type-Ordinal α) → ¬ (x < y) → ¬ (y < x) → x ＝ y
    eq-incomparable-is-decidable-Ordinal =
      ind²-Ordinal α
        ( λ x y → ¬ (x < y) → ¬ (y < x) → x ＝ y)
        ( λ {x} IHx y IHy x≮y y≮x →
          is-extensional-Ordinal α x y
            ( λ u →
              ( lower-bound-is-decidable-Ordinal x y
                  ( λ u<x u≮y y≮u → IHx u<x y u≮y y≮u)
                  ( y≮x)
                  ( u) ,
                lower-bound-is-decidable-Ordinal y x
                  ( λ u<y u≮x x≮u → inv (IHy u<y x≮u u≮x))
                  ( x≮y)
                  ( u))))

  abstract
    is-trichotomous-is-decidable-le-Ordinal :
      is-trichotomous-Ordinal α
    is-trichotomous-is-decidable-le-Ordinal =
      is-trichotomous-is-decidable-le-eq-incomparable-Strict-Order
        ( strict-order-Ordinal α)
        ( dle-α)
        ( eq-incomparable-is-decidable-Ordinal)
```

### Trichotomy implies weak trichotomy

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (H : is-trichotomous-Ordinal α)
  where

  ge-not-eq-not-le-is-trichotomous-Ordinal :
    (x y : type-Ordinal α) →
    ¬ le-Ordinal α x y → ¬ (x ＝ y) → le-Ordinal α y x
  ge-not-eq-not-le-is-trichotomous-Ordinal =
    ge-not-eq-not-le-Trichotomous-Strict-Order
      ( strict-order-Ordinal α , H)

module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  ge-not-eq-not-le-Trichotomous-Ordinal :
    (x y : type-Trichotomous-Ordinal α) →
    ¬ le-Trichotomous-Ordinal α x y →
    ¬ (x ＝ y) →
    le-Trichotomous-Ordinal α y x
  ge-not-eq-not-le-Trichotomous-Ordinal =
    ge-not-eq-not-le-is-trichotomous-Ordinal
      ( ordinal-Trichotomous-Ordinal α)
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α)
```

### Trichotomous ordinals are cotransitive

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (H : is-trichotomous-Ordinal α)
  where

  is-cotransitive-le-is-trichotomous-Ordinal :
    (x y z : type-Ordinal α) →
    le-Ordinal α x z →
    disjunction-type (le-Ordinal α x y) (le-Ordinal α y z)
  is-cotransitive-le-is-trichotomous-Ordinal =
    is-cotransitive-le-Trichotomous-Strict-Order
      ( strict-order-Ordinal α , H)

module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  is-cotransitive-le-Trichotomous-Ordinal :
    (x y z : type-Trichotomous-Ordinal α) →
    le-Trichotomous-Ordinal α x z →
    disjunction-type
      ( le-Trichotomous-Ordinal α x y)
      ( le-Trichotomous-Ordinal α y z)
  is-cotransitive-le-Trichotomous-Ordinal =
    is-cotransitive-le-is-trichotomous-Ordinal
      ( ordinal-Trichotomous-Ordinal α)
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α)
```

### Trichotomous ordinals are decidable

```agda
module _
  {l1 l2 : Level}
  (α : Ordinal l1 l2)
  (tα : is-trichotomous-Ordinal α)
  where

  is-decidable-le-is-trichotomous-Ordinal :
    (x y : type-Ordinal α) → is-decidable (le-Ordinal α x y)
  is-decidable-le-is-trichotomous-Ordinal x y =
    rec-ternary-coproduct
      ( inl)
      ( λ x=y →
        inr
          ( λ x<y →
            is-irreflexive-le-Ordinal α y
              ( tr (λ t → le-Ordinal α t y) x=y x<y)))
      ( λ y<x →
        inr
          ( λ x<y →
            is-irreflexive-le-Ordinal α x
              ( transitive-le-Ordinal α x y x y<x x<y)))
      ( tα x y)

  is-decidable-eq-is-trichotomous-Ordinal :
    (x y : type-Ordinal α) → is-decidable (x ＝ y)
  is-decidable-eq-is-trichotomous-Ordinal x y =
    rec-ternary-coproduct
      ( λ x<y →
        inr
          ( λ x=y →
            is-irreflexive-le-Ordinal α y
              ( tr (λ t → le-Ordinal α t y) x=y x<y)))
      ( inl)
      ( λ y<x →
        inr
          ( λ x=y →
            is-irreflexive-le-Ordinal α y
              ( tr (le-Ordinal α y) x=y y<x)))
      ( tα x y)

  has-decidable-equality-is-trichotomous-Ordinal :
    has-decidable-equality (type-Ordinal α)
  has-decidable-equality-is-trichotomous-Ordinal =
    is-decidable-eq-is-trichotomous-Ordinal
```

```agda
module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  is-decidable-le-Trichotomous-Ordinal :
    (x y : type-Trichotomous-Ordinal α) →
    is-decidable (le-Trichotomous-Ordinal α x y)
  is-decidable-le-Trichotomous-Ordinal =
    is-decidable-le-is-trichotomous-Ordinal
      ( ordinal-Trichotomous-Ordinal α)
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α)

  has-decidable-equality-Trichotomous-Ordinal :
    has-decidable-equality (type-Trichotomous-Ordinal α)
  has-decidable-equality-Trichotomous-Ordinal =
    has-decidable-equality-is-trichotomous-Ordinal
      ( ordinal-Trichotomous-Ordinal α)
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α)

  discrete-type-Trichotomous-Ordinal : Discrete-Type l1
  discrete-type-Trichotomous-Ordinal =
    ( type-Trichotomous-Ordinal α ,
      has-decidable-equality-Trichotomous-Ordinal)
```

### Trichotomous ordinals are total

```agda
module _
  {l1 l2 : Level}
  (α : Trichotomous-Ordinal l1 l2)
  where

  is-total-leq-Trichotomous-Ordinal :
    is-total-Poset (poset-Trichotomous-Ordinal α)
  is-total-leq-Trichotomous-Ordinal x y =
    rec-ternary-coproduct
      ( λ x<y → inl-disjunction (leq-le-Trichotomous-Ordinal α x<y))
      ( λ x=y → inl-disjunction (leq-eq-Trichotomous-Ordinal α x=y))
      ( λ y<x → inr-disjunction (leq-le-Trichotomous-Ordinal α y<x))
      ( is-trichotomous-ordinal-Trichotomous-Ordinal α x y)

  total-order-Trichotomous-Ordinal : Total-Order l1 (l1 ⊔ l2)
  total-order-Trichotomous-Ordinal =
    ( poset-Trichotomous-Ordinal α ,
      is-total-leq-Trichotomous-Ordinal)
```
