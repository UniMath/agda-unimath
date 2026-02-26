# Trichotomous strict preorders

```agda
module order-theory.trichotomous-strict-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.cotransitive-strict-preorders
open import order-theory.similarity-of-elements-strict-preorders
open import order-theory.strict-orders
open import order-theory.strict-preorders
```

</details>

## Idea

A [strict preorder](order-theory.strict-preorders.md) is
{{#concept "trichotomous" Agda=is-trichotomous-Strict-Preorder Agda=Trichotomous-Strict-Preorder}}
if for every two elements `x` and `y`, either `x < y`, `x ＝ y`, or `y < x`.

Trichotomous strict preorders are in particular extensional, and hence coincide
with [trichotomous strict orders](order-theory.trichotomous-strict-orders.md).

## Definitions

### The predicate on strict preorders of being trichotomous

```agda
is-trichotomous-Strict-Preorder :
  {l1 l2 : Level} → Strict-Preorder l1 l2 → UU (l1 ⊔ l2)
is-trichotomous-Strict-Preorder A =
  (x y : type-Strict-Preorder A) →
  (le-Strict-Preorder A x y) + (x ＝ y) + (le-Strict-Preorder A y x)
```

### The type of trichotomous strict preorders

```agda
Trichotomous-Strict-Preorder : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Trichotomous-Strict-Preorder l1 l2 =
  Σ (Strict-Preorder l1 l2) is-trichotomous-Strict-Preorder

module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Preorder l1 l2)
  where

  strict-preorder-Trichotomous-Strict-Preorder : Strict-Preorder l1 l2
  strict-preorder-Trichotomous-Strict-Preorder = pr1 A

  type-Trichotomous-Strict-Preorder : UU l1
  type-Trichotomous-Strict-Preorder =
    type-Strict-Preorder strict-preorder-Trichotomous-Strict-Preorder

  le-prop-Trichotomous-Strict-Preorder :
    Relation-Prop l2 type-Trichotomous-Strict-Preorder
  le-prop-Trichotomous-Strict-Preorder =
    le-prop-Strict-Preorder strict-preorder-Trichotomous-Strict-Preorder

  le-Trichotomous-Strict-Preorder :
    Relation l2 type-Trichotomous-Strict-Preorder
  le-Trichotomous-Strict-Preorder =
    le-Strict-Preorder strict-preorder-Trichotomous-Strict-Preorder

  is-prop-le-Trichotomous-Strict-Preorder :
    (x y : type-Trichotomous-Strict-Preorder) →
    is-prop (le-Trichotomous-Strict-Preorder x y)
  is-prop-le-Trichotomous-Strict-Preorder =
    is-prop-le-Strict-Preorder strict-preorder-Trichotomous-Strict-Preorder

  is-irreflexive-le-Trichotomous-Strict-Preorder :
    is-irreflexive le-Trichotomous-Strict-Preorder
  is-irreflexive-le-Trichotomous-Strict-Preorder =
    is-irreflexive-le-Strict-Preorder strict-preorder-Trichotomous-Strict-Preorder

  is-transitive-le-Trichotomous-Strict-Preorder :
    is-transitive le-Trichotomous-Strict-Preorder
  is-transitive-le-Trichotomous-Strict-Preorder =
    is-transitive-le-Strict-Preorder strict-preorder-Trichotomous-Strict-Preorder

  is-trichotomous-Strict-Preorder-Trichotomous-Strict-Preorder :
    is-trichotomous-Strict-Preorder strict-preorder-Trichotomous-Strict-Preorder
  is-trichotomous-Strict-Preorder-Trichotomous-Strict-Preorder = pr2 A

  trichotomy-Trichotomous-Strict-Preorder :
    (x y : type-Trichotomous-Strict-Preorder) →
    (le-Trichotomous-Strict-Preorder x y) + (x ＝ y) + (le-Trichotomous-Strict-Preorder y x)
  trichotomy-Trichotomous-Strict-Preorder =
    is-trichotomous-Strict-Preorder-Trichotomous-Strict-Preorder
```

## Properties

### Trichotomous strict preorders are strict orders

```agda
module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Preorder l1 l2)
  where

  abstract
    extensionality-Trichotomous-Strict-Preorder :
      extensionality-principle-Strict-Preorder
        ( strict-preorder-Trichotomous-Strict-Preorder A)
    extensionality-Trichotomous-Strict-Preorder x y s =
      rec-ternary-coproduct
        ( λ x<y →
          ex-falso
            ( is-irreflexive-le-Trichotomous-Strict-Preorder A y
              ( pr1 (pr2 s y) x<y)))
        ( λ x=y → x=y)
        ( λ y<x →
          ex-falso
            ( is-irreflexive-le-Trichotomous-Strict-Preorder A x
              ( pr2 (pr2 s x) y<x)))
        ( trichotomy-Trichotomous-Strict-Preorder A x y)

  strict-order-Trichotomous-Strict-Preorder : Strict-Order l1 l2
  strict-order-Trichotomous-Strict-Preorder =
    ( strict-preorder-Trichotomous-Strict-Preorder A ,
      extensionality-Trichotomous-Strict-Preorder)

  is-set-type-Trichotomous-Strict-Preorder :
    is-set (type-Trichotomous-Strict-Preorder A)
  is-set-type-Trichotomous-Strict-Preorder =
    is-set-type-Strict-Order strict-order-Trichotomous-Strict-Preorder
```

### Being trichotomous is a property

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Preorder l1 l2)
  where

  abstract
    is-prop-trichotomy-is-trichotomous-Strict-Preorder :
      is-trichotomous-Strict-Preorder A →
      (x y : type-Strict-Preorder A) →
      is-prop ((le-Strict-Preorder A x y) + (x ＝ y) + (le-Strict-Preorder A y x))
    is-prop-trichotomy-is-trichotomous-Strict-Preorder tA x y =
      is-prop-coproduct
        ( λ x<y →
          rec-coproduct
            ( λ x=y →
              is-irreflexive-le-Strict-Preorder A y
                ( tr (λ t → le-Strict-Preorder A t y) x=y x<y))
            ( λ y<x →
              is-irreflexive-le-Strict-Preorder A x
                ( is-transitive-le-Strict-Preorder A x y x y<x x<y)))
        ( is-prop-le-Strict-Preorder A x y)
        ( is-prop-coproduct
          ( λ x=y y<x →
            is-irreflexive-le-Strict-Preorder A y
              ( tr (le-Strict-Preorder A y) x=y y<x))
          ( is-set-type-Trichotomous-Strict-Preorder (A , tA) x y)
          ( is-prop-le-Strict-Preorder A y x))

  abstract
    is-prop-is-trichotomous-Strict-Preorder :
      is-prop (is-trichotomous-Strict-Preorder A)
    is-prop-is-trichotomous-Strict-Preorder tA =
      is-prop-Π
        ( λ x →
          is-prop-Π (is-prop-trichotomy-is-trichotomous-Strict-Preorder tA x))
        ( tA)

  is-trichotomous-prop-Strict-Preorder : Prop (l1 ⊔ l2)
  is-trichotomous-prop-Strict-Preorder =
    ( is-trichotomous-Strict-Preorder A ,
      is-prop-is-trichotomous-Strict-Preorder)
```

### Trichotomy implies weak trichotomy

```agda
module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Preorder l1 l2)
  where

  ge-not-eq-not-le-Trichotomous-Strict-Preorder :
    (x y : type-Trichotomous-Strict-Preorder A) →
    ¬ le-Trichotomous-Strict-Preorder A x y →
    ¬ (x ＝ y) →
    le-Trichotomous-Strict-Preorder A y x
  ge-not-eq-not-le-Trichotomous-Strict-Preorder x y x≮y x≠y =
    rec-ternary-coproduct
      ( λ x<y → ex-falso (x≮y x<y))
      ( λ x=y → ex-falso (x≠y x=y))
      ( λ y<x → y<x)
      ( trichotomy-Trichotomous-Strict-Preorder A x y)
```

### Trichotomous strict preorders are cotransitive

```agda
module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Preorder l1 l2)
  where

  is-cotransitive-le-Trichotomous-Strict-Preorder :
    is-cotransitive-le-Strict-Preorder
      ( strict-preorder-Trichotomous-Strict-Preorder A)
  is-cotransitive-le-Trichotomous-Strict-Preorder x y z x<z =
    rec-ternary-coproduct
      ( λ x<y →
        inl-disjunction x<y)
      ( λ x=y →
        inr-disjunction
          ( tr (λ t → le-Trichotomous-Strict-Preorder A t z) x=y x<z))
      ( λ y<x →
        inr-disjunction
          ( is-transitive-le-Trichotomous-Strict-Preorder A y x z x<z y<x))
      ( trichotomy-Trichotomous-Strict-Preorder A x y)
```

### Trichotomous strict preorders are decidable

```agda
module _
  {l1 l2 : Level}
  (A : Trichotomous-Strict-Preorder l1 l2)
  where

  is-decidable-le-Trichotomous-Strict-Preorder :
    (x y : type-Trichotomous-Strict-Preorder A) →
    is-decidable (le-Trichotomous-Strict-Preorder A x y)
  is-decidable-le-Trichotomous-Strict-Preorder x y =
    rec-ternary-coproduct
      ( inl)
      ( λ x=y →
        inr
          ( λ x<y →
            is-irreflexive-le-Trichotomous-Strict-Preorder A y
              ( tr (λ t → le-Trichotomous-Strict-Preorder A t y) x=y x<y)))
      ( λ y<x →
        inr
          ( λ x<y →
            is-irreflexive-le-Trichotomous-Strict-Preorder A x
              ( is-transitive-le-Trichotomous-Strict-Preorder A x y x y<x x<y)))
      ( trichotomy-Trichotomous-Strict-Preorder A x y)

  is-decidable-eq-Trichotomous-Strict-Preorder :
    (x y : type-Trichotomous-Strict-Preorder A) → is-decidable (x ＝ y)
  is-decidable-eq-Trichotomous-Strict-Preorder x y =
    rec-ternary-coproduct
      ( λ x<y →
        inr
          ( λ x=y →
            is-irreflexive-le-Trichotomous-Strict-Preorder A y
              ( tr (λ t → le-Trichotomous-Strict-Preorder A t y) x=y x<y)))
      ( inl)
      ( λ y<x →
        inr
          ( λ x=y →
            is-irreflexive-le-Trichotomous-Strict-Preorder A y
              ( tr (le-Trichotomous-Strict-Preorder A y) x=y y<x)))
      ( trichotomy-Trichotomous-Strict-Preorder A x y)

  has-decidable-equality-Trichotomous-Strict-Preorder :
    has-decidable-equality (type-Trichotomous-Strict-Preorder A)
  has-decidable-equality-Trichotomous-Strict-Preorder =
    is-decidable-eq-Trichotomous-Strict-Preorder
```

### Decidable strict preorders with extensional incomparability are trichotomous

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Preorder l1 l2)
  (dle-A :
    (x y : type-Strict-Preorder A) →
    is-decidable (le-Strict-Preorder A x y))
  (eq-incomparable-A :
    (x y : type-Strict-Preorder A) →
    ¬ le-Strict-Preorder A x y → ¬ le-Strict-Preorder A y x → x ＝ y)
  where

  is-trichotomous-is-decidable-le-eq-incomparable-Strict-Preorder :
    is-trichotomous-Strict-Preorder A
  is-trichotomous-is-decidable-le-eq-incomparable-Strict-Preorder x y =
    rec-coproduct
      ( inl)
      ( λ x≮y →
        rec-coproduct
          ( λ y<x → inr (inr y<x))
          ( λ y≮x → inr (inl (eq-incomparable-A x y x≮y y≮x)))
          ( dle-A y x))
      ( dle-A x y)
```
