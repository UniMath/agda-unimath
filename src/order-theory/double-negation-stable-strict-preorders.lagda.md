# Double negation stable strict preorders

```agda
module order-theory.double-negation-stable-strict-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-equality
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.double-negation-elimination

open import order-theory.strict-orders
open import order-theory.strict-preorders
```

</details>

## Idea

A [strict preorder](order-theory.strict-preorders.md) is
{{#concept "double negation stable" Disambiguation="strict preorder" Agda=has-double-negation-stable-le-Strict-Preorder Agda=Double-Negation-Stable-Strict-Preorder}}
if for all pairs of elements `x` and `y` the implication `¬¬ (x < y) ⇒ (x < y)`
holds.

## Definitions

### The predicate on strict preorders

```agda
has-double-negation-stable-le-Strict-Preorder :
  {l1 l2 : Level} → Strict-Preorder l1 l2 → UU (l1 ⊔ l2)
has-double-negation-stable-le-Strict-Preorder P =
  (x y : type-Strict-Preorder P) →
  has-double-negation-elim (le-Strict-Preorder P x y)
```

### The type of double negation stable strict preorders

```agda
Double-Negation-Stable-Strict-Preorder :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Double-Negation-Stable-Strict-Preorder l1 l2 =
  Σ (Strict-Preorder l1 l2) has-double-negation-stable-le-Strict-Preorder

module _
  {l1 l2 : Level}
  (A : Double-Negation-Stable-Strict-Preorder l1 l2)
  where

  strict-preorder-Double-Negation-Stable-Strict-Preorder :
    Strict-Preorder l1 l2
  strict-preorder-Double-Negation-Stable-Strict-Preorder = pr1 A

  type-Double-Negation-Stable-Strict-Preorder : UU l1
  type-Double-Negation-Stable-Strict-Preorder =
    type-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder)

  le-prop-Double-Negation-Stable-Strict-Preorder :
    Relation-Prop l2 type-Double-Negation-Stable-Strict-Preorder
  le-prop-Double-Negation-Stable-Strict-Preorder =
    le-prop-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder)

  le-Double-Negation-Stable-Strict-Preorder :
    Relation l2 type-Double-Negation-Stable-Strict-Preorder
  le-Double-Negation-Stable-Strict-Preorder =
    le-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder)

  is-prop-le-Double-Negation-Stable-Strict-Preorder :
    (x y : type-Double-Negation-Stable-Strict-Preorder) →
    is-prop (le-Double-Negation-Stable-Strict-Preorder x y)
  is-prop-le-Double-Negation-Stable-Strict-Preorder =
    is-prop-le-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder)

  is-irreflexive-le-Double-Negation-Stable-Strict-Preorder :
    is-irreflexive le-Double-Negation-Stable-Strict-Preorder
  is-irreflexive-le-Double-Negation-Stable-Strict-Preorder =
    is-irreflexive-le-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder)

  is-transitive-le-Double-Negation-Stable-Strict-Preorder :
    is-transitive le-Double-Negation-Stable-Strict-Preorder
  is-transitive-le-Double-Negation-Stable-Strict-Preorder =
    is-transitive-le-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder)

  has-double-negation-stable-le-Double-Negation-Stable-Strict-Preorder :
    has-double-negation-stable-le-Strict-Preorder
      strict-preorder-Double-Negation-Stable-Strict-Preorder
  has-double-negation-stable-le-Double-Negation-Stable-Strict-Preorder =
    pr2 A
```

## Properties

### Weak trichotomy gives double negation stable strict inequality

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Preorder l1 l2)
  (ge-neq-nle-A :
    (x y : type-Strict-Preorder A) →
    ¬ le-Strict-Preorder A x y →
    ¬ (x ＝ y) →
    le-Strict-Preorder A y x)
  where

  has-double-negation-stable-le-ge-neq-nle-Strict-Preorder :
    has-double-negation-stable-le-Strict-Preorder A
  has-double-negation-stable-le-ge-neq-nle-Strict-Preorder x y nnx<y =
    ge-neq-nle-A y x
      ( λ y<x →
        nnx<y
          ( λ x<y →
            is-irreflexive-le-Strict-Preorder A x
              ( is-transitive-le-Strict-Preorder A x y x y<x x<y)))
      ( λ y=x →
        nnx<y
          ( λ x<y →
            is-irreflexive-le-Strict-Preorder A y
              ( tr (λ t → le-Strict-Preorder A t y) (inv y=x) x<y)))
```

### Weak trichotomy gives extensional incomparability

```agda
module _
  {l1 l2 : Level}
  (A : Strict-Preorder l1 l2)
  (ge-neq-nle-A :
    (x y : type-Strict-Preorder A) →
    ¬ le-Strict-Preorder A x y →
    ¬ (x ＝ y) →
    le-Strict-Preorder A y x)
  (dneq-A : has-double-negation-stable-equality (type-Strict-Preorder A))
  where

  ge-neq-nle-eq-incomparable-Strict-Preorder :
    (x y : type-Strict-Preorder A) →
    ¬ le-Strict-Preorder A x y →
    ¬ le-Strict-Preorder A y x →
    x ＝ y
  ge-neq-nle-eq-incomparable-Strict-Preorder x y x≮y y≮x =
    dneq-A x y (λ x≠y → y≮x (ge-neq-nle-A x y x≮y x≠y))
```

### Extensional incomparability and double negation stability gives weak trichotomy

```agda
module _
  {l1 l2 : Level}
  (A : Double-Negation-Stable-Strict-Preorder l1 l2)
  (eq-inc-A :
    (x y : type-Double-Negation-Stable-Strict-Preorder A) →
    ¬ le-Double-Negation-Stable-Strict-Preorder A x y →
    ¬ le-Double-Negation-Stable-Strict-Preorder A y x →
    x ＝ y)
  where

  extensionality-eq-incomparable-Double-Negation-Stable-Strict-Preorder :
    extensionality-principle-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder A)
  extensionality-eq-incomparable-Double-Negation-Stable-Strict-Preorder =
    extensionality-eq-incomparable-Strict-Preorder
      ( strict-preorder-Double-Negation-Stable-Strict-Preorder A)
      ( eq-inc-A)

  ge-neq-nle-eq-incomparable-Double-Negation-Stable-Strict-Preorder :
    (x y : type-Double-Negation-Stable-Strict-Preorder A) →
    ¬ le-Double-Negation-Stable-Strict-Preorder A x y →
    ¬ (x ＝ y) →
    le-Double-Negation-Stable-Strict-Preorder A y x
  ge-neq-nle-eq-incomparable-Double-Negation-Stable-Strict-Preorder
    x y x≮y x≠y =
    has-double-negation-stable-le-Double-Negation-Stable-Strict-Preorder A y x
      ( λ y≮x → x≠y (eq-inc-A x y x≮y y≮x))
```
