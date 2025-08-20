# The inequality on the directed interval type

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.inequality-directed-interval
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders

open import simplicial-type-theory.directed-interval I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

The
{{#concept "directed relation" Disambiguation="on the directed interval type" Agda=_≤-Δ¹_}}
on the [directed interval type](simplicial-type-theory.directed-interval.md)
`Δ¹` is a [total order](order-theory.total-orders.md) with `0▵` as the
[bottom element](order-theory.bottom-elements-posets.md), and `1▵` as the
[top element](order-theory.top-elements-posets.md).

**Computational behavior.** Although the directed interval is defined from the
bounded total order `I`, it is marked `opaque`, meaning that we have to state
explicitly to Agda that we wish to unfold the basic definitions in order for
Agda to draw any connection between the two objects at a later point.

## Definitions

### The directed relation on the directed interval

```agda
opaque
  unfolding Δ¹

  infix 30 _≤-Δ¹_

  _≤-Δ¹_ : Δ¹ → Δ¹ → UU I2
  _≤-Δ¹_ = leq-Nontrivial-Bounded-Total-Order I

  is-prop-leq-Δ¹ : {x y : Δ¹} → is-prop (x ≤-Δ¹ y)
  is-prop-leq-Δ¹ {x} {y} = is-prop-leq-Nontrivial-Bounded-Total-Order I x y

leq-Δ¹-Prop : (x y : Δ¹) → Prop I2
leq-Δ¹-Prop x y = (x ≤-Δ¹ y , is-prop-leq-Δ¹)

leq-Δ¹ : Δ¹ → Δ¹ → UU I2
leq-Δ¹ = _≤-Δ¹_
```

### The directed relation is a total order

```agda
opaque
  unfolding Δ¹ _≤-Δ¹_

  refl-leq-Δ¹ : {x : Δ¹} → x ≤-Δ¹ x
  refl-leq-Δ¹ {x} = refl-leq-Nontrivial-Bounded-Total-Order I x

  transitive-leq-Δ¹ : {x y z : Δ¹} → y ≤-Δ¹ z → x ≤-Δ¹ y → x ≤-Δ¹ z
  transitive-leq-Δ¹ {x} {y} {z} =
    transitive-leq-Nontrivial-Bounded-Total-Order I x y z

  antisymmetric-leq-Δ¹ : {x y : Δ¹} → x ≤-Δ¹ y → y ≤-Δ¹ x → x ＝ y
  antisymmetric-leq-Δ¹ {x} {y} =
    antisymmetric-leq-Nontrivial-Bounded-Total-Order I x y

  is-total-leq-Δ¹ : (x y : Δ¹) → disjunction-type (x ≤-Δ¹ y) (y ≤-Δ¹ x)
  is-total-leq-Δ¹ =
    is-total-Total-Order (total-order-Nontrivial-Bounded-Total-Order I)

total-leq-Δ¹' : {x y : Δ¹} → (x ≤-Δ¹ y) * (y ≤-Δ¹ x)
total-leq-Δ¹' {x} {y} =
  map-join-disjunction-Prop
    ( leq-Δ¹-Prop x y)
    ( leq-Δ¹-Prop y x)
    ( is-total-leq-Δ¹ x y)
```

**Note.** We define totality using the
[join operation](synthetic-homotopy-theory.joins-of-types.md) on types as we may
commonly want to eliminate the directed relation into types, and not just
propositions. Moreover, we can enable rewrite rules for the join operation by
importing the module
[`synthetic-homotopy-theory.rewriting-pushouts`](synthetic-homotopy-theory.rewriting-pushouts.md),
since it is defined in terms of the
[standard pushout](synthetic-homotopy-theory.pushouts.md).

### The source and target of the directed interval are bottom and top elements

```agda
opaque
  unfolding Δ¹ _≤-Δ¹_

  min-leq-Δ¹ : {x : Δ¹} → 0▵ ≤-Δ¹ x
  min-leq-Δ¹ {x} = is-bottom-element-bottom-Nontrivial-Bounded-Total-Order I x

  max-leq-Δ¹ : {x : Δ¹} → x ≤-Δ¹ 1▵
  max-leq-Δ¹ {x} = is-top-element-top-Nontrivial-Bounded-Total-Order I x
```

## Operations

### The binary max function on the directed interval

```agda
cocone-max-Δ¹ : (t s : Δ¹) → cocone pr1 pr2 Δ¹
cocone-max-Δ¹ t s =
  ( (λ _ → s) , (λ _ → t) , (λ (p , q) → antisymmetric-leq-Δ¹ q p))

max-Δ¹ : Δ¹ → Δ¹ → Δ¹
max-Δ¹ t s = cogap-join Δ¹ (cocone-max-Δ¹ t s) total-leq-Δ¹'

abstract
  compute-left-max-Δ¹ : {t s : Δ¹} → s ≤-Δ¹ t → max-Δ¹ t s ＝ t
  compute-left-max-Δ¹ {t} {s} p =
    ( ap
      ( cogap-join Δ¹ (cocone-max-Δ¹ t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-Δ¹ is-prop-leq-Δ¹))) ∙
    ( compute-inr-cogap-join (cocone-max-Δ¹ t s) p)

abstract
  compute-right-max-Δ¹ : {t s : Δ¹} → t ≤-Δ¹ s → max-Δ¹ t s ＝ s
  compute-right-max-Δ¹ {t} {s} p =
    ( ap
      ( cogap-join Δ¹ (cocone-max-Δ¹ t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-Δ¹ is-prop-leq-Δ¹))) ∙
    ( compute-inl-cogap-join (cocone-max-Δ¹ t s) p)
```

### The binary minimum function on the directed interval

```agda
cocone-min-Δ¹ : (t s : Δ¹) → cocone pr1 pr2 Δ¹
cocone-min-Δ¹ t s =
  ( (λ _ → t) , (λ _ → s) , (λ (p , q) → antisymmetric-leq-Δ¹ p q))

min-Δ¹ : Δ¹ → Δ¹ → Δ¹
min-Δ¹ t s = cogap-join Δ¹ (cocone-min-Δ¹ t s) total-leq-Δ¹'

abstract
  compute-left-min-Δ¹ : {t s : Δ¹} (p : t ≤-Δ¹ s) → min-Δ¹ t s ＝ t
  compute-left-min-Δ¹ {t} {s} p =
    ( ap
      ( cogap-join Δ¹ (cocone-min-Δ¹ t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-Δ¹ is-prop-leq-Δ¹))) ∙
    ( compute-inl-cogap-join (cocone-min-Δ¹ t s) p)

abstract
  compute-right-min-Δ¹ : {t s : Δ¹} (p : s ≤-Δ¹ t) → min-Δ¹ t s ＝ s
  compute-right-min-Δ¹ {t} {s} p =
    ( ap
      ( cogap-join Δ¹ (cocone-min-Δ¹ t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-Δ¹ is-prop-leq-Δ¹))) ∙
    ( compute-inr-cogap-join (cocone-min-Δ¹ t s) p)
```

### The inequality binary propositional relation on the directed interval

```agda
min-leq-eq-Δ¹ : {x y : Δ¹} → x ＝ 0▵ → x ≤-Δ¹ y
min-leq-eq-Δ¹ refl = min-leq-Δ¹

max-leq-eq-Δ¹ : {x y : Δ¹} → y ＝ 1▵ → x ≤-Δ¹ y
max-leq-eq-Δ¹ refl = max-leq-Δ¹

leq-eq-Δ¹ : {x y : Δ¹} → x ＝ y → x ≤-Δ¹ y
leq-eq-Δ¹ refl = refl-leq-Δ¹

leq-inv-eq-Δ¹ : {x y : Δ¹} → x ＝ y → y ≤-Δ¹ x
leq-inv-eq-Δ¹ = leq-eq-Δ¹ ∘ inv
```

### The poset structure on the directed interval

```agda
Δ¹-Preorder : Preorder I1 I2
pr1 Δ¹-Preorder = Δ¹
pr1 (pr2 Δ¹-Preorder) = leq-Δ¹-Prop
pr1 (pr2 (pr2 Δ¹-Preorder)) x = refl-leq-Δ¹ {x}
pr2 (pr2 (pr2 Δ¹-Preorder)) x y z = transitive-leq-Δ¹

Δ¹-Poset : Poset I1 I2
pr1 Δ¹-Poset = Δ¹-Preorder
pr2 Δ¹-Poset x y = antisymmetric-leq-Δ¹
```

### The total order on the directed interval

```agda
Δ¹-Total-Order : Total-Order I1 I2
Δ¹-Total-Order = (Δ¹-Poset , is-total-leq-Δ¹)
```

## Properties

### The directed interval is a set

```agda
is-set-Δ¹ : is-set Δ¹
is-set-Δ¹ = is-set-type-Poset Δ¹-Poset

Δ¹-Set : Set I1
Δ¹-Set = (Δ¹ , is-set-Δ¹)

Id-Δ¹-Prop : Δ¹ → Δ¹ → Prop I1
Id-Δ¹-Prop = Id-Prop Δ¹-Set

{-# INLINE Id-Δ¹-Prop #-}
```

### The maximal element is not less than or equal to the bottom element of the directed interval

```agda
not-leq-target-source-Δ¹ : ¬ (1▵ ≤-Δ¹ 0▵)
not-leq-target-source-Δ¹ leq-1-0 =
  is-nontrivial-Δ¹ (antisymmetric-leq-Δ¹ min-leq-Δ¹ leq-1-0)
```

### The directed relation `t ≤-Δ¹ s` is equivalent to the relation `max-Δ¹ t s ＝ s`

> This remains to be formalized.

### The directed relation `t ≤-Δ¹ s` is equivalent to the relation `min-Δ¹ t s ＝ t`

> This remains to be formalized.

### The canonical inclusion of the booleans into the directed interval is an embedding

```agda
is-emb-map-directed-interval-bool : is-emb map-directed-interval-bool
is-emb-map-directed-interval-bool =
  is-emb-is-injective is-set-Δ¹ is-injective-map-directed-interval-bool
```

### The canonical inclusion of the booleans into the directed interval preserves and reflects its ordering

> This remains to be formalized.
