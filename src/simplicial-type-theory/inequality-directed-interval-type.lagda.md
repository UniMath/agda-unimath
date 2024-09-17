# The inequality on the directed interval type

```agda
module simplicial-type-theory.inequality-directed-interval-type where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
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

open import simplicial-type-theory.directed-interval-type

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
```

</details>

## Idea

The
{{#concept "directed relation" Disambiguation="on the directed interval type" Agda=_≤-𝟚_}}
on the
[directed interval type](simplicial-type-theory.directed-interval-type.md) `𝟚`
is a [total order](order-theory.total-orders.md) with `0₂` as the
[bottom element](order-theory.bottom-elements-posets.md), and `1₂` as the
[top element](order-theory.top-elements-posets.md).

## Postulates

### The directed relation on the directed interval

```agda
postulate
  _≤-𝟚_ : 𝟚 → 𝟚 → UU lzero

  is-prop-leq-𝟚 : {x y : 𝟚} → is-prop (x ≤-𝟚 y)

infix 30 _≤-𝟚_

leq-𝟚 : 𝟚 → 𝟚 → UU lzero
leq-𝟚 = _≤-𝟚_
```

### The directed relation is a total order

```agda
postulate
  refl-leq-𝟚 : {x : 𝟚} → x ≤-𝟚 x

  transitive-leq-𝟚 : {x y z : 𝟚} → y ≤-𝟚 z → x ≤-𝟚 y → x ≤-𝟚 z

  antisymmetric-leq-𝟚 : {x y : 𝟚} → x ≤-𝟚 y → y ≤-𝟚 x → x ＝ y

  total-leq-𝟚 : {x y : 𝟚} → (x ≤-𝟚 y) * (y ≤-𝟚 x)
```

**Note.** We define totality using the
[join operation](synthetic-homotopy-theory.joins-of-types.md) on types as we may
commonly want to eliminate the directed relation into types, and not just
propositions. Moreover, the join operation is defined in terms of the
[standard pushout](synthetic-homotopy-theory.pushouts.md) which we can enable
rewrite rules for by importing the module
[`synthetic-homotopy-theory.rewriting-pushouts`](synthetic-homotopy-theory.rewriting-pushouts.md).

### The source and target of the directed interval are bottom and top elements

```agda
postulate
  min-leq-𝟚 : {x : 𝟚} → 0₂ ≤-𝟚 x

  max-leq-𝟚 : {x : 𝟚} → x ≤-𝟚 1₂
```

## Operations

### The binary max function on the directed interval

```agda
cocone-max-𝟚 : (t s : 𝟚) → cocone pr1 pr2 𝟚
cocone-max-𝟚 t s =
  ( (λ _ → s) , (λ _ → t) , (λ (p , q) → antisymmetric-leq-𝟚 q p))

max-𝟚 : 𝟚 → 𝟚 → 𝟚
max-𝟚 t s = cogap-join 𝟚 (cocone-max-𝟚 t s) total-leq-𝟚

abstract
  compute-left-max-𝟚 : {t s : 𝟚} → s ≤-𝟚 t → max-𝟚 t s ＝ t
  compute-left-max-𝟚 {t} {s} p =
    ( ap
      ( cogap-join 𝟚 (cocone-max-𝟚 t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-𝟚 is-prop-leq-𝟚))) ∙
    ( compute-inr-cogap-join (cocone-max-𝟚 t s) p)

abstract
  compute-right-max-𝟚 : {t s : 𝟚} → t ≤-𝟚 s → max-𝟚 t s ＝ s
  compute-right-max-𝟚 {t} {s} p =
    ( ap
      ( cogap-join 𝟚 (cocone-max-𝟚 t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-𝟚 is-prop-leq-𝟚))) ∙
    ( compute-inl-cogap-join (cocone-max-𝟚 t s) p)
```

### The binary minimum function on the directed interval

```agda
cocone-min-𝟚 : (t s : 𝟚) → cocone pr1 pr2 𝟚
cocone-min-𝟚 t s =
  ( (λ _ → t) , (λ _ → s) , (λ (p , q) → antisymmetric-leq-𝟚 p q))

min-𝟚 : 𝟚 → 𝟚 → 𝟚
min-𝟚 t s = cogap-join 𝟚 (cocone-min-𝟚 t s) total-leq-𝟚

abstract
  compute-left-min-𝟚 : {t s : 𝟚} (p : t ≤-𝟚 s) → min-𝟚 t s ＝ t
  compute-left-min-𝟚 {t} {s} p =
    ( ap
      ( cogap-join 𝟚 (cocone-min-𝟚 t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-𝟚 is-prop-leq-𝟚))) ∙
    ( compute-inl-cogap-join (cocone-min-𝟚 t s) p)

abstract
  compute-right-min-𝟚 : {t s : 𝟚} (p : s ≤-𝟚 t) → min-𝟚 t s ＝ s
  compute-right-min-𝟚 {t} {s} p =
    ( ap
      ( cogap-join 𝟚 (cocone-min-𝟚 t s))
      ( eq-is-prop (is-prop-join-is-prop is-prop-leq-𝟚 is-prop-leq-𝟚))) ∙
    ( compute-inr-cogap-join (cocone-min-𝟚 t s) p)
```

## Definitions

### The inequality binary propositional relation on the directed interval

```agda
leq-𝟚-Prop : (x y : 𝟚) → Prop lzero
leq-𝟚-Prop x y = (x ≤-𝟚 y , is-prop-leq-𝟚)

{-# INLINE leq-𝟚-Prop #-}

min-leq-eq-𝟚 : {x y : 𝟚} → x ＝ 0₂ → x ≤-𝟚 y
min-leq-eq-𝟚 refl = min-leq-𝟚

max-leq-eq-𝟚 : {x y : 𝟚} → y ＝ 1₂ → x ≤-𝟚 y
max-leq-eq-𝟚 refl = max-leq-𝟚

leq-eq-𝟚 : {x y : 𝟚} → x ＝ y → x ≤-𝟚 y
leq-eq-𝟚 refl = refl-leq-𝟚

leq-inv-eq-𝟚 : {x y : 𝟚} → x ＝ y → y ≤-𝟚 x
leq-inv-eq-𝟚 = leq-eq-𝟚 ∘ inv
```

### The poset structure on the directed interval

```agda
𝟚-Preorder : Preorder lzero lzero
pr1 𝟚-Preorder = 𝟚
pr1 (pr2 𝟚-Preorder) = leq-𝟚-Prop
pr1 (pr2 (pr2 𝟚-Preorder)) x = refl-leq-𝟚 {x}
pr2 (pr2 (pr2 𝟚-Preorder)) x y z = transitive-leq-𝟚

𝟚-Poset : Poset lzero lzero
pr1 𝟚-Poset = 𝟚-Preorder
pr2 𝟚-Poset x y = antisymmetric-leq-𝟚
```

### The total order on the directed interval

```agda
is-total-leq-𝟚 : is-total-Poset 𝟚-Poset
is-total-leq-𝟚 x y =
  map-disjunction-join-Prop (leq-𝟚-Prop x y) (leq-𝟚-Prop y x) (total-leq-𝟚)

𝟚-Total-Order : Total-Order lzero lzero
𝟚-Total-Order = (𝟚-Poset , is-total-leq-𝟚)
```

## Properties

### The directed interval is a set

```agda
is-set-𝟚 : is-set 𝟚
is-set-𝟚 = is-set-type-Poset 𝟚-Poset

𝟚-Set : Set lzero
𝟚-Set = (𝟚 , is-set-𝟚)

Id-𝟚-Prop : 𝟚 → 𝟚 → Prop lzero
Id-𝟚-Prop = Id-Prop 𝟚-Set

{-# INLINE Id-𝟚-Prop #-}
```

### The maximal element is not less than or equal to the bottom element of the directed interval

```agda
not-leq-target-source-𝟚 : ¬ (1₂ ≤-𝟚 0₂)
not-leq-target-source-𝟚 leq-1-0 =
  is-nontrivial-𝟚 (antisymmetric-leq-𝟚 min-leq-𝟚 leq-1-0)
```

### The directed relation `t ≤-𝟚 s` is equivalent to the relation `max-𝟚 t s ＝ s`

> This remains to be formalized.

### The directed relation `t ≤-𝟚 s` is equivalent to the relation `min-𝟚 t s ＝ t`

> This remains to be formalized.

### The canonical inclusion of the booleans into the directed interval is an embedding

```agda
is-emb-map-directed-interval-bool : is-emb map-directed-interval-bool
is-emb-map-directed-interval-bool =
  is-emb-is-injective is-set-𝟚 is-injective-map-directed-interval-bool
```

### The canonical inclusion of the booleans into the directed interval preserves and reflects its ordering

> This remains to be formalized.
