# The standard inequality relation on booleans

```agda
module foundation.inequality-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations
open import foundation.booleans
open import foundation.decidable-equality
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.involutions
open import foundation.logical-operations-booleans
open import foundation.negated-equality
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.tight-apartness-relations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.sets

open import order-theory.decidable-total-orders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The type of {{#concept "booleans" WD="Boolean domain" WDID=Q3269980 Agda=bool}}
is a [2-element type](univalent-combinatorics.2-element-types.md) with elements
`true false : bool`, which is used for reasoning with
[decidable propositions](foundation-core.decidable-propositions.md).

## Definitions

### The standard inequality relation on booleans

```agda
leq-bool-Decidable-Prop : bool → bool → Decidable-Prop lzero
leq-bool-Decidable-Prop x y = decidable-prop-bool (hom-bool x y)

leq-bool-Prop : bool → bool → Prop lzero
leq-bool-Prop x y = prop-Decidable-Prop (leq-bool-Decidable-Prop x y)

leq-bool : bool → bool → UU lzero
leq-bool x y = type-Decidable-Prop (leq-bool-Decidable-Prop x y)

is-decidable-leq-bool : {x y : bool} → is-decidable (leq-bool x y)
is-decidable-leq-bool {x} {y} =
  is-decidable-Decidable-Prop (leq-bool-Decidable-Prop x y)

is-prop-leq-bool : {x y : bool} → is-prop (leq-bool x y)
is-prop-leq-bool {x} {y} = is-prop-type-Prop (leq-bool-Prop x y)
```

## Properties

### Reflexivity

```agda
refl-leq-bool : {x : bool} → leq-bool x x
refl-leq-bool {true} = star
refl-leq-bool {false} = star

refl-leq-bool' : (x : bool) → leq-bool x x
refl-leq-bool' x = refl-leq-bool {x}

leq-eq-bool : {x y : bool} → x ＝ y → leq-bool x y
leq-eq-bool {x} refl = refl-leq-bool' x
```

### Transitivity

```agda
transitive-leq-bool :
  {x y z : bool} → leq-bool y z → leq-bool x y → leq-bool x z
transitive-leq-bool {true} {true} {true} p q = star
transitive-leq-bool {false} {y} {z} p q = star
```

### Antisymmetry

```agda
antisymmetric-leq-bool :
  {x y : bool} → leq-bool x y → leq-bool y x → x ＝ y
antisymmetric-leq-bool {true} {true} p q = refl
antisymmetric-leq-bool {false} {false} p q = refl
```

### Linearity

```agda
cases-linear-leq-bool : {x y : bool} → leq-bool x y + leq-bool y x
cases-linear-leq-bool {true} {true} = inr star
cases-linear-leq-bool {true} {false} = inr star
cases-linear-leq-bool {false} {y} = inl star

linear-leq-bool : {x y : bool} → disjunction-type (leq-bool x y) (leq-bool y x)
linear-leq-bool {x} {y} = unit-trunc-Prop (cases-linear-leq-bool {x} {y})
```

### The maximal and minimal elements

```agda
max-leq-bool : {x : bool} → leq-bool x true
max-leq-bool {true} = star
max-leq-bool {false} = star

min-leq-bool : {x : bool} → leq-bool false x
min-leq-bool = star
```

### The decidable total order on booleans

```agda
bool-Preorder : Preorder lzero lzero
bool-Preorder =
  ( bool ,
    leq-bool-Prop ,
    refl-leq-bool' ,
    ( λ x y z → transitive-leq-bool {x} {y} {z}))

bool-Poset : Poset lzero lzero
bool-Poset = (bool-Preorder , (λ x y → antisymmetric-leq-bool {x} {y}))

bool-Total-Order : Total-Order lzero lzero
bool-Total-Order = (bool-Poset , (λ x y → linear-leq-bool {x} {y}))

bool-Decidable-Total-Order : Decidable-Total-Order lzero lzero
bool-Decidable-Total-Order =
  ( bool-Poset ,
    ( λ x y → linear-leq-bool {x} {y}) ,
    ( λ x y → is-decidable-Decidable-Prop (leq-bool-Decidable-Prop x y)))
```

### Interactions between the inequality relation and the disjunction operation

```agda
leq-or-bool : {x y : bool} → leq-bool x (or-bool x y)
leq-or-bool {true} {y} = star
leq-or-bool {false} {y} = star

leq-or-bool' : {x y : bool} → leq-bool y (or-bool x y)
leq-or-bool' {true} {true} = star
leq-or-bool' {true} {false} = star
leq-or-bool' {false} {true} = star
leq-or-bool' {false} {false} = star

leq-left-or-bool : {x y : bool} → leq-bool x y → leq-bool (or-bool x y) y
leq-left-or-bool {true} {true} p = star
leq-left-or-bool {false} {true} p = star
leq-left-or-bool {false} {false} p = star

leq-right-or-bool : {x y : bool} → leq-bool x y → leq-bool (or-bool y x) y
leq-right-or-bool {x} {true} p = star
leq-right-or-bool {false} {false} p = star

leq-or-bool'' :
  {x y z : bool} → leq-bool x z → leq-bool y z → leq-bool (or-bool x y) z
leq-or-bool'' {true} {y} {true} p q = star
leq-or-bool'' {false} {true} {true} p q = star
leq-or-bool'' {false} {false} {true} p q = star
leq-or-bool'' {false} {false} {false} p q = star
```

### Interactions between the inequality relation and the conjunction operation

```agda
leq-and-bool : {x y : bool} → leq-bool (and-bool x y) x
leq-and-bool {true} {true} = star
leq-and-bool {false} {true} = star
leq-and-bool {true} {false} = star
leq-and-bool {false} {false} = star

leq-and-bool' : {x y : bool} → leq-bool (and-bool x y) y
leq-and-bool' {true} {true} = star
leq-and-bool' {true} {false} = star
leq-and-bool' {false} {y} = star

leq-left-and-bool : {x y : bool} → leq-bool x y → leq-bool x (and-bool x y)
leq-left-and-bool {true} {true} p = star
leq-left-and-bool {false} {y} p = star

leq-right-and-bool : {x y : bool} → leq-bool x y → leq-bool x (and-bool y x)
leq-right-and-bool {true} {true} p = star
leq-right-and-bool {false} {y} p = star

leq-and-bool'' :
  {x y z : bool} → leq-bool x y → leq-bool x z → leq-bool x (and-bool y z)
leq-and-bool'' {true} {true} {true} p q = star
leq-and-bool'' {false} {y} {z} p q = star
```
