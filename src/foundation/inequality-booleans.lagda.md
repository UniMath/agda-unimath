# The standard inequality relation on booleans

```agda
module foundation.inequality-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.logical-operations-booleans
open import foundation.propositional-truncations
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.identity-types
open import foundation-core.propositions

open import order-theory.decidable-total-orders
open import order-theory.posets
open import order-theory.preorders
open import order-theory.total-orders
```

</details>

## Idea

The
{{#concept "standard inequality relation" Disambiguation="on booleans" Agda=leq-bool}}
on [booleans](foundation.booleans.md) is the
[partial order](order-theory.posets.md) defined by the logical connective `⇒`,
i.e. `(x ≤ y) := (x ⇒ y)`. This means it is the unique partial order on the
booleans satisfying the four inequalities

```text
  false ≤ false
  false ≤ true
  true ≤ true
  true ≰ false.
```

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
linear-leq-bool : {x y : bool} → leq-bool x y + leq-bool y x
linear-leq-bool {true} {true} = inr star
linear-leq-bool {true} {false} = inr star
linear-leq-bool {false} {y} = inl star

is-total-leq-bool :
  (x y : bool) → disjunction-type (leq-bool x y) (leq-bool y x)
is-total-leq-bool x y = unit-trunc-Prop (linear-leq-bool {x} {y})
```

### The maximal and minimal elements

```agda
leq-true-bool : {x : bool} → leq-bool x true
leq-true-bool {true} = star
leq-true-bool {false} = star

leq-false-bool : {x : bool} → leq-bool false x
leq-false-bool = star

eq-leq-true-bool : {x : bool} → leq-bool true x → x ＝ true
eq-leq-true-bool {true} p = refl

eq-leq-false-bool : {x : bool} → leq-bool x false → x ＝ false
eq-leq-false-bool {false} p = refl
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
bool-Total-Order = (bool-Poset , is-total-leq-bool)

bool-Decidable-Total-Order : Decidable-Total-Order lzero lzero
bool-Decidable-Total-Order =
  ( bool-Poset ,
    is-total-leq-bool ,
    ( λ x y → is-decidable-Decidable-Prop (leq-bool-Decidable-Prop x y)))
```

### Interactions between the inequality relation and the disjunction operation

```agda
left-leq-or-bool : {x y : bool} → leq-bool x (or-bool x y)
left-leq-or-bool {true} {y} = star
left-leq-or-bool {false} {y} = star

right-leq-or-bool : {x y : bool} → leq-bool y (or-bool x y)
right-leq-or-bool {true} {true} = star
right-leq-or-bool {true} {false} = star
right-leq-or-bool {false} {true} = star
right-leq-or-bool {false} {false} = star

leq-left-or-bool : {x y : bool} → leq-bool x y → leq-bool (or-bool x y) y
leq-left-or-bool {true} {true} p = star
leq-left-or-bool {false} {true} p = star
leq-left-or-bool {false} {false} p = star

leq-right-or-bool : {x y : bool} → leq-bool x y → leq-bool (or-bool y x) y
leq-right-or-bool {x} {true} p = star
leq-right-or-bool {false} {false} p = star

is-upper-bound-or-bool :
  {x y z : bool} → leq-bool x z → leq-bool y z → leq-bool (or-bool x y) z
is-upper-bound-or-bool {true} {y} {true} p q = star
is-upper-bound-or-bool {false} {true} {true} p q = star
is-upper-bound-or-bool {false} {false} {true} p q = star
is-upper-bound-or-bool {false} {false} {false} p q = star
```

### Interactions between the inequality relation and the conjunction operation

```agda
left-leq-and-bool : {x y : bool} → leq-bool (and-bool x y) x
left-leq-and-bool {true} {true} = star
left-leq-and-bool {false} {true} = star
left-leq-and-bool {true} {false} = star
left-leq-and-bool {false} {false} = star

right-leq-and-bool : {x y : bool} → leq-bool (and-bool x y) y
right-leq-and-bool {true} {true} = star
right-leq-and-bool {true} {false} = star
right-leq-and-bool {false} {y} = star

leq-left-and-bool : {x y : bool} → leq-bool x y → leq-bool x (and-bool x y)
leq-left-and-bool {true} {true} p = star
leq-left-and-bool {false} {y} p = star

leq-right-and-bool : {x y : bool} → leq-bool x y → leq-bool x (and-bool y x)
leq-right-and-bool {true} {true} p = star
leq-right-and-bool {false} {y} p = star

is-lower-bound-and-bool :
  {x y z : bool} → leq-bool x y → leq-bool x z → leq-bool x (and-bool y z)
is-lower-bound-and-bool {true} {true} {true} p q = star
is-lower-bound-and-bool {false} {y} {z} p q = star
```

```agda
is-false-is-false-leq-bool :
  {x y : bool} → leq-bool x y → is-false y → is-false x
is-false-is-false-leq-bool {false} {false} p refl = refl

is-true-is-true-leq-bool :
  {x y : bool} → leq-bool x y → is-true x → is-true y
is-true-is-true-leq-bool {true} {true} p refl = refl
```

## See also

- The underlying category of the poset of booleans is called
  [the representing arrow category](category-theory.representing-arrow-category.md).
