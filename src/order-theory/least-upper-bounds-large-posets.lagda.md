# Least upper bounds in large posets

```agda
module order-theory.least-upper-bounds-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import order-theory.dependent-products-large-posets
open import order-theory.large-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.similarity-of-elements-large-posets
open import order-theory.upper-bounds-large-posets
```

</details>

## Idea

A
{{#concept "binary least upper bound" Disambiguation="in a large poset" Agda=is-least-binary-upper-bound-Large-Poset}}
on a pair of elements `a`, `b` in a [large poset](order-theory.large-posets.md)
`P` is an element `x` in `P` such that the
[logical equivalence](foundation.logical-equivalences.md)

```text
  is-binary-upper-bound-Large-Poset P a b y ↔ (x ≤ y)
```

holds for every `y` in `P`.

Similarly, a
{{#concept "least upper bound" Disambiguation="in a large poset" WD="supremum" WDID=Q215071 Agda=is-least-upper-bound-family-of-elements-Large-Poset}}
of a family of elements `a : I → P` in a large poset `P` is an element `x` in
`P` such that the logical equivalence

```text
  is-binary-upper-bound-Large-Poset P a b y ↔ (x ≤ y)
```

holds for every `y` in `P`.

Similarly, a least upper bound of a family of elements `a : I → P` in a large
poset `P` is an element `x` in `P` such that the logical equivalence

```text
  is-upper-bound-family-of-elements-Large-Poset P a y ↔ (x ≤ y)
```

holds for every `y` in `P`.

## Definitions

### The predicate on large posets of being a least binary upper bound of a pair of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-least-binary-upper-bound-Large-Poset :
    {l3 : Level} (x : type-Large-Poset P l3) → UUω
  is-least-binary-upper-bound-Large-Poset x =
    {l4 : Level} (y : type-Large-Poset P l4) →
    is-binary-upper-bound-Large-Poset P a b y ↔ leq-Large-Poset P x y
```

### The predicate on large posets of being a least upper bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-least-upper-bound-family-of-elements-Large-Poset :
    type-Large-Poset P l3 → UUω
  is-least-upper-bound-family-of-elements-Large-Poset y =
    {l4 : Level} (z : type-Large-Poset P l4) →
    is-upper-bound-family-of-elements-Large-Poset P x z ↔ leq-Large-Poset P y z

  leq-is-least-upper-bound-family-of-elements-Large-Poset :
    (y : type-Large-Poset P l3) →
    is-least-upper-bound-family-of-elements-Large-Poset y →
    {l4 : Level} (z : type-Large-Poset P l4) →
    is-upper-bound-family-of-elements-Large-Poset P x z →
    leq-Large-Poset P y z
  leq-is-least-upper-bound-family-of-elements-Large-Poset y H z K =
    forward-implication (H z) K
```

### The predicate on families of elements in large posets of having least upper bounds

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (γ : Level)
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  record
    has-least-upper-bound-family-of-elements-Large-Poset : UUω
    where
    field
      sup-has-least-upper-bound-family-of-elements-Large-Poset :
        type-Large-Poset P (γ ⊔ l1 ⊔ l2)
      is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset :
        is-least-upper-bound-family-of-elements-Large-Poset P x
          sup-has-least-upper-bound-family-of-elements-Large-Poset

  open has-least-upper-bound-family-of-elements-Large-Poset public
```

## Properties

### Binary least upper bounds are upper bounds

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset :
    {l3 : Level} {y : type-Large-Poset P l3} →
    is-least-binary-upper-bound-Large-Poset P a b y →
    is-binary-upper-bound-Large-Poset P a b y
  is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset H =
    backward-implication (H _) (refl-leq-Large-Poset P _)
```

### Binary least upper bounds are lesser than all binary upper bounds

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  leq-is-least-binary-upper-bound-Large-Poset :
    {l3 : Level} {y : type-Large-Poset P l3} →
    is-least-binary-upper-bound-Large-Poset P a b y →
    {l4 : Level} (z : type-Large-Poset P l4) →
    is-binary-upper-bound-Large-Poset P a b z →
    leq-Large-Poset P y z
  leq-is-least-binary-upper-bound-Large-Poset H z =
    forward-implication (H z)
```

### The least upper bound of `x` and `y` is the least upper bound of `y` and `x`

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  abstract
    is-binary-least-upper-bound-swap-Large-Poset :
      {l3 : Level} (y : type-Large-Poset P l3) →
      is-least-binary-upper-bound-Large-Poset P a b y →
      is-least-binary-upper-bound-Large-Poset P b a y
    is-binary-least-upper-bound-swap-Large-Poset _ H z =
      H z ∘iff iff-equiv commutative-product
```

### Binary least upper bounds are unique up to similarity of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  where

  sim-is-least-binary-upper-bound-Large-Poset :
    {l3 l4 : Level} {x : type-Large-Poset P l3} {y : type-Large-Poset P l4} →
    is-least-binary-upper-bound-Large-Poset P a b x →
    is-least-binary-upper-bound-Large-Poset P a b y →
    sim-Large-Poset P x y
  pr1 (sim-is-least-binary-upper-bound-Large-Poset H K) =
    forward-implication (H _)
      ( backward-implication (K _) (refl-leq-Large-Poset P _))
  pr2 (sim-is-least-binary-upper-bound-Large-Poset H K) =
    forward-implication (K _)
      ( backward-implication (H _) (refl-leq-Large-Poset P _))

module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 l3 : Level}
  (a : type-Large-Poset P l1) (b : type-Large-Poset P l2)
  (c : type-Large-Poset P l3)
  where

  preserves-is-least-binary-upper-bound-sim-Large-Poset :
    {l4 l5 : Level} {a' : type-Large-Poset P l4} {b' : type-Large-Poset P l5} →
    sim-Large-Poset P a a' →
    sim-Large-Poset P b b' →
    is-least-binary-upper-bound-Large-Poset P a b c →
    is-least-binary-upper-bound-Large-Poset P a' b' c
  pr1
    (preserves-is-least-binary-upper-bound-sim-Large-Poset
      {a' = a'} {b' = b'} a~a' b~b' lub-ab-c d)
    (a'≤d , b'≤d)
    = forward-implication
      ( lub-ab-c d)
      ( transitive-leq-Large-Poset P a a' d a'≤d (pr1 a~a') ,
        transitive-leq-Large-Poset P b b' d b'≤d (pr1 b~b'))
  pr2
    (preserves-is-least-binary-upper-bound-sim-Large-Poset
      {a' = a'} {b' = b'} a~a' b~b' lub-ab-c d)
    c≤d
    =
      let
        (a≤d , b≤d) = backward-implication (lub-ab-c d) c≤d
      in
        ( transitive-leq-Large-Poset P a' a d a≤d (pr2 a~a') ,
          transitive-leq-Large-Poset P b' b d b≤d (pr2 b~b'))

  preserves-is-least-binary-upper-bound-left-sim-Large-Poset :
    {l4 : Level} {a' : type-Large-Poset P l4} →
    sim-Large-Poset P a a' →
    is-least-binary-upper-bound-Large-Poset P a b c →
    is-least-binary-upper-bound-Large-Poset P a' b c
  preserves-is-least-binary-upper-bound-left-sim-Large-Poset a~a' =
    preserves-is-least-binary-upper-bound-sim-Large-Poset
      ( a~a')
      ( refl-sim-Large-Poset P b)

  preserves-is-least-binary-upper-bound-right-sim-Large-Poset :
    {l4 : Level} {b' : type-Large-Poset P l4} →
    sim-Large-Poset P b b' →
    is-least-binary-upper-bound-Large-Poset P a b c →
    is-least-binary-upper-bound-Large-Poset P a b' c
  preserves-is-least-binary-upper-bound-right-sim-Large-Poset =
    preserves-is-least-binary-upper-bound-sim-Large-Poset
      ( refl-sim-Large-Poset P a)
```

### Least upper bounds of families of elements are upper bounds

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} {x : I → type-Large-Poset P l2}
  where

  is-upper-bound-is-least-upper-bound-family-of-elements-Large-Poset :
    {l3 : Level} {y : type-Large-Poset P l3} →
    is-least-upper-bound-family-of-elements-Large-Poset P x y →
    is-upper-bound-family-of-elements-Large-Poset P x y
  is-upper-bound-is-least-upper-bound-family-of-elements-Large-Poset H =
    backward-implication (H _) (refl-leq-Large-Poset P _)
```

### Least upper bounds of families of elements are unique up to similarity of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} {x : I → type-Large-Poset P l2}
  where

  sim-is-least-upper-bound-family-of-elements-Large-Poset :
    {l3 l4 : Level} {y : type-Large-Poset P l3} {z : type-Large-Poset P l4} →
    is-least-upper-bound-family-of-elements-Large-Poset P x y →
    is-least-upper-bound-family-of-elements-Large-Poset P x z →
    sim-Large-Poset P y z
  pr1 (sim-is-least-upper-bound-family-of-elements-Large-Poset H K) =
    forward-implication
      ( H _)
      ( is-upper-bound-is-least-upper-bound-family-of-elements-Large-Poset P K)
  pr2 (sim-is-least-upper-bound-family-of-elements-Large-Poset H K) =
    forward-implication
      ( K _)
      ( is-upper-bound-is-least-upper-bound-family-of-elements-Large-Poset P H)
```

### A family of least upper bounds of families of elements in a family of large poset is a least upper bound in their dependent product

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  {l1 : Level} {I : UU l1} (P : I → Large-Poset α β)
  {l2 l3 : Level} {J : UU l2} (a : J → type-Π-Large-Poset P l3)
  {l4 : Level} (x : type-Π-Large-Poset P l4)
  where

  is-least-upper-bound-Π-Large-Poset :
    ( (i : I) →
      is-least-upper-bound-family-of-elements-Large-Poset
        ( P i)
        ( λ j → a j i)
        ( x i)) →
    is-least-upper-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a x
  is-least-upper-bound-Π-Large-Poset H y =
    logical-equivalence-reasoning
      is-upper-bound-family-of-elements-Large-Poset (Π-Large-Poset P) a y
      ↔ ( (i : I) →
          is-upper-bound-family-of-elements-Large-Poset
            ( P i)
            ( λ j → a j i)
            ( y i))
        by
        inv-iff
          ( logical-equivalence-is-upper-bound-family-of-elements-Π-Large-Poset
            ( P)
              ( a)
              ( y))
      ↔ leq-Π-Large-Poset P x y
        by
        iff-Π-iff-family (λ i → H i (y i))
```

### Least upper bounds in small posets from least upper bounds in large posets

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-least-upper-bound-family-of-elements-poset-Large-Poset :
    (y : type-Large-Poset P l2) →
    is-least-upper-bound-family-of-elements-Large-Poset P x y →
    is-least-upper-bound-family-of-elements-Poset
      ( poset-Large-Poset P l2) (x) (y)
  is-least-upper-bound-family-of-elements-poset-Large-Poset y is-lub-y z =
    is-lub-y z
```
