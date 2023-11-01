# Spans of types

```agda
module foundation.spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
```

</details>

## Idea

A **(binary) span** is a pair of functions with a common domain, i.e., it is a
diagram of the form

```text
  A <----- S -----> B.
```

More precisely, a **binary span from `A` to `B`** consists of a type `S` and two
maps `f : S → A` and `g : S → B`. In this case, the types `A` and `B` are also
referred to as the **domain** and **codomain** of the span, respectively, and
the type `S` is referred to as the **spanning type** of the span.

We also consider the notion of **total (binary) span**, which consists of two
types `A` and `B` and a binary span from `A` to `B`.

More generally, given a family of types `A i` indexed by `i : I`, a **span** on
`A` consists of a type `S` and a family of maps `f i : S → A i` indexed by
`i : I`.

## Definition

### (Binary) spans with fixed domain and codomain

```agda
span-fixed-domain-codomain :
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
span-fixed-domain-codomain l A B =
  Σ (UU l) (λ X → (X → A) × (X → B))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (c : span-fixed-domain-codomain l3 A B)
  where

  spanning-type-span-fixed-domain-codomain : UU l3
  spanning-type-span-fixed-domain-codomain = pr1 c

  left-map-span-fixed-domain-codomain :
    spanning-type-span-fixed-domain-codomain → A
  left-map-span-fixed-domain-codomain = pr1 (pr2 c)

  right-map-span-fixed-domain-codomain :
    spanning-type-span-fixed-domain-codomain → B
  right-map-span-fixed-domain-codomain = pr2 (pr2 c)
```

### Identity spans with fixed domain and codomain

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  id-span-fixed-domain-codomain : span-fixed-domain-codomain l1 X X
  pr1 id-span-fixed-domain-codomain = X
  pr1 (pr2 id-span-fixed-domain-codomain) = id
  pr2 (pr2 id-span-fixed-domain-codomain) = id
```

### (Binary) spans

```agda
span : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
span l1 l2 l3 =
  Σ (UU l1) (λ A → Σ (UU l2) (λ B → span-fixed-domain-codomain l3 A B))

module _
  {l1 l2 l3 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  where

  make-span :
    (S → A) → (S → B) → span l2 l3 l1
  pr1 (make-span f g) = A
  pr1 (pr2 (make-span f g)) = B
  pr1 (pr2 (pr2 (make-span f g))) = S
  pr1 (pr2 (pr2 (pr2 (make-span f g)))) = f
  pr2 (pr2 (pr2 (pr2 (make-span f g)))) = g

module _
  {l1 l2 l3 : Level} (s : span l1 l2 l3)
  where

  domain-span : UU l1
  domain-span = pr1 s

  codomain-span : UU l2
  codomain-span = pr1 (pr2 s)

  span-fixed-domain-codomain-span :
    span-fixed-domain-codomain l3 domain-span codomain-span
  span-fixed-domain-codomain-span = pr2 (pr2 s)

  spanning-type-span : UU l3
  spanning-type-span =
    spanning-type-span-fixed-domain-codomain span-fixed-domain-codomain-span

  left-map-span : spanning-type-span → domain-span
  left-map-span =
    left-map-span-fixed-domain-codomain span-fixed-domain-codomain-span

  right-map-span : spanning-type-span → codomain-span
  right-map-span =
    right-map-span-fixed-domain-codomain span-fixed-domain-codomain-span
```

### Constant spans

```agda
module _
  {l1 : Level}
  where

  constant-span : UU l1 → span l1 l1 l1
  pr1 (constant-span X) = X
  pr1 (pr2 (constant-span X)) = X
  pr2 (pr2 (constant-span X)) = id-span-fixed-domain-codomain
```

### Spans of fixed families of types

```agda
module _
  {l1 l2 : Level} (l3 : Level) {I : UU l1} (A : I → UU l2)
  where

  span-fixed-family-of-types : UU (l1 ⊔ l2 ⊔ lsuc l3)
  span-fixed-family-of-types = Σ (UU l3) (λ S → (i : I) → S → A i)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  (s : span-fixed-family-of-types l3 A)
  where

  spanning-type-span-fixed-family-of-types : UU l3
  spanning-type-span-fixed-family-of-types = pr1 s

  map-span-fixed-family-of-types :
    (i : I) → spanning-type-span-fixed-family-of-types → A i
  map-span-fixed-family-of-types = pr2 s
```

### Spans of families of types

Note: We might have to rename the following definition of spans of families of
types to _spans of families of types with fixed indexing type_.

```agda
span-family-of-types :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
span-family-of-types l2 l3 I =
  Σ (I → UU l2) (λ A → span-fixed-family-of-types l3 A)

module _
  {l1 l2 l3 : Level} {I : UU l1} (s : span-family-of-types l2 l3 I)
  where

  family-span-family-of-types : I → UU l2
  family-span-family-of-types = pr1 s

  span-fixed-family-of-types-span-family-of-types :
    span-fixed-family-of-types l3 family-span-family-of-types
  span-fixed-family-of-types-span-family-of-types = pr2 s

  spanning-type-span-family-of-types : UU l3
  spanning-type-span-family-of-types =
    spanning-type-span-fixed-family-of-types
      ( span-fixed-family-of-types-span-family-of-types)

  map-span-family-of-types :
    (i : I) → spanning-type-span-family-of-types →
    family-span-family-of-types i
  map-span-family-of-types =
    map-span-fixed-family-of-types
      ( span-fixed-family-of-types-span-family-of-types)
```

### Extensions of spans with fixed domain and codomain

#### Extensions on both sides

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3} {B' : UU l4}
  where

  extend-span-fixed-domain-codomain :
    span-fixed-domain-codomain l5 A B → (A → A') → (B → B') →
    span-fixed-domain-codomain l5 A' B'
  pr1 (extend-span-fixed-domain-codomain s f g) =
    spanning-type-span-fixed-domain-codomain s
  pr1 (pr2 (extend-span-fixed-domain-codomain s f g)) =
    f ∘ left-map-span-fixed-domain-codomain s
  pr2 (pr2 (extend-span-fixed-domain-codomain s f g)) =
    g ∘ right-map-span-fixed-domain-codomain s
```

#### Extensions on the left

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {A' : UU l2}
  {B : UU l3}
  where

  left-extend-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A B → (A → A') →
    span-fixed-domain-codomain l4 A' B
  left-extend-span-fixed-domain-codomain s f =
    extend-span-fixed-domain-codomain s f id
```

#### Extensions on the right

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1}
  {B : UU l3} {B' : UU l4}
  where

  right-extend-span-fixed-domain-codomain :
    span-fixed-domain-codomain l4 A B → (B → B') →
    span-fixed-domain-codomain l4 A B'
  right-extend-span-fixed-domain-codomain s g =
    extend-span-fixed-domain-codomain s id g
```

### Extensions of spans

#### Extensions on both sides

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  where

  extend-span :
    (s : span l1 l2 l3)
    {A' : UU l4} (f : domain-span s → A')
    {B' : UU l5} (g : codomain-span s → B') →
    span l4 l5 l3
  pr1 (extend-span s {A'} f {B'} g) = A'
  pr1 (pr2 (extend-span s {A'} f {B'} g)) = B'
  pr2 (pr2 (extend-span s {A'} f {B'} g)) =
    extend-span-fixed-domain-codomain (span-fixed-domain-codomain-span s) f g
```

#### Etensions on the left

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  left-extend-span :
    (s : span l1 l2 l3) {A' : UU l4} (f : domain-span s → A') → span l4 l2 l3
  left-extend-span s f = extend-span s f id
```

#### Extensions on the right

```agda
module _
  {l1 l2 l3 l4 : Level}
  where

  right-extend-span :
    (s : span l1 l2 l3) {B' : UU l4} (g : codomain-span s → B') → span l1 l4 l3
  right-extend-span s g = extend-span s id g
```

### The opposite of a span with fixed domain and codomain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  opposite-span-fixed-domain-codomain :
    span-fixed-domain-codomain l3 A B →
    span-fixed-domain-codomain l3 B A
  pr1 (opposite-span-fixed-domain-codomain s) =
    spanning-type-span-fixed-domain-codomain s
  pr1 (pr2 (opposite-span-fixed-domain-codomain s)) =
    right-map-span-fixed-domain-codomain s
  pr2 (pr2 (opposite-span-fixed-domain-codomain s)) =
    left-map-span-fixed-domain-codomain s
```

### Permutations of spans of fixed families of types

Permutations of spans of fixed families of types are a generalization of the
opposite of a binary span with fixed domain and codomain.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  where

  permutation-span-fixed-family-of-types :
    (e : I ≃ I) → span-fixed-family-of-types l3 A →
    span-fixed-family-of-types l3 (A ∘ map-equiv e)
  pr1 (permutation-span-fixed-family-of-types e s) =
    spanning-type-span-fixed-family-of-types s
  pr2 (permutation-span-fixed-family-of-types e s) i =
    map-span-fixed-family-of-types s (map-equiv e i)
```

## See also

- The dual concept of spans is [cospans](foundation.cospans.md).
- In [`foundation.binary-type-duality`](foundation.binary-type-duality.md) we
  show that [binary relations](foundation.binary-relations.md) are equivalently
  described as spans of types.
