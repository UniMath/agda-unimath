# Lifts of families of elements

```agda
module foundation.lifts-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

Consider a family of elements `a : (i : I) → A i` and a type family

```text
  B : (i : I) → A i → 𝒰.
```

A {{#concept "dependent lift" Disambiguation="family of elements"}} of the
family of elements `a` to the type family `B` is a family of elements

```text
  (i : I) → B i (a i).
```

An important special case occurs when `a : I → A` is a family of elements of a
fixed type `A`, and `B` is a type family over `A`. In this case, a
{{#concept "lift" Disambiguation="family of elements"}} of the family of
elements `a` is a family of elements

```text
  (i : I) → B (a i).
```

## Definitions

### Dependent lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  (B : (i : I) → A i → UU l3)
  where

  dependent-lift-family-of-elements : UU (l1 ⊔ l3)
  dependent-lift-family-of-elements = (i : I) → B i (a i)
```

### Lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : UU l2} (a : I → A) (B : A → UU l3)
  where

  lift-family-of-elements : UU (l1 ⊔ l3)
  lift-family-of-elements = dependent-lift-family-of-elements a (λ _ → B)
```

### Dependent lifts of binary families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} (a : (i : I) → A i)
  {B : (i : I) → A i → UU l3} (C : (i : I) (x : A i) → B i x → UU l4)
  where

  dependent-lift-binary-family-of-elements : UU (l1 ⊔ l3 ⊔ l4)
  dependent-lift-binary-family-of-elements =
    dependent-lift-family-of-elements a (λ i x → (y : B i x) → C i x y)
```

### Lifts of binary families of elements

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : UU l2} (a : I → A)
  {B : A → UU l3} {C : (x : A) → B x → UU l4}
  where

  lift-binary-family-of-elements : UU (l1 ⊔ l3 ⊔ l4)
  lift-binary-family-of-elements =
    dependent-lift-binary-family-of-elements a (λ _ → C)
```

### Dependent double lifts of families of elements

Given a lift `a` of `h : (i : I) → J i` to a type family
`A : (i : I) → J i → 𝒰`, a
{{#concept "dependent double lift" Disambiguation="families of elements"}} of
`h` and `a` to a type family

```text
  B : (i : I) (j : J i) → A i j → 𝒰
```

is a family of elements

```text
  (i : I) → B i (h i) (a i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `h` and `a` to the type family `B`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {J : I → UU l2} {h : (i : I) → J i}
  (A : (i : I) → J i → UU l3) (a : dependent-lift-family-of-elements h A)
  (B : (i : I) (j : J i) → A i j → UU l4)
  where

  dependent-double-lift-family-of-elements : UU (l1 ⊔ l4)
  dependent-double-lift-family-of-elements =
    dependent-lift-family-of-elements a (λ i → B i (h i))
```

### Double lifts of families of elements

Given a lift `a` of `h : I → J` to a type family `A : J → 𝒰`, a
{{#concept "double lift" Disambiguation="families of elements"}} of `h` and `a`
to a type family

```text
  B : (j : J) → A j → 𝒰
```

is a family of elements

```text
  (i : I) → B (h i) (a i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `h` and `a` to the type family `B`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {J : UU l2} {h : I → J}
  (A : J → UU l3) (a : lift-family-of-elements h A) (B : (j : J) → A j → UU l4)
  where

  double-lift-family-of-elements : UU (l1 ⊔ l4)
  double-lift-family-of-elements =
    dependent-lift-family-of-elements a (λ i → B (h i))
```
