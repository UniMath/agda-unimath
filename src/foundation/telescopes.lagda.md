# Telescopes

```agda
module foundation.telescopes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
```

</details>

## Idea

A **telescope**, or **iterated type family**, is a list of type families
`(A₀, A₁, A₂, ..., A_n)` consisting of

- a type `A₀`,
- a type family `A₁ : A₀ → 𝒰`,
- a type family `A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰`,
- ...
- a type family `A_n : (x₀ : A₀) ... (x_(n-1) : A_(n-1) x₀ ... x_(n-2)) → 𝒰`.

We say that a telescope `(A₀,...,A_n)` has **length** `n+1`. In other words, the
length of the telescope `(A₀,...,A_n)` is the length of the (dependent) list
`(A₀,...,A_n)`.

We encode the type of telescopes as a family of inductive types

```text
  telescope : (l : Level) → ℕ → UUω
```

The type of telescopes is a [directed tree](trees.directed-trees.md)

```text
  ... → T₃ → T₂ → T₁ → T₀,
```

where `T_n` is the type of all telescopes of length `n`, and the map from
`T_(n+1)` to `T_n` maps `(A₀,...,A_n)` to `(A₀,...,A_(n-1))`. The type of such
directed trees can be defined as a coinductive record type, and we will define
the tree `T` of telescopes as a particular element of this tree.

## Definitions

### Telescopes

```agda
data
  telescope : (l : Level) → ℕ → UUω
  where
  base-telescope :
    {l1 : Level} → UU l1 → telescope l1 0
  cons-telescope :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} →
    (X → telescope l2 n) → telescope (l1 ⊔ l2) (succ-ℕ n)

open telescope public
```

### Transformations on telescopes

Given an operation on universes, we can apply it at the base of the telescope.

```agda
apply-base-telescope :
  {l1 : Level} {n : ℕ}
  (P : {l : Level} → UU l → UU l) → telescope l1 n → telescope l1 n
apply-base-telescope P (base-telescope A) = base-telescope (P A)
apply-base-telescope P (cons-telescope A) =
  cons-telescope (λ x → apply-base-telescope P (A x))
```

### Telescopes as instance arguments

To get Agda to infer telescopes, we help it along a little using
[instance arguments](https://agda.readthedocs.io/en/latest/language/instance-arguments.html).
These are a special kind of implicit argument in Agda that are resolved by the
instance resolution algorithm. We register building blocks for this algorithm to
use below, i.e. _instances_. Then Agda will attempt to use those to construct
telescopes of the appropriate kind when asked to.

In the case of telescopes, this has the unfortunate disadvantage that we can
only define instances for fixed length telescopes. We have defined instances of
telescopes up to length 18, so although Agda cannot infer a telescope of a
general length using this approach, it can infer them up to this given length.

```agda
instance-telescope : {l : Level} {n : ℕ} → {{telescope l n}} → telescope l n
instance-telescope {{x}} = x

instance
  instance-telescope⁰ : {l : Level} {X : UU l} → telescope l 0
  instance-telescope⁰ {X = X} = base-telescope X

  instance-telescope¹ :
    { l1 l : Level} {A1 : UU l1} {X : A1 → UU l} → telescope (l1 ⊔ l) 1
  instance-telescope¹ {X = X} =
    cons-telescope (λ x → instance-telescope⁰ {X = X x})

  instance-telescope² :
    { l1 l2 l : Level} {A1 : UU l1} {A2 : A1 → UU l2}
    { X : (x1 : A1) → A2 x1 → UU l} → telescope (l1 ⊔ l2 ⊔ l) 2
  instance-telescope² {X = X} =
    cons-telescope (λ x → instance-telescope¹ {X = X x})

  instance-telescope³ :
    { l1 l2 l3 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { X : (x1 : A1) (x2 : A2 x1) (x2 : A3 x1 x2) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l) 3
  instance-telescope³ {X = X} =
    cons-telescope (λ x → instance-telescope² {X = X x})

  instance-telescope⁴ :
    { l1 l2 l3 l4 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { X : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l) 4
  instance-telescope⁴ {X = X} =
    cons-telescope (λ x → instance-telescope³ {X = X x})

  instance-telescope⁵ :
    { l1 l2 l3 l4 l5 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l) 5
  instance-telescope⁵ {X = X} =
    cons-telescope (λ x → instance-telescope⁴ {X = X x})

  instance-telescope⁶ :
    { l1 l2 l3 l4 l5 l6 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l) 6
  instance-telescope⁶ {X = X} =
    cons-telescope (λ x → instance-telescope⁵ {X = X x})

  instance-telescope⁷ :
    { l1 l2 l3 l4 l5 l6 l7 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l) 7
  instance-telescope⁷ {X = X} =
    cons-telescope (λ x → instance-telescope⁶ {X = X x})

  instance-telescope⁸ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l) 8
  instance-telescope⁸ {X = X} =
    cons-telescope (λ x → instance-telescope⁷ {X = X x})

  instance-telescope⁹ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l) 9
  instance-telescope⁹ {X = X} =
    cons-telescope (λ x → instance-telescope⁸ {X = X x})

  instance-telescope¹⁰ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l) 10
  instance-telescope¹⁰ {X = X} =
    cons-telescope (λ x → instance-telescope⁹ {X = X x})

  instance-telescope¹¹ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l} →
    telescope (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l) 11
  instance-telescope¹¹ {X = X} =
    cons-telescope (λ x → instance-telescope¹⁰ {X = X x})

  instance-telescope¹² :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { A12 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l12}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) → UU l} →
    telescope
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l12 ⊔ l)
      ( 12)
  instance-telescope¹² {X = X} =
    cons-telescope (λ x → instance-telescope¹¹ {X = X x})

  instance-telescope¹³ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { A12 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l12}
    { A13 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) → UU l13}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) → UU l} →
    telescope
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l12 ⊔ l13 ⊔ l)
      ( 13)
  instance-telescope¹³ {X = X} =
    cons-telescope (λ x → instance-telescope¹² {X = X x})

  instance-telescope¹⁴ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { A12 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l12}
    { A13 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) → UU l13}
    { A14 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) → UU l14}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) → UU l} →
    telescope
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l12 ⊔ l13 ⊔
        l14 ⊔ l)
      ( 14)
  instance-telescope¹⁴ {X = X} =
    cons-telescope (λ x → instance-telescope¹³ {X = X x})

  instance-telescope¹⁵ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { A12 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l12}
    { A13 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) → UU l13}
    { A14 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) → UU l14}
    { A15 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) → UU l15}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) → UU l} →
    telescope
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l12 ⊔ l13 ⊔
        l14 ⊔ l15 ⊔ l)
      ( 15)
  instance-telescope¹⁵ {X = X} =
    cons-telescope (λ x → instance-telescope¹⁴ {X = X x})

  instance-telescope¹⁶ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { A12 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l12}
    { A13 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) → UU l13}
    { A14 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) → UU l14}
    { A15 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) → UU l15}
    { A16 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) → UU l16}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
      (x16 : A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) → UU l} →
    telescope
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l12 ⊔ l13 ⊔
        l14 ⊔ l15 ⊔ l16 ⊔ l)
      ( 16)
  instance-telescope¹⁶ {X = X} =
    cons-telescope (λ x → instance-telescope¹⁵ {X = X x})

  instance-telescope¹⁷ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { A12 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l12}
    { A13 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) → UU l13}
    { A14 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) → UU l14}
    { A15 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) → UU l15}
    { A16 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) → UU l16}
    { A17 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
      (x16 : A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) → UU l17}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
      (x16 : A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
      (x17 : A17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) →
      UU l} →
    telescope
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l12 ⊔ l13 ⊔
        l14 ⊔ l15 ⊔ l16 ⊔ l17 ⊔ l)
      ( 17)
  instance-telescope¹⁷ {X = X} =
    cons-telescope (λ x → instance-telescope¹⁶ {X = X x})

  instance-telescope¹⁸ :
    { l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l : Level}
    { A1 : UU l1} {A2 : A1 → UU l2} {A3 : (x1 : A1) → A2 x1 → UU l3}
    { A4 : (x1 : A1) (x2 : A2 x1) → A3 x1 x2 → UU l4}
    { A5 : (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3) → UU l5}
    { A6 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) → UU l6}
    { A7 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5) → UU l7}
    { A8 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) → UU l8}
    { A9 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7) →
      UU l9}
    { A10 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) →
      UU l10}
    { A11 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9) →
      UU l11}
    { A12 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) → UU l12}
    { A13 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) → UU l13}
    { A14 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) → UU l14}
    { A15 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13) → UU l15}
    { A16 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14) → UU l16}
    { A17 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
      (x16 : A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) → UU l17}
    { A18 :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
      (x16 : A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
      (x17 : A17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) →
      UU l18}
    { X :
      (x1 : A1) (x2 : A2 x1) (x3 : A3 x1 x2) (x4 : A4 x1 x2 x3)
      (x5 : A5 x1 x2 x3 x4) (x6 : A6 x1 x2 x3 x4 x5)
      (x7 : A7 x1 x2 x3 x4 x5 x6) (x8 : A8 x1 x2 x3 x4 x5 x6 x7)
      (x9 : A9 x1 x2 x3 x4 x5 x6 x7 x8) (x10 : A10 x1 x2 x3 x4 x5 x6 x7 x8 x9)
      (x11 : A11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10)
      (x12 : A12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11)
      (x13 : A13 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12)
      (x14 : A14 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)
      (x15 : A15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14)
      (x16 : A16 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)
      (x17 : A17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)
      (x18 : A18 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) →
      UU l} →
    telescope
      ( l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ l7 ⊔ l8 ⊔ l9 ⊔ l10 ⊔ l11 ⊔ l12 ⊔ l13 ⊔
        l14 ⊔ l15 ⊔ l16 ⊔ l17 ⊔ l18 ⊔ l)
      ( 18)
  instance-telescope¹⁸ {X = X} =
    cons-telescope (λ x → instance-telescope¹⁷ {X = X x})
```

## See also

- [Dependent telescopes](foundation.dependent-telescopes.md)
- [Iterated Σ-types](foundation.iterated-dependent-pair-types.md)
- [Iterated Π-types](foundation.iterated-dependent-product-types.md)
