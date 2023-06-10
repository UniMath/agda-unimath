# Dependent pair types

```agda
module foundation.dependent-pair-types where

open import foundation-core.dependent-pair-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Idea

When `B` is a family of types over `A`, then we can form the type of pairs
`pair a b` consisting of an element `a : A` and an element `b : B a`. Such pairs
are called dependent pairs, since the type of the second component depends on
the first component.

## Properties

### Transport in a family of dependent pair types

```agda
tr-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) (p : a0 ＝ a1) (z : Σ (B a0) (λ x → C a0 x)) →
  tr (λ a → (Σ (B a) (C a))) p z ＝
  pair (tr B p (pr1 z)) (tr (ind-Σ C) (eq-pair-Σ p refl) (pr2 z))
tr-Σ C refl z = refl
```

### Transport in a family over a dependent pair type

```agda
tr-eq-pair-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A}
  {B : A → UU l2} {b0 : B a0} {b1 : B a1} (C : (Σ A B) → UU l3)
  (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) (u : C (a0 , b0)) →
  tr C (eq-pair-Σ p q) u ＝
  tr (λ x → C (a1 , x)) q (tr C (eq-pair-Σ p refl) u)
tr-eq-pair-Σ C refl refl u = refl
```
