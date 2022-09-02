---
title: Equational reasoning
---

Tom de Jong, 27 May 2022.
Elisabeth Bonnevier, 31 May 2022.
Egbert Rijke, 31 August 2022.
Szumie Xie, 31 August 2022.

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equational-reasoning where

open import foundation.identity-types using (_＝_; refl; _∙_; inv)
open import foundation.dependent-pair-types using (pair)
open import foundation.equivalences using (_≃_; _∘e_; id-equiv; inv-equiv)
open import foundation.functions using (id)
open import foundation.logical-equivalences using (_↔_; _∘iff_)
open import foundation.universe-levels using (Level; UU)
open import order-theory.preorders using
  ( Preorder; element-Preorder; leq-Preorder; transitive-leq-Preorder;
    refl-leq-Preorder)
```

## Idea

Often it's convenient to reason by chains of (in)equalities or equivalences,
i.e., to write a proof in the following form:

```md
X ≃ A by equiv-1
  ≃ B by equiv-2
  ≃ C by equiv-3
```

or
```md
x ≤ X by ineq-1 to
a ≤ X by ineq-2 to
b ≤ X by ineq-3 to
c ∎ X
```

where `equiv-x` and `ineq-x` are proofs of respectively the equivalences or
inequalities. The symbol ∎ marks the end of a chain.

Because we will want to have equational reasoning for both identifications and
equivalences and we can't use the same symbol twice, we use ∎ for
identifications and ■ for equivalences in the code below.

For inequalities we also need to pass the preorder as an argument.

We write Agda code that allows for such reasoning. The code for equational
reasoning for equalities and equivalences is based on Martín Escardó's Agda code
[1,2] and the Agda standard library [3].


## Definitions

### Equational reasoning for identifications

```agda
module _
  {l : Level} {X : UU l}
  where

  infixl 1 equational-reasoning_
  infixl 0 step-equational-reasoning

  equational-reasoning_ : (x : X) → x ＝ x
  equational-reasoning x = refl

  step-equational-reasoning :
    {x y : X} → (x ＝ y) → (u : X) → (y ＝ u) → (x ＝ u)
  step-equational-reasoning p z q = p ∙ q

  syntax step-equational-reasoning p z q = p ＝ z by q
```

### Equational reasoning for equivalences

```agda
infixl 1 equivalence-reasoning_
infixl 0 step-equivalence-reasoning

equivalence-reasoning_ : {l1 : Level} (X : UU l1) → X ≃ X
equivalence-reasoning X = id-equiv

step-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (Z : UU l3) → (Y ≃ Z) → (X ≃ Z)
step-equivalence-reasoning e Z f = f ∘e e

syntax step-equivalence-reasoning e Z f = e ≃ Z by f
```

### Equational reasoning for logical equivalences

```agda
infixl 1 logical-equivalence-reasoning_
infixl 0 step-logical-equivalence-reasoning

logical-equivalence-reasoning_ : {l1 : Level} (X : UU l1) → X ↔ X
logical-equivalence-reasoning X = pair id id

step-logical-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ↔ Y) → (Z : UU l3) → (Y ↔ Z) → (X ↔ Z)
step-logical-equivalence-reasoning e Z f = f ∘iff e

syntax step-logical-equivalence-reasoning e Z f = e ↔ Z by f
```

### Equational reasoning for preorders

Note: In an equational reasoning argument, the preorder is always specified at the last step. So do we really need to specify it at each of the earlier steps?

```agda
private
  transitivity :
    {l1 l2 : Level} (X : Preorder l1 l2)
    (x : element-Preorder X) {y z : element-Preorder X} →
    leq-Preorder X x y → leq-Preorder X y z → leq-Preorder X x z
  transitivity X x {y} {z} u v = transitive-leq-Preorder X x y z v u

syntax transitivity X x u v = x ≤ X by u to v
infixr 0 transitivity

private
  reflexivity :
    {l1 l2 : Level} (X : Preorder l1 l2) (x : element-Preorder X) →
    leq-Preorder X x x
  reflexivity = refl-leq-Preorder

syntax reflexivity X x = x ∎ X
infix 1 reflexivity
```

For a preorder `X` we thus write the chains as follows

```md
x ≤ X by ineq-1 to
y ≤ X by ineq-2 to
z ∎ X
```

## References

1. Martín Escardó. https://github.com/martinescardo/TypeTopology/blob/master/source/Id.lagda
2. Martín Escardó. https://github.com/martinescardo/TypeTopology/blob/master/source/UF-Equiv.lagda
3. The Agda standard library. https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda
