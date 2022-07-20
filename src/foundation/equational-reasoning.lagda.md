---
title: Equational reasoning
---

Tom de Jong, 27 May 2022.
Elisabeth Bonnevier, 31 May 2022.

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equational-reasoning where

open import foundation.identity-types using (_＝_; refl; _∙_; inv)
open import foundation.equivalences using (_≃_; _∘e_; id-equiv; inv-equiv)
open import foundation.universe-levels using (Level; UU)
open import order-theory.preorders using
  ( Preorder; element-Preorder; leq-Preorder; transitive-leq-Preorder;
    refl-leq-Preorder)
```

## Idea

Often it's convenient to reason by chains of (in)equalities or equivalences,
i.e., to write a proof in the following form:

```md
X ≃ by equiv-1 to
A ≃ by equiv-2 to
B ≃ by equiv-3 to
Y ∎e
```

or
```md
x ≤ X by ineq-1 than
a ≤ X by ineq-2 than
b ≤ X by ineq-3 than
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
infix 1 _∎
infixr 0 step-equational-reasoning

step-equational-reasoning :
  {l : Level} {X : UU l} (x : X) {y z : X} → y ＝ z → x ＝ y → x ＝ z
step-equational-reasoning _ q p = p ∙ q

_∎ : {l : Level} {X : UU l} (x : X) → x ＝ x
x ∎ = refl

syntax step-equational-reasoning x q p = x ＝ by p to q
```

### Equational reasoning for equivalences

```agda
infix 1 _∎e
infixr 0 step-equivalence-reasoning

step-equivalence-reasoning :
  {l1 l2 l3 : Level} (X : UU l1) {Y : UU l2 } {Z : UU l3} →
  Y ≃ Z → X ≃ Y → X ≃ Z
step-equivalence-reasoning _ g f = g ∘e f

_∎e : {l : Level} (X : UU l) → X ≃ X
X ∎e = id-equiv

syntax step-equivalence-reasoning X g f = X ≃ by f to g
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

syntax transitivity X x u v = x ≤ X by u than v
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
x ≤ X by ineq-1 than
y ≤ X by ineq-2 than
z ∎ X
```

## References

1. Martín Escardó. https://github.com/martinescardo/TypeTopology/blob/master/source/Id.lagda
2. Martín Escardó. https://github.com/martinescardo/TypeTopology/blob/master/source/UF-Equiv.lagda
3. The Agda standard library. https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda
