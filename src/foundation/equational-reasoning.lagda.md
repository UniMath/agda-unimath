# Equational reasoning

Elisabeth Bonnevier, 31 May 2022.
Egbert Rijke, 31 August 2022.
Szumie Xie, 31 August 2022.

```agda
module foundation.equational-reasoning where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.logical-equivalences
open import foundation-core.universe-levels

open import order-theory.preorders
```

</details>

## Idea

Often it is convenient to reason by chains of (in)equalities or equivalences,
i.e., to write a proof in the following form:

```md
X ≃ A by equiv-1
  ≃ B by equiv-2
  ≃ C by equiv-3
```

or

```md
x ≤ a by ineq-1 inside X
  ≤ b by ineq-2 inside X
  ≤ c by ineq-3 inside X
```

where `equiv-x` and `ineq-x` are proofs of respectively the equivalences or
inequalities. Note that for inequalities we also need to pass the preorder as an argument.

We write Agda code that allows for such reasoning. The code for equational
reasoning for equalities and equivalences is based on Martín Escardó's Agda code
[1,2] and the Agda standard library [3].

## Definitions

### Equational reasoning for identifications

```agda
infixl 1 equational-reasoning_
infixl 0 step-equational-reasoning

equational-reasoning_ :
  {l : Level} {X : UU l} (x : X) → x ＝ x
equational-reasoning x = refl

step-equational-reasoning :
  {l : Level} {X : UU l} {x y : X} →
  (x ＝ y) → (u : X) → (y ＝ u) → (x ＝ u)
step-equational-reasoning p z q = p ∙ q

syntax step-equational-reasoning p z q = p ＝ z by q
```

For equalities we thus write the chains as follows

```md
equational-reasoning
  x ＝ y by eq-1
    ＝ z by eq-2
    ＝ v by eq-3
```

### Equational reasoning for function homotopies

```agda
infixl 1 homotopy-reasoning_
infixl 0 step-homotopy-reasoning

homotopy-reasoning_ :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  (f : (x : X) → Y x) → f ~ f
homotopy-reasoning f = refl-htpy

step-homotopy-reasoning :
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  {f g : (x : X) → Y x} → (f ~ g) →
  (h : (x : X) → Y x) → (g ~ h) → (f ~ h)
step-homotopy-reasoning p h q = p ∙h q

syntax step-homotopy-reasoning p h q = p ~ h by q
```

For function homotopies we thus write the chains as follows

```md
homotopy-reasoning
  f ~ g by htpy-1
    ~ h by htpy-2
    ~ i by htpy-3
```

### Equational reasoning for equivalences

```agda
infixl 1 equivalence-reasoning_
infixl 0 step-equivalence-reasoning

equivalence-reasoning_ :
  {l1 : Level} (X : UU l1) → X ≃ X
equivalence-reasoning X = id-equiv

step-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (Z : UU l3) → (Y ≃ Z) → (X ≃ Z)
step-equivalence-reasoning e Z f = f ∘e e

syntax step-equivalence-reasoning e Z f = e ≃ Z by f
```

For equivalences we thus write the chains as follows

```md
equivalence-reasoning
  X ≃ Y by equiv-1
    ≃ Z by equiv-2
    ≃ V by equiv-3
```

### Equational reasoning for logical equivalences

```agda
infixl 1 logical-equivalence-reasoning_
infixl 0 step-logical-equivalence-reasoning

logical-equivalence-reasoning_ :
  {l1 : Level} (X : UU l1) → X ↔ X
logical-equivalence-reasoning X = pair id id

step-logical-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ↔ Y) → (Z : UU l3) → (Y ↔ Z) → (X ↔ Z)
step-logical-equivalence-reasoning e Z f = f ∘iff e

syntax step-logical-equivalence-reasoning e Z f = e ↔ Z by f
```

For logical equivalences we thus write the chains as follows

```md
logical-equivalence-reasoning
  X ↔ Y by equiv-1
    ↔ Z by equiv-2
    ↔ V by equiv-3
```

### Equational reasoning for preorders

```agda
infixl 1 preorder_reasoning_
infixl 0 step-preorder-reasoning

preorder_reasoning_ :
  {l1 l2 : Level} (X : Preorder l1 l2)
  (x : element-Preorder X) → leq-Preorder X x x
preorder_reasoning_ = refl-leq-Preorder

step-preorder-reasoning :
  {l1 l2 : Level} (X : Preorder l1 l2)
  {x y : element-Preorder X} → leq-Preorder X x y →
  (z : element-Preorder X) → leq-Preorder X y z → leq-Preorder X x z
step-preorder-reasoning X {x} {y} u z v =
  transitive-leq-Preorder X x y z v u

syntax step-preorder-reasoning X u z v = u ≤ z by v inside X
```

For a preorder `X` we thus write the chains as follows

```md
preorder X reasoning
  x ≤ y by ineq-1 inside X
    ≤ z by ineq-2 inside X
    ≤ v by ineq-3 inside X
```

## References

1. Martín Escardó. <https://github.com/martinescardo/TypeTopology/blob/master/source/Id.lagda>
2. Martín Escardó. <https://github.com/martinescardo/TypeTopology/blob/master/source/UF-Equiv.lagda>
3. The Agda standard library. <https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/PropositionalEquality/Core.agda>
