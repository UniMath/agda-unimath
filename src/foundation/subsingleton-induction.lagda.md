# Subsingleton induction

```agda
module foundation.subsingleton-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.singleton-induction
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.sections
```

</details>

## Idea

{{#concept "Subsingleton induction" Agda=ind-subsingleton}} on a type `A` is a
slight variant of [singleton induction](foundation.singleton-induction.md) which
in turn is a principle analogous to induction for the
[unit type](foundation.unit-type.md). Subsingleton induction uses the
observation that a type equipped with an element is
[contractible](foundation-core.contractible-types.md) if and only if it is a
[proposition](foundation-core.propositions.md).

Subsingleton induction states that given a type family `B` over `A`, to
construct a section of `B` it suffices to provide an element of `B a` for some
`a : A`.

## Definition

### Subsingleton induction

```agda
is-subsingleton :
  (l1 : Level) {l2 : Level} (A : UU l2) → UU (lsuc l1 ⊔ l2)
is-subsingleton l A = {B : A → UU l} (a : A) → section (ev-point a {B})

ind-is-subsingleton :
  {l1 l2 : Level} {A : UU l1} →
  ({l : Level} → is-subsingleton l A) → {B : A → UU l2} (a : A) →
  B a → (x : A) → B x
ind-is-subsingleton is-subsingleton-A a = pr1 (is-subsingleton-A a)

compute-ind-is-subsingleton :
  {l1 l2 : Level} {A : UU l1} (H : {l : Level} → is-subsingleton l A) →
  {B : A → UU l2} (a : A) → ev-point a {B} ∘ ind-is-subsingleton H {B} a ~ id
compute-ind-is-subsingleton is-subsingleton-A a = pr2 (is-subsingleton-A a)
```

## Properties

### Propositions satisfy subsingleton induction

```agda
abstract
  ind-subsingleton :
    {l1 l2 : Level} {A : UU l1} (is-prop-A : is-prop A)
    {B : A → UU l2} (a : A) → B a → (x : A) → B x
  ind-subsingleton is-prop-A {B} a =
    ind-singleton a (is-proof-irrelevant-is-prop is-prop-A a) B

abstract
  compute-ind-subsingleton :
    {l1 l2 : Level} {A : UU l1}
    (is-prop-A : is-prop A) {B : A → UU l2} (a : A) →
    ev-point a {B} ∘ ind-subsingleton is-prop-A {B} a ~ id
  compute-ind-subsingleton is-prop-A {B} a =
    compute-ind-singleton a (is-proof-irrelevant-is-prop is-prop-A a) B
```

### A type satisfies subsingleton induction if and only if it is a proposition

```agda
is-subsingleton-is-prop :
  {l1 l2 : Level} {A : UU l1} → is-prop A → is-subsingleton l2 A
is-subsingleton-is-prop is-prop-A {B} a =
  is-singleton-is-contr a (is-proof-irrelevant-is-prop is-prop-A a) B

abstract
  is-prop-ind-subsingleton :
    {l1 : Level} (A : UU l1) →
    ({l2 : Level} {B : A → UU l2} (a : A) → B a → (x : A) → B x) → is-prop A
  is-prop-ind-subsingleton A S =
    is-prop-is-proof-irrelevant
      ( λ a → is-contr-ind-singleton A a (λ B → S {B = B} a))

abstract
  is-prop-is-subsingleton :
    {l1 : Level} (A : UU l1) → ({l2 : Level} → is-subsingleton l2 A) → is-prop A
  is-prop-is-subsingleton A S = is-prop-ind-subsingleton A (pr1 ∘ S)
```

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
