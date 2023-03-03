# Function classes

<details>
<summary>Imports</summary>
```agda
module orthogonal-factorization-systems.function-classes where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```
</details>

## Idea

A function class is a subtype of the type of all functions.

## Definition

```agda
function-class : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
function-class l1 l2 l3 = {A : UU l1} {B : UU l2} → (A → B) → Prop l3
```

We say a function class is **equivalence closed** if it contains the
equivalences.

```agda
is-equiv-closed-function-class :
  {l1 l2 l3 : Level} → function-class l1 l2 l3 → UU (lsuc l1 ⊔ lsuc l2 ⊔ l3)
is-equiv-closed-function-class {l1} {l2} {l3} c =
  (A : UU l1) (B : UU l2) (f : A → B) → is-equiv f → type-Prop (c f)

equiv-closed-function-class :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
equiv-closed-function-class l1 l2 l3 =
  Σ (function-class l1 l2 l3) (is-equiv-closed-function-class)
```

We say a function class is **composition closed** if it is closed under taking
composites.

```agda
is-composition-closed-function-class :
  {l1 l2 : Level} → function-class l1 l1 l2 → UU (lsuc l1 ⊔ l2)
is-composition-closed-function-class {l1} {l2} c =
  (A B C : UU l1) (f : A → B) (g : B → C) →
  type-Prop (c f) → type-Prop (c g) →
  type-Prop (c (g ∘ f))

composition-closed-function-class :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
composition-closed-function-class l1 l2 =
  Σ (function-class l1 l1 l2) (is-composition-closed-function-class)
```

## Properties

### Equivalence closedness is a property

```agda
is-prop-is-equiv-closed-function-class :
  {l1 l2 l3 : Level} (c : function-class l1 l2 l3) →
  is-prop (is-equiv-closed-function-class c)
is-prop-is-equiv-closed-function-class c =
  is-prop-Π λ A → is-prop-Π λ B → is-prop-Π λ f →
    is-prop-function-type (is-prop-type-Prop (c f))

is-equiv-closed-function-class-Prop :
  {l1 l2 l3 : Level} → function-class l1 l2 l3 → Prop (lsuc l1 ⊔ lsuc l2 ⊔ l3)
pr1 (is-equiv-closed-function-class-Prop c) =
  is-equiv-closed-function-class c
pr2 (is-equiv-closed-function-class-Prop c) =
  is-prop-is-equiv-closed-function-class c
```

### Composition closedness is a property

```agda
is-prop-is-composition-closed-function-class :
  {l1 l2 : Level} (c : function-class l1 l1 l2) →
  is-prop (is-composition-closed-function-class c)
is-prop-is-composition-closed-function-class c =
  is-prop-Π λ A → is-prop-Π λ B → is-prop-Π λ C →
    is-prop-Π λ f → is-prop-Π λ g →
      is-prop-function-type (is-prop-function-type
        ( is-prop-type-Prop (c (g ∘ f))))

is-composition-closed-function-class-Prop :
  {l1 l2 : Level} → function-class l1 l1 l2 → Prop (lsuc l1 ⊔ l2)
pr1 (is-composition-closed-function-class-Prop c) =
  is-composition-closed-function-class c
pr2 (is-composition-closed-function-class-Prop c) =
  is-prop-is-composition-closed-function-class c
```
