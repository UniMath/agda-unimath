# Function types

```agda
module foundation-core.function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

Functions are primitive in Agda. Here we construct some basic functions

## Examples

### The identity function

```agda
id : {l : Level} {A : UU l} → A → A
id a = a

idω : {A : UUω} → A → A
idω a = a
```

### Dependent composition of functions

```agda
infixr 15 _∘_

_∘_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (a : A) → B a → UU l3} →
  ({a : A} → (b : B a) → C a b) → (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) a = g (f a)
```

### Evaluation at a point

```agda
ev-point :
  {l1 l2 : Level} {A : UU l1} (a : A) {P : A → UU l2} → ((x : A) → P x) → P a
ev-point a f = f a

ev-point' :
  {l1 l2 : Level} {A : UU l1} (a : A) {X : UU l2} → (A → X) → X
ev-point' a f = f a
```

### Precomposition functions

```agda
precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)
```

### Postcomposition functions

```agda
postcomp :
  {l1 l2 l3 : Level}
  {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X → Y) → (A → X) → (A → Y)
postcomp A f h = f ∘ h

map-Π :
  {l1 l2 l3 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) →
  ((i : I) → A i) →
  ((i : I) → B i)
map-Π f h i = f i (h i)

map-Π' :
  {l1 l2 l3 l4 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) →
  ((i : I) → A i → B i) →
  ((j : J) → A (α j)) →
  ((j : J) → B (α j))
map-Π' α f = map-Π (f ∘ α)
```
