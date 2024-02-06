# Whiskering operations

```agda
module foundation.whiskering-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

Consider a type `A` with a [binary relation](foundation.binary-relations.md)
`R : A → A → 𝒰`, which comes equipped with a multiplicative operation

```text
  μ : (x y z : A) → R x y → R y z → R x z.
```

Furthermore, assume that each `R x y` comes equipped with a further binary
relation `E : R x y → R x y → 𝒰`. A
{{#concept "left whiskering operation" Agda=left-whiskering-operation}} on `E`
with respect to `μ` is an operation

```text
  (f : R x y) {g h : R y z} → E g h → E (μ f g) (μ f h).
```

Similarly, a
{{#concept "right whiskering operation" Agda=right-whiskering-operation}} on `E`
with respect to `μ` is an operation

```text
  {g h : R x y} → E g h → (f : R y z) → E (μ g f) (μ h f).
```

The general notion of whiskering is introduced in order to establish a clear
naming scheme for all the variations of whiskering that exist in the
`agda-unimath` library:

1. In
   [whiskering identifications with respect to concatenation](foundation.whiskering-identifications-concatenation.md)
   we define the whiskering operations

   ```text
     left-whisker-concat :
       (p : x ＝ y) {q r : y ＝ z} → q ＝ r → p ∙ q ＝ p ∙ r
   ```

   and

   ```text
     right-whisker-concat :
       {p q : x ＝ y} → p ＝ q → (r : y ＝ z) → p ∙ r ＝ q ∙ r
   ```

   with respect to concatenation of identifications.

2. In
   [whiskering homotopies with respect to composition](foundation.whiskering-homotopies-composition.md)
   we define the whiskering operations

   ```text
     left-whisker-comp :
       (f : B → C) {g h : A → B} → g ~ h → f ∘ g ~ f ∘ h
   ```

   and

   ```text
     right-whisker-comp :
       {f g : B → C} → (f ~ g) → (h : A → B) → f ∘ h ~ g ∘ h
   ```

   of homotopies with respect to composition of functions.

3. In
   [whiskering homotopies with respect to concatenation](foundation.whiskering-homotopies-concatenation.md)
   we define the whiskering operations

   ```text
     left-whisker-comp-concat :
       (H : f ~ g) {K L : g ~ h} → K ~ L → H ∙h K ~ H ∙h L
   ```

   and

   ```text
     right-whisker-comp-concat :
       {H K : f ~ g} → H ~ K → (L : g ~ h) → H ∙h L ~ K ∙h L
   ```

   of homotopies with respect to concatenation of homotopies.

4. In
   [whsikering higher homotopies with respect to composition](foundation.whiskering-higher-homotopies-composition.md)
   we define the whiskering operations

   ```text
     left-whisker-comp² :
       (f : B → C) {g h : A → B} {H K : g ~ h} → H ~ K → f ·l H ~ f ·l K
   ```

   and

   ```text
     right-whisker-comp² :
       {f g : B → C} {H K : f ~ g} → H ~ K → (h : A → B) → H ·r h ~ K ·r h
   ```

   of higher homotopies with respect to composition of functions.

## Definitions

### Left whiskering operations

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (R : A → A → UU l2)
  where

  left-whiskering-operation :
    (μ : {x y z : A} → R x y → R y z → R x z) →
    ({x y : A} → R x y → R x y → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  left-whiskering-operation μ E =
    {x y z : A} (f : R x y) {g h : R y z} → E g h → E (μ f g) (μ f h)

  left-whiskering-operation' :
    (μ : {x y z : A} → R y z → R x y → R x z) →
    ({x y : A} → R x y → R x y → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  left-whiskering-operation' μ E =
    {x y z : A} (f : R y z) {g h : R x y} → E g h → E (μ f g) (μ f h)
```

### Right whiskering operations

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (R : A → A → UU l2)
  where

  right-whiskering-operation :
    (μ : {x y z : A} → R x y → R y z → R x z) →
    ({x y : A} → R x y → R x y → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  right-whiskering-operation μ E =
    {x y z : A} {f g : R x y} → E f g → (h : R y z) → E (μ f h) (μ g h)

  right-whiskering-operation' :
    (μ : {x y z : A} → R y z → R x y → R x z) →
    ({x y : A} → R x y → R x y → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  right-whiskering-operation' μ E =
    {x y z : A} {f g : R y z} → E f g → (h : R x y) → E (μ f h) (μ g h)
```

### Double whiskering operations

Double whiskering operations are operations that simultaneously perform
whiskering on the left and on the right.

Note that double whiskering should not be confused with iterated whiskering on
the left or with iterated whiskering on the right.

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (R : A → A → UU l2)
  where

  double-whiskering-operation :
    (μ : {x y z : A} → R x y → R y z → R x z) →
    ({x y : A} → R x y → R x y → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  double-whiskering-operation μ E =
    {x' x y y' : A} (h : R x' x) {f g : R x y} (e : E f g) (k : R y y') →
    E (μ (μ h f) k) (μ (μ h g) k)

  double-whiskering-operation' :
    (μ : {x y z : A} → R y z → R x y → R x z) →
    ({x y : A} → R x y → R x y → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  double-whiskering-operation' μ E =
    {x' x y y' : A} (h : R y y') {f g : R x y} (e : E f g) (k : R x' x) →
    E (μ (μ h f) k) (μ (μ h g) k)
```
