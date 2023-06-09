# Dependent cocones under spans

```agda
module synthetic-homotopy-theory.dependent-cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

Consider a span `𝒮 := (A <-- S --> B)` and a
[cocone structure](synthetic-homotopy-theory.cocones-under-spans.md) `c` of `𝒮`
into a type `X`. Furthermore, consider a type family `P` over `X`. In this case
we may consider _dependent_ cocone structures on `P` over `c`.

A **dependent cocone** `d` over `(i , j , H)` on `P` consists of two dependent
functions

```text
  i' : (a : A) → P (i a)
  j' : (b : B) → P (j b)
```

and a family of identifications

```text
  (s : S) → tr P (H s) (i' (f s)) ＝ j' (g s).
```

## Definitions

### Dependent cocones

```agda
dependent-cocone :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l5)
dependent-cocone {S = S} {A} {B} f g c P =
  Σ ( (a : A) → P ((pr1 c) a))
    ( λ hA →
      Σ ( (b : B) → P (pr1 (pr2 c) b))
        ( λ hB → (s : S) → tr P (pr2 (pr2 c) s) (hA (f s)) ＝ hB (g s)))

dependent-cocone-map :
  { l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4}
  ( f : S → A) (g : S → B) (c : cocone f g X) (P : X → UU l5) →
  ( (x : X) → P x) → dependent-cocone f g c P
dependent-cocone-map f g c P h =
  ( λ a → h (pr1 c a)) ,
  ( λ b → h (pr1 (pr2 c) b)) ,
  ( λ s → apd h (pr2 (pr2 c) s))
```
