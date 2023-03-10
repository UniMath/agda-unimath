# The universal property of pushouts

```agda
module synthetic-homotopy-theory.universal-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-pullbacks
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-pushouts
```

</details>

## Definition

### The universal property of pushouts

```agda
universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} →
  cocone f g X → UU _
universal-property-pushout l f g c =
  (Y : UU l) → is-equiv (cocone-map f g {Y = Y} c)

module _
  {l1 l2 l3 l4 l5 : Level}
  {S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  (f : S → A) (g : S → B) (c : cocone f g X)
  (up-c : {l : Level} → universal-property-pushout l f g c)
  (d : cocone f g Y)
  where

  map-universal-property-pushout : X → Y
  map-universal-property-pushout = map-inv-is-equiv (up-c Y) d

  htpy-cocone-map-universal-property-pushout :
    htpy-cocone f g (cocone-map f g c map-universal-property-pushout) d
  htpy-cocone-map-universal-property-pushout =
    htpy-cocone-eq f g
      ( cocone-map f g c map-universal-property-pushout)
      ( d)
      ( issec-map-inv-is-equiv (up-c Y) d)

  uniqueness-map-universal-property-pushout :
    is-contr ( Σ (X → Y) (λ h → htpy-cocone f g (cocone-map f g c h) d))
  uniqueness-map-universal-property-pushout =
    is-contr-is-equiv'
      ( fib (cocone-map f g c) d)
      ( tot (λ h → htpy-cocone-eq f g (cocone-map f g c h) d))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ h → is-equiv-htpy-cocone-eq f g (cocone-map f g c h) d))
      ( is-contr-map-is-equiv (up-c Y) d)
```

### The pullback property of pushouts

The universal property of the pushout of a span `S` can also be stated as a pullback-property: a cocone `c ≐ pair i (pair j H)` with vertex `X` satisfies the universal property of the pushout of `S` if and only if the square

```md
  Y^X -----> Y^B
   |          |
   |          |
   V          V
  Y^A -----> Y^S
```

is a pullback square for every type `Y`. Below, we first define the cone of this commuting square, and then we introduce the type pullback-property-pushout, which states that the above square is a pullback.

```agda
htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : f ~ g) (C : UU l3) →
  (precomp f C) ~ (precomp g C)
htpy-precomp H C h = eq-htpy (h ·l H)

compute-htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (htpy-precomp (refl-htpy' f) C) ~ refl-htpy
compute-htpy-precomp f C h = eq-htpy-refl-htpy (h ∘ f)

cone-pullback-property-pushout :
  {l1 l2 l3 l4 l : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (Y : UU l) →
  cone (λ (h : A → Y) → h ∘ f) (λ (h : B → Y) → h ∘ g) (X → Y)
pr1 (cone-pullback-property-pushout f g {X} c Y) =
  precomp (horizontal-map-cocone f g c) Y
pr1 (pr2 (cone-pullback-property-pushout f g {X} c Y)) =
  precomp (vertical-map-cocone f g c) Y
pr2 (pr2 (cone-pullback-property-pushout f g {X} c Y)) =
  htpy-precomp (coherence-square-cocone f g c) Y

pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
pullback-property-pushout l {S} {A} {B} f g {X} c =
  (Y : UU l) → is-pullback
    ( precomp f Y)
    ( precomp g Y)
    ( cone-pullback-property-pushout f g c Y)
```

## Properties

### The 3-for-2 property of pushouts

```agda
module _
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y)
  ( h : X → Y) (KLM : htpy-cocone f g (cocone-map f g c h) d)
  where

  triangle-map-cocone :
    { l6 : Level} (Z : UU l6) →
    ( cocone-map f g d) ~ ((cocone-map f g c) ∘ (λ (k : Y → Z) → k ∘ h))
  triangle-map-cocone Z k =
    inv
      ( ( cocone-map-comp f g c h k) ∙
        ( ap
          ( λ t → cocone-map f g t k)
          ( eq-htpy-cocone f g (cocone-map f g c h) d KLM)))

  is-equiv-up-pushout-up-pushout :
    ( up-c : {l : Level} → universal-property-pushout l f g c) →
    ( up-d : {l : Level} → universal-property-pushout l f g d) →
    is-equiv h
  is-equiv-up-pushout-up-pushout up-c up-d =
    is-equiv-is-equiv-precomp h
      ( λ l Z →
        is-equiv-right-factor-htpy
          ( cocone-map f g d)
          ( cocone-map f g c)
          ( precomp h Z)
          ( triangle-map-cocone Z)
          ( up-c Z)
          ( up-d Z))

  up-pushout-up-pushout-is-equiv :
    is-equiv h →
    ( up-c : {l : Level} → universal-property-pushout l f g c) →
    {l : Level} → universal-property-pushout l f g d
  up-pushout-up-pushout-is-equiv is-equiv-h up-c Z =
    is-equiv-comp-htpy
      ( cocone-map f g d)
      ( cocone-map f g c)
      ( precomp h Z)
      ( triangle-map-cocone Z)
      ( is-equiv-precomp-is-equiv h is-equiv-h Z)
      ( up-c Z)

  up-pushout-is-equiv-up-pushout :
    ( up-d : {l : Level} → universal-property-pushout l f g d) →
    is-equiv h →
    {l : Level} → universal-property-pushout l f g c
  up-pushout-is-equiv-up-pushout up-d is-equiv-h Z =
    is-equiv-left-factor-htpy
      ( cocone-map f g d)
      ( cocone-map f g c)
      ( precomp h Z)
      ( triangle-map-cocone Z)
      ( up-d Z)
      ( is-equiv-precomp-is-equiv h is-equiv-h Z)
```

### Pushouts are uniquely unique

```agda
uniquely-unique-pushout :
  { l1 l2 l3 l4 l5 : Level}
  { S : UU l1} {A : UU l2} {B : UU l3} {X : UU l4} {Y : UU l5}
  ( f : S → A) (g : S → B) (c : cocone f g X) (d : cocone f g Y) →
  ( up-c : {l : Level} → universal-property-pushout l f g c) →
  ( up-d : {l : Level} → universal-property-pushout l f g d) →
  is-contr
    ( Σ (X ≃ Y) (λ e → htpy-cocone f g (cocone-map f g c (map-equiv e)) d))
uniquely-unique-pushout f g c d up-c up-d =
  is-contr-total-Eq-subtype
    ( uniqueness-map-universal-property-pushout f g c up-c d)
    ( is-property-is-equiv)
    ( map-universal-property-pushout f g c up-c d)
    ( htpy-cocone-map-universal-property-pushout f g c up-c d)
    ( is-equiv-up-pushout-up-pushout f g c d
      ( map-universal-property-pushout f g c up-c d)
      ( htpy-cocone-map-universal-property-pushout f g c up-c d)
      ( up-c)
      ( up-d))
```

### The universal property of pushouts is equivalent to the pullback property of pushouts

In order to show that the universal property of pushouts is equivalent to the pullback property, we show that the maps `cocone-map` and the gap map fit in a commuting triangle, where the third map is an equivalence. The claim then follows from the 3-for-2 property of equivalences.

```agda
triangle-pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  {l : Level} (Y : UU l) →
  ( cocone-map f g c) ~
  ( ( tot (λ i' → tot (λ j' p → htpy-eq p))) ∘
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y)))
triangle-pullback-property-pushout-universal-property-pushout
  {S = S} {A = A} {B = B} f g c Y h =
    eq-pair-Σ refl
      ( eq-pair-Σ refl
        ( inv (issec-eq-htpy (h ·l coherence-square-cocone f g c))))

pullback-property-pushout-universal-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  universal-property-pushout l f g c → pullback-property-pushout l f g c
pullback-property-pushout-universal-property-pushout
  l f g c up-c Y =
  is-equiv-right-factor-htpy
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))
    ( up-c Y)

universal-property-pushout-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2}
  {B : UU l3} (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  pullback-property-pushout l f g c → universal-property-pushout l f g c
universal-property-pushout-pullback-property-pushout
  l f g c pb-c Y =
  is-equiv-comp-htpy
    ( cocone-map f g c)
    ( tot (λ i' → tot (λ j' p → htpy-eq p)))
    ( gap (λ h → h ∘ f) (λ h → h ∘ g) (cone-pullback-property-pushout f g c Y))
    ( triangle-pullback-property-pushout-universal-property-pushout f g c Y)
    ( pb-c Y)
    ( is-equiv-tot-is-fiberwise-equiv
      ( λ i' → is-equiv-tot-is-fiberwise-equiv
        ( λ j' → funext (i' ∘ f) (j' ∘ g))))
```

### If the vertical map of a span is an equivalence, then the vertical map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f →
  ({l : Level} → universal-property-pushout l f g c) → is-equiv (pr1 (pr2 c))
is-equiv-universal-property-pushout
  {A = A} {B} f g (pair i (pair j H)) is-equiv-f up-c =
  is-equiv-is-equiv-precomp j
    ( λ l T →
      is-equiv-is-pullback'
        ( λ (h : A → T) → h ∘ f)
        ( λ (h : B → T) → h ∘ g)
        ( cone-pullback-property-pushout f g (pair i (pair j H)) T)
        ( is-equiv-precomp-is-equiv f is-equiv-f T)
        ( pullback-property-pushout-universal-property-pushout
          l f g (pair i (pair j H)) up-c T))

equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (e : S ≃ A) (g : S → B) (c : cocone (map-equiv e) g C) →
  ({l : Level} → universal-property-pushout l (map-equiv e) g c) →
  B ≃ C
pr1 (equiv-universal-property-pushout e g c up-c) =
  vertical-map-cocone (map-equiv e) g c
pr2 (equiv-universal-property-pushout e g c up-c) =
  is-equiv-universal-property-pushout
    ( map-equiv e)
    ( g)
    ( c)
    ( is-equiv-map-equiv e)
    ( up-c)

universal-property-pushout-is-equiv :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f → is-equiv (pr1 (pr2 c)) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv f g (pair i (pair j H)) is-equiv-f is-equiv-j {l} =
  let c = (pair i (pair j H)) in
  universal-property-pushout-pullback-property-pushout l f g c
    ( λ T → is-pullback-is-equiv'
      ( λ h → h ∘ f)
      ( λ h → h ∘ g)
      ( cone-pullback-property-pushout f g c T)
      ( is-equiv-precomp-is-equiv f is-equiv-f T)
      ( is-equiv-precomp-is-equiv j is-equiv-j T))
```

### If the horizontal map of a span is an equivalence, then the horizontal map of a cocone on it is an equivalence if and only if the cocone is a pushout

```agda
is-equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g →
  ({l : Level} → universal-property-pushout l f g c) →
  is-equiv (horizontal-map-cocone f g c)
is-equiv-universal-property-pushout' f g c is-equiv-g up-c =
  is-equiv-is-equiv-precomp
    ( horizontal-map-cocone f g c)
    ( λ l T →
      is-equiv-is-pullback
        ( precomp f T)
        ( precomp g T)
        ( cone-pullback-property-pushout f g c T)
        ( is-equiv-precomp-is-equiv g is-equiv-g T)
        ( pullback-property-pushout-universal-property-pushout
          l f g c up-c T))

equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (e : S ≃ B) (c : cocone f (map-equiv e) C) →
  ({l : Level} → universal-property-pushout l f (map-equiv e) c) →
  A ≃ C
equiv-universal-property-pushout' f e c up-c =
  pair
    ( pr1 c)
    ( is-equiv-universal-property-pushout'
      ( f)
      ( map-equiv e)
      ( c)
      ( is-equiv-map-equiv e)
      ( up-c))

universal-property-pushout-is-equiv' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g → is-equiv (pr1 c) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv'
  f g (pair i (pair j H)) is-equiv-g is-equiv-i {l} =
  let c = (pair i (pair j H)) in
  universal-property-pushout-pullback-property-pushout l f g c
    ( λ T → is-pullback-is-equiv
      ( precomp f T)
      ( precomp g T)
      ( cone-pullback-property-pushout f g c T)
      ( is-equiv-precomp-is-equiv g is-equiv-g T)
      ( is-equiv-precomp-is-equiv i is-equiv-i T))
```
