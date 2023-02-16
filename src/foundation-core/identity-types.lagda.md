#  Identity types

```agda
{-# OPTIONS --safe #-}

module foundation-core.identity-types where

open import foundation-core.constant-maps
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.universe-levels
```

## Idea

The equality relation on a type is a reflexive relation, with the universal property that it maps uniquely into any other reflexive relation. In type theory, we introduce the identity type as an inductive family of types, where the induction principle can be understood as expressing that the identity type is the least reflexive relation.

### Notation of the identity type

We include two notations for the identity type. First, we introduce the identity type using Martin-Löf's original notation `Id`. Then we introduce as a secondary option the infix notation `_＝_`.

**Note**: The equals sign in the infix notation is not the standard equals sign on your keyboard, but it is the [full width equals sign](https://www.fileformat.info/info/unicode/char/ff1d/index.htm). Note that the full width equals sign is slightly wider, and it is highlighted in blue just like all the other defined constructions in Agda. In order to type the full width equals sign in Agda emacs mode, you need to add it to your agda input method as follows:

- Type `M-x customize-variable` and press enter.
- Type `agda-input-user-translations` and press enter.
- Click the `INS` button
- Type the regular equals sign `=` in the Key sequence field.
- Click the `INS` button
- Type the full width equals sign `＝` in the translations field.
- Click the `Apply and save` button.

After completing these steps, you can type `\=` in order to obtain the full width equals sign `＝`.

## Defnition

```agda
data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

{-# BUILTIN EQUALITY Id  #-}

_＝_ : {l : Level} {A : UU l} → A → A → UU l
(a ＝ b) = Id a b
```

### The induction principle

Agda's pattern matching machinery allows us to define many operations on the identity type directly. However, sometimes it is useful to explicitly have the induction principle of the identity type.

```agda
ind-Id :
  {i j : Level} {A : UU i} (x : A) (B : (y : A) (p : x ＝ y) → UU j) →
  (B x refl) → (y : A) (p : x ＝ y) → B y p
ind-Id x B b y refl = b
```

## Structure

### Concatenation of identifications

```agda
module _
  {l : Level} {A : UU l}
  where
  
  _∙_ : {x y z : A} → x ＝ y → y ＝ z → x ＝ z
  refl ∙ q = q

  concat : {x y : A} → x ＝ y → (z : A) → y ＝ z → x ＝ z
  concat p z q = p ∙ q

  concat' : (x : A) {y z : A} → y ＝ z → x ＝ y → x ＝ z
  concat' x q p = p ∙ q
```

### Inverting identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv : {x y : A} → x ＝ y → y ＝ x
  inv refl = refl
```

### The groupoidal laws for types

```agda
module _
  {l : Level} {A : UU l}
  where
  
  assoc :
    {x y z w : A} (p : x ＝ y) (q : y ＝ z) (r : z ＝ w) →
    ((p ∙ q) ∙ r) ＝ (p ∙ (q ∙ r))
  assoc refl q r = refl

  left-unit : {x y : A} {p : x ＝ y} → (refl ∙ p) ＝ p
  left-unit = refl
  
  right-unit : {x y : A} {p : x ＝ y} → (p ∙ refl) ＝ p
  right-unit {p = refl} = refl
  
  left-inv : {x y : A} (p : x ＝ y) → ((inv p) ∙ p) ＝ refl
  left-inv refl = refl
  
  right-inv : {x y : A} (p : x ＝ y) → (p ∙ (inv p)) ＝ refl
  right-inv refl = refl
  
  inv-inv : {x y : A} (p : x ＝ y) → (inv (inv p)) ＝ p
  inv-inv refl = refl

  distributive-inv-concat :
    {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z) →
    (inv (p ∙ q)) ＝ ((inv q) ∙ (inv p))
  distributive-inv-concat refl refl = refl
```

### Concatenation is injective

```agda
module _
  {l1 : Level} {A : UU l1}
  where
  
  is-injective-concat :
    {x y z : A} (p : x ＝ y) {q r : y ＝ z} → (p ∙ q) ＝ (p ∙ r) → q ＝ r
  is-injective-concat refl s = s

  is-injective-concat' :
    {x y z : A} (r : y ＝ z) {p q : x ＝ y} → (p ∙ r) ＝ (q ∙ r) → p ＝ q
  is-injective-concat' refl s = (inv right-unit) ∙ (s ∙ right-unit)
```

### Functorial action of identity types

```agda
ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : x ＝ y) →
  (f x) ＝ (f y)
ap f refl = refl
```

### Laws for `ap`

```agda
ap-id :
  {i : Level} {A : UU i} {x y : A} (p : x ＝ y) → (ap id p) ＝ p
ap-id refl = refl

ap-comp :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (g : B → C)
  (f : A → B) {x y : A} (p : x ＝ y) → (ap (g ∘ f) p) ＝ ((ap g ∘ ap f) p)
ap-comp g f refl = refl

ap-refl :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x : A) →
  (ap f (refl {x = x})) ＝ refl
ap-refl f x = refl

ap-concat :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y z : A}
  (p : x ＝ y) (q : y ＝ z) → (ap f (p ∙ q)) ＝ ((ap f p) ∙ (ap f q))
ap-concat f refl q = refl

ap-inv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A}
  (p : x ＝ y) → (ap f (inv p)) ＝ (inv (ap f p))
ap-inv f refl = refl

ap-const :
  {i j : Level} {A : UU i} {B : UU j} (b : B) {x y : A}
  (p : x ＝ y) → (ap (const A B b) p) ＝ refl
ap-const b refl = refl  
```

### Transposing inverses

The fact that `inv-con` and `con-inv` are equivalences is recorded in `equivalences`.

```agda
inv-con :
  {i : Level} {A : UU i} {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z)
  (r : x ＝ z) → ((p ∙ q) ＝ r) → q ＝ ((inv p) ∙ r)
inv-con refl q r s = s 

con-inv :
  {i : Level} {A : UU i} {x y : A} (p : x ＝ y) {z : A} (q : y ＝ z)
  (r : x ＝ z) → ((p ∙ q) ＝ r) → p ＝ (r ∙ (inv q))
con-inv p refl r s = ((inv right-unit) ∙ s) ∙ (inv right-unit)
```

### Commuting squares of identifications

```agda
module _
  {l : Level} {A : UU l} {x y1 y2 z : A}
  where
  
  square :
    (p-left : x ＝ y1) (p-bottom : y1 ＝ z)
    (p-top : x ＝ y2) (p-right : y2 ＝ z) → UU l
  square p-left p-bottom p-top p-right =
    (p-left ∙ p-bottom) ＝ (p-top ∙ p-right)

  sq-left-whisk :
    {p1 p1' : x ＝ y1} (s : p1 ＝ p1') {q1 : y1 ＝ z} {p2 : x ＝ y2}
    {q2 : y2 ＝ z} → square p1 q1 p2 q2 → square p1' q1 p2 q2
  sq-left-whisk refl sq = sq

  sq-top-whisk :
    (p1 : x ＝ y1) (q1 : y1 ＝ z) (p2 : x ＝ y2) {p2' : x ＝ y2} (s : p2 ＝ p2')
    (q2 : y2 ＝ z) → square p1 q1 p2 q2 → square p1 q1 p2' q2
  sq-top-whisk p1 q1 p2 refl q2 sq = sq
```

### Transport

We introduce transport. The fact that `tr B p` is an equivalence is recorded in `equivalences`.

```agda
tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : x ＝ y) → B x → B y
tr B refl b = b

path-over :
  {i j : Level} {A :  UU i} (B : A → UU j) {x x' : A} (p : x ＝ x') →
  B x → B x' → UU j
path-over B p y y' = (tr B p y) ＝ y'

refl-path-over :
  {i j : Level} {A : UU i} (B : A → UU j) (x : A) (y : B x) →
  path-over B refl y y
refl-path-over B x y = refl
```

### Lifting equality to the total space

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  lift-eq-Σ :
    {x y : A} (p : x ＝ y) (b : B x) → (pair x b) ＝ (pair y (tr B p b))
  lift-eq-Σ refl b = refl
```

### laws for transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  tr-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) (b : B x) →
    tr B (p ∙ q) b ＝ tr B q (tr B p b)
  tr-concat refl q b = refl

  eq-transpose-tr :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    v ＝ (tr B p u) → (tr B (inv p) v) ＝ u
  eq-transpose-tr refl q = q

  eq-transpose-tr' :
    {x y : A} (p : x ＝ y) {u : B x} {v : B y} →
    (tr B p u) ＝ v → u ＝ (tr B (inv p) v)
  eq-transpose-tr' refl q = q

tr-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : A → C) (g : (x : A) → B x → D (f x)) {x y : A} (p : x ＝ y) (z : B x) →
  (tr D (ap f p) (g x z)) ＝ (g y (tr B p z))
tr-ap f g refl z = refl

preserves-tr :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) {i j : I} (p : i ＝ j) (x : A i) →
  f j (tr A p x) ＝ tr B p (f i x)
preserves-tr f refl x = refl

tr-Id-left :
  {l1 : Level} {A : UU l1} {a b c : A} (q : Id b c) (p : Id b a) →
  Id (tr (λ y → Id y a) q p) ((inv q) ∙ p)
tr-Id-left refl p  = refl

tr-Id-right :
  {l1 : Level} {A : UU l1} {a b c : A} (q : Id b c) (p : Id a b) →
  Id (tr (λ y → Id a y) q p) (p ∙ q)
tr-Id-right refl refl = refl

tr-const :
  {i j : Level} {A : UU i} {B : UU j} {x y : A} (p : Id x y) (b : B) →
  Id (tr (λ (a : A) → B) p b) b
tr-const refl b = refl
```

### The Mac Lane pentagon for identity types

```agda
Mac-Lane-pentagon :
  {i : Level} {A : UU i} {a b c d e : A}
  (p : a ＝ b) (q : b ＝ c) (r : c ＝ d) (s : d ＝ e) →
  let α₁ = (ap (λ t → t ∙ s) (assoc p q r))
      α₂ = (assoc p (q ∙ r) s)
      α₃ = (ap (λ t → p ∙ t) (assoc q r s))
      α₄ = (assoc (p ∙ q) r s)
      α₅ = (assoc p q (r ∙ s))
  in
  ((α₁ ∙ α₂) ∙ α₃) ＝ (α₄ ∙ α₅)
Mac-Lane-pentagon refl refl refl refl = refl
```

### The binary action on paths

```agda
ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') → (f x y) ＝ (f x' y')
ap-binary f refl refl = refl

ap-binary-diagonal :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → A → B) →
  {x x' : A} (p : x ＝ x') → (ap-binary f p p) ＝ (ap (λ a → f a a) p)
ap-binary-diagonal f refl = refl  

triangle-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  (ap-binary f p q) ＝ (ap (λ z → f z y) p ∙ ap (f x') q)
triangle-ap-binary f refl refl = refl

triangle-ap-binary' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y y' : B} (q : y ＝ y') →
  (ap-binary f p q) ＝ (ap (f x) q ∙ ap (λ z → f z y') p)
triangle-ap-binary' f refl refl = refl

left-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x : A} {y y' : B} (q : y ＝ y') →
  (ap-binary f refl q) ＝ (ap (f x) q)
left-unit-ap-binary f refl = refl

right-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : x ＝ x') {y : B} →
  (ap-binary f p refl) ＝ (ap (λ z → f z y) p)
right-unit-ap-binary f refl = refl

ap-binary-comp :
  {l1 l2 l3 l4 l5 : Level} {X : UU l4} {Y : UU l5} {A : UU l1} {B : UU l2} {C : UU l3}
  (H : A → B → C) (f : X → A) (g : Y → B) {x0 x1 : X} (p : x0 ＝ x1)
  {y0 y1 : Y} (q : y0 ＝ y1) → (ap-binary (λ x y → H (f x) (g y)) p q) ＝
  ap-binary H (ap f p) (ap g q) 
ap-binary-comp H f g refl refl = refl

ap-binary-comp-diagonal :
  {l1 l2 l3 l4 : Level} {A' : UU l4} {A : UU l1} {B : UU l2} {C : UU l3}
  (H : A → B → C) (f : A' → A) (g : A' → B) {a'0 a'1 : A'} (p : a'0 ＝ a'1) →
  (ap (λ z → H (f z) (g z)) p) ＝ ap-binary H (ap f p) (ap g p)
ap-binary-comp-diagonal H f g p =
  inv (ap-binary-diagonal (λ x y → H (f x) (g y)) p) ∙ (ap-binary-comp H f g p p)

ap-binary-comp' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : C → D) (H : A → B → C) {a0 a1 : A} (p : a0 ＝ a1) {b0 b1 : B} (q : b0 ＝ b1) →
  (ap-binary (λ a b → f (H a b)) p q) ＝ (ap f (ap-binary H p q))
ap-binary-comp' f H refl refl = refl

ap-binary-permute :
  {l1 l2 l3 : Level} {A : UU l1} {a0 a1 : A} {B : UU l2} {b0 b1 : B} {C : UU l3} (f : A → B → C) →
  (p : a0 ＝ a1) (q : b0 ＝ b1) → (ap-binary (λ y x → f x y) q p) ＝ (ap-binary f p q)
ap-binary-permute f refl refl = refl  
```

### Action on identifications of dependent functions

```agda
apd :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) {x y : A}
  (p : x ＝ y) → (tr B p (f x)) ＝ (f y)
apd f refl = refl

apd-const :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A}
  (p : Id x y) → Id (apd f p) ((tr-const p (f x)) ∙ (ap f p))
apd-const f refl = refl
```
