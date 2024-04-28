# Transport along higher identifications

```agda
module foundation.transport-along-higher-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

### The action on identifications of transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  where

  tr² : (B : A → UU l2) (α : p ＝ p') (b : B x) → (tr B p b) ＝ (tr B p' b)
  tr² B α b = ap (λ t → tr B t b) α

module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  {α α' : p ＝ p'}
  where

  tr³ : (B : A → UU l2) (β : α ＝ α') (b : B x) → (tr² B α b) ＝ (tr² B α' b)
  tr³ B β b = ap (λ t → tr² B t b) β
```

### Computing 2-dimensional transport in a family of identifications with a fixed source

```agda
module _
  {l : Level} {A : UU l} {a b c : A} {q q' : b ＝ c}
  where

  tr²-Id-right :
    (α : q ＝ q') (p : a ＝ b) →
    coherence-square-identifications
      ( tr-Id-right q p)
      ( tr² (Id a) α p)
      ( left-whisker-concat p α)
      ( tr-Id-right q' p)
  tr²-Id-right α p =
    inv-nat-htpy (λ (t : b ＝ c) → tr-Id-right t p) α
```

### Coherences and algebraic identities for `tr²`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr²-concat :
    {p p' p'' : x ＝ y} (α : p ＝ p') (α' : p' ＝ p'') (b : B x) →
    (tr² B (α ∙ α') b) ＝ (tr² B α b ∙ tr² B α' b)
  tr²-concat α α' b = ap-concat (λ t → tr B t b) α α'

module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr²-left-whisker :
    (p : x ＝ y) {q q' : y ＝ z} (β : q ＝ q') (b : B x) →
    coherence-square-identifications
      ( tr-concat p q b)
      ( tr² B (left-whisker-concat p β) b)
      ( right-whisker-comp (tr² B β) (tr B p) b)
      ( tr-concat p q' b)
  tr²-left-whisker refl refl b = refl

  tr²-right-whisker :
    {p p' : x ＝ y} (α : p ＝ p') (q : y ＝ z) (b : B x) →
    coherence-square-identifications
      ( tr-concat p q b)
      ( tr² B (right-whisker-concat α q) b)
      ( left-whisker-comp (tr B q) (tr² B α) b)
      ( tr-concat p' q b)
  tr²-right-whisker refl refl b = inv right-unit
```

#### Coherences and algebraic identities for `tr³`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr³-commutative-htpy-commutative-concat :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') (b : B x) →
    coherence-square-identifications
      ( ( right-whisker-concat
          ( tr²-concat (left-whisker-concat p β)
          ( right-whisker-concat α q') b)
          ( tr-concat p' q' b)) ∙
        ( vertical-pasting-coherence-square-identifications
          ( tr-concat p q b)
          ( tr² B (left-whisker-concat p β) b)
          ( right-whisker-comp (tr² B β) (tr B p) b)
          ( tr-concat p q' b)
          ( tr² B (right-whisker-concat α q') b)
          ( left-whisker-comp (tr B q') (tr² B α) b)
          ( tr-concat p' q' b)
          ( tr²-left-whisker p β b)
          ( tr²-right-whisker α q' b)))
      ( right-whisker-concat
        ( tr³
          ( B)
          ( commutative-left-whisker-right-whisker-concat β α)
          ( b))
        ( tr-concat p' q' b))
      ( left-whisker-concat
        ( tr-concat p q b)
        ( commutative-right-whisker-left-whisker-htpy (tr² B β) (tr² B α) b))
      ( ( right-whisker-concat
          ( tr²-concat
            ( right-whisker-concat α q)
            ( left-whisker-concat p' β) b)
          ( tr-concat p' q' b)) ∙
        ( vertical-pasting-coherence-square-identifications
          ( tr-concat p q b)
          ( tr² B (right-whisker-concat α q) b)
          ( left-whisker-comp (tr B q) (tr² B α) b)
          ( tr-concat p' q b)
          ( tr² B (left-whisker-concat p' β) b)
          ( right-whisker-comp (tr² B β) (tr B p') b)
          ( tr-concat p' q' b)
          ( tr²-right-whisker α q b)
          ( tr²-left-whisker p' β b)))
  tr³-commutative-htpy-commutative-concat {q = refl} refl {p = refl} refl b =
    refl
```
