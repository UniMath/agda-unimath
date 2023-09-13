# Formalization of the Symmetry book - 27 sequences

```agda
module synthetic-homotopy-theory.27-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies
```

</details>

We introduce two types of sequences: one with the arrows going up and one with
the arrows going down.

```agda
Sequence :
  ( l : Level) → UU (lsuc l)
Sequence l = Σ (ℕ → UU l) (λ A → (n : ℕ) → A n → A (succ-ℕ n))

type-seq :
  { l : Level} (A : Sequence l) → (n : ℕ) → UU l
type-seq A = pr1 A

map-seq :
  { l : Level} (A : Sequence l) →
  ( n : ℕ) → (type-seq A n) → (type-seq A (succ-ℕ n))
map-seq A = pr2 A
```

### Characterizing the identity type of `Sequence`

```agda
naturality-hom-Seq :
  { l1 l2 : Level} (A : Sequence l1) (B : Sequence l2)
  ( h : (n : ℕ) → type-seq A n → type-seq B n) (n : ℕ) → UU (l1 ⊔ l2)
naturality-hom-Seq A B h n =
  ((map-seq B n) ∘ (h n)) ~ ((h (succ-ℕ n)) ∘ (map-seq A n))

equiv-Seq :
  { l1 l2 : Level} (A : Sequence l1) (B : Sequence l2) → UU (l1 ⊔ l2)
equiv-Seq A B =
  Σ ( (n : ℕ) → (type-seq A n) ≃ (type-seq B n))
    ( λ e → (n : ℕ) →
      naturality-hom-Seq A B (λ n → map-equiv (e n)) n)

reflexive-equiv-Seq :
  { l1 : Level} (A : Sequence l1) → equiv-Seq A A
reflexive-equiv-Seq A =
  pair
    ( λ n → id-equiv)
    ( λ n → refl-htpy)

equiv-eq-Seq :
  { l1 : Level} (A B : Sequence l1) → Id A B → equiv-Seq A B
equiv-eq-Seq A .A refl = reflexive-equiv-Seq A

is-contr-total-equiv-Seq :
  { l1 : Level} (A : Sequence l1) →
  is-contr (Σ (Sequence l1) (equiv-Seq A))
is-contr-total-equiv-Seq A =
  is-contr-total-Eq-structure
    ( λ B g (e : (n : ℕ) → (type-seq A n) ≃ B n) →
      (n : ℕ) → naturality-hom-Seq A (pair B g) (λ n → map-equiv (e n)) n)
    ( is-contr-total-Eq-Π
      ( λ n X → type-seq A n ≃ X)
      ( λ n → is-contr-total-equiv (type-seq A n)))
    ( pair (type-seq A) (λ n → id-equiv))
    ( is-contr-total-Eq-Π
      ( λ n h → h ~ (map-seq A n))
      ( λ n → is-contr-total-htpy' (map-seq A n)))

is-equiv-equiv-eq-Seq :
  { l1 : Level} (A B : Sequence l1) → is-equiv (equiv-eq-Seq A B)
is-equiv-equiv-eq-Seq A =
  fundamental-theorem-id
    ( is-contr-total-equiv-Seq A)
    ( equiv-eq-Seq A)

eq-equiv-Seq :
  { l1 : Level} {A B : Sequence l1} → equiv-Seq A B → Id A B
eq-equiv-Seq {A = A} {B} =
  map-inv-is-equiv (is-equiv-equiv-eq-Seq A B)
```

### Cocones on a type sequence

```agda
cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) (X : UU l2) → UU (l1 ⊔ l2)
cocone-sequence A X =
  Σ ( (n : ℕ) → type-seq A n → X) (λ i →
    (n : ℕ) → (i n) ~ ((i (succ-ℕ n)) ∘ (map-seq A n)))

map-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c : cocone-sequence A X) →
  ( n : ℕ) → type-seq A n → X
map-cocone-sequence A c = pr1 c

triangle-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c : cocone-sequence A X) →
  ( n : ℕ) →
  ( map-cocone-sequence A c n) ~
  ( (map-cocone-sequence A c (succ-ℕ n)) ∘ (map-seq A n))
triangle-cocone-sequence A c = pr2 c
```

### We characterize the identity type of `cocone-sequence`

```agda
naturality-htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1)
  {X : UU l2} (c c' : cocone-sequence A X) →
  ( H : (n : ℕ) → (map-cocone-sequence A c n) ~ (map-cocone-sequence A c' n)) →
  ( n : ℕ) → UU (l1 ⊔ l2)
naturality-htpy-cocone-sequence A c c' H n =
  ( (H n) ∙h (triangle-cocone-sequence A c' n)) ~
      ( ( triangle-cocone-sequence A c n) ∙h
        ( (H (succ-ℕ n)) ·r (map-seq A n)))

htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2}
  ( c c' : cocone-sequence A X) → UU (l1 ⊔ l2)
htpy-cocone-sequence A c c' =
  Σ ( (n : ℕ) → (map-cocone-sequence A c n) ~ (map-cocone-sequence A c' n))
    ( λ H → (n : ℕ) → naturality-htpy-cocone-sequence A c c' H n)

reflexive-htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} →
  ( c : cocone-sequence A X) → htpy-cocone-sequence A c c
reflexive-htpy-cocone-sequence A c =
  pair
    ( λ n → refl-htpy)
    ( λ n → inv-htpy-right-unit-htpy)

htpy-cocone-sequence-eq :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} →
  ( c c' : cocone-sequence A X) → Id c c' → htpy-cocone-sequence A c c'
htpy-cocone-sequence-eq A c .c refl =
  reflexive-htpy-cocone-sequence A c

is-contr-total-htpy-cocone-sequence :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c : cocone-sequence A X) →
  is-contr (Σ (cocone-sequence A X) (htpy-cocone-sequence A c))
is-contr-total-htpy-cocone-sequence A c =
  is-contr-total-Eq-structure
    ( λ j t H →
      (n : ℕ) → naturality-htpy-cocone-sequence A c (pair j t) H n)
    ( is-contr-total-Eq-Π
      ( λ n j → map-cocone-sequence A c n ~ j)
      ( λ n → is-contr-total-htpy (map-cocone-sequence A c n)))
    ( pair
      ( map-cocone-sequence A c)
      ( λ n → refl-htpy))
    ( is-contr-total-Eq-Π
      ( λ n H → H ~ ((triangle-cocone-sequence A c n) ∙h refl-htpy))
      ( λ n → is-contr-total-htpy'
        ( (triangle-cocone-sequence A c n) ∙h refl-htpy)))

is-equiv-htpy-cocone-sequence-eq :
  { l1 l2 : Level} (A : Sequence l1) {X : UU l2} (c c' : cocone-sequence A X) →
  is-equiv (htpy-cocone-sequence-eq A c c')
is-equiv-htpy-cocone-sequence-eq A c =
  fundamental-theorem-id
    ( is-contr-total-htpy-cocone-sequence A c)
    ( htpy-cocone-sequence-eq A c)
```

### The universal property of sequential colimits

```agda
cocone-sequence-map :
  { l1 l2 l3 : Level} (A : Sequence l1)
  {X : UU l2} → cocone-sequence A X →
  (Y : UU l3) → (X → Y) → cocone-sequence A Y
cocone-sequence-map A c Y h =
  pair
    ( λ n → h ∘ (map-cocone-sequence A c n))
    ( λ n → h ·l (triangle-cocone-sequence A c n))

universal-property-sequential-colimit :
  ( l : Level) {l1 l2 : Level} (A : Sequence l1) {X : UU l2}
  ( c : cocone-sequence A X) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-sequential-colimit l A c =
  (Y : UU l) → is-equiv (cocone-sequence-map A c Y)
```
