```agda
module synthetic-homotopy-theory.junk-delete where

open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.24-pushouts
open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```


## Definition

### Suspension of ordinary types

```agda
suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-structure X Y = Σ Y (λ N → Σ Y (λ S → (x : X) → N ＝ S))

N-suspension-structure :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (suspension-structure X Y) → Y
N-suspension-structure c = pr1 c

S-suspension-structure :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → (suspension-structure X Y) → Y
S-suspension-structure c = (pr1 ∘ pr2) c

merid-suspension-structure :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (c : suspension-structure X Y) → X → ((N-suspension-structure c) ＝ ( S-suspension-structure c))
merid-suspension-structure c = (pr2 ∘ pr2) c

suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone X Y = cocone (const X unit star) (const X unit star) Y

cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → suspension-cocone X Y
cocone-suspension-structure X Y (pair N (pair S merid)) =
  pair
    ( const unit Y N)
    ( pair
      ( const unit Y S)
      ( merid))

universal-property-suspension' :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  (susp-str : suspension-structure X Y) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension' l X Y susp-str-Y =
  universal-property-pushout l
    ( const X unit star)
    ( const X unit star)
    ( cocone-suspension-structure X Y susp-str-Y)

is-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (lsuc l ⊔ l1 ⊔ l2)
is-suspension l X Y =
  Σ (suspension-structure X Y) (universal-property-suspension' l X Y)

suspension :
  {l : Level} → UU l → UU l
suspension X = pushout (const X unit star) (const X unit star)

N-susp :
  {l : Level} {X : UU l} → suspension X
N-susp {X = X} = inl-pushout (const X unit star) (const X unit star) star

S-susp :
  {l : Level} {X : UU l} → suspension X
S-susp {X = X} = inr-pushout (const X unit star) (const X unit star) star

merid-susp :
  {l : Level} {X : UU l} → X → Id (N-susp {X = X}) (S-susp {X = X})
merid-susp {X = X} = glue-pushout (const X unit star) (const X unit star)

suspension-structure-suspension :
  {l : Level} (X : UU l) → suspension-structure X (suspension X)
pr1 (suspension-structure-suspension X) = N-susp
pr1 (pr2 (suspension-structure-suspension X)) = S-susp
pr2 (pr2 (suspension-structure-suspension X)) = merid-susp
```

## Properties

### The universal property of the suspension as a pushout

```agda
ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) → (Y → Z) → suspension-structure X Z
ev-suspension (pair N (pair S merid)) Z h =
  pair (h N) (pair (h S) (h ·l merid))

universal-property-suspension :
  (l : Level) {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-suspension l X Y susp-str-Y =
  (Z : UU l) → is-equiv (ev-suspension susp-str-Y Z)

comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z ≃ suspension-structure X Z
comparison-suspension-cocone X Z =
  equiv-Σ
    ( λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))
    ( equiv-universal-property-unit Z)
    ( λ z1 →
      equiv-Σ
        ( λ z2 → (x : X) → Id (z1 star) z2)
        ( equiv-universal-property-unit Z)
        ( λ z2 → id-equiv))

map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z → suspension-structure X Z
map-comparison-suspension-cocone X Z =
  map-equiv (comparison-suspension-cocone X Z)

is-equiv-map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (map-comparison-suspension-cocone X Z)
is-equiv-map-comparison-suspension-cocone X Z =
  is-equiv-map-equiv (comparison-suspension-cocone X Z)

triangle-ev-suspension :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (susp-str-Y : suspension-structure X Y) →
  (Z : UU l3) →
  ( ( map-comparison-suspension-cocone X Z) ∘
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X Y susp-str-Y))) ~
  ( ev-suspension susp-str-Y Z)
triangle-ev-suspension (pair N (pair S merid)) Z h = refl

is-equiv-ev-suspension :
  { l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  ( susp-str-Y : suspension-structure X Y) →
  ( up-Y : universal-property-suspension' l3 X Y susp-str-Y) → 
  ( Z : UU l3) → is-equiv (ev-suspension susp-str-Y Z)
is-equiv-ev-suspension {X = X} susp-str-Y up-Y Z =
  is-equiv-comp
    ( ev-suspension susp-str-Y Z)
    ( map-comparison-suspension-cocone X Z)
    ( cocone-map
      ( const X unit star)
      ( const X unit star)
      ( cocone-suspension-structure X _ susp-str-Y))
    ( inv-htpy (triangle-ev-suspension susp-str-Y Z))
    ( up-Y Z)
    ( is-equiv-map-comparison-suspension-cocone X Z)
```

### The suspension of a contractible type is contractible

```agda
is-contr-suspension-is-contr :
  {l : Level} {X : UU l} → is-contr X → is-contr (suspension X)
is-contr-suspension-is-contr {l} {X} is-contr-X =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-pushout (const X unit star) (const X unit star))))
    ( is-equiv-universal-property-pushout
      ( const X unit star)
      ( const X unit star)
      ( cocone-pushout
        ( const X unit star)
        ( const X unit star))
      ( is-equiv-is-contr (const X unit star) is-contr-X is-contr-unit)
      ( up-pushout (const X unit star) (const X unit star)))
    ( is-contr-unit)
```

#### Characterization of equalities in `suspension-structure`

```agda
htpy-suspension-structure : {l1 l2 : Level} {X : UU l1} {Z : UU l2} 
  (c c' : suspension-structure X Z) → UU (l1 ⊔ l2)
htpy-suspension-structure
 {X = X} c c' =
  Σ ((N-suspension-structure c) ＝ (N-suspension-structure c'))
  (λ p → Σ (( S-suspension-structure c) ＝ ( S-suspension-structure c'))
  (λ q → (x : X) → (((inv p) ∙ ( merid-suspension-structure c x)) ∙ q)
  ＝ ( merid-suspension-structure c' x)))

refl-htpy-suspension-structure : {l1 l2 : Level} {X : UU l1} {Z : UU l2} 
  {c : suspension-structure X Z} → htpy-suspension-structure c c
refl-htpy-suspension-structure = refl , (refl , (λ x → right-unit))

htpy-eq-suspension-structure : 
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} 
  {c c' : suspension-structure X Z} →
  (c ＝ c') → htpy-suspension-structure c c'
htpy-eq-suspension-structure refl = refl-htpy-suspension-structure  

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {N : Z} (S : Z) (merid : X → N ＝ S)
  where

  test'''' : (y : X → N ＝ S) →
    (merid ＝ y) ≃ ((x : X) → (merid x ∙ refl) ＝ y x)
  test'''' y = equiv-concat-htpy (λ x → right-unit) y ∘e (equiv-funext {f = merid} {g = y})
  
  test : (w : Σ Z (λ z → (X → N ＝ z))) → ((S , merid) ＝ w) ≃ (Σ (S ＝ (pr1 w)) (λ q → (x : X) → ((merid x) ∙ q) ＝ ((pr2 w) x)))
  test (S' , merid') = extensionality-Σ {Eq-A = λ z → S ＝ z}
                         (λ H q → (x : X) → (merid x ∙ q) ＝ H x) refl (λ x → right-unit) (λ x → (id , is-equiv-id)) (λ y → test'''' y) (S' , merid')

{-
  {c c' : suspension-structure X Z}
  {p : (N-suspension-structure c) ＝ (N-suspension-structure c')}
  (q : (S-suspension-structure c) ＝ (S-suspension-structure c'))
  (H : (x : X) → (((inv p) ∙ ( merid-suspension-structure c x)) ∙ q) ＝ (merid-suspension-structure c' x)

  extensionality-suspension-structure : (z : (Σ (( S-suspension-structure c) ＝ ( S-suspension-structure c'))
    (λ q → (x : X) → (((inv p) ∙ ( merid-suspension-structure c x)) ∙ q) ＝ (merid-suspension-structure c' x)))) → 
    ((q , H) ＝ z) ≃ 
  extensionality-suspension-structure = {!extensionality-Σ!} -}


suspension-structure-eq-htpy-suspension-structure' :
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c c' : suspension-structure X Z) →
  (htpy-suspension-structure c c') → c ＝ c'
suspension-structure-eq-htpy-suspension-structure' (N , S , h) (N' , S' , h') (refl , refl , H) =
  eq-pair-Σ refl (eq-pair-Σ refl
  (eq-htpy (λ x → (inv right-unit) ∙ H x)))



module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {s : suspension-structure X Z}
  where

  contr-map-htpy-suspension-structure :
    (x : Σ (suspension-structure X Z) (λ c → htpy-suspension-structure s c)) →
    (s , refl-htpy-suspension-structure) ＝ x
  contr-map-htpy-suspension-structure (c , p , q , H) = eq-pair-Σ (suspension-structure-eq-htpy-suspension-structure' s c (p , (q , H))) {!!}
  
  is-contr-htpy-suspension-structure : is-contr (Σ (suspension-structure X Z) (λ c → htpy-suspension-structure s c))
  is-contr-htpy-suspension-structure = (s , refl-htpy-suspension-structure) , {!!}
```
