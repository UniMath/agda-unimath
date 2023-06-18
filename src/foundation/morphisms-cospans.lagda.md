# Morphisms of cospans

```agda
module foundation.morphisms-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A morphism of cospans is a commuting diagram of the form

```text
  A -----> X <----- B
  |        |        |
  |        |        |
  V        V        V
  A' ----> X' <---- B'
```

## Definitions

### Morphisms of cospans

```agda
hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l1' ⊔ l2' ⊔ l3')
hom-cospan {A = A} {B} {X} f g {A'} {B'} {X'} f' g' =
  Σ (A → A') (λ hA →
    Σ (B → B') (λ hB →
      Σ (X → X') (λ hX →
        ((f' ∘ hA) ~ (hX ∘ f)) × ((g' ∘ hB) ~ (hX ∘ g)))))
```

### Identity morphisms of cospans

```agda
id-hom-cospan :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X) →
  hom-cospan f g f g
pr1 (id-hom-cospan f g) = id
pr1 (pr2 (id-hom-cospan f g)) = id
pr1 (pr2 (pr2 (id-hom-cospan f g))) = id
pr1 (pr2 (pr2 (pr2 (id-hom-cospan f g)))) = refl-htpy
pr2 (pr2 (pr2 (pr2 (id-hom-cospan f g)))) = refl-htpy
```

### Rotating cospans of cospans

```agda
cospan-hom-cospan-rotate :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan (pr1 h) (pr1 h') (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
pr1
  ( cospan-hom-cospan-rotate f g f' g' f'' g''
    ( pair hA (pair hB (pair hX (pair HA HB))))
    ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))) = f'
pr1
  ( pr2
    ( cospan-hom-cospan-rotate f g f' g' f'' g''
      ( pair hA (pair hB (pair hX (pair HA HB))))
      ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))) = f''
pr1
  ( pr2
    ( pr2
      ( cospan-hom-cospan-rotate f g f' g' f'' g''
        ( pair hA (pair hB (pair hX (pair HA HB))))
        ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))))) = f
pr1
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HA
pr2
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HA'

cospan-hom-cospan-rotate' :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan f' g' f g) (h' : hom-cospan f'' g'' f g) →
  hom-cospan
    (pr1 (pr2 h)) (pr1 (pr2 h')) (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
pr1
  ( cospan-hom-cospan-rotate' f g f' g' f'' g''
    ( pair hA (pair hB (pair hX (pair HA HB))))
    ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))) = g'
pr1
  ( pr2
    ( cospan-hom-cospan-rotate' f g f' g' f'' g''
      ( pair hA (pair hB (pair hX (pair HA HB))))
      ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))) = g''
pr1
  ( pr2
    ( pr2
      ( cospan-hom-cospan-rotate' f g f' g' f'' g''
        ( pair hA (pair hB (pair hX (pair HA HB))))
        ( pair hA' (pair hB' (pair hX' (pair HA' HB'))))))) = g
pr1
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate' f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HB
pr2
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-rotate' f g f' g' f'' g''
          ( pair hA (pair hB (pair hX (pair HA HB))))
          ( pair hA' (pair hB' (pair hX' (pair HA' HB')))))))) = inv-htpy HB'
```
