# Morphisms of cospan diagrams

```agda
module foundation.morphisms-cospan-diagrams where
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

A {{#concept "morphism of cospan diagrams" Agda=hom-cospan-diagram}} is a
commuting diagram of the form

```text
  A ─────> X <───── B
  │        │        │
  │        │        │
  ∨        ∨        ∨
  A' ────> X' <──── B'.
```

## Definitions

### Morphisms of cospan diagrams

```agda
hom-cospan-diagram :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X') →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l1' ⊔ l2' ⊔ l3')
hom-cospan-diagram {A = A} {B} {X} f g {A'} {B'} {X'} f' g' =
  Σ ( A → A')
    ( λ hA →
      Σ ( B → B')
        ( λ hB →
          Σ ( X → X')
            ( λ hX → (f' ∘ hA ~ hX ∘ f) × (g' ∘ hB ~ hX ∘ g))))
```

### Identity morphisms of cospan diagrams

```agda
id-hom-cospan-diagram :
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X) →
  hom-cospan-diagram f g f g
pr1 (id-hom-cospan-diagram f g) = id
pr1 (pr2 (id-hom-cospan-diagram f g)) = id
pr1 (pr2 (pr2 (id-hom-cospan-diagram f g))) = id
pr1 (pr2 (pr2 (pr2 (id-hom-cospan-diagram f g)))) = refl-htpy
pr2 (pr2 (pr2 (pr2 (id-hom-cospan-diagram f g)))) = refl-htpy
```

### Rotating cospan diagrams of cospan diagrams

```agda
cospan-hom-cospan-diagram-rotate :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan-diagram f' g' f g) (h' : hom-cospan-diagram f'' g'' f g) →
  hom-cospan-diagram (pr1 h) (pr1 h') (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
pr1
  ( cospan-hom-cospan-diagram-rotate f g f' g' f'' g''
    ( hA , hB , hX , HA , HB)
    ( hA' , hB' , hX' , HA' , HB')) = f'
pr1
  ( pr2
    ( cospan-hom-cospan-diagram-rotate f g f' g' f'' g''
      ( hA , hB , hX , HA , HB)
      ( hA' , hB' , hX' , HA' , HB'))) = f''
pr1
  ( pr2
    ( pr2
      ( cospan-hom-cospan-diagram-rotate f g f' g' f'' g''
        ( hA , hB , hX , HA , HB)
        ( hA' , hB' , hX' , HA' , HB')))) = f
pr1
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-diagram-rotate f g f' g' f'' g''
          ( hA , hB , hX , HA , HB)
          ( hA' , hB' , hX' , HA' , HB'))))) = inv-htpy HA
pr2
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-diagram-rotate f g f' g' f'' g''
          ( hA , hB , hX , HA , HB)
          ( hA' , hB' , hX' , HA' , HB'))))) = inv-htpy HA'

cospan-hom-cospan-diagram-rotate' :
  {l1 l2 l3 l1' l2' l3' l1'' l2'' l3'' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'} (f' : A' → X') (g' : B' → X')
  {A'' : UU l1''} {B'' : UU l2''} {X'' : UU l3''}
  (f'' : A'' → X'') (g'' : B'' → X'')
  (h : hom-cospan-diagram f' g' f g) (h' : hom-cospan-diagram f'' g'' f g) →
  hom-cospan-diagram
    (pr1 (pr2 h)) (pr1 (pr2 h')) (pr1 (pr2 (pr2 h))) (pr1 (pr2 (pr2 h')))
pr1
  ( cospan-hom-cospan-diagram-rotate' f g f' g' f'' g''
    ( hA , hB , hX , HA , HB)
    ( hA' , hB' , hX' , HA' , HB')) = g'
pr1
  ( pr2
    ( cospan-hom-cospan-diagram-rotate' f g f' g' f'' g''
      ( hA , hB , hX , HA , HB)
      ( hA' , hB' , hX' , HA' , HB'))) = g''
pr1
  ( pr2
    ( pr2
      ( cospan-hom-cospan-diagram-rotate' f g f' g' f'' g''
        ( hA , hB , hX , HA , HB)
        ( hA' , hB' , hX' , HA' , HB')))) = g
pr1
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-diagram-rotate' f g f' g' f'' g''
          ( hA , hB , hX , HA , HB)
          ( hA' , hB' , hX' , HA' , HB'))))) = inv-htpy HB
pr2
  ( pr2
    ( pr2
      ( pr2
        ( cospan-hom-cospan-diagram-rotate' f g f' g' f'' g''
          ( hA , hB , hX , HA , HB)
          ( hA' , hB' , hX' , HA' , HB'))))) = inv-htpy HB'
```
