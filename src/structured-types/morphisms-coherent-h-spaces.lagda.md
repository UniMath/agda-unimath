# Morphisms of coherent H-spaces

```agda
module structured-types.morphisms-coherent-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups

open import structured-types.coherent-h-spaces
open import structured-types.pointed-maps
```

</details>

## Idea

Morphisms of wild unital magmas are pointed maps that preserve the unital binary operation, including its laws.

## Definition

### Morphisms of wild unital magmas

```agda
preserves-left-unit-law-mul :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (μ : A → A → A) {eA : A} → ((x : A) → Id (μ eA x) x) →
  (ν : B → B → B) {eB : B} → ((y : B) → Id (ν eB y) y) →
  (f : A → B) → Id (f eA) eB → preserves-mul μ ν f → UU (l1 ⊔ l2)
preserves-left-unit-law-mul {A = A} {B} μ {eA} lA ν {eB} lB f p μf =
  (x : A) → Id (ap f (lA x)) (μf eA x ∙ (ap (λ t → ν t (f x)) p ∙ lB (f x)))

preserves-right-unit-law-mul :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (μ : A → A → A) {eA : A} → ((x : A) → Id (μ x eA) x) →
  (ν : B → B → B) {eB : B} → ((y : B) → Id (ν y eB) y) →
  (f : A → B) → Id (f eA) eB → preserves-mul μ ν f → UU (l1 ⊔ l2)
preserves-right-unit-law-mul {A = A} {B} μ {eA} rA ν {eB} rB f p μf =
  (x : A) → Id (ap f (rA x)) (μf x eA ∙ (ap (ν (f x)) p ∙ rB (f x)))

preserves-coh-unit-laws-mul :
  {l1 l2 : Level} (M : Coherent-H-Space l1) (N : Coherent-H-Space l2) →
  ( f : pointed-type-Coherent-H-Space M →* pointed-type-Coherent-H-Space N) →
  ( μf :
    preserves-mul (mul-Coherent-H-Space M) (mul-Coherent-H-Space N) (pr1 f)) →
  preserves-left-unit-law-mul
    ( mul-Coherent-H-Space M)
    ( left-unit-law-mul-Coherent-H-Space M)
    ( mul-Coherent-H-Space N)
    ( left-unit-law-mul-Coherent-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  preserves-right-unit-law-mul
    ( mul-Coherent-H-Space M)
    ( right-unit-law-mul-Coherent-H-Space M)
    ( mul-Coherent-H-Space N)
    ( right-unit-law-mul-Coherent-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  UU l2
preserves-coh-unit-laws-mul M
  (pair (pair N ._) μ)
  (pair f refl) μf lf rf =
  Id (ap (ap f) cM ∙ rf eM) (lf eM ∙ ap (concat (μf eM eM) (f eM)) cN)
  where
  eM = unit-Coherent-H-Space M
  cM = coh-unit-laws-mul-Coherent-H-Space M
  cN = pr2 (pr2 (pr2 μ))
```

### Second description of preservation of the coherent unit laws

```agda
preserves-coh-unit-laws-mul' :
  {l1 l2 : Level} (M : Coherent-H-Space l1) (N : Coherent-H-Space l2) →
  ( f : pointed-type-Coherent-H-Space M →* pointed-type-Coherent-H-Space N) →
  ( μf :
    preserves-mul (mul-Coherent-H-Space M) (mul-Coherent-H-Space N) (pr1 f)) →
  preserves-left-unit-law-mul
    ( mul-Coherent-H-Space M)
    ( left-unit-law-mul-Coherent-H-Space M)
    ( mul-Coherent-H-Space N)
    ( left-unit-law-mul-Coherent-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  preserves-right-unit-law-mul
    ( mul-Coherent-H-Space M)
    ( right-unit-law-mul-Coherent-H-Space M)
    ( mul-Coherent-H-Space N)
    ( right-unit-law-mul-Coherent-H-Space N)
    ( pr1 f)
    ( pr2 f)
    ( μf) →
  UU l2
preserves-coh-unit-laws-mul' M N f μf lf rf =
  Id { A =
       Id (ap (pr1 f) (lM eM) ∙ ef) ((μf eM eM ∙ ap-binary μN ef ef) ∙ rN eN)}
     ( ( horizontal-concat-Id² (lf eM) (inv (ap-id ef))) ∙
       ( ( ap
           ( λ t → t ∙ (ap id ef))
           ( inv
             ( assoc
               ( μf eM eM)
               ( ap (mul-Coherent-H-Space' N (pr1 f eM)) ef)
               ( lN (pr1 f eM))))) ∙
         ( ( assoc
             ( μf eM eM ∙ ap (mul-Coherent-H-Space' N (pr1 f eM)) ef)
             ( lN (pr1 f eM))
             ( ap id ef)) ∙
           ( ( ap
               ( λ t →
                 ( μf eM eM ∙ ap (mul-Coherent-H-Space' N (pr1 f eM)) ef) ∙ t)
               ( nat-htpy lN ef)) ∙
             ( ( inv
                 ( assoc
                   ( μf eM eM ∙ ap (mul-Coherent-H-Space' N (pr1 f eM)) ef)
                   ( ap (μN eN) ef)
                   ( lN eN))) ∙
               ( ( ap
                   ( λ t → t ∙ lN eN)
                   ( assoc
                     ( μf eM eM)
                     ( ap (mul-Coherent-H-Space' N (pr1 f eM)) ef)
                     ( ap (μN eN) ef))) ∙
                 ( horizontal-concat-Id²
                   ( ap
                     ( λ t → μf eM eM ∙ t)
                     ( inv (triangle-ap-binary μN ef ef)))
                   ( cN))))))))
     ( ( ap (λ t → t ∙ ef) (ap (ap (pr1 f)) cM)) ∙
       ( ( horizontal-concat-Id² (rf eM) (inv (ap-id ef))) ∙
         ( ( ap
             ( λ t → t ∙ ap id ef)
             ( inv
               ( assoc (μf eM eM) (ap (μN (pr1 f eM)) ef) (rN (pr1 f eM))))) ∙
           ( ( assoc
               ( μf eM eM ∙ ap (μN (pr1 f eM)) ef)
               ( rN (pr1 f eM))
               ( ap id ef)) ∙
             ( ( ap
                 ( λ t → (μf eM eM ∙ ap (μN (pr1 f eM)) ef) ∙ t)
                 ( nat-htpy rN ef)) ∙
               ( ( inv
                   ( assoc
                     ( μf eM eM ∙ ap (μN (pr1 f eM)) ef)
                     ( ap (mul-Coherent-H-Space' N eN) ef)
                     ( rN eN))) ∙
                 ( ap
                   ( λ t → t ∙ rN eN)
                   ( ( assoc
                       ( μf eM eM)
                       ( ap (μN (pr1 f eM)) ef)
                       ( ap (mul-Coherent-H-Space' N eN) ef)) ∙
                     ( ap
                       ( λ t → μf eM eM ∙ t)
                       ( inv (triangle-ap-binary' μN ef ef)))))))))))
  where
  eM = unit-Coherent-H-Space M
  μM = mul-Coherent-H-Space M
  lM = left-unit-law-mul-Coherent-H-Space M
  rM = right-unit-law-mul-Coherent-H-Space M
  cM = coh-unit-laws-mul-Coherent-H-Space M
  eN = unit-Coherent-H-Space N
  μN = mul-Coherent-H-Space N
  lN = left-unit-law-mul-Coherent-H-Space N
  rN = right-unit-law-mul-Coherent-H-Space N
  cN = coh-unit-laws-mul-Coherent-H-Space N
  ef = pr2 f

preserves-unital-mul :
  {l1 l2 : Level} (M : Coherent-H-Space l1) (N : Coherent-H-Space l2) →
  (f : pointed-type-Coherent-H-Space M →* pointed-type-Coherent-H-Space N) →
  UU (l1 ⊔ l2)
preserves-unital-mul M N f =
  Σ ( preserves-mul μM μN (pr1 f))
    ( λ μ11 →
      Σ ( preserves-left-unit-law-mul μM lM μN lN (pr1 f) (pr2 f) μ11)
        ( λ μ01 →
          Σ ( preserves-right-unit-law-mul μM rM μN rN (pr1 f) (pr2 f) μ11)
            ( λ μ10 → preserves-coh-unit-laws-mul M N f μ11 μ01 μ10)))
  where
  μM = mul-Coherent-H-Space M
  lM = left-unit-law-mul-Coherent-H-Space M
  rM = right-unit-law-mul-Coherent-H-Space M
  μN = mul-Coherent-H-Space N
  lN = left-unit-law-mul-Coherent-H-Space N
  rN = right-unit-law-mul-Coherent-H-Space N

hom-Coherent-H-Space :
  {l1 l2 : Level} (M : Coherent-H-Space l1) (N : Coherent-H-Space l2) →
  UU (l1 ⊔ l2)
hom-Coherent-H-Space M N =
  Σ ( pointed-type-Coherent-H-Space M →* pointed-type-Coherent-H-Space N)
    ( preserves-unital-mul M N)

-- Homotopies of morphisms of wild unital magmas

preserves-mul-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (μA : A → A → A) (μB : B → B → B) →
  {f g : A → B} (μf : preserves-mul μA μB f) (μg : preserves-mul μA μB g) →
  (f ~ g) → UU (l1 ⊔ l2)
preserves-mul-htpy {A = A} μA μB μf μg H =
  (a b : A) → Id (μf a b ∙ ap-binary μB (H a) (H b)) (H (μA a b) ∙ μg a b)

{-
preserves-left-unit-law-mul-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (μA : A → A → A) {eA : A} (lA : (a : A) → Id (μA eA a) a)
  (μB : B → B → B) {eB : B} (lB : (b : B) → Id (μB eB b) b)
  {f : A → B} {pf : Id (f eA) eB} (μf : preserves-mul μA μB f)
  (lf : preserves-left-unit-law-mul μA lA μB lB f pf μf)
  {g : A → B} {pg : Id (g eA) eB} (μg : preserves-mul μA μB g)
  (lg : preserves-left-unit-law-mul μA lA μB lB g pg μg) →
  {H : f ~ g} (μH : preserves-mul-htpy μA μB μf μg H) (pH : Id pf (H eA ∙ pg)) →
  UU (l1 ⊔ l2)
preserves-left-unit-law-mul-htpy μA lA μB lB μf lf μg lg μH pH = {!!}
-}
```
