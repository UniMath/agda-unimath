# The difference between integers

```agda
module elementary-number-theory.difference-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers

open import foundation.identity-types
open import foundation.interchange-law
```

</details>

# The difference between integers

Since integers of the form `x - y` occur often, we introduce them here and derive their basic properties relative to `succ-ℤ`, `neg-ℤ`, and `add-ℤ`. The file `multiplication-integers` imports `difference-integers` and more properties are derived there.

```
diff-ℤ : ℤ → ℤ → ℤ
diff-ℤ x y = add-ℤ x (neg-ℤ y)

ap-diff-ℤ : {x x' y y' : ℤ} → x ＝ x' → y ＝ y' → diff-ℤ x y ＝ diff-ℤ x' y'
ap-diff-ℤ p q = ap-binary diff-ℤ p q

eq-diff-ℤ : {x y : ℤ} → is-zero-ℤ (diff-ℤ x y) → x ＝ y
eq-diff-ℤ {x} {y} H =
  ( inv (right-unit-law-add-ℤ x)) ∙
  ( ( ap (add-ℤ x) (inv (left-inverse-law-add-ℤ y))) ∙
    ( ( inv (associative-add-ℤ x (neg-ℤ y) y)) ∙
      ( ( ap (add-ℤ' y) H) ∙
        ( left-unit-law-add-ℤ y))))

is-zero-diff-ℤ' : (x : ℤ) → is-zero-ℤ (diff-ℤ x x)
is-zero-diff-ℤ' x = right-inverse-law-add-ℤ x

is-zero-diff-ℤ :
  {x y : ℤ} → x ＝ y → is-zero-ℤ (diff-ℤ x y)
is-zero-diff-ℤ {x} {.x} refl = is-zero-diff-ℤ' x

left-zero-law-diff-ℤ : (x : ℤ) → diff-ℤ zero-ℤ x ＝ neg-ℤ x
left-zero-law-diff-ℤ x = left-unit-law-add-ℤ (neg-ℤ x)

right-zero-law-diff-ℤ : (x : ℤ) → diff-ℤ x zero-ℤ ＝ x
right-zero-law-diff-ℤ x = right-unit-law-add-ℤ x

left-successor-law-diff-ℤ :
  (x y : ℤ) → diff-ℤ (succ-ℤ x) y ＝ succ-ℤ (diff-ℤ x y)
left-successor-law-diff-ℤ x y = left-successor-law-add-ℤ x (neg-ℤ y)

right-successor-law-diff-ℤ :
  (x y : ℤ) → diff-ℤ x (succ-ℤ y) ＝ pred-ℤ (diff-ℤ x y)
right-successor-law-diff-ℤ x y =
  ap (add-ℤ x) (neg-succ-ℤ y) ∙ right-predecessor-law-add-ℤ x (neg-ℤ y)

left-predecessor-law-diff-ℤ :
  (x y : ℤ) → diff-ℤ (pred-ℤ x) y ＝ pred-ℤ (diff-ℤ x y)
left-predecessor-law-diff-ℤ x y = left-predecessor-law-add-ℤ x (neg-ℤ y)

right-predecessor-law-diff-ℤ :
  (x y : ℤ) → diff-ℤ x (pred-ℤ y) ＝ succ-ℤ (diff-ℤ x y)
right-predecessor-law-diff-ℤ x y =
  ap (add-ℤ x) (neg-pred-ℤ y) ∙ right-successor-law-add-ℤ x (neg-ℤ y)

triangle-diff-ℤ :
  (x y z : ℤ) → add-ℤ (diff-ℤ x y) (diff-ℤ y z) ＝ diff-ℤ x z
triangle-diff-ℤ x y z =
  ( associative-add-ℤ x (neg-ℤ y) (diff-ℤ y z)) ∙
  ( ap
    ( add-ℤ x)
    ( ( inv (associative-add-ℤ (neg-ℤ y) y (neg-ℤ z))) ∙
      ( ( ap (add-ℤ' (neg-ℤ z)) (left-inverse-law-add-ℤ y)) ∙
        ( left-unit-law-add-ℤ (neg-ℤ z)))))

distributive-neg-diff-ℤ :
  (x y : ℤ) → neg-ℤ (diff-ℤ x y) ＝ diff-ℤ y x
distributive-neg-diff-ℤ x y =
  ( distributive-neg-add-ℤ x (neg-ℤ y)) ∙
  ( ( ap (add-ℤ (neg-ℤ x)) (neg-neg-ℤ y)) ∙
    ( commutative-add-ℤ (neg-ℤ x) y))

interchange-law-add-diff-ℤ : interchange-law add-ℤ diff-ℤ
interchange-law-add-diff-ℤ x y u v =
  ( interchange-law-add-add-ℤ x (neg-ℤ y) u (neg-ℤ v)) ∙
  ( ap (add-ℤ (add-ℤ x u)) (inv (distributive-neg-add-ℤ y v)))

interchange-law-diff-add-ℤ : interchange-law diff-ℤ add-ℤ
interchange-law-diff-add-ℤ x y u v = inv (interchange-law-add-diff-ℤ x u y v)

left-translation-diff-ℤ :
  (x y z : ℤ) → diff-ℤ (add-ℤ z x) (add-ℤ z y) ＝ diff-ℤ x y
left-translation-diff-ℤ x y z =
  ( interchange-law-diff-add-ℤ z x z y) ∙
  ( ( ap (add-ℤ' (diff-ℤ x y)) (right-inverse-law-add-ℤ z)) ∙
    ( left-unit-law-add-ℤ (diff-ℤ x y)))

right-translation-diff-ℤ :
  (x y z : ℤ) → diff-ℤ (add-ℤ x z) (add-ℤ y z) ＝ diff-ℤ x y
right-translation-diff-ℤ x y z =
  ( ap-diff-ℤ (commutative-add-ℤ x z) (commutative-add-ℤ y z)) ∙
  ( left-translation-diff-ℤ x y z)
```

```agda
diff-succ-ℤ : (x y : ℤ) → diff-ℤ (succ-ℤ x) (succ-ℤ y) ＝ diff-ℤ x y
diff-succ-ℤ x y =
  ( ap (add-ℤ (succ-ℤ x)) (neg-succ-ℤ y)) ∙
  ( ( left-successor-law-add-ℤ x (pred-ℤ (neg-ℤ y))) ∙
    ( ( ap succ-ℤ (right-predecessor-law-add-ℤ x (neg-ℤ y))) ∙
      ( issec-pred-ℤ (diff-ℤ x y))))
```
