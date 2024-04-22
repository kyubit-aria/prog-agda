module magic-cw where
import Relation.Binary.PropositionalEquality as Eq

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


record IsMagical {A : Set} (_∙_ : A → A → A) : Set where
  field
    left         : ∀ x y → (x ∙ y) ∙ y  ≡  x
    right        : ∀ x y → y ∙ (y ∙ x)  ≡  x


record IsCommuntative {A : Set} (_∙_ : A → A → A) : Set where
  field
    comm         : ∀ x y → x ∙ y  ≡ y ∙ x



open IsMagical
open IsCommuntative

magic-is-commutative : {A : Set}
  (_∙_ : A → A → A)
  → IsMagical _∙_
  → IsCommuntative _∙_
magic-is-commutative {A} f m = record { comm = λ x y → magic-to-comm-f x y m }
  where
    magic-to-comm-f : (x y : A) → (IsMagical f) → (f x y ≡ f y x)
    magic-to-comm-f x y record { left = l ; right = r }
      = f x y
          ≡⟨ sym (r (f x y) y) ⟩
        f y (f y (f x y))
          ≡⟨ cong (λ e → f y e) (comm (magic-is-commutative f m) y (f x y)) ⟩
        f y (f (f x y) y)
          ≡⟨ cong (λ e → f y e) (l x y) ⟩
        f y x ∎
